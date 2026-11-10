/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollaries
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `initialize_bob_session` (Block `75`) at SPQR V1

Relocatable (`[LibsignalPlacement]` / `[LibsignalFullPlacement]`) proofs of `initialize_bob_session`
(Block `75`) at SPQR V1, composing `InitBobCutPlaced` and `InitBobPlaced` with the
`spqr::initial_state` seam at `lsmpl.base 327`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace CryptoVerification.E2E.V1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState
  (initialStateStack initialStateValue paramsAt InitialStateGhost
   initialStateResultAt initialStateOnPanic)

/-- Relocatable inner `Spec` of `spqr::initial_state` (Block `327`) at `lsLogFilterAddr`. -/
def _root_.CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) : Spec InitialStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s.sp initialStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s0.sp initialStateStack
  onPanic := fun _ s0 sf => initialStateOnPanic s0 sf

/-- Plain `subroutine_ok` seam for `spqr::initial_state` at `lsmpl.base 327`. -/
def _root_.CryptoVerification.Cli.E2E.V1.InitialStatePlacedOk [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_75 H) (lsmpl.base 327)
    (CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec A F)

/-- `withBobMemInv Φ`-guarded `subroutine_ok` seam for `spqr::initial_state` at `lsmpl.base 327`
(instantiates to `withLsCodeRoLoaded lsmpl` for `Φ = LibsignalCodeRoLoaded lsmpl` and
`withLsFrozen lsmpl` for `Φ = LibsignalFrozen lsmpl`). -/
def _root_.CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk [LibsignalPlacement]
    (Φ : Memory → Prop) (A : RustAlloc) (F : ShaCompress) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_75 H) (lsmpl.base 327)
    (withBobMemInv Φ (CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec A F))

theorem _root_.CryptoVerification.Cli.E2E.V1.initialStateMemInvPlacedOk_of_plain [LibsignalPlacement]
    (Φ : Memory → Prop) {A : RustAlloc} {F : ShaCompress} {H : LibsignalHooks}
    (h : CryptoVerification.Cli.E2E.V1.InitialStatePlacedOk A F H) :
    CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk Φ A F H := by
  refine subroutine_ok_mono h (fun _ _ _ hm => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withBobMemInv] at hm
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hm
  exact hm.2

theorem _root_.CryptoVerification.Cli.E2E.V1.initialStateMemInvPlacedOk_mono [LibsignalPlacement]
    {Φ₁ Φ₂ : Memory → Prop} (himp : ∀ m, Φ₂ m → Φ₁ m)
    {A : RustAlloc} {F : ShaCompress} {H : LibsignalHooks}
    (h : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk Φ₁ A F H) :
    CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk Φ₂ A F H := by
  refine subroutine_ok_mono h (fun _ _ s0 hm => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withBobMemInv] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hm ⊢
  exact ⟨himp s0.mem hm.1, hm.2⟩

private def bobFrameRestPlaced (sp0 : BitVec 64) (pq ck : SignalPqxdh.Bytes) : SepProp :=
  ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

private theorem bobFrameAtSpqr_entails_placed (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes)
    (hrk : rk.length = 32) :
    bobFrameAtSpqr sp0 rk pq ck ⊢
      memRegion (sp0 - 768#64) 32 ∗ bobFrameRestPlaced sp0 pq ck := by
  unfold bobFrameAtSpqr bobFrameRestPlaced
  have hlen : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hm : ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 768#64) 32 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp0 - 768#64) (bytesToBv8 rk)
  exact sepConj_mono_left hm

private theorem sub488_merge_placed (sp0 : BitVec 64) (pq ck : SignalPqxdh.Bytes)
    (hpq : pq.length = 32) (hck : ck.length = 32) :
    paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
    ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 ⊢
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 := by
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  have h104 :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ⊢ memRegion (sp0 - 488#64) 104 := by
    unfold paramsAt CryptoVerification.Cli.E2E.V1.bobSpqrParams
    simp only [hpq_len, Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    rw [ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 8) (k := 96)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 8) (k := 88)
        (b' := sp0 - 472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 472#64) (n := 4) (k := 84)
        (b' := sp0 - 468#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 468#64) (n := 4) (k := 80)
        (b' := sp0 - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 464#64) (n := 4) (k := 76)
        (b' := sp0 - 460#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 460#64) (n := 4) (k := 72)
        (b' := sp0 - 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 456#64) (n := 4) (k := 68)
        (b' := sp0 - 452#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 452#64) (n := 32) (k := 36)
        (b' := sp0 - 420#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 420#64) (n := 32) (k := 4)
        (b' := sp0 - 388#64) rfl (by bv_omega) (by decide)]
    have hm_pq : ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 452#64) 32 := by
      rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 452#64) (bytesToBv8 pq)
    have hm_ck : ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 420#64) 32 := by
      rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 420#64) (bytesToBv8 ck)
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono (pointsTo32_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono hm_pq
                    (sepConj_mono hm_ck
                      (pointsTo32_entails_memRegion _ _)))))))))
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  have hrearr :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 =
      (paramsAt (sp0 - 488#64) (sp0 - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams pq) ∗
       ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
       ((sp0 - 388#64) ↦₃₂ 0#32)) ∗ memRegion (sp0 - 384#64) 288 := by ac_rfl
  rw [hrearr]
  exact sepConj_mono_left h104

private theorem sub768_merge_280_placed (sp0 : BitVec 64) (rk pq ck : SignalPqxdh.Bytes)
    (hrk : rk.length = 32) (hpq : pq.length = 32) (hck : ck.length = 32) :
    memRegion (sp0 - 768#64) 32 ∗
    ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 672#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 668#64) 12 ∗
    ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
    ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ∗ memRegion (sp0 - 544#64) 56 ⊢
      memRegion (sp0 - 768#64) 280 := by
  have hrk_len : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  rw [ProofLib.memRegion_split' (b := sp0 - 768#64) (n := 32) (k := 248)
      (b' := sp0 - 736#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 736#64) (n := 32) (k := 216)
      (b' := sp0 - 704#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 704#64) (n := 32) (k := 184)
      (b' := sp0 - 672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 672#64) (n := 4) (k := 180)
      (b' := sp0 - 668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 668#64) (n := 12) (k := 168)
      (b' := sp0 - 656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 656#64) (n := 32) (k := 136)
      (b' := sp0 - 624#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 624#64) (n := 32) (k := 104)
      (b' := sp0 - 592#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 592#64) (n := 4) (k := 100)
      (b' := sp0 - 588#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 588#64) (n := 12) (k := 88)
      (b' := sp0 - 576#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 576#64) (n := 32) (k := 56)
      (b' := sp0 - 544#64) rfl (by bv_omega) (by decide)]
  have hm_pq736 : ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 736#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 736#64) (bytesToBv8 pq)
  have hm_ck704 : ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 704#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 704#64) (bytesToBv8 ck)
  have hm_rk656 : ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 656#64) 32 := by
    rw [← hrk_len]; exact pointsToBytes_entails_memRegion (sp0 - 656#64) (bytesToBv8 rk)
  have hm_ck624 : ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 624#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 624#64) (bytesToBv8 ck)
  have hm_pq576 : ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 576#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 576#64) (bytesToBv8 pq)
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono hm_pq736
      (sepConj_mono hm_ck704
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono hm_rk656
              (sepConj_mono hm_ck624
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (Entails.refl _)
                    (sepConj_mono hm_pq576
                      (Entails.refl _))))))))))

private theorem stack_final_eq_placed (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
    stackAt (sp0 - 768#64) Initiator.pqxdhEntryStack ∗
    memRegion (sp0 - 768#64) 280 ∗
    memRegion (sp0 - 488#64) 344 ∗
    memRegion (sp0 - 144#64) 48 ∗
    memRegion (sp0 - 96#64) 96 =
      stackAt sp0 (stageP2bStack + 0x700) := by
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_extra sp0, stackAt_initBob_entry sp0,
    ← (ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
      memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12),
    ← sepConj_assoc (memRegion (sp0 - 488#64) 344), hsplit]
  ac_rfl

private theorem sepWPp_seq_placed {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

theorem _root_.CryptoVerification.Cli.E2E.V1.initialStateFrozenPlacedOk_of_codeRoLoaded
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : LibsignalHooks}
    (h : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalCodeRoLoaded lsmpl) A F H) :
    CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalFrozen lsmpl) A F H := by
  refine subroutine_ok_mono h (fun _ _ _ hm => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withBobMemInv] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hm ⊢
  exact ⟨⟨LibsignalCodeLoaded.of_codeLoaded hm.1.2, hm.1.1⟩, hm.2⟩

private theorem call_spqr_memInv {α : Type} {prog : Program} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (withBobMemInv Φ spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, (s.mem ⊨ P ∗ (F ∗ R)) → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withBobMemInv]) :
    SepWPp prog ret s (P ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  have hm' : s.mem ⊨ (withBobMemInv Φ spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withBobMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hΦ, hpre R hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right
  · dsimp only [withBobMemInv] at hoom_post
    rw [hoom sm] at hoom_post
    exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withBobMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm
        (hkf s.mem sm.mem hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withBobMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · dsimp only [withBobMemInv] at hpost
    exact (hexit sm code _ hex hpost).elim

set_option maxHeartbeats 1200000 in
/-- Relocatable `withBobMemInv Φ` proof of `initialize_bob_session` (Block `75`) at SPQR V1 when
`Model.acceptKeys P inp = some drKey`, parameterized over `Pqxdh::accept` (`lsmpl.base 79`) and
`spqr::initial_state` (`lsmpl.base 327`). -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_memInv_placed_of_accept
    [LibsignalPlacement] {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hΦ_cl : ∀ m, Φ m → LibsignalCodeLoaded lsmpl m)
    (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A)))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk Φ A F H)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hΦ0 : Φ s0.mem)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) := by
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  let Frame1 : SepProp :=
    memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame
  have hpb3 := initBob_to_spqr_full_memInv_placed_of_accept hkf hWF h_accept s0 inp ikBPk spkBPk
    argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame1
    hΦ0 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc
  refine sepWPp_seq_placed
    (SepWPp.weaken_pre
      (Entails.of_eq (by
        dsimp only [Frame1]
        rw [CryptoVerification.Cli.E2E.V1.bobV1_stack_extra s0.sp]
        ac_rfl))
      hpb3) ?_
  intro s1 P1 hpc1 hrun1
    ⟨hent1, hΦ1, _, hsp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hx30_1, htr1, hvregs1⟩
  let FrameCall : SepProp :=
    ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
    ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
    (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
    ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    bobFrameRestPlaced s0.sp drKey.pqrKey drKey.chainKey ∗
    (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
    pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
    ((argPtr + 297#64) ↦₈ 0#8) ∗
    memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗ Frame
  have hent1_call : P1 ⊢
      (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
       ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
       memRegion (s0.sp - 768#64) 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗ stackAt s1.sp initialStateStack) ∗ FrameCall := by
    refine Entails.trans hent1 ?_
    dsimp only [Frame1, FrameCall]
    rw [CryptoVerification.Cli.E2E.V1.bobSpqrCutCells_eq_paramsAt s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey
      drKey.chainKey spkBPk inp.spkBSk hlen_pq, hsp1]
    have hrearr :
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
        bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
        pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
        ((argPtr + 297#64) ↦₈ 0#8) ∗
        memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) =
        bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
         stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack) ∗
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
         pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
         ((argPtr + 297#64) ↦₈ 0#8) ∗
         memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗ Frame) := by ac_rfl
    rw [hrearr, CryptoVerification.Cli.E2E.V1.bobV1_stack_join s0.sp]
    exact Entails.trans
      (sepConj_mono_left
        (bobFrameAtSpqr_entails_placed s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey hlen_rk))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hent1_call ?_
  let gx : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost :=
    ⟨s0.sp - 488#64, s0.sp - 768#64, s0.sp - 576#64, CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey⟩
  have hsp1_align : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]
    revert hsp0_align; bv_bits
  refine call_spqr_memInv hkf hΦ1 hinit (x := gx) (F := FrameCall)
    hpc1 hrun1 hsp1_align hx30_1
    (fun R hm => ?_)
    (fun sf code R' _ hex => ?_)
    (fun sf _ R hm => ?_)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hΦ2 => ?_)
  · dsimp only [CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec,
      CryptoVerification.Cli.E2E.V1.bobSpqrParams, gx]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hx0_1, hx8_1, hpqr_ne, ?_⟩, hm⟩
    simp [bytesToBv8, hlen_pq]
  · dsimp only [CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1
  · dsimp only [CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateOnPanic] at hm
    exact ProofLib.allowPanic_frame
      (φ := allocFailedIn s1 sf ∧ s1.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, hsub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htr1] at haf hsub
        exact ⟨haf, hsub⟩) hm
  · dsimp only [CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec,
      CryptoVerification.SpqrV1.Top.InitialState.initialStateResultAt,
      RustHeap.vecU8, gx]
    rw [hsp1, sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by
      simp only [CryptoVerification.Cli.E2E.V1.vecU8At_eq_header_bobBuf, vecHeader,
        sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      rfl)) ?_
    refine SepWPp.exists_elim fun spqrCap => SepWPp.exists_elim fun spqrBufPtr => ?_
    obtain ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, _, _, _, hx27_2, _, _, hvregs2⟩ := hcs2
    let v := initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)
    let spqrLen := BitVec.ofNat 64 v.length
    let Frame2 : SepProp :=
      CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
      ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
      ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
      ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
      memRegion (s0.sp - 588#64) 12 ∗
      ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
      memRegion (s0.sp - 544#64) 56 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
      ((argPtr + 297#64) ↦₈ 0#8) ∗
      initBobSavedRegs s0.sp s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame
    have hent2 :
        paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
        ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗
        ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 768#64) initialStateStack ∗ FrameCall ⊢
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
        ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
        ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
        memRegion (s0.sp - 488#64) 344 ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
        ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
        (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
        ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
        memRegion outPtr 344 ∗
        stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗ Frame2 := by
      dsimp only [FrameCall, Frame2, bobFrameRestPlaced]
      rw [← CryptoVerification.Cli.E2E.V1.bobV1_stack_join s0.sp,
        pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
          ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
          ((s0.sp - 768#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
          ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗
          ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
          CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool ∗
          (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack) ∗
          (((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           (((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗ ((s0.sp - 672#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 668#64) 12 ∗ ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 588#64) 12 ∗ memRegion (s0.sp - 544#64) 56 ∗
            ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
            ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
           (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
            pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗ Frame) =
          (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey) ∗
           ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
          (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
           ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
           ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           memRegion outPtr 344 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
           CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey).authKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           initBobSavedRegs s0.sp s0 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) := by
        ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left (sub488_merge_placed s0.sp drKey.pqrKey drKey.chainKey hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb1 := initBob_session_build_placed hshim halloc hdealloc hmemcpy hpanic
      s0 s2 argPtr ratchetKeyPairPtr outPtr spqrCap spqrBufPtr spqrLen
      ikBPk inp.hdr.ikAPk inp.hdr.ekAPk spkBPk inp.spkBSk drKey.rootKey drKey.chainKey Frame2
      (hΦ_cl s2.mem hΦ2)
      _h_10 hlen_ikA hlen_ekA _h_11 hlen_spkSk hlen_rk hlen_ck
      hsp0_align hrun2 hpc2 (hsp2.trans hsp1)
      (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (hx21_2.trans hx21_1)
      (hx23_2.trans hx23_1) (hx27_2.trans hx27_1) (htr2.trans htr1) (hvregs2.trans hvregs1)
    refine sepWPp_seq_placed
      (SepWPp.weaken_pre hent2 hpb1) ?_
    intro s3 P3 hpc3 hrun3
      ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
       ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
       pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
       hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
       hent3, _, _, _, hsp3, htr3, hvregs3⟩
    let sessBytes := bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    let FrameEpi : SepProp :=
      (outPtr ↦ₛ sessBytes) ∗
      CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
      bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
      A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
      A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
      A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
      stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗
      memRegion (s0.sp - 768#64) 280 ∗
      memRegion (s0.sp - 488#64) 344 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      A.pool ∗ Frame
    have hent3_epi : P3 ⊢ initBobSavedRegs s0.sp s0 ∗ FrameEpi := by
      refine Entails.trans hent3 ?_
      dsimp only [Frame2, FrameEpi, sessBytes, bobParamsFieldsAt, CryptoVerification.Cli.E2E.V1.bobSpqrParams]
      rw [pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
            spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
            pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
          memRegion (s0.sp - 768#64) 32 ∗
          ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
          ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
          ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
          memRegion (s0.sp - 488#64) 344 ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
          ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
          (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
          ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
          (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
          (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
          A.live remoteIkBoxPtr 33 1 ∗
          (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
          (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
          A.live baseKeyBoxPtr 33 1 ∗
          (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
          A.live ratchetPubBoxPtr 33 1 ∗
          (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
          (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
          stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗ A.pool ∗
          (CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           memRegion (s0.sp - 144#64) 48 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗
           initBobSavedRegs s0.sp s0 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) =
          (memRegion (s0.sp - 768#64) 32 ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56) ∗
          (initBobSavedRegs s0.sp s0 ∗
           (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
             spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
             pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
           CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr v ∗
           ((argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
             ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
             pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
            ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
           (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
           (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
           A.live remoteIkBoxPtr 33 1 ∗
           (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
           (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
           A.live baseKeyBoxPtr 33 1 ∗
           (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
           A.live ratchetPubBoxPtr 33 1 ∗
           (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
           (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
           stackAt (s0.sp - 768#64) Initiator.pqxdhEntryStack ∗
           memRegion (s0.sp - 488#64) 344 ∗
           memRegion (s0.sp - 144#64) 48 ∗
           A.pool ∗ Frame) := by ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left
          (sub768_merge_280_placed s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey
            hlen_rk hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb2 := initBob_epilogue_placed (H := H) s0 s3 FrameEpi hsp0_align hrun3 hpc3 hsp3 hvregs3
    refine SepWPp.of_sepWP_ret
      (SepWP.weaken_pre hent3_epi
        (SepWP.mono
          hpb2
          (fun sf Pf _ _ ⟨hPf, hrun_f, hpc_f, hsp_f, hcs_f, htr_f⟩ => ?_)))
    refine ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
      Entails.trans hPf (Entails.of_eq (by
        dsimp only [FrameEpi, sessBytes, spqrLen, v]
        rw [← stack_final_eq_placed s0.sp]
        ac_rfl)),
      hrun_f, hpc_f, hsp_f, hcs_f, htr_f.trans htr3⟩

/-- Specialization of `initializeBobSession_ok_v1_memInv_placed_of_accept` to
`Φ = LibsignalCodeRoLoaded lsmpl`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_placed_of_accept
    [LibsignalPlacement] {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalCodeRoLoaded lsmpl) A F H)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_memInv_placed_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk)
    (fun _ h => h.1)
    hWF hshim halloc hdealloc hmemcpy hpanic h_accept hinit
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hcro hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

/-- Specialization of `initializeBobSession_ok_v1_memInv_placed_of_accept` to
`Φ = LibsignalFrozen lsmpl`. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_frozen_placed_of_accept
    [LibsignalPlacement] {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalFrozen lsmpl) A F H)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_memInv_placed_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    (fun _ h => LibsignalCodeLoaded.of_codeLoaded h.2)
    hWF hshim halloc hdealloc hmemcpy hpanic h_accept hinit
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

/-- Closed `[LibsignalFullPlacement]` proof of `initialize_bob_session` (Block `75`) at SPQR V1,
discharging `Pqxdh::accept` (Block `79`) internally and taking only the `spqr::initial_state` seam. -/
theorem _root_.CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_full_placed
    [LibsignalFullPlacement] {P : Primitives} {C : Crypto} {A : RustAlloc} {F : ShaCompress}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hmemcpy_sess : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalCodeRoLoaded lsmpl) A F H)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ CryptoVerification.Cli.E2E.V1.bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            CryptoVerification.Cli.E2E.V1.bobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (CryptoVerification.Cli.E2E.V1.bobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0) :=
  CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_frozen_placed_of_accept
    hWF hH.noAllocShim hH.alloc hH.dealloc hmemcpy_sess hH.handleError
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)
    (CryptoVerification.Cli.E2E.V1.initialStateMemInvPlacedOk_mono
      (fun _ h => ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩) hinit)
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc

end CryptoVerification.E2E.V1
