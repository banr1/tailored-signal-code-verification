/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedA
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `Pqxdh::accept` (Block `79`), Part A: Envelope and `opk = none` Branch

Defines the deterministic allocator event list `acceptOptFieldsEvents` and envelope
`AcceptOptFieldsEnv` across all branches of Block `79`, proves `pqxdhAccept_opt_fields_opk_none_placed_ok`
on `lsProg_79 H` under `[LibsignalFullPlacement]` and `RustCliAllocBudget M`, and discharges Block
`207` `PrivateKey::calculate_agreement` from `AgreeBudget.calculateAgreement_placed_ok`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  noAllocShimSpec framelessMemcpySpec lsMemcpySym calculateAgreementSpec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding
  PqxdhHkdfExtractPlacedOk PqxdhHkdfExpandMultiInfoPlacedOk
  pqxdhHkdfExtractNonePlacedSpec pqxdhHkdfExtractSomePlacedSpec pqxdhHkdfExpandCellsPlacedSpec
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding
  Bytes acceptCalculateAgreementPlacedBaseSpec calculateAgreementStack
  ecPubKeyIsCanonicalCallSpec pqxdhAcceptOptFieldsInnerPlacedSpec
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget VmPreserved coarseCostModel coarseStep coarseStepReserve fitsEvents_append
  rustAllocEvents rustDeallocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget (
  PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
  pqxdhHkdfExpandCellsPlacedSpec pqxdhHkdfExtractNonePlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  SepWPp_call_hag_placed
  acceptCalculateAgreementPlacedBaseSpec calculateAgreementEvents
  ecPubKeyIsCanonicalCallSpec pqxdhAcceptOptFieldsInnerPlacedSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpySpec noAllocShimSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget (calculateAgreement_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  CalculateAgreementEnv calculateAgreementSpec
)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

/-! ## 1. Exact Allocator Event List, Envelope, & Hook Specs for Block `79` -/

/-- `VmPreserved`-strengthened contract for `libcrux_ml_kem::mlkem1024::kyber::decapsulate`. -/
def kyberDecapsStubBudgetSpec (P : Primitives) : Spec KyberDecapsCall :=
  withVmPreserved (kyberDecapsStubSpec P)

/-- Exact deterministic `AllocEvent` list emitted by `Pqxdh::accept` (Block `79`) across all
branches (`!isCanonical`, `dh1..dh3` zero-secret rejections, `opk = none`, and `opk = some`
rejection/acceptance, including the `32`-byte ML-KEM shared-secret `Box<[u8]>` cycle). -/
def acceptOptFieldsEvents (P : Primitives) (inp : AcceptKeysInput) : List AllocEvent :=
  if !P.isCanonical inp.hdr.ekAPk then
    rustAllocEvents 28 1
  else
    let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
    if P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0 then
      rustAllocEvents 192 1 ++ rustDeallocEvents 192 1
    else if P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0 then
      rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1
    else if P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0 then
      rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1
    else
      match inp.opkBSk? with
      | none =>
        rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
          rustDeallocEvents 192 1
      | some opkSk =>
        if P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0 then
          rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1
        else
          rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
            rustDeallocEvents 192 1

/-- Allocator event envelope for `Pqxdh::accept` (Block `79`). -/
def AcceptOptFieldsEnv (P : Primitives) (inp : AcceptKeysInput) (evs : List AllocEvent) : Prop :=
  evs = acceptOptFieldsEvents P inp

theorem fitsEnv_acceptOptFieldsEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (P : Primitives) (inp : AcceptKeysInput) :
    FitsEnv M lim st (AcceptOptFieldsEnv P inp) ↔
      FitsEvents M lim st (acceptOptFieldsEvents P inp) :=
  FitsEnv.eq_iff

example :
    FitsEvents coarseCostModel ⟨64, 67108864, 536870912, true⟩ coarseCostModel.init
      (rustAllocEvents 28 1) ∧
    FitsEvents coarseCostModel ⟨64, 67108864, 536870912, true⟩ coarseCostModel.init
      (let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
       rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
         rustDeallocEvents 192 1) := by
  have hevs1 : rustAllocEvents 28 1 = [.alloc 28] := by decide
  have hevs2 :
      (let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
       rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
         rustDeallocEvents 192 1) =
      [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
       .alloc 32, .free 1 32, .alloc 32, .free 1 32,
       .alloc 32, .free 1 32, .free 1 192] := by decide
  rw [hevs1, hevs2]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

attribute [local irreducible] FitsEvents

private theorem sepWPp_alloc_post {M : AllocCostModel} {prog : Program} {ret : BitVec 64}
    {s_pre s : State} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sp sp' : BitVec 64} {size align : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hsp : sp = sp')
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 → (s.readReg64 (.gpr 0#5)).toNat % align = 0 →
      s.trace = s_pre.trace →
      SepWPp prog ret s
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
          stackAt sp' allocHookStack ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp)
    (hne : s.readReg64 (.gpr 0#5) ≠ 0#64 := by assumption)
    (hal : (s.readReg64 (.gpr 0#5)).toNat % align = 0 := by omega)
    (hacp : AllocCallPreserved s_pre s := by assumption) :
    SepWPp prog ret s
      (A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
        stackAt sp allocHookStack ∗
        A.live (s.readReg64 (.gpr 0#5)) size align ∗
        memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp := by
  subst hsp
  exact hok hne hal hacp.2.1

/-- `pqxdhAcceptOptFieldsInnerPlacedSpec` specialized to `AcceptOptFieldsEnv P` and restricted to
`g.inp.opkBSk? = none`. -/
def pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AcceptFieldsCallGhost × M.σ) :=
  { pqxdhAcceptOptFieldsInnerPlacedSpec P A lim (AcceptOptFieldsEnv P) with
    pre := fun (g, st) s =>
      ⌜g.inp.opkBSk? = none⌝ ∗
        (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim (AcceptOptFieldsEnv P)).pre (g, st) s }

private theorem hookSat_noAllocShim_of_rustAllocShimVm {H : LibsignalHooks}
    (h : HookSat H Keys.lsRustNoAllocShimSym rustAllocShimVmSpec) :
    HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec := by
  refine HookSat.mono h fun u R s0 hp => ⟨u, R, hp, fun sf hq => ?_⟩
  dsimp only [rustAllocShimVmSpec, noAllocShimSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hq.1.1.2.1, hq.1.2⟩, hq.2⟩

private theorem hookSat_framelessMemcpy_of_allocMemcpyVm {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym framelessMemcpySpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [framelessMemcpySpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec,
    allocMemcpyVmSpec] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hq => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    rwa [sepConj_assoc]
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0f, hacp.2.1, hvm⟩, ?_⟩
    rwa [← sepConj_assoc]

/-! ## 2. Budget-Threaded `opk = none` Proof on Block `79` -/

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem toUTF8_data_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [List.utf8Encode]

private theorem incomingBaseKeyInvalidBytes_eq_list :
    incomingBaseKeyInvalidBytes =
      bytesToBv8 ("incoming base key is invalid".toList.flatMap String.utf8EncodeChar) := by
  unfold incomingBaseKeyInvalidBytes
  rw [toUTF8_data_toList]

private theorem infoPqxdh_eq_list :
    infoPqxdh =
      "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toList.flatMap String.utf8EncodeChar := by
  unfold infoPqxdh
  exact toUTF8_data_toList "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"

private theorem infoPqxdh_eq_INFO_PQXDH : infoPqxdh = INFO_PQXDH := by
  rw [infoPqxdh, INFO_PQXDH, byteArray_toList_eq_data]

private theorem lsroCheck_incomingBaseKeyInvalid :
    lsroCheck "libsignal_protocol:.rodata..Lanon.393" incomingBaseKeyInvalidBytes = true := by
  rw [incomingBaseKeyInvalidBytes_eq_list]
  exact eagerReduce (Eq.refl true)

private theorem lsroCheck_infoPqxdh_accept :
    lsroCheck "libsignal_protocol:.rodata..Lanon.352" (bytesToBv8 infoPqxdh) = true := by
  rw [infoPqxdh_eq_list]
  exact eagerReduce (Eq.refl true)

private theorem infoPqxdh_len_bv : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by
  rw [← infoPqxdh_eq_INFO_PQXDH, infoPqxdh_eq_list]
  rfl

private theorem sepWP_instantiate_ro2_post_exists {α : Type _} {prog : Program}
    {target_pc : BitVec 64} {s : State} {P L₁ L₂ R : SepProp} {Q : State → α → SepProp}
    {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (L₁ ∗ (L₂ ∗ Q sf w)) ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (L₁ ∗ (L₂ ∗ (∃∗ a, Q sf a))) ∗ R) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (Entails.sepExists_intro w))))
      (h1 hm), h2⟩

set_option maxHeartbeats 8000000 in
/-- Relocatable budget-threaded `Pqxdh::accept` (Block `79`) on the `g.inp.opkBSk? = none` branch
under `[LibsignalFullPlacement]`. -/
theorem pqxdhAccept_opt_fields_opk_none_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubBudgetSpec P)) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec P A lim)) := by
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) lsroCheck_incomingBaseKeyInvalid ?_
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.352")
    (roBytes := bytesToBv8 infoPqxdh) lsroCheck_infoPqxdh_accept ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := subroutine_ok_allocNoOom_of_budget (hook_ok_79_of_mem h_alloc (by decide))
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  have hdecaps := hook_ok_79_of_mem h_decaps (by decide)
  have hext_none := h_hkdf_extract.1
  have hexp' := h_hkdf_expand 12
  simp only [rustCliDeallocBudgetSpec, AllocCallPreserved] at hdealloc
  simp only [kyberDecapsStubBudgetSpec, withVmPreserved, kyberDecapsStubSpec] at hdecaps
  simp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec] at hext_none
  simp only [pqxdhHkdfExpandCellsPlacedSpec] at hexp'
  simp only [withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec,
    cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  clear h_shim h_alloc h_dealloc h_memcpy h_decaps h_hkdf_extract h_hkdf_expand
  unfold withLsFrozen withRoSlice pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec
    pqxdhAcceptOptFieldsInnerPlacedSpec
  wpp_init x s0
  rcases x with ⟨⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩, st⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  have hopk_none_in : inp.opkBSk? = none := ‹_›
  have hfits_env : FitsEnv M lim st (AcceptOptFieldsEnv P inp) := ‹_›
  have hfits_all : FitsEvents M lim st (acceptOptFieldsEvents P inp) :=
    (fitsEnv_acceptOptFieldsEnv_iff P inp).mp hfits_env
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  unfold pqxdhAcceptOptFieldsAt
  refine SepWPp.of_sepWP_lsfull hF0 (mid := lsmpl.base 202) ?_
  wp_steps_sync_pool (lsmpl.base 202)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF0_1; try simp only [arm64_norm] at hF0_1
  refine SepWPp.of_sepWP_lsfull hF0_1 (mid := (blkPl_79).base + 52#64) ?_
  have hcanon0 := subroutine_ok_withMemEq_of_withCodeLoaded
    (spec := ecPubKeyIsCanonicalCallSpec P) h_canon hF0_1.code
  simp only [ecPubKeyIsCanonicalCallSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpec] at hcanon0
  wp_call hcanon0 ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hacc_none : Initiator.Model.acceptKeys P inp = none :=
      acceptKeys_eq_none_of_not_canonical P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
        hikAPk hekAPk hcanon_b
    have hevs_eq : acceptOptFieldsEvents P inp = rustAllocEvents 28 1 := by
      simp [acceptOptFieldsEvents, hcanon_b]
    have hfits28 : FitsEvents M lim st (rustAllocEvents 28 1) := hevs_eq ▸ hfits_all
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := (blkPl_79).base + 216#64) ?_
    wp_steps_sync_pool (lsρ Keys.lsRustNoAllocShimSym)
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
    wp_steps_sync_pool (lsρ Keys.lsRustAllocSym)
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrl28 : LibsignalBinary.Heap.RustLayoutOk 28 1 :=
      ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    wp_call halloc (28, 1, st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      fun halloc0 halign0 htr0 => ?_
    refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
      (by sep_focus) ?_; sep_elim_exists'
    refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
    sep_elim_exists'
    refine SepWPp.fold
      (Entails.of_eq (rodata_incoming_split1 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
      (by sep_focus) ?_
    apply SepWPp.of_sepWP_ret
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    apply sepWP_seg_ls_vm (Q := (blkPC_79).rebase (blkPl_79).base (hooksException H))
      blkLib_eq_79 (mid := s0.readReg64 Reg.lr)
    intro _m_strip
    wp_steps
    refine SepWP.fold
      (Entails.of_eq (rodata_incoming_1_to_2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
      (by sep_focus) ?_
    wp_steps
    refine SepWP.fold
      (Entails.of_eq (rodata_incoming_split2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")).symm)
      (by sep_focus) ?_
    refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_
    sep_elim_exists'; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    refine SepWP.fold (err28_anyHeap_intro A.repAlloc _ _ _)
      (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus) ?_
    refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
      _ _ _ _ (by decide)) (by sep_focus) ?_
    refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
    refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
    · simp only [arm64_norm, *]
    refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
    rw [hacc_none]
    have henv_out : AcceptOptFieldsEnv P inp (rustAllocEvents 28 1) := hevs_eq.symm
    clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
    refine sepWP_instantiate_ro2_post_exists (rustAllocEvents 28 1) ?_
    simp only [sepConj_assoc, *]; wp_done
  · have hsp_align_eq : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
    have hsp_orr1 : (s0.sp - 4912#64) ||| 1#64 = s0.sp - 4911#64 := sp_sub4912_orr_one hsp_align_eq
    have hsp_orr2 : (s0.sp - 1744#64) ||| 1#64 = s0.sp - 1743#64 := sp_sub1744_orr_one hsp_align_eq
    obtain ⟨ss, hss, hss_len, hfit_ss⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hdecaps_some : (P.kemDecaps inp.pqspkBSk inp.hdr.kemCt).isSome = true := by simp [hss]
    have hss_bv_len : (bytesToBv8 ss).length = 32 := by simp [bytesToBv8, hss_len]
    have hpqSk_drop_len : ((bytesToBv8 inp.pqspkBSk).drop 1).length = 3167 := by
      simp [bytesToBv8, hpqSk]
    have hkemCt_drop_len : ((bytesToBv8 inp.hdr.kemCt).drop 1).length = 1567 := by
      simp [bytesToBv8, hkemCt]
    obtain ⟨s0_w, s1_w, s2_w, s3_w, -, hss_cells⟩ := exists_unpack64_of_length_32 hss_bv_len
    have hro_dbf : infoPqxdh = INFO_PQXDH := infoPqxdh_eq_INFO_PQXDH
    have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := infoPqxdh_len_bv
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    have hcanon_keep : AcceptCanonTrue P inp := ⟨hcanon_b⟩
    simp only [hcanon_ec, ↓reduceIte] at *
    clear hcanon_b hcanon_ec
    have hcanon_b : P.isCanonical inp.hdr.ekAPk = true := hcanon_keep.out
    clear hcanon_keep
    have hfits192 : FitsEvents M lim st (rustAllocEvents 192 1) := by
      unfold acceptOptFieldsEvents at hfits_all
      simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfits_all
      split_ifs at hfits_all with hd1 hd2 hd3
      · exact ((fitsEvents_append M lim _ _ st).mp hfits_all).1
      · rw [List.append_assoc] at hfits_all
        exact ((fitsEvents_append M lim _ _ st).mp hfits_all).1
      · rw [List.append_assoc, List.append_assoc] at hfits_all
        exact ((fitsEvents_append M lim _ _ st).mp hfits_all).1
      · simp only [hopk_none_in] at hfits_all
        rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at hfits_all
        exact ((fitsEvents_append M lim _ _ st).mp hfits_all).1
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps_sync_pool (lsρ Keys.lsRustNoAllocShimSym)
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
    wp_steps_sync_pool (lsρ Keys.lsRustAllocSym)
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrl192 : LibsignalBinary.Heap.RustLayoutOk 192 1 :=
      ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    wp_call halloc (192, 1, st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      fun halloc192 halign192 htr192 => ?_
    let st_192 := M.stepEvents (rustAllocEvents 192 1) st
    have hfits_ag1 : FitsEvents M lim st_192 (calculateAgreementEvents P inp.spkBSk inp.hdr.ikAPk) := by
      unfold acceptOptFieldsEvents at hfits_all
      simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfits_all
      by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
      · exact of_eq_true (by
          simp only [calculateAgreementEvents, hd1, ↓reduceIte]
          exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
      · simp only [calculateAgreementEvents, hd1, ↓reduceIte] at hfits_all ⊢
        split_ifs at hfits_all with hd2 hd3
        · rw [List.append_assoc, List.append_assoc] at hfits_all
          exact ((fitsEvents_append M lim _ _ st_192).mp
            ((fitsEvents_append M lim (rustAllocEvents 192 1) _ st).mp hfits_all).2).1
        · rw [List.append_assoc, List.append_assoc, List.append_assoc] at hfits_all
          exact ((fitsEvents_append M lim _ _ st_192).mp
            ((fitsEvents_append M lim (rustAllocEvents 192 1) _ st).mp hfits_all).2).1
        · simp only [hopk_none_in] at hfits_all
          rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
            List.append_assoc] at hfits_all
          exact ((fitsEvents_append M lim _ _ st_192).mp
            ((fitsEvents_append M lim (rustAllocEvents 192 1) _ st).mp hfits_all).2).1
    refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
    sep_elim_exists'
    refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
    refine SepWPp.of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_
    wp_steps_sync_pool (lsmpl.base 207)
    refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF3; try simp only [arm64_norm] at hF3
    refine SepWPp_call_hag_placed hWF h_agree hF3.to_frozen
      (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
      (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
      (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk, hfits_ag1⟩
      (by sep_focus)
      (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 _hfr1 => ?_)
      (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hfr4 => ?_)
    · have hacc_none : Initiator.Model.acceptKeys P inp = none :=
        acceptKeys_eq_none_of_dh1_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true› hikAPk
          hekAPk hcanon_b hdh1
      have hevs_eq :
          acceptOptFieldsEvents P inp = rustAllocEvents 192 1 ++ rustDeallocEvents 192 1 := by
        simp [acceptOptFieldsEvents, hcanon_b, hdh1]
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
      rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
        hcs29, hvregs1⟩
      simp only [arm64_norm]
        at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
      refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
      wp_steps_sync_pool (lsρ acceptRustDeallocSym)
      wp_call hdealloc (_, 192, 1, st_192)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
      refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
        0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      rw [hacc_none]
      have hst_eq :
          M.stepEvents (rustDeallocEvents 192 1) st_192 =
            M.stepEvents (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) st := by
        dsimp only [st_192]; rw [← M.stepEvents_append]
      rw [hst_eq]
      have henv_out :
          AcceptOptFieldsEnv P inp (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) :=
        hevs_eq.symm
      clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
      refine sepWP_instantiate_ro2_post_exists (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) ?_
      simp only [sepConj_assoc, *]; wp_done
    · have hF4 : LsFullFrozenInv lsmpl sf1 := LsFullFrozenInv.of_frozen hfr4
      have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
      have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
        simp [bytesToBv8, hdh1_len]
      have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
        simp [F_X25519, hdh1_len]
      let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
      let st_dh1_a := M.stepEvents (rustAllocEvents 32 1) st_192
      let st_dh1 := M.stepEvents (rustDeallocEvents 32 1) st_dh1_a
      have hst_dh1_eq : st_dh1 = M.stepEvents (rustAllocEvents 192 1 ++ dhCycle) st := by
        dsimp only [st_dh1, st_dh1_a, st_192, dhCycle]
        rw [← M.stepEvents_append, ← M.stepEvents_append]
      have hfits_ag2 : FitsEvents M lim st_dh1 (calculateAgreementEvents P inp.ikBSk inp.hdr.ekAPk) := by
        unfold acceptOptFieldsEvents at hfits_all
        simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, ↓reduceIte] at hfits_all
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · exact of_eq_true (by
            simp only [calculateAgreementEvents, hd2, ↓reduceIte]
            exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
        · simp only [calculateAgreementEvents, hd2, ↓reduceIte] at hfits_all ⊢
          rw [hst_dh1_eq]
          split_ifs at hfits_all with hd3
          · have h1 := ((fitsEvents_append M lim (rustAllocEvents 192 1 ++ dhCycle) _ st).mp
              (by dsimp only [dhCycle]; simpa only [List.append_assoc] using hfits_all)).2
            exact ((fitsEvents_append M lim (rustAllocEvents 32 1) _ _).mp
              (by dsimp only [dhCycle] at h1; simpa only [List.append_assoc] using h1)).1
          · simp only [hopk_none_in] at hfits_all
            have h1 := ((fitsEvents_append M lim (rustAllocEvents 192 1 ++ dhCycle) _ st).mp
              (by dsimp only [dhCycle]; simpa only [List.append_assoc] using hfits_all)).2
            exact ((fitsEvents_append M lim (rustAllocEvents 32 1) _ _).mp
              (by dsimp only [dhCycle] at h1; simpa only [List.append_assoc] using h1)).1
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
      rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
        hcs29, hvregs1⟩
      simp only [arm64_norm]
        at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
      refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_
      wp_steps_sync_pool (lsρ lsMemcpySym)
      wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩
      refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
      wp_steps_sync_pool (lsρ acceptRustDeallocSym)
      refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
        (by sep_focus) ?_
      wp_call hdealloc (dh1_ptr, 32, 1, st_dh1_a)
      wp_steps_sync_pool (lsmpl.base 207)
      refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
        inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
      refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF5; try simp only [arm64_norm] at hF5
      refine SepWPp_call_hag_placed hWF h_agree hF5.to_frozen
        (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
        (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
        (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
        (ret_pc := (blkPl_79).base + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk, hfits_ag2⟩
        (by sep_focus)
        (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 _hfr2 => ?_)
        (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hfr6 => ?_)
      · have hacc_none : Initiator.Model.acceptKeys P inp = none :=
          acceptKeys_eq_none_of_dh2_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
            hikAPk hekAPk hcanon_b hdh1 hdh2
        have hevs_eq :
            acceptOptFieldsEvents P inp =
              rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1 := by
          simp only [acceptOptFieldsEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2,
            ↓reduceIte, dhCycle]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
        rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
          hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
        simp only [arm64_norm]
          at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
             hcs2_29 hvregs2
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
        apply SepWPp.of_sepWP_ret
        wp_steps_sync_pool (lsρ acceptRustDeallocSym)
        wp_call hdealloc (_, 192, 1, st_dh1)
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
        refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
          0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        rw [hacc_none]
        have hst_eq :
            M.stepEvents (rustDeallocEvents 192 1) st_dh1 =
              M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) st := by
          rw [hst_dh1_eq, ← M.stepEvents_append]
        rw [hst_eq]
        have henv_out :
            AcceptOptFieldsEnv P inp
              (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) :=
          hevs_eq.symm
        clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
        refine sepWP_instantiate_ro2_post_exists
          (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) ?_
        simp only [sepConj_assoc, *]; wp_done
      · have hF6 : LsFullFrozenInv lsmpl sf2 := LsFullFrozenInv.of_frozen hfr6
        have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
        have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
          simp [bytesToBv8, hdh2_len]
        have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
          P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
        let st_dh2_a := M.stepEvents (rustAllocEvents 32 1) st_dh1
        let st_dh2 := M.stepEvents (rustDeallocEvents 32 1) st_dh2_a
        have hst_dh2_eq :
            st_dh2 = M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle) st := by
          dsimp only [st_dh2, st_dh2_a]
          rw [hst_dh1_eq, ← M.stepEvents_append, ← M.stepEvents_append]
        have hfits_ag3 :
            FitsEvents M lim st_dh2 (calculateAgreementEvents P inp.spkBSk inp.hdr.ekAPk) := by
          unfold acceptOptFieldsEvents at hfits_all
          simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2, ↓reduceIte]
            at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · exact of_eq_true (by
              simp only [calculateAgreementEvents, hd3, ↓reduceIte]
              exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
          · simp only [calculateAgreementEvents, hd3, hopk_none_in, ↓reduceIte] at hfits_all ⊢
            rw [hst_dh2_eq]
            have h1 := ((fitsEvents_append M lim
                (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle) _ st).mp
              (by dsimp only [dhCycle]; simpa only [List.append_assoc] using hfits_all)).2
            exact ((fitsEvents_append M lim (rustAllocEvents 32 1) _ _).mp
              (by dsimp only [dhCycle] at h1 ⊢; simpa only [List.append_assoc] using h1)).1
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
        rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
          hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
        simp only [arm64_norm]
          at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
             hcs2_29 hvregs2
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_
        wp_steps_sync_pool (lsρ lsMemcpySym)
        wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩
        refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
        wp_steps_sync_pool (lsρ acceptRustDeallocSym)
        refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
          (by sep_focus) ?_
        wp_call hdealloc (dh2_ptr, 32, 1, st_dh2_a)
        wp_steps_sync_pool (lsmpl.base 207)
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
          P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
          (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF7; try simp only [arm64_norm] at hF7
        refine SepWPp_call_hag_placed hWF h_agree hF7.to_frozen
          (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
          (ret_pc := (blkPl_79).base + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk,
            hfits_ag3⟩
          (by sep_focus)
          (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 _hfr3 => ?_)
          (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hfr8 => ?_)
        · have hacc_none : Initiator.Model.acceptKeys P inp = none :=
            acceptKeys_eq_none_of_dh3_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
              hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
          have hevs_eq :
              acceptOptFieldsEvents P inp =
                rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1 := by
            simp only [acceptOptFieldsEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1,
              hdh2, hdh3, ↓reduceIte, dhCycle]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
          rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
            hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
          simp only [arm64_norm]
            at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
               hcs3_29 hvregs3
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret
          wp_steps_sync_pool (lsρ acceptRustDeallocSym)
          wp_call hdealloc (_, 192, 1, st_dh2)
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
          refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
            0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
            (by sep_focus) ?_; rw [hacc_none]
          have hst_eq :
              M.stepEvents (rustDeallocEvents 192 1) st_dh2 =
                M.stepEvents
                  (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) st := by
            rw [hst_dh2_eq, ← M.stepEvents_append]
          rw [hst_eq]
          have henv_out :
              AcceptOptFieldsEnv P inp
                (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) :=
            hevs_eq.symm
          clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
          refine sepWP_instantiate_ro2_post_exists
            (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) ?_
          simp only [sepConj_assoc, *]; wp_done
        · have hF8 : LsFullFrozenInv lsmpl sf3 := LsFullFrozenInv.of_frozen hfr8
          have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh3_len]
          have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
            by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
          rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
            hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
          simp only [arm64_norm]
            at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
               hcs3_29 hvregs3
          cases hopk_eq : inp.opkBSk? with
          | some _ => simp [hopk_eq] at hopk_none_in
          | none =>
            let st_dh3_a := M.stepEvents (rustAllocEvents 32 1) st_dh2
            let st_dh3 := M.stepEvents (rustDeallocEvents 32 1) st_dh3_a
            have hst_dh3_eq :
                st_dh3 =
                  M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle) st := by
              dsimp only [st_dh3, st_dh3_a]
              rw [hst_dh2_eq, ← M.stepEvents_append, ← M.stepEvents_append]
            have hevs_eq :
                acceptOptFieldsEvents P inp =
                  rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1 := by
              simp only [acceptOptFieldsEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1,
                hdh2, hdh3, hopk_eq, ↓reduceIte, dhCycle]
            have hfits_ss32 : FitsEvents M lim st_dh3 (rustAllocEvents 32 1) := by
              have h0 :
                  FitsEvents M lim st
                    (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                      rustDeallocEvents 192 1) :=
                hevs_eq ▸ hfits_all
              rw [hst_dh3_eq]
              have h1 := ((fitsEvents_append M lim
                  (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle) _ st).mp
                (by dsimp only [dhCycle] at h0 ⊢; simpa only [List.append_assoc] using h0)).2
              exact ((fitsEvents_append M lim (rustAllocEvents 32 1) _ _).mp
                (by dsimp only [dhCycle] at h1 ⊢; simpa only [List.append_assoc] using h1)).1
            have hikm160_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
              ss).length = 160 := by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hss_len]
            have hikm160_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
              ss).length = 160#64 := by rw [hikm160_len]
            have hacc_some : Initiator.Model.acceptKeys P inp = some (Initiator.Model.deriveDRKeys P
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)) :=
              acceptKeys_eq_some_of_opk_none P inp ss ‹inp.trustedPeer = true›
                ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hss
            have hprk160_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
              P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
              P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss))).length = 32 := by
              simp [bytesToBv8, hkdfExtractRef_length]
            have hprk160_len32 : (hkdfExtractRef P none (F_X25519 ++
              P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
              P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)).length = 32 :=
              hkdfExtractRef_length P none _
            obtain ⟨p0, p1, p2, p3, -, hprk160⟩ := exists_unpack64_of_length_32 hprk160_len
            obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm160, hout160⟩ :=
              exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)
            simp only [Bool.false_eq_true, ↓reduceIte, emp_sepConj]
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.of_sepWP_lsfull hF8 (mid := (blkPl_79).base + 944#64) ?_
            wp_steps_sync_pool (lsρ lsMemcpySym)
            wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            wp_steps_sync_pool (lsρ acceptRustDeallocSym)
            refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
              (by sep_focus) ?_
            wp_call hdealloc (dh3_ptr, 32, 1, st_dh3_a)
            refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
              P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
              (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh3_ptr 32#64 0#64)
              (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
            sep_elim_exists'
            refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp)) (by sep_focus) ?_
            sep_elim_exists'
            refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
            sep_elim_exists'
            wp_steps_sync_pool (lsρ lsMemcpySym)
            wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            wp_steps_sync_pool (lsρ lsMemcpySym)
            wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64, (bytesToBv8 inp.hdr.kemCt).drop 1⟩
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
            refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_
            wp_steps_sync_pool (lsρ acceptKyberDecapsSym)
            wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
              s0.sp - 176#64⟩
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            wp_steps_sync_pool (lsρ Keys.lsRustNoAllocShimSym)
            wp_call hshim ()
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            wp_steps_sync_pool (lsρ Keys.lsRustAllocSym)
            have hrl32 : LibsignalBinary.Heap.RustLayoutOk 32 1 :=
              ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
            wp_call halloc (32, 1, st_dh3)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF9; try simp only [arm64_norm] at hF9
            refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
              fun halloc32 halign32 htr32 => ?_
            let st_ss_a := M.stepEvents (rustAllocEvents 32 1) st_dh3
            let st_ss := M.stepEvents (rustDeallocEvents 32 1) st_ss_a
            (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
            refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
            refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
            sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (ss_and_vec128_split _ _)) (by sep_focus) ?_
            sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_lsfull hF9
            wp_steps_sync_pool (lsρ acceptRustDeallocSym)
            refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
            wp_call hdealloc (_, 32, 1, st_ss_a)
            refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (ss_vec_add128_merge _ hss_cells) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
              P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
              P.x25519 inp.spkBSk inp.hdr.ekAPk) ss 128 (by simp only [bytesToBv8,
              List.length_map, hpfx3_len]))) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp)) (by sep_focus) ?_
            wp_steps_sync_pool (lsmpl.base 54)
            apply SepWP.checkpoint_lsfull (by wp_norm_lhs) (by wp_norm_lhs)
            intro hF10; try simp only [arm64_norm] at hF10
            have hF10_cro := hF10.to_lscro
            wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
              P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
              P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss, s0.sp - 4944#64)
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            refine SepWP.fold (vec_ok_160_merge _ hikm160_len) (by sep_focus) ?_
            refine SepWP.fold (prk_sub4912_eq s0.sp hprk160) (by sep_focus) ?_
            refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
            sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac160 => ?_
            wp_steps_sync_pool (lsmpl.base 53)
            apply Keys.SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
            intro hF11; try simp only [arm64_norm] at hF11
            have hF11_cro := hF11.to_lscro
            refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac160) (by sep_focus) ?_
            (conv => arg 4; simp only [arm64_norm, ← hinfo_len])
            wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
              P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
              P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss), s0.sp - 4912#64,
              lsmpl.ρ "libsignal_protocol:.rodata..Lanon.352",
              INFO_PQXDH, s0.sp - 176#64, s0.sp - 4944#64); sep_elim_exists'
            (conv => arg 4; rw [hinfo_len])
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
              8#5)))) (by sep_focus) ?_; sep_elim_exists'
            refine SepWP.fold (okm_sub176_eq s0.sp hokm160) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
            sep_elim_exists'
            wp_steps_sync_pool (lsρ acceptRustDeallocSym)
            wp_call hdealloc (_, 192, 1, st_ss)
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout160)
              (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
              (by sep_focus) ?_
            refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
              (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
              (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
            have hst_eq :
                M.stepEvents (rustDeallocEvents 192 1) st_ss =
                  M.stepEvents
                    (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                      rustDeallocEvents 192 1) st := by
              dsimp only [st_ss, st_ss_a]
              rw [hst_dh3_eq, ← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append]
              simp only [dhCycle, List.append_assoc]
            rw [hst_eq]
            have henv_out :
                AcceptOptFieldsEnv P inp
                  (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1) :=
              hevs_eq.symm
            clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
            refine sepWP_instantiate_ro2_post_exists
              (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
                rustDeallocEvents 192 1) ?_
            simp only [sepConj_assoc, *]; wp_done

theorem pqxdhAccept_opt_fields_opk_none_placed_ok_of_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym rustAllocShimVmSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubBudgetSpec P)) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec P A lim)) :=
  pqxdhAccept_opt_fields_opk_none_placed_ok hWF h_canon h_agree h_hkdf_extract h_hkdf_expand
    (hookSat_noAllocShim_of_rustAllocShimVm h_shim) h_alloc h_dealloc
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy) h_decaps

/-! ## 4. Discharging `h_agree` from `AgreeBudget.calculateAgreement_placed_ok` (Block `207`) -/

/-- Alignment of `Keys.DefsBudget.calculateAgreementEvents` and
`AcceptBudget.calculateAgreementEvents` under `PrimitivesMatchCrypto P C`. -/
private theorem calculateAgreementEvents_eq {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C)
    (ourA : BitVec 64) (ourSk32 : Bytes) (theirA : BitVec 64) (theirPk32 : Bytes)
    (ret : BitVec 64) :
    LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents C.X
      ⟨ourA, ⟨E2E.u8Vec 32 ourSk32⟩, theirA, ⟨E2E.u8Vec 32 theirPk32⟩, ret⟩ =
    calculateAgreementEvents P ourSk32 theirPk32 := by
  let ss := C.X (Ratchet.clampScalar (E2E.u8Vec 32 ourSk32)) (E2E.u8Vec 32 theirPk32)
  have hx25519 : P.x25519 ourSk32 theirPk32 = E2E.vecU8 ss := hP.x25519_eq ourSk32 theirPk32
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres :
        calculateAgreement C.X (⟨E2E.u8Vec 32 theirPk32⟩ : PublicKey)
          (⟨E2E.u8Vec 32 ourSk32⟩ : PrivateKey) = none :=
      Keys.calculateAgreement_eq_none hzero
    have hp_zero : P.x25519 ourSk32 theirPk32 = List.replicate 32 0 := by
      rw [hx25519, ← toU8_bytesToBv8 (List.replicate 32 0), bytesToBv8_replicate]
      unfold E2E.vecU8
      rw [hzero]
      rfl
    unfold LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents
      calculateAgreementEvents
    simp only [hres, hp_zero, ↓reduceIte]
  · have hres :
        calculateAgreement C.X (⟨E2E.u8Vec 32 theirPk32⟩ : PublicKey)
          (⟨E2E.u8Vec 32 ourSk32⟩ : PrivateKey) = some ss :=
      Keys.calculateAgreement_eq_some hzero
    have hp_ne : P.x25519 ourSk32 theirPk32 ≠ List.replicate 32 0 := by
      intro h
      apply hzero
      have hb := congrArg bytesToBv8 h
      rw [hx25519, bytesToBv8_vecU8, bytesToBv8_replicate] at hb
      exact hb
    unfold LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents
      calculateAgreementEvents
    simp only [hres, hp_ne, ↓reduceIte]

/-- Implication from `Keys.DefsBudget.calculateAgreementSpec` (`AgreeBudget`) to
`AcceptBudget.acceptCalculateAgreementPlacedBaseSpec` under `PrimitivesMatchCrypto P C`. -/
theorem subroutine_ok_acceptCalculateAgreement_of_agreeBudget [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (hP : PrimitivesMatchCrypto P C)
    (hraw : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec M A lim C.X))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)) := by
  refine subroutine_ok_map hraw ?_
  rintro ⟨⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩, st⟩ R s0 hpre
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [acceptCalculateAgreementPlacedBaseSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, hpre⟩
  let xg : CalculateAgreementGhost :=
    ⟨ourA, ⟨E2E.u8Vec 32 ourSk32⟩, theirA, ⟨E2E.u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hevs_eq :
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents C.X xg =
        calculateAgreementEvents P ourSk32 theirPk32 :=
    calculateAgreementEvents_eq hP ourA ourSk32 theirA theirPk32 ret
  have hfits_env : FitsEnv M lim st (CalculateAgreementEnv C.X xg) := by
    intro evs hevs
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    exact hfits
  refine ⟨(xg, st), R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, calculateAgreementSpec,
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementSpecWithStack]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        ((⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
            FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
          (xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ (xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
          memRegion xg.ret 24 ∗ A.pool lim st s0 ∗ stackAt sp calculateAgreementStack) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
              FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
            ((xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
              (memRegion xg.ret 24 ∗ (A.pool lim st s0 ∗
                (stackAt sp calculateAgreementStack ∗ R)))))) := by
      sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hfr, ⟨hx0, hx1, hx8, hfits_env⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec,
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementSpecWithStack,
      acceptCalculateAgreementPlacedBaseSpec] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [hour_list, htheir_list, hsp_eq] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hevs⟩, hpost⟩
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    refine ⟨htr, ?_⟩
    have hE := calculateAgreementResultAt_entails_pqxdh hP A.repAlloc ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A.repAlloc ret (calculateAgreement C.X xg.their xg.our) ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool lim (M.stepEvents (calculateAgreementEvents P ourSk32 theirPk32) st) sf ∗
            stackAt sp calculateAgreementStack ∗ R) := by
      ac_nf at hpost ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢

/-- Block `207` `subroutine_ok` for `acceptCalculateAgreementPlacedBaseSpec` bridged directly from
`AgreeBudget.calculateAgreement_placed_ok`. -/
theorem acceptCalculateAgreement_placed_ok_of_agreeBudget [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks}
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H Keys.lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H Keys.lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_cteq : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl
        LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H Keys.lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)) :=
  subroutine_ok_acceptCalculateAgreement_of_agreeBudget hP
    (calculateAgreement_placed_ok h_dh h_shdrop h_cteq h_shim h_alloc h_stdrop)

/-- Cross-block transfer of `acceptCalculateAgreement_placed_ok_of_agreeBudget` to any caller block
`i < 619` (including Block `79`). -/
theorem acceptCalculateAgreement_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H Keys.lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H Keys.lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_cteq : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl
        LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H Keys.lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)) :=
  keys_ls_subroutine_ok_of_block_cro
    (acceptCalculateAgreement_placed_ok_of_agreeBudget hP h_dh h_shdrop h_cteq h_shim h_alloc
      h_stdrop)
    hi (by decide) (by decide)

/-- `_of_hooks` corollary of `pqxdhAccept_opt_fields_opk_none_placed_ok` with `h_agree` (`lsmpl.base 207`)
discharged from `AgreeBudget.calculateAgreement_placed_ok`. -/
theorem pqxdhAccept_opt_fields_opk_none_placed_ok_of_hooks [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_dh : HookSat H Keys.lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H Keys.lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_cteq : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl
        LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_stdrop : HookSat H Keys.lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubBudgetSpec P)) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec P A lim)) :=
  pqxdhAccept_opt_fields_opk_none_placed_ok hWF h_canon
    (acceptCalculateAgreement_placed_ok_of_block (callerProg := lsProg_79 H) (i := 79)
      hP h_dh h_shdrop h_cteq h_shim h_alloc h_stdrop)
    h_hkdf_extract h_hkdf_expand h_shim h_alloc h_dealloc h_memcpy h_decaps

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
