/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClonePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

/-!
# Placed `SessionRecord::serialize` (`Prev1`) Bridge and CLI Contract Assembly

Bridges `SerializePrev1BodyPlacedOkStmt` to the 48-byte and canonical-ghost `SessionRecord::serialize`
contracts under `[LibsignalPlacement]`, closing them from `SerContractsXPlaced` and instantiating
them on `cliGhostExterns`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Bin
open Proofs.libsignal.Hooks2

private theorem stackAt_sub_split_k5b_pl (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

private theorem stackAt_recordSerialize_split_k5b_pl (sp : BitVec 64) :
    stackAt sp CryptoVerification.E2E.Bin.recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
        (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗
      stackAt sp serializeStackX :=
  stackAt_sub_split_k5b_pl sp serializeStackX CryptoVerification.E2E.Bin.recordSerializeStack
    serializeStackX_le_recordSerializeStack (by decide)

private theorem memRegion_48_split_32_16_k5b_pl (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

private theorem pack_withLsCodeLoaded_k5b {pl : Obj.MultiPlacement} {α : Type} {S : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hp : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl S).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm _ ⌜LibsignalCodeLoaded pl s0.mem⌝, satisfies_pure_sepConj]
  exact ⟨hcl, hp⟩

theorem serializePrev1_placed_ok_codeLoaded [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hBody : SerializePrev1BodyPlacedOkStmt A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1Spec A)) := by
  unfold SerializePrev1BodyPlacedOkStmt at hBody
  intro x R s0 hpc hrun hpre hal hL
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [serializePrev1Spec] at hpre'
  rw [sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
      memRegion_48_split_32_16_k5b_pl x.out,
      stackAt_recordSerialize_split_k5b_pl s0.sp,
      sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have henc : encodeRecordPrev1Mem x.G x.sess x.enc = encodeRecordPrev1 x.sess x.enc :=
    encodeRecordPrev1Mem_eq_of_canon x.enc hcanon.toCanonSession
  let x_body : SerializePrev1BodyGhost :=
    ⟨x.self, x.out, x.prevCap, x.prevPtr, x.G, x.sess, x.enc⟩
  let R_body : SepProp :=
    memRegion (x.out + 32#64) 16 ∗
      memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
        (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗ R
  have hpre_body : s0.mem ⊨ (withLsCodeLoaded lsmpl (serializePrev1BodySpecX A)).pre x_body s0 ∗ R_body := by
    refine pack_withLsCodeLoaded_k5b hcl ?_
    dsimp only [serializePrev1BodySpecX, x_body, R_body]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, henc.symm ▸ hlen⟩, ?_⟩
    exact Satisfies.of_eq hmem (by ac_rfl)
  rcases hBody x_body R_body s0 hpc hrun hpre_body hal hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withLsCodeLoaded, serializePrev1BodySpecX, x_body, R_body] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    rw [henc] at hq_mem
    dsimp only [withLsCodeLoaded, serializePrev1Spec]
    rw [sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
        stackAt_recordSerialize_split_k5b_pl s0.sp,
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    exact Satisfies.of_eq hq_mem (by ac_rfl)
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withLsCodeLoaded, serializePrev1BodySpecX, serializePrev1Spec, R_body] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ memRegion (x.out + 32#64) 16 ∗
        memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
          (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    exact Arm64.Satisfies.mono hany (Satisfies.of_eq hq_mem (by ac_rfl))
  · dsimp only [withLsCodeLoaded, serializePrev1BodySpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [withLsCodeLoaded, serializePrev1BodySpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim

theorem serializePrev1_placed_bridge [LibsignalPlacement] : SerializePrev1PlacedBridgeStmt := by
  intro A H hBody
  exact ls_subroutine_ok_cl_of_callee (callerProg := lsProg_52 H) (j := 52)
    (serializePrev1_placed_ok_codeLoaded hBody)

theorem serializePrev1CanonX_of_body_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hBody : SerializePrev1BodyPlacedOkStmt A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecX A)) := by
  intro x R s0 hpc hrun hpre hal hL
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  simp only [serializePrev1CanonSpecX,
    sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc]] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩ := hpre'
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  have hpre_body : s0.mem ⊨ (withLsCodeLoaded lsmpl (serializePrev1BodySpecX A)).pre x s0 ∗ R := by
    refine pack_withLsCodeLoaded_k5b hcl ?_
    simp only [serializePrev1BodySpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, henc.symm ▸ hlen⟩, Satisfies.of_eq hmem (by ac_rfl)⟩
  rcases hBody x R s0 hpc hrun hpre_body hal hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withLsCodeLoaded, serializePrev1BodySpecX] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [withLsCodeLoaded, serializePrev1CanonSpecX]
    rw [sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.of_eq (henc ▸ hq_mem) (by ac_rfl)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hq⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))⟩

/-! ## Closed contracts from `SerContractsXPlaced` -/

theorem serializePrev1Body_placed_ok_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : SerContractsXPlaced A H) :
    SerializePrev1BodyPlacedOkStmt A H := by
  have hDR : DoReservePlacedOkX A H := Proofs.libsignal.Hooks2.do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX A H :=
    CryptoVerification.LibsignalTripleRatchet.Prost.encode_varint_placed_ok_of_doReserve_x A H hDR
  exact serializePrev1Body_placed_ok hC
    (CryptoVerification.E2E.Record.Serialization.sessionClone_placed_ok_ext hC)
    hEV
    (Proofs.libsignal.Hooks2.encodeRaw_placed_ok_of_serContractsX hC)
    (vecVecClone1_placed_okX_of_ser hC)
    (serField2_placed_step hC hDR hEV)
    (serPrev1Tail_placed_ok hC
      (Proofs.libsignal.Hooks2.drop_session_structure_local1_placed_ok_ext hC.alloc))

theorem serializePrev1_placed_ok_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : SerContractsXPlaced A H) :
    SerializePrev1PlacedOkStmt (lsProg_52 H) A :=
  serializePrev1_placed_bridge A H (serializePrev1Body_placed_ok_of_serContractsX hC)

theorem serializePrev1Body_placed_cl_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1BodySpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1Body_placed_ok_of_serContractsX hC)

theorem serializePrev1_placed_cl_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    SerializePrev1PlacedOkStmt callerProg A :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1_placed_ok_codeLoaded (serializePrev1Body_placed_ok_of_serContractsX hC))

theorem serializePrev1CanonX_placed_cl_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1CanonX_of_body_placed (serializePrev1Body_placed_ok_of_serContractsX hC))

theorem serializePrev1Body_placed_lscro_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A)) :=
  SignalSession.Cli.Store.PlacedCommon.ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1Body_placed_ok_of_serContractsX hC) hblk

theorem serializePrev1CanonX_placed_lscro_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1CanonSpecX A)) :=
  SignalSession.Cli.Store.PlacedCommon.ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1CanonX_of_body_placed (serializePrev1Body_placed_ok_of_serContractsX hC)) hblk

theorem serializePrev1_placed_lscro_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1Spec A)) :=
  SignalSession.Cli.Store.PlacedCommon.ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializePrev1_placed_ok_codeLoaded (serializePrev1Body_placed_ok_of_serContractsX hC)) hblk

/-- Instantiates `serializePrev1BodySpecX` at `E2E.HooksE.A0` and `cliGhostExterns` under
`StoreKit.withLsCodeRoLoaded`. -/
theorem serializePrev1Body_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CryptoVerification.SignalSession.Cli.RunGlue.CliGhostHooks)
    (W : CryptoVerification.SignalSession.CliHooks) {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns gh
        (CryptoVerification.SignalSession.cliExternsPlaced mmpl W))]
    (hG : CryptoVerification.SignalSession.Cli.Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (serializePrev1BodySpecX E2E.HooksE.A0)) :=
  serializePrev1Body_placed_lscro_of_serContractsX
    (SignalSession.Cli.Store.SerGlueX.serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1CanonX_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CryptoVerification.SignalSession.Cli.RunGlue.CliGhostHooks)
    (W : CryptoVerification.SignalSession.CliHooks) {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns gh
        (CryptoVerification.SignalSession.cliExternsPlaced mmpl W))]
    (hG : CryptoVerification.SignalSession.Cli.Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (serializePrev1CanonSpecX E2E.HooksE.A0)) :=
  serializePrev1CanonX_placed_lscro_of_serContractsX
    (SignalSession.Cli.Store.SerGlueX.serContractsX_cli_placed mmpl gh W hG) hblk

theorem serializePrev1_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CryptoVerification.SignalSession.Cli.RunGlue.CliGhostHooks)
    (W : CryptoVerification.SignalSession.CliHooks) {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns gh
        (CryptoVerification.SignalSession.cliExternsPlaced mmpl W))]
    (hG : CryptoVerification.SignalSession.Cli.Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (serializePrev1Spec E2E.HooksE.A0)) :=
  serializePrev1_placed_lscro_of_serContractsX
    (SignalSession.Cli.Store.SerGlueX.serContractsX_cli_placed mmpl gh W hG) hblk

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
