/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Sym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyX
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Proof of `SessionFiles::store_session::{closure#0}`

Proves `sessStorePoll_cli_placed_ok` (Block `570`) and transfers it onto any caller block program
`prog` using the unbounded-chain `SessionRecord::serialize` contract (`serializeCanonSpecX`,
Block `52`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StorePollCli

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open Proofs.libsignal.Hooks2 (serializeCanonSpecX serializeStackX)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi

/-! ## 1. Extended `SessionRecord::serialize` (`serializeCanonSpecX`) on Block `52` -/

/-- Unbounded-chain `SessionRecord::serialize` (`serializeCanonSpecX`, Block `52`). -/
theorem serializeCanon_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : Proofs.libsignal.Hooks2.SerContractsXPlaced A H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX A)) := by
  have hDR := Proofs.libsignal.Hooks2.do_reserve_placed_ok_ext_x hC.alloc
  have hEV := Prost.encode_varint_placed_ok_of_doReserve_x A H hDR
  have hRaw := Proofs.libsignal.Hooks2.encodeRaw_placed_ok_of_serContractsX hC
  have hDrop := Proofs.libsignal.Hooks2.drop_session_structure_local1_placed_ok_ext hC.alloc
  have hClone := CryptoVerification.E2E.Record.Serialization.sessionClone_placed_ok_ext hC
  exact Proofs.libsignal.Hooks2.serializeCanonX_of_serialize_placedX
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.serialize_placed_ok_of_leaves_ext
      hC hClone hEV hRaw hDrop)

/-! ## 2. Symbol Resolution & Cell-Oriented Callee Wrappers -/

private theorem sp570_addrText_target [LibsignalPlacement] :
    (blkPl_570).ρ addressTextName = lsmpl.base 594 := by
  simp only [arm64_norm]

private theorem sp570_serialize_target [LibsignalPlacement] :
    (blkPl_570).ρ recordSerializeName = lsmpl.base 52 := by
  simp only [arm64_norm]

private theorem sp570_dirPut_target [LibsignalPlacement] :
    (blkPl_570).ρ dirPutName = lsmpl.base 542 := by
  simp only [arm64_norm]

private theorem close_panic_subgoal_placed {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem cells_26_split_placed (sp : BitVec 64) :
    cells (sp - 208#64) 26 =
      storePollSlack sp ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 144#64) 4 ∗
        cells (sp - 96#64) 5 ∗ cells (sp - 48#64) 6 := by
  rw [show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 6 + 19 from rfl, cells_split_sub sp 200 152 6 19,
    show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
    show (18 : Nat) = 4 + 14 from rfl, cells_split_sub sp 144 112 4 14,
    show (14 : Nat) = 2 + 12 from rfl, cells_split_sub sp 112 96 2 12,
    show (12 : Nat) = 5 + 7 from rfl, cells_split_sub sp 96 56 5 7,
    show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6]
  dsimp only [storePollSlack]
  ac_rfl

private theorem cells_sub_4_eq_placed (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq_placed (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq_placed (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq_placed (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

theorem addrText_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {addrStk calleeStk : Nat}
    (hAddr : subroutine_ok prog (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hle : addrStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 594)
      (withLsRoCl lsmpl (addrTextCellsSpec A calleeStk)) := by
  have hAddrRo := subroutine_ok_rocl_of_withLsCodeRoLoaded hAddr
  intro ⟨addrA, g, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := extract_withLsRoCl hpre
  simp only [addrTextCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - addrStk)
  let callG : AddrTextGhost := ⟨addrA, g, ret⟩
  have hpre0 : s0.mem ⊨
      (withLsRoCl lsmpl
        { pre := fun x s =>
            ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.addr ∧ x.g.name.bytes.length < 2 ^ 32⌝ ∗
              protocolAddressAt A x.g x.addr ∗ memRegion x.ret 24 ∗ stackAt s.sp addrStk ∗ A.pool
          post := fun x s0 sf =>
            ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (addressText x.g.val) ∗
              protocolAddressAt A x.g x.addr ∗ stackAt s0.sp addrStk ∗ A.pool
          onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsRoCl_pre hcrl0 ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hAddrRo callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withLsRoCl, addrTextCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withLsRoCl, addrTextCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [withLsRoCl] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsRoCl] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem serialize_cells_placed_ok_x [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hSer : subroutine_ok prog (lsmpl.base 52)
      (withLsRoCl lsmpl (serializeCanonSpecX A)))
    (hle : serializeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 52)
      (withLsRoCl lsmpl (serializeCellsSpec A calleeStk)) := by
  intro ⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := extract_withLsRoCl hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStackX)
  let callG : E2E.Record.Serialization.SerializeGhost := ⟨recA, out, g, r⟩
  have hpre0 : s0.mem ⊨ (withLsRoCl lsmpl (serializeCanonSpecX A)).pre
      callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsRoCl_pre hcrl0 ?_
    dsimp only [serializeCanonSpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hSer callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withLsRoCl, serializeCanonSpecX, serializeCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨bCap, bPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withLsRoCl, serializeCanonSpecX, E2E.Record.Serialization.allocPanic,
      serializeCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [withLsRoCl, serializeCanonSpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [withLsRoCl, serializeCanonSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem vecU8_intro_placed (A : RustAlloc) (v bCap bPtr : BitVec 64)
    (bs : List (BitVec 8)) :
    ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bs ⊢ vecU8 A v bs := by
  have heq :
      ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A bCap bPtr bs =
      vecU8At A v bCap bPtr bs := by
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    rfl
  rw [heq]
  exact Entails.sepExists_right bCap (Entails.sepExists_right bPtr (Entails.refl _))

theorem dirPut_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {putStk calleeStk : Nat}
    (hPut : subroutine_ok prog (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hle : putStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 542)
      (withLsRoCl lsmpl (dirPutCellsSpec A calleeStk)) := by
  have hPutRo := subroutine_ok_rocl_of_withLsCodeRoLoaded hPut
  intro ⟨self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := extract_withLsRoCl hpre
  simp only [dirPutCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - putStk)
  let callG : DirPutGhost := ⟨self, dir, nameV, name, bytesV, bytes⟩
  have hmem_vec : s0.mem ⊨ vecU8 A bytesV bytes ∗
      (dirAt A self dir ∗ vecU8 A nameV name ∗ stackAt s0.sp putStk ∗ A.pool ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left (vecU8_intro_placed A bytesV bCap bPtr bytes)) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨
      (withLsRoCl lsmpl
        { pre := fun x s =>
            ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameV ∧ s.readReg64 .x2 = x.bytesV ∧
              x.dir.changed.length < 2 ^ 32⌝ ∗
              dirAt A x.self x.dir ∗ vecU8 A x.nameV x.name ∗ vecU8 A x.bytesV x.bytes ∗
              stackAt s.sp putStk ∗ A.pool
          post := fun x s0 sf =>
            ⌜sf.trace = s0.trace⌝ ∗ dirAt A x.self (x.dir.put x.name x.bytes) ∗
              memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ stackAt s0.sp putStk ∗ A.pool
          onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsRoCl_pre hcrl0 ?_
    dsimp only [callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hmem_vec using 1; ac_rfl
  rcases hPutRo callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withLsRoCl, dirPutCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hq ⊢
    rcases hq with ⟨m2, m1, m0, n2, n1, n0, hq⟩
    refine ⟨n0, n1, n2, m0, m1, m2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withLsRoCl, dirPutCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [withLsRoCl] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsRoCl] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 3. Symbolic Execution on Block `570` (`lsProg_570 H`) & Outer Wrapper -/

theorem sessStorePollInner_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {addrStk putStk : Nat}
    (hAddr : subroutine_ok (lsProg_570 H) (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hSer : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (withLsRoCl lsmpl (serializeCanonSpecX A)))
    (hPut : subroutine_ok (lsProg_570 H) (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hhi : max (max addrStk serializeStackX) (max putStk extHookStack) ≤ 2 ^ 64) :
    subroutine_ok (lsProg_570 H) (blkPl_570).base
      (StoreKit.withLsCodeRoLoaded lsmpl
        (cliStorePollInnerSpec A
          (max (max addrStk serializeStackX) (max putStk extHookStack)))) := by
  let calleeStk := max (max addrStk serializeStackX) (max putStk extHookStack)
  have hAddrCells : subroutine_ok (lsProg_570 H) ((blkPl_570).ρ addressTextName)
      (withLsRoCl lsmpl (addrTextCellsSpec A calleeStk)) :=
    sp570_addrText_target.symm ▸ addrText_cells_placed_ok (calleeStk := calleeStk)
      hAddr (by omega) hhi
  have hSerCells : subroutine_ok (lsProg_570 H) ((blkPl_570).ρ recordSerializeName)
      (withLsRoCl lsmpl (serializeCellsSpec A calleeStk)) :=
    sp570_serialize_target.symm ▸ serialize_cells_placed_ok_x (calleeStk := calleeStk)
      hSer (by omega) hhi
  have hPutCells : subroutine_ok (lsProg_570 H) ((blkPl_570).ρ dirPutName)
      (withLsRoCl lsmpl (dirPutCellsSpec A calleeStk)) :=
    sp570_dirPut_target.symm ▸ dirPut_cells_placed_ok (calleeStk := calleeStk)
      hPut (by omega) hhi
  clear hAddr hSer hPut
  dsimp only [StoreKit.withLsCodeRoLoaded]
  simp (config := { maxSteps := 2000000 }) only [cliStorePollInnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split_placed, cells_sub_4_eq_placed, cells_sub_5_eq_placed,
    cells_sub_6_200_eq_placed, cells_sub_6_48_eq_placed,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  apply sepWPp_of_sepWP_lscro hcrl0 (mid := (blkPl_570).ρ addressTextName)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro hAddrCells hcrl1
    (x.call.call.addrA, x.call.call.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf_p _ hm
    exact close_panic_subgoal_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply sepWPp_of_sepWP_lscro hcrl_sf (mid := (blkPl_570).ρ recordSerializeName)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl2
  wp_call_lscro hSerCells hcrl2
    (x.call.call.recA, s0.sp - 144#64,
      E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g, x.call.call.record,
      _, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf_p _ hm
    exact close_panic_subgoal_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply sepWPp_of_sepWP_lscro hcrl_sf_1 (mid := (blkPl_570).ρ dirPutName)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3
  wp_call_lscro hPutCells hcrl3
    (x.self, x.dir, s0.sp - 200#64, addressText x.call.call.addr.val,
      s0.sp - 176#64, w, w_1, E2E.Record.encodeRecord x.call.call.record, s0.sp - 208#64)
  case panic =>
    intro sf_p _ hm
    exact close_panic_subgoal_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem sessStorePoll_of_inner_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {entry : BitVec 64} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollInnerSpec A calleeStk)))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok prog entry (sessStorePollSpecPlaced A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hcanon : E2E.Record.Serialization.CanonRecord
      (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record := by
    refine canonRecord_of_satisfies_sessionRecordAt A x.call.call.recA
      x.call.call.g x.call.call.record
      ((x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        A.pool ∗ stackAt s0.sp stk ∗ R) s0.mem ?_
    convert hmem using 1; ac_rfl
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.call.fut) (v := x.self)
      (R := ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [← E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq] at hmem
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.call.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollInnerSpec A calleeStk)).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliStorePollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir, hcanon⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollInnerSpec, sessStorePollSpecPlaced,
      sessStoreBoxAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq] at hq
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollInnerSpec, sessStorePollSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- CLI instantiation of `SessionFiles::store_session::{closure#0}` (Block `570`) transferred onto
any caller block program `prog` (e.g. `initProgPlaced W`). -/
theorem sessStorePoll_cli_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {W : CliHooks} {H : LibsignalHooks} [IsLsBlockProg prog i H] (B : RunBudgets)
    (hh : RunHooksPlaced W A H)
    (hAddr : subroutine_ok (lsProg_594 H) (lsmpl.base 594)
      (addrTextSpecPlaced A cliAddrTextStk))
    (hPut : subroutine_ok (lsProg_542 H) (lsmpl.base 542)
      (dirPutSpecPlaced A cliDirPutStk))
    (hi : i < 619 := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 570)
      (sessStorePollSpecPlaced A (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0xd0 + max (max cliAddrTextStk serializeStackX)
      (max cliDirPutStk extHookStack) ≤ 516880 := by decide
  have hAddr570 : subroutine_ok (lsProg_570 H) (lsmpl.base 594)
      (addrTextSpecPlaced A cliAddrTextStk) := by
    have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := lsProg_570 H) hAddr
    exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [withLsRoCl, StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  have hSer570 : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (withLsRoCl lsmpl (serializeCanonSpecX A)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := lsProg_570 H)
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (serializeCanon_placed_ok_x hh.ser))
  have hPut570 : subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (dirPutSpecPlaced A cliDirPutStk) := by
    have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := lsProg_570 H) hPut
    exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [withLsRoCl, StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  have h570 : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A (stk - cliInitiateFrame)) :=
    sessStorePoll_of_inner_placed
      (fun hhi => sessStorePollInner_placed_ok_x hAddr570 hSer570 hPut570 hhi)
      (by omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := prog) h570 hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsRoCl, StoreKit.withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StorePollCli
