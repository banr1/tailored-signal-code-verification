/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<SessionFiles as SessionStore>::store_session::{closure#0}` at `serializeStackX`

Proves `sessStorePollSpecPlaced` on Block `570` (`lsProg_570 H`) at `serializeStackX` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.StorePollX

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Store.StorePoll
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers

section Placed

theorem serialize_cells_placed_okX [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)))
    (hle : Proofs.libsignal.Hooks2.serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (serializeCellsSpec A calleeStk)) := by
  intro ⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - Proofs.libsignal.Hooks2.serializeStackX)
  let callG : E2E.Record.Serialization.SerializeGhost := ⟨recA, out, g, r⟩
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [Proofs.libsignal.Hooks2.serializeCanonSpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hSer callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, Proofs.libsignal.Hooks2.serializeCanonSpecX,
      serializeCellsSpec, callG] at hq ⊢
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
    dsimp only [StoreKit.withLsCodeRoLoaded, Proofs.libsignal.Hooks2.serializeCanonSpecX,
      E2E.Record.Serialization.allocPanic, serializeCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Block `570` (`store_session::{closure#0}`) meets `sessStorePollSpecPlaced A stk`
at `serializeStackX` (`withLsCodeLoaded` `serializeCanonSpecX`). -/
theorem sessStorePoll_placed_ok_of_depsX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (_hC : AllocContractsXCliPlaced A H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hstk : 0xd0 + max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
      (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570) (sessStorePollSpecPlaced A stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_cl_to_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePoll_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serialize_cells_placed_okX hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

end Placed

end CryptoVerification.SignalSession.Cli.Store.StorePollX
