/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers

/-!
# Placed Stage P2 Over-Path Program Aliases and Callee Contracts

Defines `[LibsignalPlacement]` program and entry aliases (`lsProg_518`, `(blkPl_518).base`) and
relocatable callee contracts for `promote_matching_session` (block 50) and `promote_state`
(block 47).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Block 518 (`message_decrypt_prekey` handshake closure) program under `[LibsignalPlacement]`. -/
abbrev stageP2OverProgPlaced [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  lsProg_518 ext

/-- Block 518 entry address `(blkPl_518).base` under `[LibsignalPlacement]`. -/
abbrev stageP2OverEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  (blkPl_518).base

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Relocatable `subroutine_ok` contract for a `promote_matching_session` miss at block 50
(`lsmpl.base 50`). -/
def PromoteMatchingMissAtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
    (withLsCl lsmpl (p2PromoteMatchingMissAtSpec A coroPtr g recG sess msgVer serBytes))

def PromoteMatchingMissGenPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
    (withLsCl lsmpl (p2PromoteMatchingMissGenSpec A))

theorem promoteMatchingMissAt_placed_of_gen [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenPlacedProp A ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess msgVer serBytes := by
  intro x R s0 hpc hrun hpre halign hL
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ (withLsCl lsmpl (p2PromoteMatchingMissGenSpec A)).pre xg s0 ∗ R := by
    refine Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, xg, g']
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  rcases hGen xg R s0 hpc hrun hpre' halign hL with
    ⟨sf, hsteps, ⟨hret, hcs, hpost⟩ | hpan | hexit | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcs, ?_⟩⟩
    refine Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl hexit))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr hoom))⟩

/-- Relocatable `withLsCl` contract for `SessionRecord::promote_state` at block 47
(`lsmpl.base 47`). -/
def PromoteOverAtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 47)
    (withLsCl lsmpl (p2PromoteOverAtSpec A coroPtr g recG sess))

def PromoteOverGenPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 47)
    (withLsCl lsmpl (p2PromoteOverGenSpec A))

theorem promoteOverAt_placed_of_gen [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenPlacedProp A ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (OverP2.clearPendingGhost recG) (OverP2.clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtPlacedProp A ext coroPtr g recG sess := by
  intro x R s0 hpc hrun hpre halign hL
  let xg : P2PromoteOverGenGhost := ⟨coroPtr + 0xe0#64, x.src, g.prevCap, g.prevPtr, recG, sess, x.newBs⟩
  have hrec_eq :
      prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess =
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr [] ∗
      sessionStateReprAt A (coroPtr + 0xe0#64 + 0x18#64) recG sess := by
    rw [prevEmpty_sessionAt_eq_sessionRecordAt]
    rfl
  have hpre' : s0.mem ⊨ (withLsCl lsmpl (p2PromoteOverGenSpec A)).pre xg s0 ∗ R := by
    refine Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [p2PromoteOverAtSpec, p2PromoteOverGenSpec, xg]
    refine Entails.pure_left fun ⟨h0, h1, hnb⟩ => ?_
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          (A.pool ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          (A.pool ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX)) := by
      ac_rfl
    rw [hre, hrec_eq]
    exact Entails.pure_right ⟨h0, h1, hnb, hlen⟩ (Entails.of_eq (by ac_rfl))
  rcases hGen xg R s0 hpc hrun hpre' halign hL with
    ⟨sf, hsteps, ⟨hret, hcs, hpost⟩ | hpan | hexit | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcs, ?_⟩⟩
    refine Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    dsimp only [p2PromoteOverAtSpec, p2PromoteOverGenSpec, xg]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl hexit))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr hoom))⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
end

