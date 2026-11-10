/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafVarintPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafReservePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.VarintBridge

/-!
# Relocatable Leaf Callee Contracts for Inlined `SessionStructure::decode`

Relocatable (`[LibsignalPlacement]`) callee contract propositions (`SkipField6PlacedOkExtX` on
Block `510` and `GrowOneMessageKeyPlacedOkExtX` on Block `519`) on `lsProg_518 ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed
open Proofs.libsignal.Stage1X

/-- Relocatable `[LibsignalPlacement]` contract for `prost::encoding::skip_field::<&mut &[u8]> [local#5]`
(Block `510`, `(blkPl_510).base = lsmpl.base 510`) on `lsProg_518 ext`. -/
def SkipField6PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 510)
    (withLsCl lsmpl (skipField3Spec A))

/-- Relocatable `[LibsignalPlacement]` contract for
`<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one`
(Block `519`, `(blkPl_519).base = lsmpl.base 519`) on `lsProg_518 ext`. -/
def GrowOneMessageKeyPlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
    (withLsCl lsmpl (growOneChainSpecX A))

theorem subroutine_ok_skipField3_or_placed [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64} {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A depth P)))
    (h2 : subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A depth Q))) :
    subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A depth (fun x => P x ∨ Q x))) := by
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCl, skipField3SpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · apply h1 x R s0 hpc hrun _ hsp
    dsimp only [withLsCl, skipField3SpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · apply h2 x R s0 hpc hrun _ hsp
    dsimp only [withLsCl, skipField3SpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipField3_imp_placed [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64} {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A depth Q))) :
    subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A depth P)) := by
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCl, skipField3SpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  apply h x R s0 hpc hrun _ hsp
  dsimp only [withLsCl, skipField3SpecAt]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem skipField3SpecAt_reaches_outcome_placed_eq [LibsignalPlacement] (prog : Program)
    (A : RustAlloc) (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCl lsmpl (skipField3SpecAt A x.depth P)) x R s0 s0 =
      reaches_outcome prog (withLsCl lsmpl (skipField3Spec A)) x R s0 s0 :=
  reaches_outcome_eq_of_parts_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

theorem subroutine_ok_skipField3Spec_of_at_depth_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCl lsmpl (skipField3Spec A)) := by
  intro x R s0 hpc hrun hpre hsp
  have hpre' := hpre
  dsimp only [withLsCl, skipField3Spec] at hpre'
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  rw [← skipField3SpecAt_reaches_outcome_placed_eq prog A (fun _ => True) x R s0]
  apply h x.depth hdepth x R s0 hpc hrun _ hsp
  dsimp only [withLsCl, skipField3SpecAt]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
