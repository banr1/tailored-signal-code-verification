/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.ChainLen
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.DropsLocal1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRaw
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.MsgKeyLen
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SerializeBody
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionClone
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionLen
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.VecVecClone
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization

theorem serialize_ok_x (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hA : AllocContractsX img A ext) :
    OkAtX img ext serializeName (serializeSpecX A) := by
  have hDR : OkAtX img ext doReserveName (doReserveSpecX A) := do_reserve_ok_ext_x hA
  have hEV : Prost.EncodeVarintOkExtX img A ext :=
    Prost.encodeVarint_ok_ext_x img A ext hDR
  have hmk_raw := msgKeyLen_ok img.base A ext
  have hchain_raw := chainLen_ok img.base A ext hmk_raw
  have hmk : OkAtX img ext msgKeyLenName (msgKeyLenSpec A) :=
    subroutine_ok_inImage_of_ok hmk_raw
  have hchain : OkAtX img ext chainLenName (chainLenSpec A) :=
    subroutine_ok_inImage_of_ok hchain_raw
  exact serialize_ok_of_leaves img A ext hA
    (sessionClone_ok img A ext hA)
    (vecVecCloneEmpty_ok_x img ext)
    (subroutine_ok_inImage_of_ok (sessionLen_ok img.base A ext hchain_raw))
    hEV
    (encodeRaw_ok img A ext hA hEV hDR
      (encodeChain_ok img A ext hA hEV hDR hchain hmk))
    hDR
    (drop_session_structure_local1_ok_x hA)

theorem serializeCanon_of_serialize_x (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (h : OkAtX img ext serializeName (serializeSpecX A)) :
    OkAtX img ext serializeName (serializeCanonSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp_align => ?_
  dsimp only [Spec.inImage] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨hinv, hp'⟩
  simp only [serializeCanonSpecX] at hp'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  obtain ⟨⟨h0, h8, hcanon, hlen⟩, hrest⟩ := hp'
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  have hpre : s0.mem ⊨ ((serializeSpecX A).inImage img).pre x s0 ∗ R := by
    refine satisfies_inImage_pre hinv ?_
    simp only [serializeSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen⟩, hrest⟩
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [Spec.inImage, serializeSpecX, serializeCanonSpecX, henc] using hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem serializeCanon_ok_x (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hA : AllocContractsX img A ext) :
    OkAtX img ext serializeName (serializeCanonSpecX A) :=
  serializeCanon_of_serialize_x img A ext (serialize_ok_x img A ext hA)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
