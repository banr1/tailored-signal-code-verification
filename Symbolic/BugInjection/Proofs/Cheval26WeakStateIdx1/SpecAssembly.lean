/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78b
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecAssembly
open Symbolic.BugInjection.Proofs.Common443
structure SpecLeaves : Prop where
  memo40 : WsIdx1CensusOwn.Split40MemoCensusOwn
  memo81 : WsIdx1CensusOwn.Split81MemoCensusOwn
theorem specObls_of (L : SpecLeaves) : SpecTop.SpecObls where
  noFull := NoFull.noFull
  ptDead := by rintro n (rfl | rfl | rfl); exact PtPrefixInv35.ptDeadAt35; exact PtPrefixInv38.ptDeadAt38; exact PtPrefixInv78b.ptDeadAt78
  notKnown := BobDone.notKnown
  noBsc := by
    rintro n (rfl | rfl)
    · intro r S g ms p hfits hnb hex hp
      obtain ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex', hdf, hinv, hown, hx⟩ :=
        WsIdx1Decomp40.split40DecompSwapRepOwn_of WsIdx1PrefSafe40.pref40 r S g ms p hfits hnb hex hp
      refine ⟨g, ms', hex', WsIdx1DecryptNoop.not_readCollision_of_decryptNoop hdf, _, hx, ?_⟩
      have hM' := L.memo40 r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; intro h; unfold DY.Libsignal.Composed.Refinement.BobStartCollision DY.Libsignal.Composed.Refinement.BobSessionStartCollidesOrImplicitRejects at h; dsimp only at h
      rcases hP : DY.Libsignal.TripleRatchet.parseTrSignalMsg (WsIdx1CensusDefs.x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg with _ | msg <;>
        simp only [WsIdx1Split40Census.split40NewTerms, hP] at h hM'
      · exact hM' h
      · exact h.elim (fun hm => hM' (CompExcuse.memoCollisionOn_bobTrials_to_bobTerms hP hm)) (WsIdx1Split40OwnSalt.split40OwnSaltMac r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ msg hfits hp hinv hP)
    · exact WsIdx1CensusOwn.noBscAt81_of_own
        (WsIdx1Decomp81.split81DecompSwapRepOwn_of (WsIdx1PrefSafe81.pref81_of_enum fun hpre => WsIdx1Prefix81Enum.split81PrefixEnum_of_pre hpre))
        WsIdx1Split81MemoDefs.split81PinObl L.memo81
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecAssembly
