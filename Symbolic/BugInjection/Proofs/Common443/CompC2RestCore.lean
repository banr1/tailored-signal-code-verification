/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ
public import Symbolic.BugInjection.Proofs.Common443.CompRI0OnTable
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2RestCore
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.X25519 (isLowOrderKey)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Census443Defs CompFreshDistinct CompRI0TermInj CompRI0OnTable CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompRQRestCensusZ
theorem compPubOfIdx_ne_zeroDh : ∀ i : Fin 12, compPubOfIdx i ≠ CompRI0Census.zeroDh := by decide +kernel
theorem compDefaultPub_ne_zeroDh : compDefaultPub ≠ CompRI0Census.zeroDh := by decide +kernel
theorem compDhByIdx_ne_zeroDh : ∀ i j : Fin 12, compDhByIdx i j ≠ CompRI0Census.zeroDh := by decide +kernel
theorem compDefaultDh_ne_zeroDh : compDefaultDh ≠ CompRI0Census.zeroDh := by decide +kernel
theorem compPubOfOpt_ne_zeroDh (o : Option (Fin 12)) : compPubOfOpt o ≠ CompRI0Census.zeroDh := by cases o <;> [exact compDefaultPub_ne_zeroDh; exact compPubOfIdx_ne_zeroDh _]
theorem compDefaultPub_not_lowOrder : isLowOrderKey (compDefaultPub.map BitVec.toNat) = false := by decide +kernel
theorem compPubOfOpt_not_lowOrder (o : Option (Fin 12)) : isLowOrderKey ((compPubOfOpt o).map BitVec.toNat) = false := by cases o <;> [exact compDefaultPub_not_lowOrder; exact compPubOfIdx_not_lowOrder _]
theorem compLookupDh_ne_zeroDh {s p : HwBytes} (hlo : isLowOrderKey (p.map BitVec.toNat) = false) : compLookupDh s p ≠ CompRI0Census.zeroDh := by
  unfold compLookupDh; rw [hlo]; simp only [Bool.false_eq_true, ↓reduceIte]
  split <;> [exact compDhByIdx_ne_zeroDh _ _; exact compDefaultDh_ne_zeroDh]
section Gamma
variable (S : Sem) (g : Ghost)
theorem gamma_dhPk_ne_zeroDh (s : DY.Bytes) : gamma compI0 S g (DY.DiffieHellman.dhPk s) ≠ CompRI0Census.zeroDh := by rw [gamma_dhPk_compI0]; exact compPubOfOpt_ne_zeroDh _
theorem isLowOrderKey_gamma_dhPk (s : DY.Bytes) : isLowOrderKey ((gamma compI0 S g (DY.DiffieHellman.dhPk s)).map BitVec.toNat) = false := by rw [gamma_dhPk_compI0]; exact compPubOfOpt_not_lowOrder _
theorem gamma_dh_ne_zeroDh (p s : DY.Bytes) (hlo : isLowOrderKey ((gamma compI0 S g p).map BitVec.toNat) = false) : gamma compI0 S g (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ≠ CompRI0Census.zeroDh := by rw [gamma_dh_pack_compI0]; exact compLookupDh_ne_zeroDh hlo
end Gamma
def DhPtNotLow (S : Sem) (g : Ghost) (u : DY.Bytes) : Prop := ∀ p s : DY.Bytes, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) → isLowOrderKey ((gamma compI0 S g p).map BitVec.toNat) = false
theorem gamma_x_ne_zeroDh {S : Sem} {g : Ghost} {u : DY.Bytes} (hX : IsX u) (h : DhPtNotLow S g u) : gamma compI0 S g u ≠ CompRI0Census.zeroDh := by
  rcases hX with ⟨s, rfl⟩ | ⟨p, s, rfl⟩
  · exact gamma_dhPk_ne_zeroDh S g s
  · exact gamma_dh_ne_zeroDh S g p s (h p s rfl)
theorem dhPtNotLow_of_dhPk {S : Sem} {g : Ghost} {u : DY.Bytes} (h : ∀ p s : DY.Bytes, u = (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) → ∃ q, p = DY.DiffieHellman.dhPk q) : DhPtNotLow S g u := by intro p s hps; obtain ⟨q, rfl⟩ := h p s hps; exact isLowOrderKey_gamma_dhPk S g q
theorem dhPtNotLow_of_not_dh {S : Sem} {g : Ghost} {u : DY.Bytes} (h : ¬ IsDh u) : DhPtNotLow S g u := fun p s hps => absurd ⟨p, s, hps⟩ h
theorem mem_storedSecrets_setup_cases {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hopk : r.withOpk = false) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) {u : DY.Bytes} (hu : u ∈ storedSecrets (runTraceMoves r ms)) : ∃ ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState, u = Comparse.serialize ls ∧ ((ls.participant = r.alice ∧ ls.state.sk = randTerm 0 32) ∨ (ls.participant = r.bob ∧ (ls.state.sk = randTerm 5 32 ∨ ls.state.sk = randTerm 10 32 ∨ ls.state.sk = randTerm 16 64))) := by
  obtain ⟨j, _, ⟨part, kind, sk⟩, hat, rfl⟩ := CompRX0NBSC38Parts.mem_storedSecrets_iff.mp hu; refine ⟨⟨part, kind, sk⟩, rfl, ?_⟩; have hkind := (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach).stOK part ⟨kind, sk⟩ j hat; dsimp only [Symbolic.Swarm.COMPOSED.CompInv.KindOK] at hkind ⊢
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · exact Or.inl ⟨rfl, CompSetupSecrecy.setupSecret_0 hNe⟩
    · exact Or.inr ⟨rfl, Or.inl (CompSetupSecrecy.setupSecret_1 hNe)⟩
  | signedPrekey =>
    obtain ⟨rfl, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hkind; exact Or.inr ⟨rfl, Or.inr (Or.inl (CompSetupSecrecy.setupSecret_2 hNe))⟩
  | pqPrekey =>
    obtain ⟨rfl, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hkind; exact Or.inr ⟨rfl, Or.inr (Or.inr (CompSetupSecrecy.setupSecret_4 hNe))⟩
  | oneTimePrekey =>
    obtain ⟨t, _, _, hev⟩ := hkind; have h0' := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe h0' with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk_true, _, _⟩ <;>
      [cases heq; cases heq; cases heq; cases heq; (rw [hopk] at hopk_true; cases hopk_true)]
theorem mem_storedSecrets_sk_cases {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hopk : r.withOpk = false) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) {u : DY.Bytes} (hu : u ∈ storedSecrets (runTraceMoves r ms)) : ∃ ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState, u = Comparse.serialize ls ∧ (ls.state.sk = randTerm 0 32 ∨ ls.state.sk = randTerm 5 32 ∨ ls.state.sk = randTerm 10 32 ∨ ls.state.sk = randTerm 16 64) := by
  obtain ⟨ls, rfl, ⟨_, h⟩ | ⟨_, h⟩⟩ := mem_storedSecrets_setup_cases hNe hopk hns hreach hu
  · exact ⟨ls, rfl, Or.inl h⟩
  · exact ⟨ls, rfl, Or.inr h⟩
end Symbolic.BugInjection.Proofs.Common443.CompC2RestCore
