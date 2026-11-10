/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRBobInit
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.Swarm.CREF
variable {S : Sem} {g : Ghost}
theorem setupSecret_0 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 0 = randTerm 0 32 :=
  CompSetupSecrecy.setupSecret_0 hNe
theorem setupSecret_1 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 1 = randTerm 5 32 :=
  CompSetupSecrecy.setupSecret_1 hNe
theorem setupSecret_2 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 2 = randTerm 10 32 :=
  CompSetupSecrecy.setupSecret_2 hNe
theorem setupPublic_4 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 4 = DY.DiffieHellman.dhPk (randTerm 10 32) :=
  CompSetupSecrecy.setupPublic_4 hNe
theorem not_sendMatches_encOut_of_dh1 (r : Records) (b : HwBytes) (tr₁ tr₂ : ExecTrace) (bob : Participant) (ikA ikBPk spkPk pqPk : DY.Bytes) (ekT ctT : DY.Bytes) (cl pq : Nat) (h1 : gamma compI0 S g (DY.Libsignal.PQXDH.agree spkPk ikA) = compDefaultDh) (hb : CompRBobInit.hasTag4 b = false) : ¬ CompRPreKeyWire.SendMatchesMoves compI0 r S g b [ekT, ctT, encOut tr₂ (iniAliceStartState tr₁ bob (Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr₁ ikA ikBPk spkPk pqPk none)) cl pq] := by unfold encOut; refine CompRBobInit.not_sendMatches_of_tagged r b ekT ctT _ _ ?_ hb; unfold encMac; exact CompRBobInit.computeMac_take4 _ _ _ _ (CompRBobInit.tt_aliceStart_macKey ikA (randTerm tr₁.length 32) ikBPk spkPk pqPk none (randTerm (tr₁.length + 1) 32) (randTerm (tr₁.length + 2) 32) _ h1)
theorem gamma_randTerm' (i : CryptoProofLib.Refinement.ExternInterpretation) (t n : Nat) : gamma i S g (randTerm t n) = if n = 0 then [] else g.σ t n := by
  unfold gamma gamma' randTerm
  show ((({ timestamp := t, size := n } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)]; unfold gRandom concretizeRandom node
  split <;> rfl
theorem gamma_setupSecret_0 {i : CryptoProofLib.Refinement.ExternInterpretation} {r : Records} (hNe : r.alice ≠ r.bob) (hc : Compat i r S g) : gamma i S g (setupSecret r 0) = secretBytes r 0 := by
  rw [setupSecret_0 hNe, gamma_randTerm']; simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte]
  have hm : ((0, 32) : Nat × Nat) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; simp
  rw [hc.1 _ hm]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
theorem gamma_setupSecret_1 {i : CryptoProofLib.Refinement.ExternInterpretation} {r : Records} (hNe : r.alice ≠ r.bob) (hc : Compat i r S g) : gamma i S g (setupSecret r 1) = secretBytes r 1 := by
  rw [setupSecret_1 hNe, gamma_randTerm']; simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte]
  have hm : ((5, 32) : Nat × Nat) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; simp
  rw [hc.1 _ hm]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
theorem gamma_setupSecret_2 {i : CryptoProofLib.Refinement.ExternInterpretation} {r : Records} (hNe : r.alice ≠ r.bob) (hc : Compat i r S g) : gamma i S g (setupSecret r 2) = secretBytes r 2 := by
  rw [setupSecret_2 hNe, gamma_randTerm']; simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte]
  have hm : ((10, 32) : Nat × Nat) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; simp
  rw [hc.1 _ hm]
  unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
theorem gamma_setupPublic_4 {r : Records} (hNe : r.alice ≠ r.bob) (hc : Compat compI0 r S g) : gamma compI0 S g (setupPublic r 4) = compLookupPub (clamp (secretBytes r 2)) := by rw [setupPublic_4 hNe, CompFreshDistinct.gamma_dhPk_compI0, ← setupSecret_2 hNe, gamma_setupSecret_2 hNe hc]
theorem not_sendMatches_bobSelf {r : Records} (hNe : r.alice ≠ r.bob) (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0) (hc : Compat compI0 r S g) (hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩) (hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩) (b : HwBytes) (hb : CompRBobInit.hasTag4 b = false) (tr₁ tr₂ : ExecTrace) (bob : Participant) (ikBPk pqPk ekT ctT : DY.Bytes) (cl pq : Nat) : ¬ CompRPreKeyWire.SendMatchesMoves compI0 r S g b [ekT, ctT, encOut tr₂ (iniAliceStartState tr₁ bob (Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr₁ (setupSecret r 1) ikBPk (setupPublic r 4) pqPk none)) cl pq] := by
  refine not_sendMatches_encOut_of_dh1 r b tr₁ tr₂ bob _ _ _ _ ekT ctT cl pq ?_ hb; refine CompRBobInit.gamma_agree_bobSelf hEq _ _ ?_ ?_
  · rw [gamma_setupSecret_1 hNe hc]; exact hs1
  · rw [gamma_setupPublic_4 hNe hc, compLookupPub, hs2]; rfl
end Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
