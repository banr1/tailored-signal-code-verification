/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
public import Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
structure TRStateOnlyKemSlot (ss₀ : DY.Bytes) (i : ExternInterpretation) (S : Sem) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  myIk : OnlyKemSlot ss₀ i S g st.myIk
  peerIk : OnlyKemSlot ss₀ i S g st.peerIk
  rk : OnlyKemSlot ss₀ i S g st.rk
  dhs : OnlyKemSlot ss₀ i S g st.dhs
  cks : OnlyKemSlot ss₀ i S g st.cks
  sid : OnlyKemSlot ss₀ i S g st.sid
  spqr : OnlyKemSlot ss₀ i S g st.spqr
  recv : ∀ d ∈ st.recv, OnlyKemSlot ss₀ i S g d.ratchetKey ∧ OnlyKemSlot ss₀ i S g d.chainKey
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (serialize_local_pqxdh_eq)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (mem_storedSecrets_iff)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (trStateStoredAt_encNextTr)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (at?_trSt_encNextTr)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (mem_storedStates_iff)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (storedStates_split38_cases)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (runMoves_snd_of_movesFrom_invisibleNoEffect)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (setupMove_vis_nil)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (runVis_split38_eq)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (aliceStart_vis_eq)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (encrypt_vis_eq)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (mem_encDraws_encNextTr)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (mem_encSend_encNextTr_none)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (mem_encSend_encNextTr_some)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (pt_terms_split38_mem)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (getMessageSentAt_of_netMsgAt)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (send_terms_split38_mem)
export Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 (runTrace_split38_swap_eq)
theorem isSetup_false_split38_swap {pre mid post : List Move} {m₀ : Move} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} (hns : ∀ m ∈ pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₁ :: post, m.isSetup = false) : ∀ m ∈ pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₂ :: post, m.isSetup = false := by
  intro m hm; simp only [List.mem_append, List.mem_cons] at hm
  rcases hm with ((hm | rfl | hm) | rfl | hm)
  · exact hns m (by simp [hm])
  · exact hns m (by simp)
  · exact hns m (by simp [hm])
  · rfl
  · exact hns m (by simp [hm])
theorem nbsc38_of_hmc {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {τ₁ : List MachineEvent} {p : PreKeyFields} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hidx : spqrIdx p = 0 ∨ spqrIdx p = 1) (hhmc : ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat), let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩; Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms) → MovesFrom InvisibleNoEffect (setupTrace r) pre → MovesFrom InvisibleNoEffect (m₀.next tr₁) mid → MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post → m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o → bobDoneBaseKeys (runTraceMoves r ms) = [] → ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (runTraceMoves r ms') (runVis r ms') ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀) []) : NBSC38 r S g v t τ₁ p := by unfold NBSC38; intro pre mid post hb shown cl e c' tr₁ o m₀ tr₂ stA hc hmr hvis hpre hmid hpost hm₀ hnil; exact not_bobStartCollision_split38_ini hNe hopk hidx hpre hmid hpost hm₀ (hhmc pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil)
end Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts
