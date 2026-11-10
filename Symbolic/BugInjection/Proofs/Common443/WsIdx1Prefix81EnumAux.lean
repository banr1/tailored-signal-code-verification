/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
attribute [local irreducible] setupPublic setupSecret
section Decomp
variable {r : Records} {pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move}
  {hb₁ hb₂ : DY.Libsignal.PQXDH.BundleHandles} {sh₁ sh₂ s₁ s₂ s₅ cl₁ cl₂ cl₅ : Nat} {w₁ w₂ w₅ : Option (Nat × Nat)}
  {b_bob a_bob : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat}
  {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx₂ : UInt32} {sh_bob : Nat}
  {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace}
theorem runTrace_split81 (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)).1) (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄)).1) : runTraceMoves r (pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: mid₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅ :: post₅) = (runMoves post₅ ((Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅)).1 := by subst htr₅ htr₄ htr_bob htr₃ htr₂ htr₁; rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]
theorem bobStart_vis_eq (tr : ExecTrace) (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (sh : Nat) : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx sh).vis tr = (bobVis tr ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx sh).next tr) mh (bobOpkPk b kh tr)).take sh := by
  have hexp : exposures tr ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx sh).next tr) = [] :=
    exposures_nil_of_not_leakKind (m := Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx sh) rfl (fun h => nomatch h)
  unfold Move.vis; dsimp only; rw [hexp, List.append_nil]
theorem runVis_split81 (hNe : r.alice ≠ r.bob) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)).1) (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄)).1) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅) post₅) : runVis r (pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: mid₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅ :: post₅) = (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).vis tr₁ ++ (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).vis tr₂ ++ (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).vis tr₃ ++ (Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).vis tr_bob ++ (Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).vis tr₄ ++ (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).vis tr₅ := by
  have h0 := runMoves_snd_of_movesFrom_invisibleNoEffect hpre₀; have h1 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₁; have h2 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₂; have h3 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₃; have h4 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₄; have h5 := runMoves_snd_of_movesFrom_invisibleNoEffect hmid₅; have h6 := runMoves_snd_of_movesFrom_invisibleNoEffect hpost₅; subst htr₅ htr₄ htr_bob htr₃ htr₂ htr₁
  change r.setupMove.vis Trace.nil ++ (runMoves _ (setupTrace r)).2 = _; rw [setupMove_vis_nil hNe, List.nil_append]; simp only [runMoves_append_snd, runMoves, h0, h1, h2, h3, h4, h5, h6, List.nil_append, List.append_nil, List.append_assoc]
theorem storedStates_split81_cases {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₁' stA₂ stB : DY.Libsignal.TripleRatchet.TRState} (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)).1) (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄)).1) (hstA₁ : stA₁ = iniAliceStartState tr₁ r.bob o₁) (hstA₁' : stA₁' = encSt tr₂ stA₁ cl₁) (hstA₂ : stA₂ = iniAliceStartState tr₄ r.bob o₂) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅) post₅) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o₁) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2)) (hm₃ : ∀ j : Nat, (((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).at? j : Option TRStEntry) = if j = ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).length - 1 then some (TRStE r.bob stB) else (tr_bob.at? j : Option TRStEntry)) (hm₄ : (Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄ = iniAliceStartTr tr₄ r.alice r.bob o₂) (hm₅ : (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅ = encNextTr tr₅ r.alice s₅ stA₂ cl₅ (tr₅.length + 2)) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hls : ls ∈ storedStates r (runTraceMoves r (pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: mid₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅ :: post₅))) : ls = ⟨r.alice, stA₁⟩ ∨ ls = ⟨r.alice, stA₁'⟩ ∨ ls = ⟨r.alice, encSt tr₃ stA₁' cl₂⟩ ∨ ls = ⟨r.alice, stA₂⟩ ∨ ls = ⟨r.alice, encSt tr₅ stA₂ cl₅⟩ ∨ ls = ⟨r.bob, stB⟩ := by
  rw [runTrace_split81 htr₁ htr₂ htr₃ htr_bob htr₄ htr₅] at hls; obtain ⟨j, _, _, hat⟩ := mem_storedStates_iff.mp hls
  have hno₁ : NoTRState tr₁ := by rw [htr₁]; exact noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre₀
  have hat₂ : (tr₂.at? j : Option TRStEntry) =
      if j = tr₁.length + 8 then some (TRStE r.alice (iniAliceStartState tr₁ r.bob o₁)) else none := by
    rw [htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid₁ j, hm₀, at?_trSt_iniAliceStartTr_of_noTRState hno₁]
  have hat₃ : (tr₃.at? j : Option TRStEntry) =
      if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁))
      else if j = tr₁.length + 8 then some (TRStE r.alice (iniAliceStartState tr₁ r.bob o₁)) else none := by
    rw [htr₃, at?_trSt_of_movesFrom_invisibleNoEffect hmid₂ j, hm₁, at?_trSt_encNextTr, hat₂]
  have hat_bob : (tr_bob.at? j : Option TRStEntry) =
      if j = tr₃.length + 5 then some (TRStE r.alice (encSt tr₃ stA₁' cl₂))
      else if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁))
      else if j = tr₁.length + 8 then some (TRStE r.alice (iniAliceStartState tr₁ r.bob o₁)) else none := by
    rw [htr_bob, at?_trSt_of_movesFrom_invisibleNoEffect hmid₃ j, hm₂, at?_trSt_encNextTr, hat₃]
  have hat₄ : (tr₄.at? j : Option TRStEntry) =
      if j = ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).length - 1
      then some (TRStE r.bob stB)
      else if j = tr₃.length + 5 then some (TRStE r.alice (encSt tr₃ stA₁' cl₂))
      else if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁))
      else if j = tr₁.length + 8 then some (TRStE r.alice (iniAliceStartState tr₁ r.bob o₁)) else none := by
    rw [htr₄, at?_trSt_of_movesFrom_invisibleNoEffect hmid₄ j, hm₃ j, hat_bob]
  have hat₅ : (tr₅.at? j : Option TRStEntry) =
      if j = tr₄.length + 8 then some (TRStE r.alice (iniAliceStartState tr₄ r.bob o₂))
      else if j = ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).length - 1
      then some (TRStE r.bob stB)
      else if j = tr₃.length + 5 then some (TRStE r.alice (encSt tr₃ stA₁' cl₂))
      else if j = tr₂.length + 5 then some (TRStE r.alice (encSt tr₂ stA₁ cl₁))
      else if j = tr₁.length + 8 then some (TRStE r.alice (iniAliceStartState tr₁ r.bob o₁)) else none := by
    rw [htr₅, at?_trSt_of_movesFrom_invisibleNoEffect hmid₅ j, hm₄, CompPrefixInvAlice.at?_trSt_iniAliceStartTr, hat₄]
  rw [at?_trSt_of_movesFrom_invisibleNoEffect hpost₅ j, hm₅, at?_trSt_encNextTr, hat₅] at hat
  split_ifs at hat with hj₅ hj₄ hjb hj₃ hj₂ hj₁
  · cases hat; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · cases hat; exact Or.inr (Or.inr (Or.inr (Or.inl (hstA₂ ▸ rfl))))
  · cases hat; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · cases hat; exact Or.inr (Or.inr (Or.inl rfl))
  · cases hat; exact Or.inr (Or.inl (hstA₁' ▸ rfl))
  · cases hat; exact Or.inl (hstA₁ ▸ rfl)
theorem pt_terms_split81_mem (hNe : r.alice ≠ r.bob) {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₁' stA₂ : DY.Libsignal.TripleRatchet.TRState} (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)).1) (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄)).1) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅) post₅) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o₁) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2)) (hm₄ : (Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄ = iniAliceStartTr tr₄ r.alice r.bob o₂) (hm₅ : (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅ = encNextTr tr₅ r.alice s₅ stA₂ cl₅ (tr₅.length + 2)) {v : VisEntry} (hv : v ∈ runVis r (pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂ :: mid₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅ :: post₅)) (hkind : v.kind = .pt) {u : DY.Bytes} (hu : u ∈ v.terms) : u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 ∨ u = randTerm tr₅.length 32 := by
  rw [runVis_split81 hNe htr₁ htr₂ htr₃ htr_bob htr₄ htr₅ hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅, aliceStart_vis_eq, encrypt_vis_eq, encrypt_vis_eq, bobStart_vis_eq, aliceStart_vis_eq, encrypt_vis_eq, hm₀, hm₁, hm₂, hm₄, hm₅, List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hv
  rcases hv with ((((hv₀ | hv₁) | hv₂) | hv₃) | hv₄) | hv₅
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₁; rw [List.mem_append] at hv₁; rcases hv₁ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl
      · exact Or.inl (List.mem_singleton.mp hu)
      · cases hkind
    · cases w₁ with
      | none => rw [mem_encSend_encNextTr_none hv_send] at hkind; cases hkind
      | some ec => rcases ec with ⟨e, c⟩; rw [mem_encSend_encNextTr_some hv_send] at hkind; cases hkind
  · unfold encVis at hv₂; rw [List.mem_append] at hv₂; rcases hv₂ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl
      · exact Or.inr (Or.inl (List.mem_singleton.mp hu))
      · cases hkind
    · cases w₂ with
      | none => rw [mem_encSend_encNextTr_none hv_send] at hkind; cases hkind
      | some ec => rcases ec with ⟨e, c⟩; rw [mem_encSend_encNextTr_some hv_send] at hkind; cases hkind
  · rcases xpl_bobVis_kind (List.mem_of_mem_take hv₃) with hk | hk | hk <;> (rw [hkind] at hk; cases hk)
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₄) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₅; rw [List.mem_append] at hv₅; rcases hv₅ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl
      · exact Or.inr (Or.inr (List.mem_singleton.mp hu))
      · cases hkind
    · cases w₅ with
      | none => rw [mem_encSend_encNextTr_none hv_send] at hkind; cases hkind
      | some ec => rcases ec with ⟨e, c⟩; rw [mem_encSend_encNextTr_some hv_send] at hkind; cases hkind
theorem send_terms_split81_mem (hNe : r.alice ≠ r.bob) {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₁' stA₂ : DY.Libsignal.TripleRatchet.TRState} (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)).1) (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄)).1) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))).next tr₅) post₅) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o₁) (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2)) (hm₄ : (Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄ = iniAliceStartTr tr₄ r.alice r.bob o₂) (hm₅ : (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))).next tr₅ = encNextTr tr₅ r.alice s₅ stA₂ cl₅ (tr₅.length + 2)) {v : VisEntry} (hv : v ∈ runVis r (pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅)) (hkind : v.kind = .send) {u : DY.Bytes} (hu : u ∈ v.terms) : u = o₁.ek ∨ u = o₁.ct ∨ u = encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∨ u = encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∨ u = o₂.ek ∨ u = o₂.ct ∨ u = encOut tr₅ stA₂ cl₅ (tr₅.length + 2) := by
  have hek₂ : NetMsgAt o₁.ek (tr₁.length + 3) tr₂ := by rw [htr₂]; exact (hm₀ ▸ netMsgAt_ek_iniAliceStartTr tr₁ r.alice r.bob o₁).mono (CompPrefixInvEnc.runMoves_le mid₁ _)
  have hct₂ : NetMsgAt o₁.ct (tr₁.length + 4) tr₂ := by rw [htr₂]; exact (hm₀ ▸ netMsgAt_ct_iniAliceStartTr tr₁ r.alice r.bob o₁).mono (CompPrefixInvEnc.runMoves_le mid₁ _)
  have hek₃ : NetMsgAt o₁.ek (tr₁.length + 3) tr₃ := by rw [htr₃]; exact (hek₂.mono (Move.le_next _ _)).mono (CompPrefixInvEnc.runMoves_le mid₂ _)
  have hct₃ : NetMsgAt o₁.ct (tr₁.length + 4) tr₃ := by rw [htr₃]; exact (hct₂.mono (Move.le_next _ _)).mono (CompPrefixInvEnc.runMoves_le mid₂ _)
  have hek₅ : NetMsgAt o₂.ek (tr₄.length + 3) tr₅ := by rw [htr₅]; exact (hm₄ ▸ netMsgAt_ek_iniAliceStartTr tr₄ r.alice r.bob o₂).mono (CompPrefixInvEnc.runMoves_le mid₅ _)
  have hct₅ : NetMsgAt o₂.ct (tr₄.length + 4) tr₅ := by rw [htr₅]; exact (hm₄ ▸ netMsgAt_ct_iniAliceStartTr tr₄ r.alice r.bob o₂).mono (CompPrefixInvEnc.runMoves_le mid₅ _)
  have hrec₂ : received tr₂ [tr₁.length + 3, tr₁.length + 4] = [o₁.ek, o₁.ct] := by unfold received; simp only [List.filterMap_cons, List.filterMap_nil, CompRVariantFree38.getMessageSentAt_of_netMsgAt hek₂, CompRVariantFree38.getMessageSentAt_of_netMsgAt hct₂]
  have hrec₃ : received tr₃ [tr₁.length + 3, tr₁.length + 4] = [o₁.ek, o₁.ct] := by unfold received; simp only [List.filterMap_cons, List.filterMap_nil, CompRVariantFree38.getMessageSentAt_of_netMsgAt hek₃, CompRVariantFree38.getMessageSentAt_of_netMsgAt hct₃]
  have hrec₅ : received tr₅ [tr₄.length + 3, tr₄.length + 4] = [o₂.ek, o₂.ct] := by unfold received; simp only [List.filterMap_cons, List.filterMap_nil, CompRVariantFree38.getMessageSentAt_of_netMsgAt hek₅, CompRVariantFree38.getMessageSentAt_of_netMsgAt hct₅]
  rw [runVis_split81 hNe htr₁ htr₂ htr₃ htr_bob htr₄ htr₅ hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅, aliceStart_vis_eq, encrypt_vis_eq, encrypt_vis_eq, bobStart_vis_eq, aliceStart_vis_eq, encrypt_vis_eq, hm₀, hm₁, hm₂, hm₄, hm₅, List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hv
  rcases hv with ((((hv₀ | hv₁) | hv₂) | hv₃) | hv₄) | hv₅
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₀) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₁; rw [List.mem_append] at hv₁; rcases hv₁ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hkind
    · rw [mem_encSend_encNextTr_some hv_send] at hu; dsimp only at hu; rw [hrec₂] at hu
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  · unfold encVis at hv₂; rw [List.mem_append] at hv₂; rcases hv₂ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hkind
    · rw [mem_encSend_encNextTr_some hv_send] at hu; dsimp only at hu; rw [hrec₃] at hu
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rcases xpl_bobVis_kind (List.mem_of_mem_take hv₃) with hk | hk | hk <;> (rw [hkind] at hk; cases hk)
  · rcases xpl_aliceVis_kind (List.mem_of_mem_take hv₄) with hk | hk <;> (rw [hkind] at hk; cases hk)
  · unfold encVis at hv₅; rw [List.mem_append] at hv₅; rcases hv₅ with hv_draws | hv_send
    · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hkind
    · rw [mem_encSend_encNextTr_some hv_send] at hu; dsimp only at hu; rw [hrec₅] at hu
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
theorem split81PrefixEnumOn_of_shape_gen (hNe : r.alice ≠ r.bob)
    {stB : DY.Libsignal.TripleRatchet.TRState} {PBob : DY.Bytes → Prop}
    (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1)
    (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1)
    (htr₃ : tr₃ = (runMoves mid₂
      ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂)).1)
    (htr_bob : tr_bob = (runMoves mid₃
      ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃)).1)
    (htr₄ : tr₄ = (runMoves mid₄
      ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)).1)
    (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄)).1)
    (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀)
    (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁) mid₁)
    (hmid₂ : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) mid₂)
    (hmid₃ : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃) mid₃)
    (hmid₄ : MovesFrom InvisibleNoEffect
      ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob) mid₄)
    (hmid₅ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄) mid₅)
    (hpost₅ : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))).next tr₅) post₅)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ =
      iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none))
    (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ =
      encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2))
    (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ =
      encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2))
    (hm₃ : ∀ j : Nat,
      (((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).at? j : Option TRStEntry) =
        if j = ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).length - 1
        then some (TRStE r.bob stB) else (tr_bob.at? j : Option TRStEntry))
    (hm₄ : (Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂).next tr₄ =
      iniAliceStartTr tr₄ r.alice r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none))
    (hm₅ : (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))).next tr₅ =
      encNextTr tr₅ r.alice s₅ (iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₅ (tr₅.length + 2))
    (hPBob : PBob (serBob r stB)) :
    let ms' := pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃ ++ Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅
    let o₁ := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := Census443Defs.iniAliceStartState tr₁ r.bob o₁
    let stA₁' := Census443Defs.encSt tr₂ stA₁ cl₁
    let o₂ := Census443Defs.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₂ := Census443Defs.iniAliceStartState tr₄ r.bob o₂
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), (u = o₁.ek ∨ u = o₁.ct ∨ u = Census443Defs.encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∨ u = Census443Defs.encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∨ u = o₂.ek ∨ u = o₂.ct ∨ u = Census443Defs.encOut tr₅ stA₂ cl₅ (tr₅.length + 2) ∨ u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 ∨ u = randTerm tr₅.length 32 ∨ u = serAlice r stA₁ ∨ u = serAlice r stA₁' ∨ u = serAlice r (Census443Defs.encSt tr₃ stA₁' cl₂) ∨ u = serAlice r stA₂ ∨ u = serAlice r (Census443Defs.encSt tr₅ stA₂ cl₅) ∨ PBob u) ∨
      u ∈ storedSecrets (runTraceMoves r ms') := by
  dsimp only; intro u hu; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encOut_eq, census_encSt_eq]; unfold prefixTerms principalTerms plaintextTerms at hu; simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at hu
  rcases hu with ((⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩ | ⟨ls, hls, rfl⟩) | hsec) | ⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩
  · refine Or.inl ?_
    rcases send_terms_split81_mem hNe htr₁ htr₂ htr₃ htr_bob htr₄ htr₅
        hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hm₀ hm₁ hm₂ hm₄ hm₅ hv_mem hv_kind hu_v with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  · refine Or.inl ?_
    rcases storedStates_split81_cases htr₁ htr₂ htr₃ htr_bob htr₄ htr₅ rfl rfl rfl
        hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hm₀ hm₁ hm₂ hm₃ hm₄ hm₅ hls with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hPBob))))))))))))))
  · exact Or.inr hsec
  · refine Or.inl ?_
    rcases pt_terms_split81_mem hNe htr₁ htr₂ htr₃ htr_bob htr₄ htr₅
        hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hm₀ hm₁ hm₂ hm₄ hm₅ hv_mem hv_kind hu_v with
      h1 | h2 | h3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))))))
end Decomp
theorem effect_index_split81 {r : Records} {pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move} {m₀ m₁ m₂ m₃ m₄ m₅ : Move} (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect (m₀.next (runMoves pre₀ (setupTrace r)).1) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect (m₄.next (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect (m₅.next (runMoves mid₅ (m₄.next (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1)).1) post₅) {k : Nat} {m : Move} (hk : (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅)[k]? = some m) (hneff : ¬ NoSessionEffect (runTraceMoves r ((pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅).take k)) m) : k = pre₀.length ∨ k = pre₀.length + 1 + mid₁.length ∨ k = pre₀.length + 1 + mid₁.length + 1 + mid₂.length ∨ k = pre₀.length + 1 + mid₁.length + 1 + mid₂.length + 1 + mid₃.length ∨ k = pre₀.length + 1 + mid₁.length + 1 + mid₂.length + 1 + mid₃.length + 1 + mid₄.length ∨ k = pre₀.length + 1 + mid₁.length + 1 + mid₂.length + 1 + mid₃.length + 1 + mid₄.length + 1 + mid₅.length := by
  rw [xpl_runTrace_eq] at hneff
  have hassoc : pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ = pre₀ ++ m₀ :: (mid₁ ++ m₁ :: (mid₂ ++ m₂ :: (mid₃ ++ m₃ :: (mid₄ ++ m₄ :: (mid₅ ++ m₅ :: post₅))))) := by simp only [List.append_assoc, List.cons_append]
  rw [hassoc] at hk hneff
  rcases mem_or_of_not_noSessionEffect_append hpre₀ hk hneff with rfl | ⟨hge₁, hk₁, hneff₁⟩
  · exact Or.inl rfl
  · rcases mem_or_of_not_noSessionEffect_append hmid₁ hk₁ hneff₁ with heq₁ | ⟨hge₂, hk₂, hneff₂⟩
    · exact Or.inr (Or.inl (by omega))
    · rcases mem_or_of_not_noSessionEffect_append hmid₂ hk₂ hneff₂ with heq₂ | ⟨hge₃, hk₃, hneff₃⟩
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · rcases mem_or_of_not_noSessionEffect_append hmid₃ hk₃ hneff₃ with heq₃ | ⟨hge₄, hk₄, hneff₄⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · rcases mem_or_of_not_noSessionEffect_append hmid₄ hk₄ hneff₄ with heq₄ | ⟨hge₅, hk₅, hneff₅⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
          · rcases mem_or_of_not_noSessionEffect_append hmid₅ hk₅ hneff₅ with heq₅ | ⟨_, hk₆, hneff₆⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
            · exact absurd (noSessionEffect_of_movesFrom_invisibleNoEffect hpost₅ hk₆) hneff₆
theorem decomp81_links_pin
    {r : Records} {ms' pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move} {m₀ m₁ m₂ m₃ m₄ m₅ : Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    (hms' : ms' = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅)
    (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀)
    (hmid₁ : MovesFrom InvisibleNoEffect (m₀.next (runMoves pre₀ (setupTrace r)).1) mid₁)
    (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1) mid₂)
    (hmid₃ : MovesFrom InvisibleNoEffect
      (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1) mid₃)
    (hmid₄ : MovesFrom InvisibleNoEffect
      (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1) mid₄)
    (hmid₅ : MovesFrom InvisibleNoEffect
      (m₄.next (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1) mid₅)
    (hpost₅ : MovesFrom InvisibleNoEffect
      (m₅.next (runMoves mid₅ (m₄.next (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂ (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1)).1) post₅)
    (hm₃_not_alice : ∀ a b idS regB hb sh, m₃ ≠ Move.aliceStart a b idS regB hb sh)
    (hm₃_not_enc : ∀ me sIdx cl pq wrap, m₃ ≠ Move.encrypt me sIdx cl pq wrap)
    (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    ∃ (hb₁ hb₂ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ sh₂ s₁ s₂ s₅ : Nat),
      let w₁ := some (tr₁.length + 3, tr₁.length + 4)
      let w₂ := some (tr₄.length + 3, tr₄.length + 4)
      let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let stA₁ := iniAliceStartState tr₁ r.bob o₁
      let stA₁' := encSt tr₂ stA₁ cl₁
      let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let stA₂ := iniAliceStartState tr₄ r.bob o₂
      m₀ = Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ ∧
      m₁ = Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁ ∧
      m₂ = Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₁ ∧
      m₄ = Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ ∧
      m₅ = Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₂ ∧
      tr₁ = (runMoves pre₀ (setupTrace r)).1 ∧
      tr₂ = (runMoves mid₁ (m₀.next tr₁)).1 ∧
      tr₃ = (runMoves mid₂ (m₁.next tr₂)).1 ∧
      tr₄ = (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂.next tr₃)).1)).1 ∧
      tr₅ = (runMoves mid₅ (m₄.next tr₄)).1 ∧
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o₁ ∧
      m₁.next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2) ∧
      m₂.next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2) ∧
      m₄.next tr₄ = iniAliceStartTr tr₄ r.alice r.bob o₂ ∧
      m₅.next tr₅ = encNextTr tr₅ r.alice s₅ stA₂ cl₅ (tr₅.length + 2) := by
  obtain ⟨_hnb, k₁, k₂, k₃, k₄, k₅, hb₁, hb₂, sh₁, sh₂, s₁, s₂, s₅, hk₁₂, hk₂₃, hk₃₄, hk₄₅, htr₁_k, hget₁, htr₂_k, hget₂, htr₃_k, hget₃, htr₄_k, hget₄, htr₅_k, hget₅, hnext₀, hnext₄, hnext₁, hnext₂, hnext₅⟩ := hlinks; rw [census_iniAliceStartTr_eq, census_iniAliceOut_eq] at hnext₀ hnext₄; rw [census_encNextTr_eq, census_iniAliceStartState_eq, census_iniAliceOut_eq] at hnext₁ hnext₅
  rw [census_encNextTr_eq, census_encSt_eq, census_iniAliceStartState_eq, census_iniAliceOut_eq] at hnext₂
  let m₀' := Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁
  let w₁ := some (tr₁.length + 3, tr₁.length + 4); let w₂ := some (tr₄.length + 3, tr₄.length + 4)
  let m₁' := Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁
  let m₂' := Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₁
  let m₄' := Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂
  let m₅' := Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₂
  have hneff₁ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₁)) m₀' := by rw [htr₁_k]; exact not_noSessionEffect_of_next_eq_iniAliceStartTr hnext₀
  have hneff₂ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₂)) m₁' := by rw [htr₂_k]; exact not_noSessionEffect_of_next_eq_encNextTr hnext₁
  have hneff₃ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₃)) m₂' := by rw [htr₃_k]; exact not_noSessionEffect_of_next_eq_encNextTr hnext₂
  have hneff₄ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₄)) m₄' := by rw [htr₄_k]; exact not_noSessionEffect_of_next_eq_iniAliceStartTr hnext₄
  have hneff₅ : ¬ NoSessionEffect (runTraceMoves r (ms'.take k₅)) m₅' := by rw [htr₅_k]; exact not_noSessionEffect_of_next_eq_encNextTr hnext₅
  rw [hms'] at hget₁ hget₂ hget₃ hget₄ hget₅ hneff₁ hneff₂ hneff₃ hneff₄ hneff₅; have hor₁ := effect_index_split81 hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hget₁ hneff₁; have hor₂ := effect_index_split81 hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hget₂ hneff₂; have hor₃ := effect_index_split81 hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hget₃ hneff₃; have hor₄ := effect_index_split81 hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hget₄ hneff₄
  have hor₅ := effect_index_split81 hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hget₅ hneff₅
  have hget_bob : (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅)[ (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃).length]? = some m₃ := by
    have h := getElem?_middle (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃) (mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅) m₃
    simp only [List.append_assoc, List.cons_append] at h ⊢; exact h
  have hlen_bob : (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃).length = pre₀.length + 1 + mid₁.length + 1 + mid₂.length + 1 + mid₃.length := by simp only [List.length_append, List.length_cons]; omega
  have hne_bob : ∀ {k : Nat} {m : Move}, (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅)[k]? = some m → m ≠ m₃ → k ≠ pre₀.length + 1 + mid₁.length + 1 + mid₂.length + 1 + mid₃.length := by intro k m hk hne hk_eq; rw [← hlen_bob] at hk_eq; subst hk_eq; rw [hget_bob] at hk; exact hne (Option.some.inj hk).symm
  have hk₁_ne := hne_bob hget₁ (fun h => hm₃_not_alice _ _ _ _ _ _ h.symm)
  have hk₂_ne := hne_bob hget₂ (fun h => hm₃_not_enc _ _ _ _ _ h.symm)
  have hk₃_ne := hne_bob hget₃ (fun h => hm₃_not_enc _ _ _ _ _ h.symm)
  have hk₄_ne := hne_bob hget₄ (fun h => hm₃_not_alice _ _ _ _ _ _ h.symm)
  have hk₅_ne := hne_bob hget₅ (fun h => hm₃_not_enc _ _ _ _ _ h.symm)
  have hk₁_eq : k₁ = pre₀.length := by omega
  have hk₂_eq : k₂ = (pre₀ ++ m₀ :: mid₁).length := by simp only [List.length_append, List.length_cons]; omega
  have hk₃_eq : k₃ = (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂).length := by simp only [List.length_append, List.length_cons]; omega
  have hk₄_eq : k₄ = (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄).length := by simp only [List.length_append, List.length_cons]; omega
  have hk₅_eq : k₅ = (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅).length := by simp only [List.length_append, List.length_cons]; omega
  subst hk₁_eq hk₂_eq hk₃_eq hk₄_eq hk₅_eq
  have hm₀_eq : m₀ = m₀' := by
    have h := getElem?_middle pre₀ (mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅) m₀
    simp only [List.append_assoc, List.cons_append] at h hget₁; exact Option.some.inj (h.symm.trans hget₁)
  have hm₁_eq : m₁ = m₁' := by
    have h := getElem?_middle (pre₀ ++ m₀ :: mid₁) (mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅) m₁
    simp only [List.append_assoc, List.cons_append] at h hget₂; exact Option.some.inj (h.symm.trans hget₂)
  have hm₂_eq : m₂ = m₂' := by
    have h := getElem?_middle (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂) (mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅) m₂
    simp only [List.append_assoc, List.cons_append] at h hget₃; exact Option.some.inj (h.symm.trans hget₃)
  have hm₄_eq : m₄ = m₄' := by
    have h := getElem?_middle (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄) (mid₅ ++ m₅ :: post₅) m₄
    simp only [List.append_assoc, List.cons_append] at h hget₄; exact Option.some.inj (h.symm.trans hget₄)
  have hm₅_eq : m₅ = m₅' := by
    have h := getElem?_middle (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅) post₅ m₅
    simp only [List.append_assoc, List.cons_append] at h hget₅; exact Option.some.inj (h.symm.trans hget₅)
  subst hm₀_eq hm₁_eq hm₂_eq hm₄_eq hm₅_eq
  have htr₁_eq : tr₁ = (runMoves pre₀ (setupTrace r)).1 := by rw [← htr₁_k, hms']; have h := take_middle pre₀ (mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅) m₀'; simp only [List.append_assoc, List.cons_append] at h ⊢; rw [h, xpl_runTrace_eq]
  have htr₂_eq : tr₂ = (runMoves mid₁ (m₀'.next tr₁)).1 := by
    rw [← htr₂_k, hms']; have h := take_middle (pre₀ ++ m₀' :: mid₁) (mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅) m₁'
    have hassoc : pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅ = (pre₀ ++ m₀' :: mid₁) ++ m₁' :: (mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅) := by simp only [List.append_assoc, List.cons_append]
    rw [hassoc, h, xpl_runTrace_eq, runMoves_append_fst, ← htr₁_eq]; rfl
  have htr₃_eq : tr₃ = (runMoves mid₂ (m₁'.next tr₂)).1 := by
    rw [← htr₃_k, hms']; have h := take_middle (pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂) (mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅) m₂'
    have hassoc : pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅ = (pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂) ++ m₂' :: (mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅) := by simp only [List.append_assoc, List.cons_append]
    rw [hassoc, h, xpl_runTrace_eq, runMoves_append_fst, runMoves_append_fst, ← htr₁_eq]
    change (runMoves mid₂ (m₁'.next (runMoves mid₁ (m₀'.next tr₁)).1)).1 = _; rw [← htr₂_eq]
  have htr₄_eq : tr₄ = (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂'.next tr₃)).1)).1 := by
    rw [← htr₄_k, hms']; have h := take_middle (pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄) (mid₅ ++ m₅' :: post₅) m₄'
    have hassoc : pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅ ++ m₅' :: post₅ = (pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄) ++ m₄' :: (mid₅ ++ m₅' :: post₅) := by simp only [List.append_assoc, List.cons_append]
    rw [hassoc, h, xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves, ← htr₁_eq, ← htr₂_eq, ← htr₃_eq]
  have htr₅_eq : tr₅ = (runMoves mid₅ (m₄'.next tr₄)).1 := by rw [← htr₅_k, hms']; have h := take_middle (pre₀ ++ m₀' :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄' :: mid₅) post₅ m₅'; rw [h, xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves, ← htr₁_eq, ← htr₂_eq, ← htr₃_eq, ← htr₄_eq]
  exact ⟨hb₁, hb₂, sh₁, sh₂, s₁, s₂, s₅, rfl, rfl, rfl, rfl, rfl, htr₁_eq, htr₂_eq, htr₃_eq, htr₄_eq, htr₅_eq, hnext₀, hnext₁, hnext₂, hnext₄, hnext₅⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
