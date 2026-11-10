/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0Mem
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Assembly
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Join
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompRX0Mem Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open CryptoProofLib.Refinement (ExternInterpretation)
theorem aliceOut_eq_iniAliceOut (tr : ExecTrace) (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) : aliceOut tr ikA ikB spk pqpk opk = CompPrefixInvAlice.iniAliceOut tr ikA ikB spk pqpk opk :=
  rfl
theorem aliceStartState_eq_ini (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : CompPrefixInvBundle.aliceStartState tr b o = CompPrefixInvAlice.iniAliceStartState tr b o :=
  rfl
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
theorem swap_and_mem_split38 {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {τ₁ : List MachineEvent} {b w : HwBytes} {p q₀ : PreKeyFields} {pre mid post : List Move} {m₀ : Move} {me : Participant} {s cl e c' : Nat} {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA : DY.Libsignal.TripleRatchet.TRState} {ek₀ : DY.Bytes} (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid (m₀.next tr₁)).1) (hek : NetMsgAt o.ek (tr₁.length + 3) tr₂) (hct : NetMsgAt o.ct (tr₁.length + 4) tr₂) (hsm : CompRPreKeyWire.SendMatchesMoves compI0 r S g w (received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)])) (hns : stA.ns = 0) (hpn : stA.pn = 0) (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) (hbk₀ : q₀.baseKey = ecKey (gamma compI0 S g o.ek)) (hkc₀ : q₀.kyberCiphertext = some (kyberKey (gamma compI0 S g o.ct))) (hp : parsePreKeyWire b = some p) (hbk : p.baseKey.take 33 = ecKey (gamma compI0 S g ek₀)) (hkc : p.kyberCiphertext = q₀.kyberCiphertext) (hpm : p.message = q₀.message) (hcan : InnerWireCanonical p) (hout : CompRPreKeyWire.PreKeyOuterMatches compI0 r b p) (hex : ExplainsMoves compI0 r S who ok g (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post) τ₁) (hkek : ek₀.AttackerKnows (runTraceMoves r (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post))) (hkct : o.ct.AttackerKnows (runTraceMoves r (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post))) (hkmsg : (encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post))) : ExplainsMoves compI0 r S who ok g (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) τ₁ ∧ (⟨ek₀, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩ : PreKeyRep) ∈ preKeyRepresentations compI0 r S g (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) b := by
  subst htr₁; have hγ := hγ_of_sendMatches hsm hlen hq₀ hbk₀ hkc₀; obtain ⟨_, _, _, _, _, hmsg₀⟩ := sendMatches_append_inv hsm hlen hq₀
  have hγm : gamma compI0 S g (encOut tr₂ stA cl (tr₂.length + 2)) = p.message := by rw [hpm, hmsg₀]
  have hfi : FaithfulInner compI0 S g (encOut tr₂ stA cl (tr₂.length + 2)) p := faithfulInner_of_gamma_encOut S g tr₂ stA cl _ p hns hpn hγm hcan; have hmem := x0_mem_of_parts hkek hkct hkmsg hp hbk (by rw [hkc, hkc₀]) hγm.symm hout hfi
  have hk : (pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post)[(pre ++ m₀ :: mid).length]? =
      some (.encrypt me s cl (tr₂.length + 2) (some (e, c'))) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have htake : (pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).take
      (pre ++ m₀ :: mid).length = pre ++ m₀ :: mid := List.take_left
  have hrt : runTraceMoves r (pre ++ m₀ :: mid) = tr₂ := (by have h := CompPrefixInvStruct.runTrace_append r [] (pre ++ m₀ :: mid); rw [List.nil_append] at h; rw [h, htr₂, CompPrefixInvStruct.runMoves_append_fst]; rfl)
  have hset : (pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).set
      (pre ++ m₀ :: mid).length
      (.encrypt me s cl (tr₂.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))) = pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2)
        (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post := by
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl
  have hγ' :
      (received (runTraceMoves r ((pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).take (pre ++ m₀ :: mid).length)) [e, c']).map (gamma compI0 S g) = (received (runTraceMoves r ((pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).take (pre ++ m₀ :: mid).length)) [(runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4]).map
        (gamma compI0 S g) := by
    rw [htake, hrt, hγ, CompRX0Assembly.received_pair_of_netMsgAt hek hct]; rfl
  have hex' := CompPrefixInvSwap.explains_set_wrap hk hγ' hex
  have htr_eq := CompPrefixInvSwap.runTrace_set_wrap
    (r := r)
    (w₂ := some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) hk
  rw [hset] at hex' htr_eq; refine ⟨hex', ?_⟩; unfold preKeyRepresentations at hmem ⊢; rw [htr_eq]; exact hmem
end Symbolic.BugInjection.Proofs.Common443.CompRX0Join
