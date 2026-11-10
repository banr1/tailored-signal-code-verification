/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
public import Symbolic.Proofs.Swarm.UA.ClassicalBridge
public import Symbolic.Proofs.Swarm.UA.XlateInv
public import Symbolic.Proofs.Swarm.UA.XlateSteps
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredClassical
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
public import Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# CLI Event Bridge

Bridge lemmas from `Explains` and `CollisionAfterExplainedPrefix` (via their `*Classical`
counterparts) to move-level `ExplainsCli`, `NoBrk`, `ReadCollision`, and `BobStartCollision`
obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Common443.CliEventBridge

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Swarm.CREF (SemReady b1_setupRandomsAt_eq b1_setupPublic_5 b1_setupPublic_6 b1_setupPublic_7)
open Symbolic.Proofs.Swarm.UA.Defs (runOk flatEntry flatExit failedSend flatEvent flatEvents callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil breakFree_of_cons
    breakFree_append breakFree_run_cons explainsClassical_of explains_of_classical
    readCollisionCli_of_classical readCollisionCliClassical_of acceptsViaCli_eq)
open Symbolic.Proofs.Swarm.UA.XlateInv (xlate_inv schedFits_prefix)
open Symbolic.Proofs.Swarm.UA.XlateSteps (VisSendPtEq memoCollisionOn_iff_of_terms
    recvRepresentations_eq preKeyRepresentations_eq recvCollision_iff reselectCollision_iff
    bobStartCollision_iff gamma_randTerm_eq stepIn_next run_bind_pure_snd attackerSend_next_eq_network)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy (NoBrk NoNewPQEv noNewPQEv_refl
    noNewPQEv_append_other noNewPQEv_append_pq setupTrace_eventLoggedAt_cases noBrk_of_le)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves RndE NetE TRStE PQStE CEvE TREvE)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (storeLocalState_tr_snd_eq logEvent_snd_eq)

section UnsealedSetupGamma
unseal DY.Bytes
private local instance (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interp S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
private local instance (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll interp S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
private local instance (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk interp) (concretizeAll interp S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
private local instance (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll interp S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
private local instance (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll interp S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
private theorem gamma_lit_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    gamma interp S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll interp S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interp S g)]; rfl
private theorem gamma_concat_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (l r : DY.Bytes) :
    gamma interp S g (DY.Concat.concat l r) = gamma interp S g l ++ gamma interp S g r := by
  unfold gamma gamma'
  show ((({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (concretizeAll interp S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interp S g)]; rfl
private theorem gamma_dhPk_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    gamma interp S g (DY.DiffieHellman.dhPk sk) =
      (interp DY.Libsignal.Refinement.x25519PublicKeySymbol [clamp (gamma interp S g sk)]).getD [] := by
  unfold gamma gamma' DY.DiffieHellman.dhPk
  show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll interp S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeDhPk interp) (concretizeAll interp S g)]; rfl
private theorem gamma_kemPk_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (seed : DY.Bytes) :
    gamma interp S g (DY.PQKem.kemPk seed) = S.kemPk (gamma interp S g seed) := by
  unfold gamma gamma' DY.PQKem.kemPk
  show ((({ sk := seed } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (concretizeAll interp S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll interp S g)]; rfl
private theorem gamma_sign_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sk nonce msg : DY.Bytes) :
    gamma interp S g (DY.Signature.sign sk nonce msg) =
      S.sign (gamma interp S g sk) (gamma interp S g nonce) (gamma interp S g msg) := by
  unfold gamma gamma' DY.Signature.sign
  show ((({ sk := sk, nonce := nonce, msg := msg } : DY.Signature.Sign.SubF DY.Bytes).pack).rec (concretizeAll interp S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll interp S g)]; rfl
private theorem gamma_encodeEC_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk : DY.Bytes) :
    gamma interp S g (DY.Libsignal.PQXDH.encodeEC pk) = 0x05#8 :: gamma interp S g pk := by
  unfold DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte; rw [gamma_concat_eq, gamma_lit_eq]; rfl
private theorem gamma_encodeKEM_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk : DY.Bytes) :
    gamma interp S g (DY.Libsignal.PQXDH.encodeKEM pk) = 0x08#8 :: gamma interp S g pk := by
  unfold DY.Libsignal.PQXDH.encodeKEM DY.Libsignal.TripleRatchet.litByte; rw [gamma_concat_eq, gamma_lit_eq]; rfl
end UnsealedSetupGamma

theorem gamma_setupPublic_eq_of_sigma_eq (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g₁ g₂ : Ghost) (hwf : ProtocolSetupWF r)
    (h₁ : ∀ p ∈ setupRandomsAt r, g₁.σ p.1 p.2 = r.fresh p.1 p.2)
    (h₂ : ∀ p ∈ setupRandomsAt r, g₂.σ p.1 p.2 = r.fresh p.1 p.2) :
    ∀ t ∈ [r.spkSigTerm, r.pqpkPubTerm, r.pqpkSigTerm],
      gamma interp S g₁ t = gamma interp S g₂ t := by
  have hmem : ∀ p ∈ ([(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] : List (Nat × Nat)),
      g₁.σ p.1 p.2 = g₂.σ p.1 p.2 := fun p hp => by
    have hp' : p ∈ setupRandomsAt r := by rw [b1_setupRandomsAt_eq r hwf.1]; exact List.mem_append_left _ hp
    rw [h₁ p hp', h₂ p hp']
  have h5 := hmem (5, 32) (by decide); have h10 := hmem (10, 32) (by decide)
  have h11 := hmem (11, 64) (by decide); have h16 := hmem (16, 64) (by decide)
  have h17 := hmem (17, 64) (by decide)
  intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · unfold ProtocolSetup.spkSigTerm
    rw [b1_setupPublic_5 r hwf.1, gamma_sign_eq, gamma_sign_eq,
      gamma_randTerm_eq interp S g₁ 5 32 (by decide), gamma_randTerm_eq interp S g₂ 5 32 (by decide),
      gamma_randTerm_eq interp S g₁ 11 64 (by decide), gamma_randTerm_eq interp S g₂ 11 64 (by decide),
      gamma_encodeEC_eq, gamma_encodeEC_eq, gamma_dhPk_eq, gamma_dhPk_eq,
      gamma_randTerm_eq interp S g₁ 10 32 (by decide), gamma_randTerm_eq interp S g₂ 10 32 (by decide),
      h5, h10, h11]
  · unfold ProtocolSetup.pqpkPubTerm
    rw [b1_setupPublic_6 r hwf.1, gamma_kemPk_eq, gamma_kemPk_eq,
      gamma_randTerm_eq interp S g₁ 16 64 (by decide), gamma_randTerm_eq interp S g₂ 16 64 (by decide), h16]
  · unfold ProtocolSetup.pqpkSigTerm
    rw [b1_setupPublic_7 r hwf.1, gamma_sign_eq, gamma_sign_eq,
      gamma_randTerm_eq interp S g₁ 5 32 (by decide), gamma_randTerm_eq interp S g₂ 5 32 (by decide),
      gamma_randTerm_eq interp S g₁ 17 64 (by decide), gamma_randTerm_eq interp S g₂ 17 64 (by decide),
      gamma_encodeKEM_eq, gamma_encodeKEM_eq, gamma_kemPk_eq, gamma_kemPk_eq,
      gamma_randTerm_eq interp S g₁ 16 64 (by decide), gamma_randTerm_eq interp S g₂ 16 64 (by decide),
      h5, h16, h17]

theorem semReady_of_compat {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    (hwf : ProtocolSetupWF r) (hc : GhostAndSemMatchSetup interp r S g) : SemReady interp r S :=
  fun g' hσ' => ⟨hσ', fun t ht =>
    gamma_setupPublic_eq_of_sigma_eq interp r S g' g hwf hσ' hc.1 t ht ▸ hc.2.1 t ht, hc.2.2⟩

theorem breakFree_cons_run (ev : RunEvent) {evs : List CliEvent}
    (h : BreakFree evs) : BreakFree (.run ev :: evs) :=
  breakFree_run_cons.mpr h

theorem breakFree_map_run : ∀ (rs : List RunEvent), BreakFree (rs.map CliEvent.run)
  | [] => breakFree_nil
  | ev :: rs => breakFree_cons_run ev (breakFree_map_run rs)

theorem signalMsgAcceptedOnlyViaCollisionClassical_of {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs₁ : List CliEvent} {ev : RunEvent} {b : HwBytes} (hbf : BreakFree evs₁)
    (h : SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev b) :
    SignalMsgAcceptedOnlyViaCollisionClassical interp r S g ss evs₁ ev b := by
  refine ⟨h.1, fun g' ss' vis' hex' hnrc => ?_⟩
  rcases h.2 g' ss' vis' (explains_of_classical hex')
      (fun hrc => hnrc (readCollisionCliClassical_of hrc hbf)) with hleft | ⟨⟨t, ht, hacct⟩, hright⟩
  · exact Or.inl hleft
  · exact Or.inr ⟨⟨t, ht, Eq.mp (congrFun (acceptsViaCli_eq hbf) t) hacct⟩,
      fun t' ht' hacct' => hright t' ht' (Eq.mpr (congrFun (acceptsViaCli_eq hbf) t') hacct')⟩

theorem preKeyStartCollidesOrRejectsClassical_of {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs₁ : List CliEvent} {b : HwBytes} {p : PreKeyFields} (hbf : BreakFree evs₁)
    (h : PreKeyStartCollidesOrRejects interp r S g ss evs₁ b p) :
    PreKeyStartCollidesOrRejectsClassical interp r S g ss evs₁ b p :=
  ⟨h.1, h.2.imp id fun hall g' ss' vis' hex' hnrc =>
    hall g' ss' vis' (explains_of_classical hex')
      (fun hrc => hnrc (readCollisionCliClassical_of hrc hbf))⟩

theorem prefixExplainingGhosts_subset_classical {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs₁ : List CliEvent} {g' : Ghost}
    (hg' : g' ∈ PrefixExplainingGhostsClassical interp r S g ss evs₁) :
    g' ∈ PrefixExplainingGhosts interp r S g ss evs₁ :=
  let ⟨hσ, vis', hex'⟩ := hg'; ⟨hσ, vis', explains_of_classical hex'⟩

theorem nextEventCollidesClassical_of {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent} (hbf : BreakFree evs₁)
    (h : NextEventCollides interp r S g ss vis evs₁ ev) :
    NextEventCollidesClassical interp r S g ss vis evs₁ ev := by
  rcases hcmd : ev.cmd with peer | peer | ⟨peer, bundle⟩ <;>
    simp only [NextEventCollides, NextEventCollidesClassical, hcmd] at h ⊢
  · exact ⟨h.1, fun g' hg' => h.2 g' (prefixExplainingGhosts_subset_classical hg')⟩
  · rcases h with ⟨hout, hinput⟩; refine ⟨hout, ?_⟩
    rcases hinp : ev.input with _ | ⟨tag, body⟩ <;> rw [hinp] at hinput
    · exact hinput
    · rcases hinput with ⟨htag, hsig⟩ | ⟨p, hp, ⟨hkb, hver, hik, hsig⟩ | ⟨hnkb, hpk⟩⟩
      · exact Or.inl ⟨htag, signalMsgAcceptedOnlyViaCollisionClassical_of hbf hsig⟩
      · exact Or.inr ⟨p, hp, Or.inl ⟨hkb, hver, hik, signalMsgAcceptedOnlyViaCollisionClassical_of hbf hsig⟩⟩
      · exact Or.inr ⟨p, hp, Or.inr ⟨hnkb, preKeyStartCollidesOrRejectsClassical_of hbf hpk⟩⟩

theorem collisionAfterExplainedPrefixClassical_of {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {evs : List CliEvent} (hbf : BreakFree evs)
    (h : CollisionAfterExplainedPrefix interp r S evs) :
    CollisionAfterExplainedPrefixClassical interp r S evs := by
  rcases h with ⟨evs₁, ev, evs₂, g, ss, vis, rfl, hex, hnext⟩
  have hbf₁ : BreakFree evs₁ := fun e he => hbf e (List.mem_append_left _ he)
  exact ⟨evs₁, ev, evs₂, g, ss, vis, rfl, explainsClassical_of hex hbf₁,
    nextEventCollidesClassical_of hbf₁ hnext⟩

@[reducible] def isBrkPQEv : DY.Libsignal.PQXDH.PQXDHEvent → Bool
  | .BrokenDH | .BrokenKEM => true | _ => false

private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b
private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a
private theorem preserves_genRand {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace}
    (n : Nat) : Preserves (NoNewPQEv P tr₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (Runs.genRand tr n).2.symm ▸ noNewPQEv_append_other hInv (RndE n) rfl
private theorem preserves_sendMessage {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace}
    (m : DY.Bytes) : Preserves (NoNewPQEv P tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Runs.sendMessage tr m).2.symm ▸ noNewPQEv_append_other hInv (NetE m) rfl
private theorem preserves_storeLocalState_tr {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (p : Participant) (st : DY.Libsignal.TripleRatchet.TRState) :
    Preserves (NoNewPQEv P tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by rw [storeLocalState_tr_snd_eq]; exact noNewPQEv_append_other hInv (TRStE p st) rfl
private theorem preserves_storeLocalState_pq {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves (NoNewPQEv P tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (Runs.storeLocalState tr p st).2.symm ▸ noNewPQEv_append_other hInv (PQStE p st) rfl
private theorem preserves_logEventPQ {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace}
    (ev : DY.Libsignal.PQXDH.PQXDHEvent) (hne : P ev = false) :
    Preserves (NoNewPQEv P tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (Runs.logEvent tr ev).2.symm ▸ noNewPQEv_append_pq hInv ev hne
private theorem preserves_logEventC {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace}
    (ev : ComposedEvent) : Preserves (NoNewPQEv P tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPQEv_append_other hInv (CEvE ev) rfl
private theorem preserves_logEventTR {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace}
    (ev : DY.Libsignal.TripleRatchet.TREvent) :
    Preserves (NoNewPQEv P tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPQEv_append_other hInv (TREvE ev) rfl
private theorem preserves_getKey {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (NoNewPQEv P tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
private theorem preserves_lookupIdentity {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (p : Participant) (h : Nat) :
    Preserves (NoNewPQEv P tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity; refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split; exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _; exact Preserves.failure
private theorem preserves_logMessageKeyAndStore {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : DY.Libsignal.TripleRatchet.TRState) :
    Preserves (NoNewPQEv P tr₀)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_logEventTR _) fun _ => preserves_storeLocalState_tr _ _
private theorem preserves_dhRatchetStep {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (st : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) :
    Preserves (NoNewPQEv P tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ => Preserves.pure _
private theorem preserves_ensureReceiverChain {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (st : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) :
    Preserves (NoNewPQEv P tr₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure
private theorem preserves_logSkippedKeys {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    {tr₀ : ExecTrace} (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (NoNewPQEv P tr₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_logEventTR _) fun _ => ih _ _

local macro "noBrkPQ_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_genRand
  | with_reducible apply preserves_storeLocalState_tr
  | with_reducible apply preserves_storeLocalState_pq | with_reducible apply preserves_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_getKey | with_reducible apply preserves_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep
  | with_reducible apply preserves_ensureReceiverChain
  | with_reducible apply preserves_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength | with_reducible apply preserves_logMessageKeyAndStore
  | with_reducible apply preserves_logEventPQ _ (by rfl) | with_reducible apply preserves_logEventC
  | with_reducible apply preserves_logEventTR | split | with_reducible intro))

private theorem preserves_aliceHandshake_noNewBrkPQEv {tr₀ : ExecTrace} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (NoNewPQEv isBrkPQEv tr₀)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; noBrkPQ_tac

private theorem preserves_bobHandshake_noNewBrkPQEv {tr₀ : ExecTrace} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (NoNewPQEv isBrkPQEv tr₀)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; noBrkPQ_tac

private def stepToNonBrkMove : Step → Move
  | .network m => .attackerSend m
  | .aliceStart a b idStateIdx regIdxB bh => .aliceStart a b idStateIdx regIdxB bh 35
  | .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx => .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 0
  | .messageEncrypt me stateIdx coinsLen pqIdx => .encrypt me stateIdx coinsLen pqIdx none
  | .messageEncryptAbort me stateIdx => .encryptAbort me stateIdx
  | .messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
      .decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false
  | .messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
      .decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false
  | .compromiseIK q idx => .compromiseIK q idx | .compromiseSPK q idx => .compromiseSPK q idx
  | .compromisePQSPK q idx => .compromisePQSPK q idx | .compromiseOPK q idx => .compromiseOPK q idx
  | .exposeKey me idx kc => .exposeKey me idx kc | .exposeSpqr me idx => .exposeSpqr me idx
  | .exposeSkipped skIdx => .exposeSkipped skIdx | _ => .reject []

private theorem stepToNonBrkMove_next {s : Step} {tr : ExecTrace}
    (hs : s.cls = .invisible ∨ s.cls = .party ∨ s.IsLeak) :
    (stepToNonBrkMove s).next tr = s.next tr := by
  cases s with
  | network m => exact attackerSend_next_eq_network m tr
  | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _
  | genPQPrekey _ _ | genOneTimePrekey _ | breakDH | breakKEM | invertDH _ | invertKEM _ =>
    rcases hs with h | h | h <;> cases h
  | _ =>
    dsimp only [stepToNonBrkMove, Move.next, Move.act, Step.next, Step.toInput]
    erw [stepIn_next]; exact run_bind_pure_snd _ tr

private theorem preserves_stepToNonBrkMove {tr₀ : ExecTrace} (s : Step) :
    Preserves (NoNewPQEv isBrkPQEv tr₀) (Move.act (stepToNonBrkMove s)) := by
  cases s
  case aliceStart a b idStateIdx regIdxB bh =>
    unfold stepToNonBrkMove Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine Preserves.bind (Preserves.bind
      (preserves_aliceHandshake_noNewBrkPQEv a b idStateIdx regIdxB bh) fun _ => ?_) fun _ => ?_ <;>
      noBrkPQ_tac
  case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    unfold stepToNonBrkMove Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
    refine Preserves.bind (Preserves.bind
      (preserves_bobHandshake_noNewBrkPQEv b a kh regIdxA mh.ek mh.ct) fun _ => ?_) fun _ => ?_ <;>
      noBrkPQ_tac
  all_goals (
    dsimp only [stepToNonBrkMove, Move.act, DY.Libsignal.TripleRatchet.messageEncrypt,
      DY.Libsignal.TripleRatchet.messageEncryptAbort,
      DY.Libsignal.TripleRatchet.messageDecryptSkipped, DY.Libsignal.PQXDH.compromiseIK,
      DY.Libsignal.PQXDH.compromiseSPK, DY.Libsignal.PQXDH.compromisePQSPK,
      DY.Libsignal.PQXDH.compromiseOPK, DY.Libsignal.TripleRatchet.exposeKey,
      DY.Libsignal.TripleRatchet.exposeSpqr, DY.Libsignal.TripleRatchet.exposeSkipped]
    try rw [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    noBrkPQ_tac)

private theorem noNewBrkPQEv_step {tr₀ tr : ExecTrace} {s : Step}
    (hs : s.cls = .invisible ∨ s.cls = .party ∨ s.IsLeak)
    (htr : NoNewPQEv isBrkPQEv tr₀ tr) : NoNewPQEv isBrkPQEv tr₀ (s.next tr) :=
  stepToNonBrkMove_next hs ▸ preserves_stepToNonBrkMove s tr htr

private theorem noNewBrkPQEv_runSteps_invisible {tr₀ : ExecTrace} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, x.cls = .invisible) → NoNewPQEv isBrkPQEv tr₀ tr →
      NoNewPQEv isBrkPQEv tr₀ (runSteps pre tr)
  | [], _, _, htr => htr
  | s :: pre, tr, hinv, htr =>
    noNewBrkPQEv_runSteps_invisible pre (s.next tr)
      (fun x hx => hinv x (List.mem_cons_of_mem _ hx))
      (noNewBrkPQEv_step (Or.inl (hinv s List.mem_cons_self)) htr)

private theorem runSteps_append (pre ss : List Step) (tr : ExecTrace) :
    runSteps (pre ++ ss) tr = runSteps ss (runSteps pre tr) := by
  induction pre generalizing tr with | nil => rfl | cons s pre ih => exact ih (s.next tr)

theorem noNewBrkPQEv_of_matchesEventsClassical {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr₀ tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis)
    (htr : NoNewPQEv isBrkPQEv tr₀ tr) : NoNewPQEv isBrkPQEv tr₀ (runSteps ss tr) := by
  induction hme with
  | nil hinv => exact noNewBrkPQEv_runSteps_invisible _ _ hinv htr
  | @run1 _ _ pre _ _ _ _ _ _ hinv hrm _ ih =>
    rw [runSteps_append, runSteps]
    exact ih (noNewBrkPQEv_step (Or.inr (Or.inl hrm.1)) (noNewBrkPQEv_runSteps_invisible pre _ hinv htr))
  | @run0 _ _ pre _ _ _ _ hinv _ _ ih =>
    rw [runSteps_append]; exact ih (noNewBrkPQEv_runSteps_invisible pre _ hinv htr)
  | @env _ _ pre s _ ev _ _ _ hinv hem _ ih =>
    have hlk : s.IsLeak := by cases ev <;> first | exact False.elim hem | exact hem.2.1
    rw [runSteps_append, runSteps]
    exact ih (noNewBrkPQEv_step (Or.inr (Or.inr hlk)) (noNewBrkPQEv_runSteps_invisible pre _ hinv htr))

theorem not_broken_of_matchesEventsClassical {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry} (hNe : r.alice ≠ r.bob)
    (hme : MatchesEventsClassical interp r S g (setupTrace r) ss evs vis) :
    ¬ (runTrace r ss).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH ∧
    ¬ (runTrace r ss).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM := by
  have hno := noNewBrkPQEv_of_matchesEventsClassical hme (noNewPQEv_refl isBrkPQEv (setupTrace r))
  have hsetup : ∀ {ev j}, isBrkPQEv ev = true → ¬ (setupTrace r).EventLoggedAt ev j := fun hp h => by
    rcases setupTrace_eventLoggedAt_cases hNe h with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> cases hp
  exact ⟨fun ⟨j, hj⟩ => hsetup rfl (hno _ j rfl hj), fun ⟨j, hj⟩ => hsetup rfl (hno _ j rfl hj)⟩

theorem noBrk_of_matchesEventsClassical {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry} {ms : List Move}
    (hNe : r.alice ≠ r.bob) (hme : MatchesEventsClassical interp r S g (setupTrace r) ss evs vis)
    (hle : runTraceMoves r ms ≤ runTrace r ss) : NoBrk r ms :=
  noBrk_of_le hle (not_broken_of_matchesEventsClassical hNe hme)

theorem noBrk_of_explainsClassical {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry} {ms : List Move}
    (hNe : r.alice ≠ r.bob) (hex : ExplainsClassical interp r S g ss vis evs)
    (htr : runTraceMoves r ms = runTrace r ss) : NoBrk r ms :=
  noBrk_of_matchesEventsClassical hNe hex.2.2.2 (htr ▸ DY.Trace.le_refl _)

theorem noBrk_of_explains_breakFree {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry} {ms : List Move}
    (hNe : r.alice ≠ r.bob) (hbf : BreakFree evs) (hex : Explains interp r S g ss vis evs)
    (htr : runTraceMoves r ms = runTrace r ss) : NoBrk r ms :=
  noBrk_of_explainsClassical hNe (explainsClassical_of hex hbf) htr

theorem xlate_inv_with_noBrk {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {evs : List CliEvent} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r) (hsched : SchedFits (callsOf evs) who ok)
    (hexp : ExplainsClassical interp r S g ss vis evs)
    (hnrc : ¬ ReadCollisionCliClassical interp r S g ss evs) :
    ∃ (τ : List MachineEvent) (ms : List Move),
      ExplainsCli interp r S who ok (flatEvents evs) τ g ms ∧
      ¬ ReadCollision interp r S g ms τ ∧ NoBrk r ms ∧
      runTraceMoves r ms = runTrace r ss ∧ honestSalts r ms = honestSaltsOf r ss ∧
      prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis ∧
      plaintextTerms (runVis r ms) = plaintextTerms vis := by
  obtain ⟨τ, ms, hex_cli, hnrc_cli, htr, hsalts, hpre, hpt⟩ :=
    xlate_inv hwf (semReady_of_compat hwf hexp.1) hsched hexp hnrc
  exact ⟨τ, ms, hex_cli, hnrc_cli, noBrk_of_explainsClassical hwf.1 hexp htr, htr, hsalts, hpre, hpt⟩

theorem not_readCollisionCliClassical_of_no_recv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {evs : List CliEvent}
    (hno : ∀ (ev : RunEvent) (out : HwBytes),
      .run ev ∈ evs → (∃ peer, ev.cmd = .recv peer) → ev.exit = some (0, out) → False) :
    ¬ ReadCollisionCliClassical interp r S g ss evs := by
  rintro ⟨evs₁, ev, evs₂, _, _, _, _, _, out, _, _, rfl, _, hcmd, hexit, _⟩
  exact hno ev out (by simp) hcmd hexit

private theorem invisible_prefix_eq_of_party :
    ∀ {pre₁ pre₂ rest₁ rest₂ : List Step} {s₁ s₂ : Step},
      (∀ x ∈ pre₁, x.cls = .invisible) → (∀ x ∈ pre₂, x.cls = .invisible) →
      s₁.cls ≠ .invisible → s₂.cls ≠ .invisible →
      pre₁ ++ s₁ :: rest₁ = pre₂ ++ s₂ :: rest₂ → pre₁ = pre₂ ∧ s₁ = s₂ ∧ rest₁ = rest₂
  | [], [], _, _, _, _, _, _, _, _, h => ⟨rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩
  | x :: _, [], _, _, _, _, h₁, _, _, hs₂, h =>
    False.elim (hs₂ ((List.cons.inj h).1 ▸ h₁ x List.mem_cons_self))
  | [], y :: _, _, _, _, _, _, h₂, hs₁, _, h =>
    False.elim (hs₁ ((List.cons.inj h).1.symm ▸ h₂ y List.mem_cons_self))
  | x :: pre₁, _ :: _, _, _, _, _, h₁, h₂, hs₁, hs₂, h => by
    obtain ⟨rfl, htail⟩ := List.cons.inj h
    obtain ⟨hp, hs, hr⟩ := invisible_prefix_eq_of_party
      (fun z hz => h₁ z (List.mem_cons_of_mem _ hz))
      (fun z hz => h₂ z (List.mem_cons_of_mem _ hz)) hs₁ hs₂ htail
    exact ⟨congrArg (x :: ·) hp, hs, hr⟩

private theorem matchesEventsClassical_prepend_invisible {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsClassicalAt interp r S g initIds (runSteps pre tr) ss evs vis →
      MatchesEventsClassicalAt interp r S g initIds tr (pre ++ ss) evs vis
  | _, _, _, _, _, .nil h => .nil fun x hx => (List.mem_append.mp hx).elim (hinv x) (h x)
  | _, _, _, _, _, .run1 (pre := pre') hp hrm hrest => by
    have hp' : ∀ x ∈ pre ++ pre', x.cls = .invisible := fun x hx => (List.mem_append.mp hx).elim (hinv x) (hp x)
    rw [← runSteps_append] at hrm hrest; simpa [List.append_assoc] using MatchesEventsClassicalAt.run1 hp' hrm hrest
  | _, _, _, _, _, .run0 (pre := pre') hp hrej hrest => by
    have hp' : ∀ x ∈ pre ++ pre', x.cls = .invisible := fun x hx => (List.mem_append.mp hx).elim (hinv x) (hp x)
    rw [← runSteps_append] at hrest; simpa [List.append_assoc] using MatchesEventsClassicalAt.run0 hp' hrej hrest
  | _, _, _, _, _, .env (pre := pre') hp hem hrest => by
    have hp' : ∀ x ∈ pre ++ pre', x.cls = .invisible := fun x hx => (List.mem_append.mp hx).elim (hinv x) (hp x)
    rw [← runSteps_append] at hem hrest; simpa [List.append_assoc] using MatchesEventsClassicalAt.env hp' hem hrest

private theorem matchesEventsClassical_split_party {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ (evs₁ : List CliEvent) {initIds : Option BundlePreKeyIds} {tr₀ : ExecTrace} {ss₁ : List Step} {vis₁ : List VisEntry}
      {m : Step} {ss₂ : List Step} {ev : RunEvent} {evs₂ : List CliEvent} {vis : List VisEntry} {out : HwBytes},
      MatchesEventsClassicalAt interp r S g initIds tr₀ ss₁ evs₁ vis₁ → m.cls = .party → ev.exit = some (0, out) →
      MatchesEventsClassicalAt interp r S g initIds tr₀ (ss₁ ++ m :: ss₂) (evs₁ ++ .run ev :: evs₂) vis →
      ∃ v ids, RunMatches interp r S g (runSteps ss₁ tr₀) m ev v ids
  | [], _, _, ss₁, _, m, ss₂, _, _, _, out, .nil hinv₁, hm_cls, hexit, hme => by
    simp only [List.nil_append] at hme; generalize hss : ss₁ ++ m :: ss₂ = ss_tot at hme
    cases hme with
    | run0 _ hrej => exact False.elim (hrej out hexit)
    | @run1 _ _ pre₂ s _ _ _ v _ hinv₂ hrm _ =>
      have hm_ne : m.cls ≠ .invisible := by rw [hm_cls]; decide
      have hs_ne : s.cls ≠ .invisible := by rw [hrm.1]; decide
      obtain ⟨rfl, rfl, rfl⟩ := invisible_prefix_eq_of_party hinv₁ hinv₂ hm_ne hs_ne
        (by simpa [List.append_assoc] using hss)
      exact ⟨v, _, hrm⟩
  | _ :: evs₁, _, _, ss₁, _, m, ss₂, _, _, _, out, hme₁, hm_cls, hexit, hme => by
    simp only [List.cons_append] at hme; generalize hss : ss₁ ++ m :: ss₂ = ss_tot at hme
    cases hme₁ with
    | @run0 _ _ _ _ _ _ _ hinv₁ hrej₁ hme_rem₁ =>
      cases hme with
      | run1 _ hrm₂ _ => obtain ⟨out₀, hexit₀⟩ := hrm₂.2.2.2.2.2.1; exact False.elim (hrej₁ out₀ hexit₀)
      | @run0 _ _ _ _ _ _ _ hinv₂ _ hme_rem₂ =>
        have h₁ := matchesEventsClassical_prepend_invisible hinv₁ hme_rem₁
        have h₂ := matchesEventsClassical_prepend_invisible hinv₂ hme_rem₂
        rw [← hss] at h₂; exact matchesEventsClassical_split_party evs₁ h₁ hm_cls hexit h₂
    | @run1 _ _ _ s₁ _ _ _ _ _ hinv₁ hrm₁ hme_rem₁ =>
      cases hme with
      | run0 _ hrej₂ _ => obtain ⟨out₀, hexit₀⟩ := hrm₁.2.2.2.2.2.1; exact False.elim (hrej₂ out₀ hexit₀)
      | @run1 _ _ _ s₂ _ _ _ _ _ hinv₂ hrm₂ hme_rem₂ =>
        have hs₁_ne : s₁.cls ≠ .invisible := by rw [hrm₁.1]; decide
        have hs₂_ne : s₂.cls ≠ .invisible := by rw [hrm₂.1]; decide
        obtain ⟨rfl, rfl, rfl⟩ := invisible_prefix_eq_of_party hinv₁ hinv₂ hs₁_ne hs₂_ne
          (by simpa [List.append_assoc] using hss)
        rw [runSteps_append, runSteps]; exact matchesEventsClassical_split_party evs₁ hme_rem₁ hm_cls hexit hme_rem₂
    | @env _ _ _ s₁ _ ev₀ _ _ _ hinv₁ hem₁ hme_rem₁ =>
      cases hme with
      | @env _ _ _ s₂ _ _ _ _ _ hinv₂ hem₂ hme_rem₂ =>
        have hs₁_ne : s₁.cls ≠ .invisible := by
          have hcls : s₁.cls = .env := by cases ev₀ <;> first | exact False.elim hem₁ | exact hem₁.1
          rw [hcls]; decide
        have hs₂_ne : s₂.cls ≠ .invisible := by
          have hcls : s₂.cls = .env := by cases ev₀ <;> first | exact False.elim hem₂ | exact hem₂.1
          rw [hcls]; decide
        obtain ⟨rfl, rfl, rfl⟩ := invisible_prefix_eq_of_party hinv₁ hinv₂ hs₁_ne hs₂_ne
          (by simpa [List.append_assoc] using hss)
        rw [runSteps_append, runSteps]; exact matchesEventsClassical_split_party evs₁ hme_rem₁ hm_cls hexit hme_rem₂

@[reducible] def isBobDonePQEv : DY.Libsignal.PQXDH.PQXDHEvent → Bool
  | .BobDone .. => true | _ => false

private theorem preserves_aliceHandshake_noNewBobDonePQEv {tr₀ : ExecTrace}
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (NoNewPQEv isBobDonePQEv tr₀)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; noBrkPQ_tac

private theorem preserves_stepToNonBrkMove_noNewBobDonePQEv {tr₀ : ExecTrace} (s : Step)
    (hno_bs : ∀ b a kh regA mh pq spqr, s ≠ .bobStart b a kh regA mh pq spqr) :
    Preserves (NoNewPQEv isBobDonePQEv tr₀) (Move.act (stepToNonBrkMove s)) := by
  cases s
  case aliceStart a b idStateIdx regIdxB bh =>
    unfold stepToNonBrkMove Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine Preserves.bind (Preserves.bind
      (preserves_aliceHandshake_noNewBobDonePQEv a b idStateIdx regIdxB bh) fun _ => ?_) fun _ => ?_ <;>
      noBrkPQ_tac
  case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    exact False.elim (hno_bs b a kh regIdxA mh pqIdx spqrMsgIdx rfl)
  all_goals (
    dsimp only [stepToNonBrkMove, Move.act, DY.Libsignal.TripleRatchet.messageEncrypt,
      DY.Libsignal.TripleRatchet.messageEncryptAbort,
      DY.Libsignal.TripleRatchet.messageDecryptSkipped, DY.Libsignal.PQXDH.compromiseIK,
      DY.Libsignal.PQXDH.compromiseSPK, DY.Libsignal.PQXDH.compromisePQSPK,
      DY.Libsignal.PQXDH.compromiseOPK, DY.Libsignal.TripleRatchet.exposeKey,
      DY.Libsignal.TripleRatchet.exposeSpqr, DY.Libsignal.TripleRatchet.exposeSkipped]
    try rw [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    noBrkPQ_tac)

private theorem noNewBobDonePQEv_step {tr₀ tr : ExecTrace} {s : Step}
    (hs : s.cls = .invisible ∨ s.cls = .party ∨ s.IsLeak)
    (hno_bs : ∀ b a kh regA mh pq spqr, s ≠ .bobStart b a kh regA mh pq spqr)
    (htr : NoNewPQEv isBobDonePQEv tr₀ tr) : NoNewPQEv isBobDonePQEv tr₀ (s.next tr) :=
  stepToNonBrkMove_next hs ▸ preserves_stepToNonBrkMove_noNewBobDonePQEv s hno_bs tr htr

private theorem noNewBobDonePQEv_runSteps_invisible {tr₀ : ExecTrace} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, x.cls = .invisible) → NoNewPQEv isBobDonePQEv tr₀ tr →
      NoNewPQEv isBobDonePQEv tr₀ (runSteps pre tr)
  | [], _, _, htr => htr
  | s :: pre, tr, hinv, htr =>
    noNewBobDonePQEv_runSteps_invisible pre (s.next tr) (fun x hx => hinv x (List.mem_cons_of_mem _ hx))
      (noNewBobDonePQEv_step (Or.inl (hinv s List.mem_cons_self))
        (fun _ _ _ _ _ _ _ hbs => by have hcls := hinv s List.mem_cons_self; rw [hbs] at hcls; cases hcls) htr)

private theorem noNewBobDonePQEv_of_matchesEventsClassical
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr₀ tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis)
    (hno_recv : ∀ ev out, .run ev ∈ evs → (∃ peer, ev.cmd = .recv peer) → ev.exit = some (0, out) → False)
    (htr : NoNewPQEv isBobDonePQEv tr₀ tr) : NoNewPQEv isBobDonePQEv tr₀ (runSteps ss tr) := by
  induction hme with
  | nil hinv => exact noNewBobDonePQEv_runSteps_invisible _ _ hinv htr
  | @run0 _ _ pre _ _ _ _ hinv _ _ ih =>
    rw [runSteps_append]
    exact ih (fun ev' out' hmem => hno_recv ev' out' (List.mem_cons_of_mem _ hmem))
      (noNewBobDonePQEv_runSteps_invisible pre _ hinv htr)
  | @run1 _ _ pre s _ ev _ _ _ hinv hrm _ ih =>
    rw [runSteps_append, runSteps]
    have hno_bs : ∀ b a kh regA mh pq spqr, s ≠ .bobStart b a kh regA mh pq spqr := by
      rintro _ _ _ _ _ _ _ rfl; obtain ⟨out, hexit⟩ := hrm.2.2.2.2.2.1; have hfits := hrm.2.2.1
      have hcmd : ∃ peer, ev.cmd = .recv peer := by
        cases h : ev.cmd <;> rw [h] at hfits <;> first | exact ⟨_, rfl⟩ | cases hfits
      exact hno_recv ev out List.mem_cons_self hcmd hexit
    exact ih (fun ev' out' hmem => hno_recv ev' out' (List.mem_cons_of_mem _ hmem))
      (noNewBobDonePQEv_step (Or.inr (Or.inl hrm.1)) hno_bs (noNewBobDonePQEv_runSteps_invisible pre _ hinv htr))
  | @env _ _ pre s _ ev _ _ _ hinv hem _ ih =>
    have hlk : s.IsLeak := by cases ev <;> first | exact False.elim hem | exact hem.2.1
    rw [runSteps_append, runSteps]
    exact ih (fun ev' out' hmem => hno_recv ev' out' (List.mem_cons_of_mem _ hmem))
      (noNewBobDonePQEv_step (Or.inr (Or.inr hlk)) (by rintro _ _ _ _ _ _ _ rfl; cases hlk)
        (noNewBobDonePQEv_runSteps_invisible pre _ hinv htr))

private theorem eventLoggedAt_of_getEventAt_some {E : Type}
    [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)] {tr : ExecTrace} {i : Nat} {ev : E}
    (h : tr.getEventAt E i = some ev) : tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  rcases hat : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT E)) with _ | ⟨ev'⟩ <;> rw [hat] at h <;> cases h; rfl

theorem bobDoneBaseKeys_nil_of_matchesEventsClassical_no_recv
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss₁ : List Step} {evs₁ : List CliEvent} {vis₁ : List VisEntry}
    (hNe : r.alice ≠ r.bob) (hme : MatchesEventsClassical interp r S g (setupTrace r) ss₁ evs₁ vis₁)
    (hno_recv : ∀ ev out, .run ev ∈ evs₁ → (∃ peer, ev.cmd = .recv peer) → ev.exit = some (0, out) → False) :
    bobDoneBaseKeys (runTrace r ss₁) = [] := by
  have hno := noNewBobDonePQEv_of_matchesEventsClassical hme hno_recv (noNewPQEv_refl isBobDonePQEv (setupTrace r))
  have hsetup : ∀ {ev j}, isBobDonePQEv ev = true → ¬ (setupTrace r).EventLoggedAt ev j := fun hp h => by
    rcases setupTrace_eventLoggedAt_cases hNe h with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> cases hp
  unfold bobDoneBaseKeys; apply List.filterMap_eq_nil_iff.mpr; intro i _
  cases hget : (runTrace r ss₁).getEventAt DY.Libsignal.PQXDH.PQXDHEvent i with
  | none => rfl
  | some ev =>
    have hlog := eventLoggedAt_of_getEventAt_some hget
    cases ev <;> first | rfl | exact False.elim (hsetup rfl (hno _ i rfl hlog))

/-- Accepted pre-key `.recv` events cannot trigger `ReadCollisionCliClassical` when no earlier
accepted `.recv` completed a `BobDone` handshake. -/
theorem not_readCollisionCliClassical_of_preKey_recv
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hNe : r.alice ≠ r.bob) (hme : MatchesEventsClassical interp r S g (setupTrace r) ss evs vis)
    (hrecv : ∀ evs₁ ev evs₂ out, evs = evs₁ ++ .run ev :: evs₂ → (∃ peer, ev.cmd = .recv peer) →
      ev.exit = some (0, out) → (parsePreKeyWire ev.input).isSome = true ∧
        (∀ ev' out', .run ev' ∈ evs₁ → (∃ peer, ev'.cmd = .recv peer) →
          ev'.exit = some (0, out') → False)) :
    ¬ ReadCollisionCliClassical interp r S g ss evs := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, body, w,
    hevs, hss, hcmd, hexit, _, hme₁, hdec, _, _⟩
  have hm_cls : m.cls = StepClass.party := by cases m <;> simp [Step.decryptMsgIdx?] at hdec <;> rfl
  have hme' : MatchesEventsClassical interp r S g (setupTrace r)
      (ss₁ ++ m :: ss₂) (evs₁ ++ .run ev :: evs₂) vis := by rwa [← hss, ← hevs]
  obtain ⟨v, _, hrm⟩ := matchesEventsClassical_split_party evs₁ hme₁ hm_cls hexit hme'
  obtain ⟨hpw_some, hno_recv₁⟩ := hrecv evs₁ ev evs₂ out hevs hcmd hexit
  have hbd_nil := bobDoneBaseKeys_nil_of_matchesEventsClassical_no_recv hNe hme₁ hno_recv₁
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hpw_some
  obtain ⟨_, _, _, _, _, _, _, _, hpf_all⟩ := hrm.2.2.2.2.2.2.2
  have hpf_p := hpf_all p hp
  cases m <;> simp [Step.decryptMsgIdx?] at hdec <;>
    (obtain ⟨ek, hek, _⟩ := hpf_p; change ek ∈ bobDoneBaseKeys (runTrace r ss₁) at hek;
     rw [hbd_nil] at hek; cases hek)

theorem not_nextEventCollidesClassical_init
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent}
    {peer : CryptoVerification.SignalSession.Address} {bundle : String}
    (hcmd : ev.cmd = .init peer bundle) :
    ¬ NextEventCollidesClassical interp r S g ss vis evs₁ ev := by
  simp [NextEventCollidesClassical, hcmd]

theorem not_nextEventCollidesClassical_send
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent}
    {peer : CryptoVerification.SignalSession.Address}
    (hwf : ProtocolSetupWF r) (hsched : SchedFits (callsOf evs₁) who ok)
    (hex : ExplainsClassical interp r S g ss vis evs₁)
    (hnrc : ¬ ReadCollisionCliClassical interp r S g ss evs₁) (hcmd : ev.cmd = .send peer)
    (hno_pt : ∀ (τ : List MachineEvent) (ms : List Move),
      ExplainsCli interp r S who ok (flatEvents evs₁) τ g ms →
      ¬ ReadCollision interp r S g ms τ → NoBrk r ms →
      BytesMatchEntry interp r S g .pt ev.input (ptEntryAt (runTraceMoves r ms)) →
      ¬ MemoCollisionOn interp r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
          (runTraceMoves r ms) (runVis r ms)
          (ptEntryAt (runTraceMoves r ms)).terms (ptEntryAt (runTraceMoves r ms)).terms) :
    ¬ NextEventCollidesClassical interp r S g ss vis evs₁ ev := by
  intro hcol; simp only [NextEventCollidesClassical, hcmd] at hcol
  obtain ⟨hbme, hall⟩ := hcol
  have hmcol := hall g ⟨rfl, vis, hex⟩
  obtain ⟨τ, ms, hex_cli, hnrc_cli, hnb, htr, _, hpre, hpt⟩ :=
    xlate_inv_with_noBrk hwf hsched hex hnrc
  exact hno_pt τ ms hex_cli hnrc_cli hnb (by rwa [htr])
    (by rw [htr]; exact (memoCollisionOn_iff_of_terms hpre hpt).mpr hmcol)

theorem not_nextEventCollidesClassical_recv_rejected
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : ev.cmd = .recv peer) (hrej : ∀ out, ev.exit ≠ some (0, out)) :
    ¬ NextEventCollidesClassical interp r S g ss vis evs₁ ev := by
  rintro hcol; simp only [NextEventCollidesClassical, hcmd] at hcol
  obtain ⟨⟨out, hexit⟩, _⟩ := hcol; exact hrej out hexit

theorem sendTerms_eq_of_prefixTerms_eq {r : ProtocolSetup} {tr : ExecTrace} {v₁ v₂ : List VisEntry}
    (hpre : prefixTerms r tr v₁ = prefixTerms r tr v₂)
    (hpt : plaintextTerms v₁ = plaintextTerms v₂) :
    (v₁.filter (·.kind == .send)).flatMap (·.terms) =
      (v₂.filter (·.kind == .send)).flatMap (·.terms) := by
  have hpr : principalTerms r tr v₁ = principalTerms r tr v₂ :=
    (List.append_left_inj (plaintextTerms v₂)).mp (by rwa [prefixTerms, prefixTerms, hpt] at hpre)
  unfold principalTerms at hpr
  exact (List.append_left_inj ((storedStates r tr).map DY.Comparse.serialize)).mp
    ((List.append_left_inj (storedSecrets tr)).mp hpr)

theorem prefixTerms_eq_of_sendTerms_eq {r : ProtocolSetup} {tr : ExecTrace} {v₁ v₂ : List VisEntry}
    (hsend : (v₁.filter (·.kind == .send)).flatMap (·.terms) =
      (v₂.filter (·.kind == .send)).flatMap (·.terms))
    (hpt : plaintextTerms v₁ = plaintextTerms v₂) :
    prefixTerms r tr v₁ = prefixTerms r tr v₂ := by
  unfold prefixTerms principalTerms; rw [hsend, hpt]

private theorem drawsMatch_filter_send
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {drs : List VisEntry} {coins : HwBytes} (h : DrawsMatch interp r S g drs coins) :
    drs.filter (·.kind == .send) = [] := by
  obtain ⟨pieces, hne, hpref, hf2⟩ := h
  clear hne hpref
  induction hf2 with
  | nil => rfl
  | @cons p v _ _ hpv _ ih => rw [List.filter_cons_of_neg (by rw [← hpv.1]; decide), ih]

theorem runMatches_filter_send_init
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {peer : CryptoVerification.SignalSession.Address} {bundle : String}
    (hcmd : ev.cmd = .init peer bundle) (hrm : RunMatches interp r S g tr s ev v initIds) :
    v.filter (·.kind == .send) = [] := by
  obtain ⟨_, _, _, _, _, ⟨out, hexit⟩, _, inp, drs, outs, rfl, hinp, hdrs, houts, _, _⟩ := hrm
  have hinp_k : inp.kind = .recv := by simpa [inputKind, hcmd] using hinp.1.symm
  have houts_nil : outs = [] := by unfold OutputsMatch at houts; rwa [hexit, hcmd] at houts
  rw [houts_nil, List.append_nil, List.filter_cons_of_neg (by rw [hinp_k]; decide),
    drawsMatch_filter_send hdrs]

theorem runMatches_filter_send_recv
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : ev.cmd = .recv peer) (hrm : RunMatches interp r S g tr s ev v initIds) :
    v.filter (·.kind == .send) = [] := by
  obtain ⟨_, _, _, _, _, ⟨out, hexit⟩, _, inp, drs, outs, rfl, hinp, hdrs, houts, _, _⟩ := hrm
  have hinp_k : inp.kind = .recv := by simpa [inputKind, hcmd] using hinp.1.symm
  unfold OutputsMatch at houts; rw [hexit, hcmd] at houts
  obtain ⟨vo, rfl, hvo⟩ := houts
  rw [List.filter_cons_of_neg (by rw [hinp_k]; decide), List.filter_append,
    drawsMatch_filter_send hdrs, List.nil_append,
    List.filter_cons_of_neg (by rw [← hvo.1]; decide), List.filter_nil]

theorem envMatchesClassical_filter_send
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {ev : EnvEvent} {v : List VisEntry}
    (hem : EnvMatchesClassical interp r S g tr s ev v) :
    v.filter (·.kind == .send) = [] := by
  cases ev <;> try exact False.elim hem
  obtain ⟨_, _, _, _, ve, rfl, hve⟩ := hem
  rw [List.filter_cons_of_neg (by rw [← hve.1]; decide), List.filter_nil]

theorem runMatches_filter_send_send
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : ev.cmd = .send peer) (hrm : RunMatches interp r S g tr s ev v initIds) :
    ∃ stateIdx coinsLen pqIdx msg,
      s = .messageEncrypt ev.party stateIdx coinsLen pqIdx ∧
      lastSent tr (s.next tr) = some msg ∧
      (runWrapped ev = true →
        ∃ ek ct, pendingPreKey tr stateIdx = some (ek, ct) ∧
          v.filter (·.kind == .send) = [⟨.send, [ek, ct, msg], .preKeySend, none⟩]) ∧
      v.filter (·.kind == .send) = encSendEntry tr (s.next tr) stateIdx (runWrapped ev) := by
  obtain ⟨_, hparty, hfits, _, hok, ⟨out, hexit⟩, hv_eq, inp, drs, outs, hv_split,
    hinp, hdrs, houts, _, _⟩ := hrm
  have hinp_k : inp.kind = .pt := by simpa [inputKind, hcmd] using hinp.1.symm
  unfold OutputsMatch at houts; rw [hexit, hcmd] at houts
  obtain ⟨vo, rfl, hvo⟩ := houts
  have hvo_k : vo.kind = .send := hvo.1.symm
  have hv_filter : v.filter (·.kind == .send) = [vo] := by
    rw [hv_split, List.filter_cons_of_neg (by rw [hinp_k]; decide), List.filter_append,
      drawsMatch_filter_send hdrs, List.nil_append,
      List.filter_cons_of_pos (by rw [hvo_k]; decide), List.filter_nil]
  have hvo_mem : vo ∈ stepView s tr (runWrapped ev) := by rw [← hv_eq, hv_split]; simp
  cases hs : s with
  | messageEncrypt me stateIdx coinsLen pqIdx =>
    rw [hs] at hparty hok hvo_mem
    have hme : me = ev.party := Option.some.inj hparty; subst hme
    dsimp only [stepView] at hvo_mem
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hvo_mem
    have hvo_ese : vo ∈ encSendEntry tr ((Step.messageEncrypt ev.party stateIdx coinsLen pqIdx).next tr)
        stateIdx (runWrapped ev) := by
      rcases List.mem_append.mp hvo_mem with h1 | hexp
      · rcases List.mem_append.mp h1 with hdr | hese
        · rcases Symbolic.Proofs.Swarm.UA.XlateSteps.encDraws_kind hdr with hk | hk <;>
            (rw [hvo_k] at hk; cases hk)
        · exact hese
      · have hk := Symbolic.Proofs.Swarm.UA.XlateSteps.exposures_kind hexp
        rw [hvo_k] at hk; cases hk
    unfold encSendEntry at hvo_ese ⊢
    rcases hls : lastSent tr ((Step.messageEncrypt ev.party stateIdx coinsLen pqIdx).next tr) with _ | w
    · simp [hls] at hvo_ese
    · refine ⟨stateIdx, coinsLen, pqIdx, w, rfl, rfl, fun hw => ?_, ?_⟩
      · rcases hppk : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩
        · simp [hls, hw, hppk] at hvo_ese
        · simp only [hls, hw, hppk, List.mem_singleton] at hvo_ese
          exact ⟨ek, ct, rfl, by rw [hv_filter, hvo_ese]⟩
      · rw [hv_filter]
        rcases hppk : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩ <;>
          cases hw : runWrapped ev <;>
          simp [hls, hw, hppk] at hvo_ese ⊢ <;>
          exact hvo_ese
  | messageEncryptAbort me stateIdx =>
    rw [hs] at hok hvo_mem; dsimp only [stepView] at hvo_mem
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hvo_mem
    rcases List.mem_append.mp hvo_mem with hdr | hexp
    · rcases Symbolic.Proofs.Swarm.UA.XlateSteps.encDraws_kind hdr with hk | hk <;>
        (rw [hvo_k] at hk; cases hk)
    · have hk := Symbolic.Proofs.Swarm.UA.XlateSteps.exposures_kind hexp
      rw [hvo_k] at hk; cases hk
  | _ => rw [hs, hcmd] at hfits; cases hfits

theorem not_nextEventCollidesClassical_recv_preKey
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent}
    {peer : CryptoVerification.SignalSession.Address}
    {tag : BitVec 8} {body : HwBytes} {p : PreKeyFields}
    (hwf : ProtocolSetupWF r) (hsched : SchedFits (callsOf evs₁) who ok)
    (hex : ExplainsClassical interp r S g ss vis evs₁)
    (hnrc : ¬ ReadCollisionCliClassical interp r S g ss evs₁)
    (hcmd : ev.cmd = .recv peer) (hinp : ev.input = tag :: body)
    (htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hp : parsePreKeyWire (tag :: body) = some p)
    (hnkb : ¬ KnownBaseKeyOn interp S g (runTrace r ss) p) (hnkm : ¬ KyberMismatch interp r p)
    (hno_bsc : ∀ (τ : List MachineEvent) (ms : List Move),
      ExplainsCli interp r S who ok (flatEvents evs₁) τ g ms →
      ¬ ReadCollision interp r S g ms τ → NoBrk r ms →
      runTraceMoves r ms = runTrace r ss → honestSalts r ms = honestSaltsOf r ss →
      prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis →
      plaintextTerms (runVis r ms) = plaintextTerms vis →
      ∃ (ms' : List Move) (x : PreKeyRep),
        runTraceMoves r ms' = runTrace r ss ∧ honestSalts r ms' = honestSaltsOf r ss ∧
        prefixTerms r (runTrace r ss) (runVis r ms') = prefixTerms r (runTrace r ss) vis ∧
        plaintextTerms (runVis r ms') = plaintextTerms vis ∧
        x ∈ preKeyRepresentations interp r S g ms' (tag :: body) ∧
        ¬ BobStartCollision interp r S g ms' p x) :
    ¬ NextEventCollidesClassical interp r S g ss vis evs₁ ev := by
  intro hcol; simp only [NextEventCollidesClassical, hcmd, hinp] at hcol
  rcases hcol.2 with ⟨htag_eq, _⟩ | ⟨p', hp', ⟨hkb, _⟩ | ⟨_, hpk⟩⟩
  · exact htag htag_eq
  · rw [hp] at hp'; cases Option.some.inj hp'; exact hnkb hkb
  · rw [hp] at hp'; cases Option.some.inj hp'
    rcases hpk.2 with hkm | hall
    · exact hnkm hkm
    · obtain ⟨τ, ms, hex_cli, hnrc_cli, hnb, htr, hsalts, hpre, hpt⟩ :=
        xlate_inv_with_noBrk hwf hsched hex hnrc
      obtain ⟨ms', x, htr', hsalts', hpre', hpt', hx, hnbsc⟩ :=
        hno_bsc τ ms hex_cli hnrc_cli hnb htr hsalts hpre hpt
      have hx_on : x ∈ preKeyRepresentationsOn interp r S g (runTrace r ss) (tag :: body) := by
        rwa [← preKeyRepresentations_eq htr']
      exact hnbsc ((bobStartCollision_iff htr' hsalts' hpre' hpt').mpr (hall g ss vis hex hnrc x hx_on))

theorem not_collisionAfterExplainedPrefix_of_splits
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs : List CliEvent} (hbf : BreakFree evs)
    (hall : ∀ evs₁ ev evs₂ g ss vis,
      evs = evs₁ ++ .run ev :: evs₂ →
      ExplainsClassical interp r S g ss vis evs₁ →
      ¬ NextEventCollidesClassical interp r S g ss vis evs₁ ev) :
    ¬ CollisionAfterExplainedPrefix interp r S evs := fun hcol =>
  let ⟨evs₁, ev, evs₂, g, ss, vis, hevs, hex, hnext⟩ :=
    collisionAfterExplainedPrefixClassical_of hbf hcol
  hall evs₁ ev evs₂ g ss vis hevs hex hnext

section Split38Swap

open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
  Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED
  Symbolic.Swarm.COMPOSED.CompTrace

theorem honestSalts_split38_swap_eq (r : ProtocolSetup) (pre mid post : List Move) (m₀ : Move)
    (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) :
    honestSalts r (pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₁ :: post) =
      honestSalts r (pre ++ m₀ :: mid ++ Move.encrypt me s cl pq w₂ :: post) := by
  unfold honestSalts; congr 1
  rw [honestKeysFrom_append (pre ++ m₀ :: mid) (Move.encrypt me s cl pq w₁ :: post),
      honestKeysFrom_append (pre ++ m₀ :: mid) (Move.encrypt me s cl pq w₂ :: post)]
  congr 1

private theorem filter_pt_encSend_nil (tr tr' : ExecTrace) (w : Option (Nat × Nat)) :
    (encSend tr tr' w).filter (·.kind == .pt) = [] := by
  unfold encSend; rcases lastSent tr tr' with _ | msg <;> rcases w with _ | ⟨e, c⟩ <;> rfl

private theorem filter_pt_encrypt_vis_swap (tr : ExecTrace) (me : Participant)
    (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) :
    ((Move.encrypt me s cl pq w₁).vis tr).filter (·.kind == .pt) =
      ((Move.encrypt me s cl pq w₂).vis tr).filter (·.kind == .pt) := by
  rw [encrypt_vis_eq, encrypt_vis_eq, encrypt_next_eq_wrap tr me s cl pq w₁ w₂]
  unfold encVis; simp only [↓reduceIte, List.filter_append, filter_pt_encSend_nil, List.append_nil]

theorem plaintextTerms_split38_swap_eq {r : ProtocolSetup} (hNe : r.alice ≠ r.bob)
    {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat}
    (w₁ w₂ : Option (Nat × Nat)) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost₁ : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) w₁).next
        (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) :
    plaintextTerms (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
      Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) w₂ :: post)) =
    plaintextTerms (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
      Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) w₁ :: post)) := by
  have hpost₂ : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) w₂).next
        (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post := by
    rwa [encrypt_next_eq_wrap _ _ _ _ _ w₂ w₁]
  unfold plaintextTerms
  rw [runVis_split38_eq hNe hpre hmid hpost₂, runVis_split38_eq hNe hpre hmid hpost₁,
      List.filter_append, List.filter_append, filter_pt_encrypt_vis_swap _ _ _ _ _ w₂ w₁]

private theorem matchesEventsClassical_nil_vis {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss [] vis) : vis = [] := by cases h; rfl

private theorem matchesEventsClassical_run_exit0_inv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry} {out : HwBytes}
    (hexit : ev.exit = some (0, out)) (h : MatchesEventsClassicalAt interp r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre s ss' v vs, ss = pre ++ s :: ss' ∧ vis = v ++ vs ∧
      RunMatches interp r S g (runSteps pre tr) s ev v initIds ∧
      MatchesEventsClassicalAt interp r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss' evs vs := by
  cases h with
  | run0 _ hrej _ => exact False.elim (hrej out hexit)
  | run1 _ hrm hmev => exact ⟨_, _, _, _, _, rfl, rfl, hrm, hmev⟩

private theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

private theorem matchesEventsClassical_init_send_sendTerms
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {ev0 ev1 : RunEvent} {vis : List VisEntry}
    {peer0 peer1 : CryptoVerification.SignalSession.Address} {bdir : String} {out0 out1 : HwBytes}
    (hcmd0 : ev0.cmd = .init peer0 bdir) (hexit0 : ev0.exit = some (0, out0))
    (hcmd1 : ev1.cmd = .send peer1) (hexit1 : ev1.exit = some (0, out1)) (hwrap1 : runWrapped ev1 = true)
    (hmev : MatchesEventsClassical interp r S g (setupTrace r) ss [.run ev0, .run ev1] vis) :
    ∃ tr₁ stateIdx ek ct msg, tr₁ ≤ runTrace r ss ∧ pendingPreKey tr₁ stateIdx = some (ek, ct) ∧
      (vis.filter (·.kind == .send)).flatMap (·.terms) = [ek, ct, msg] := by
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, rfl, hrm₀, hmev₁⟩ := matchesEventsClassical_run_exit0_inv hexit0 hmev
  obtain ⟨pre₁, s₁, ss₂, v₁, vs₂, rfl, rfl, hrm₁, hmev₂⟩ := matchesEventsClassical_run_exit0_inv hexit1 hmev₁
  cases matchesEventsClassical_nil_vis hmev₂
  have hv₀ := runMatches_filter_send_init hcmd0 hrm₀
  obtain ⟨stateIdx, _, _, msg, _, _, hwrap_fn, _⟩ := runMatches_filter_send_send hcmd1 hrm₁
  obtain ⟨ek, ct, hppk, hv₁⟩ := hwrap_fn hwrap1
  have htr_eq : runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: ss₂)) =
      runSteps ss₂ (s₁.next (runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))))) := by
    change runSteps (pre₀ ++ (s₀ :: (pre₁ ++ (s₁ :: ss₂)))) (setupTrace r) = _
    rw [runSteps_append, runSteps, runSteps_append, runSteps]
  have hle : runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))) ≤ runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: ss₂)) := by
    rw [htr_eq]; exact DY.Trace.le_trans _ _ _ (step_le_next s₁ _) (runSteps_le ss₂ _)
  refine ⟨_, stateIdx, ek, ct, msg, hle, hppk, ?_⟩
  rw [List.append_nil, List.filter_append, hv₀, hv₁]; rfl

private theorem exists_aliceDone_of_pendingPreKey {tr₀ tr : ExecTrace} {stateIdx : Nat} {ek ct : DY.Bytes}
    (hle : tr₀ ≤ tr) (hppk : pendingPreKey tr₀ stateIdx = some (ek, ct)) :
    ∃ d a b ikA ikB spk pqpk opk keys,
      tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) d := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt at hppk
  cases hat_st : (tr₀.at? stateIdx :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))) with
  | none => rw [hat_st] at hppk; cases hppk
  | some e =>
    rw [hat_st] at hppk
    dsimp only [Option.map, Option.bind] at hppk
    split at hppk
    · cases hppk
    · rw [List.findSome?_eq_some_iff] at hppk
      obtain ⟨_, ev, _, heq_evs, hmatch, _⟩ := hppk
      have hev_mem : ev ∈ DY.Libsignal.Composed.Refinement.sessionHandshakeEvents tr₀
          (e.st.state.sessionInfo e.st.participant) := by
        rw [heq_evs]; simp
      unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hev_mem
      obtain ⟨i, _, hcev_ev⟩ := List.mem_filterMap.mp hev_mem
      split at hcev_ev <;> try simp at hcev_ev
      rename_i s d hcev
      obtain ⟨_, hcev_ev⟩ := hcev_ev
      cases ev <;> simp at hmatch
      rename_i a b ikA ikB spk pqpk opk ek' ct' keys
      obtain ⟨rfl, rfl⟩ := hmatch
      have hat₀ : (tr₀.at? d : Option PQXDHEntry) = some ⟨.AliceDone a b ikA ikB spk pqpk opk ek' ct' keys⟩ := by
        rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact eventLoggedAt_of_getEventAt_some hcev_ev
      exact ⟨d, a, b, ikA, ikB, spk, pqpk, opk, keys,
        (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?
          DY.Libsignal.PQXDH.PQXDHEvent _ _ _).mpr (CompTrace.at?_le_some hle hat₀)⟩

private theorem at?_pqEv_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat)
    (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq j : Nat) :
    ((encNextTr tr₂ me sIdx stA cl pq).at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
    (tr₂.at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) := by
  unfold encNextTr encPreSaltTr; dsimp only; repeat rw [CompPrefixInvAlice.at?_append_other_eq _ _ rfl]

private theorem at?_pqEv_iniAliceStartTr (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) :
    ((iniAliceStartTr tr a b o).at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
    if j = tr.length + 5 then
      some ⟨DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩
    else (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) := by
  unfold iniAliceStartTr; dsimp only
  rw [CompPrefixInvAlice.at?_append_other_eq _ (TRStE _ _) rfl, CompPrefixInvAlice.at?_append_other_eq _ (CEvE _) rfl,
      CompPrefixInvAlice.at?_append_other_eq _ (TREvE _) rfl]
  by_cases hj : j = tr.length + 5
  · subst hj; simp only [↓reduceIte]
    exact CompPrefixInvSwap.at?_append_eq_of_eq _ _
      (by simp [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq])
  · simp only [hj, ↓reduceIte]
    by_cases hlt : j < tr.length + 5
    · rw [CompTrace.at?_append_of_lt _ _
        (by simp [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega)]
      repeat rw [CompPrefixInvAlice.at?_append_other_eq _ _ rfl]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _
        (by simp [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega),
        Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]

private theorem aliceDone_split38_pin {r : Records} (hNe : r.alice ≠ r.bob)
    {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl : Nat} {wrap : Option (Nat × Nat)} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap).next
      (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o)
    {d : Nat} {a' b' : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes} {ek ct : DY.Bytes}
    {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hEv : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
      Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) wrap :: post)).EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA ikB spk pqpk opk ek ct keys) d) :
    ek = o.ek ∧ ct = o.ct := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o
  let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := by
    subst ho; exact encrypt_next_split38_eq wrap hm₀ hmid rfl
  have htr_eq : runTraceMoves r (pre ++ m₀ :: mid ++ m₁ :: post) = (runMoves post (m₁.next tr₂)).1 := by
    change (runMoves ((pre ++ m₀ :: mid) ++ m₁ :: post) (setupTrace r)).1 = _
    rw [runMoves_append_fst, runMoves_append_fst, runMoves, runMoves]
  rw [htr_eq, eventLoggedAt_of_movesFrom_invisibleNoEffect hpost, henc] at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent),
      at?_pqEv_encNextTr, ← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at hEv
  dsimp only [tr₂] at hEv; rw [eventLoggedAt_of_movesFrom_invisibleNoEffect hmid, hm₀] at hEv
  change (iniAliceStartTr tr₁ r.alice r.bob o).EventLoggedAt _ d at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent),
      at?_pqEv_iniAliceStartTr] at hEv
  split at hEv
  · cases hEv; exact ⟨rfl, rfl⟩
  · rw [← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at hEv
    dsimp only [tr₁] at hEv; rw [eventLoggedAt_of_movesFrom_invisibleNoEffect hpre] at hEv
    rcases setupTrace_eventLoggedAt_cases hNe hEv with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h

private theorem filter_send_aliceVis_take_nil (tr₁ tr' : ExecTrace) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) :
    ((aliceVis tr₁ tr' hb).take shown).filter (·.kind == .send) = [] := by
  rw [List.filter_eq_nil_iff]; intro v hv; simp only [beq_iff_eq]
  rcases xpl_aliceVis_kind (List.mem_of_mem_take hv) with hk | hk <;> (rw [hk]; decide)

private theorem filter_send_encDraws_nil (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat)
    (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) :
    (encDraws (newRandoms tr₂ (encNextTr tr₂ me sIdx stA cl pq))).filter (·.kind == .send) = [] := by
  rw [List.filter_eq_nil_iff]; intro v hv; simp only [beq_iff_eq]
  rcases mem_encDraws_encNextTr hv with rfl | rfl <;> intro h <;> cases h

private theorem sendTerms_split38_eq {r : Records} (hNe : r.alice ≠ r.bob)
    {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next
      (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) :
    let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o
    ((runVis r (pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post)).filter
      (·.kind == .send)).flatMap (·.terms) = received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)] := by
  dsimp only
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o
  have henc : (Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂ =
      encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := by
    subst ho; exact encrypt_next_split38_eq (some (e, c')) hm₀ hmid rfl
  dsimp only [tr₁, m₀, tr₂, stA] at henc
  rw [runVis_split38_eq hNe hpre hmid hpost, aliceStart_vis_eq, encrypt_vis_eq, henc]; unfold encVis
  simp only [↓reduceIte, List.filter_append, filter_send_aliceVis_take_nil, filter_send_encDraws_nil, List.nil_append]
  unfold encSend; rw [lastSent_encNextTr]; simp

private theorem received_split38_handles_eq {tr₁ : ExecTrace} {a b : Participant}
    {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {m₀ : Move} {mid : List Move}
    (hm₀ : m₀.next tr₁ = iniAliceStartTr tr₁ a b o) (_hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid) :
    received (runMoves mid (m₀.next tr₁)).1 [tr₁.length + 3, tr₁.length + 4] = [o.ek, o.ct] := by
  have hek₀ : NetMsgAt o.ek (tr₁.length + 3) (m₀.next tr₁) := by rw [hm₀]; exact netMsgAt_ek_iniAliceStartTr tr₁ a b o
  have hct₀ : NetMsgAt o.ct (tr₁.length + 4) (m₀.next tr₁) := by rw [hm₀]; exact netMsgAt_ct_iniAliceStartTr tr₁ a b o
  have hek := CompPrefixInvAlice.getMessageSentAt_of_netMsgAt (CompTrace.at?_le_some (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁)) hek₀)
  have hct := CompPrefixInvAlice.getMessageSentAt_of_netMsgAt (CompTrace.at?_le_some (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁)) hct₀)
  simp [received, hek, hct]

private theorem getLast?_append_singleton : ∀ (xs : List DY.Bytes) (y : DY.Bytes), (xs ++ [y]).getLast? = some y
  | [], _ | [_], _ => rfl | _ :: b :: xs, y => getLast?_append_singleton (b :: xs) y

theorem prefixTerms_split38_swap_eq_of_init_send
    {r : Records} {S : Sem} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {ev0 ev1 : RunEvent} {peer0 peer1 : CryptoVerification.SignalSession.Address} {bdir : String} {out0 out1 : HwBytes}
    {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (hNe : r.alice ≠ r.bob)
    (hcmd0 : ev0.cmd = .init peer0 bdir) (hexit0 : ev0.exit = some (0, out0))
    (hcmd1 : ev1.cmd = .send peer1) (hexit1 : ev1.exit = some (0, out1)) (hwrap1 : runWrapped ev1 = true)
    (hmev : MatchesEventsClassical compI0 r S g (setupTrace r) ss [.run ev0, .run ev1] vis)
    (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
      ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next
      (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o)
    (htr : runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
      Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post) = runTrace r ss)
    (hpre_vis : prefixTerms r (runTrace r ss) (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
      Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post)) =
      prefixTerms r (runTrace r ss) vis)
    (hpt_vis : plaintextTerms (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
      Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post)) =
      plaintextTerms vis) :
    let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    prefixTerms r (runTrace r ss) (runVis r (pre ++ m₀ :: mid ++
      Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post)) =
    prefixTerms r (runTrace r ss) vis := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o
  have hpt' := (plaintextTerms_split38_swap_eq hNe (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4)) hpre hmid hpost).trans hpt_vis
  have hpost' : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := by
    rwa [encrypt_next_eq_wrap _ _ _ _ _ (some (tr₁.length + 3, tr₁.length + 4)) (some (e, c'))]
  obtain ⟨tr_s₁, stateIdx, ek, ct, msg, hle, hppk, hvis_send⟩ :=
    matchesEventsClassical_init_send_sendTerms hcmd0 hexit0 hcmd1 hexit1 hwrap1 hmev
  rw [← htr] at hle
  obtain ⟨d, a', b', ikA, ikB, spk, pqpk, opk, keys, hEv⟩ := exists_aliceDone_of_pendingPreKey hle hppk
  obtain ⟨rfl, rfl⟩ := aliceDone_split38_pin hNe ho hpre hmid hpost hm₀ hEv
  have hsend_ms := sendTerms_split38_eq hNe ho hpre hmid hpost hm₀
  have hsend_eq := sendTerms_eq_of_prefixTerms_eq hpre_vis hpt_vis
  have hlist_eq : received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)] = [o.ek, o.ct, msg] := by
    rw [← hsend_ms, hsend_eq, hvis_send]
  have hlast := congrArg List.getLast? hlist_eq; rw [getLast?_append_singleton] at hlast
  change some (encOut tr₂ stA cl (tr₂.length + 2)) = some msg at hlast
  have hmsg : encOut tr₂ stA cl (tr₂.length + 2) = msg := Option.some.inj hlast
  have hsend_ms' := sendTerms_split38_eq hNe ho hpre hmid hpost' hm₀; dsimp only at hsend_ms'
  rw [received_split38_handles_eq hm₀ hmid, hmsg] at hsend_ms'
  exact prefixTerms_eq_of_sendTerms_eq (hsend_ms'.trans hvis_send.symm) hpt'

end Split38Swap

end Symbolic.BugInjection.Proofs.Common443.CliEventBridge
