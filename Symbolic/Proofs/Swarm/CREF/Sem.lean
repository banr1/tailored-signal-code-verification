/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Composed Opaque Symbol Semantics

Defines `SemReady` and the concrete `OpaqueSymbolSemantics` instance `compSemOf` built from shared
SPQR byte operations and setup KEM/signature tables, and proves `compSemOf_ready` under
`ProtocolSetupWF`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.SHARED.SpqrBytes
  (spqrInitOf spqrChainKeyOf spqrSendStateOf spqrSendKeyOf spqrSendMsgOf spqrRecvStateOf spqrRecvKeyOf)

/-- `S` is compatible with every ghost that agrees with the records on the setup's fresh values. -/
def SemReady (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) : Prop :=
  ∀ g : Ghost, (∀ p ∈ setupRandomsAt r, g.σ p.1 p.2 = r.fresh p.1 p.2) →
    GhostAndSemMatchSetup interpretation r S g

/-- Concrete `OpaqueSymbolSemantics` for composed refinement, combining SPQR byte operations from
`Symbolic.Swarm.SHARED.SpqrBytes` with setup-compatible KEM and signature functions. -/
def compSemOf (interpretation : ExternInterpretation) (r : ProtocolSetup) : OpaqueSymbolSemantics where
  init := spqrInitOf interpretation
  chainKey := spqrChainKeyOf interpretation
  sendState := spqrSendStateOf interpretation
  sendKey := spqrSendKeyOf interpretation
  sendMsg := spqrSendMsgOf interpretation
  recvState := spqrRecvStateOf interpretation
  recvKey := spqrRecvKeyOf interpretation
  kemPk := fun sk =>
    if sk = r.fresh 16 64 then
      r.opaqueBytes (setupPublic r 6)
    else
      0xFF#8 :: sk
  kemDecap := fun _ ct => (kyberDecapsBytes interpretation r ct).getD []
  vk := fun sk => pubBytes interpretation (clamp sk)
  sign := fun _sk nonce msg =>
    match msg with
    | 0x05#8 :: _ => r.opaqueBytes (setupPublic r 5)
    | 0x08#8 :: _ => r.opaqueBytes (setupPublic r 7)
    | _ =>
      if nonce = r.fresh 11 64 then r.opaqueBytes (setupPublic r 5)
      else r.opaqueBytes (setupPublic r 7)

/-! ## Private helpers for `gamma` unfolding -/

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem b1_gamma_rand (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (idx sz : Nat) :
    gamma interpretation S g (randTerm idx sz) =
      if sz = 0 then [] else g.σ idx sz := by
  unfold gamma gamma' randTerm
  show ((({ timestamp := idx, size := sz } : DY.Random.Random DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  unfold concretizeRandom node
  split <;> rfl

private theorem b1_gamma_lit (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : ByteArray) :
    gamma interpretation S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]
  rfl

private theorem b1_gamma_concat (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (l r : DY.Bytes) :
    gamma interpretation S g (DY.Concat.concat l r) =
      gamma interpretation S g l ++ gamma interpretation S g r := by
  unfold gamma gamma'
  show ((({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]
  rfl

private theorem b1_gamma_kemPk (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (seed : DY.Bytes) :
    gamma interpretation S g (DY.PQKem.kemPk seed) =
      S.kemPk (gamma interpretation S g seed) := by
  unfold gamma gamma' DY.PQKem.kemPk
  show ((({ sk := seed } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll interpretation S g)]
  rfl

private theorem b1_gamma_sign (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (sk nonce msg : DY.Bytes) :
    gamma interpretation S g (DY.Signature.sign sk nonce msg) =
      S.sign (gamma interpretation S g sk) (gamma interpretation S g nonce)
        (gamma interpretation S g msg) := by
  unfold gamma gamma' DY.Signature.sign
  show ((({ sk := sk, nonce := nonce, msg := msg } : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll interpretation S g)]
  rfl

private theorem b1_gamma_encodeEC (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.PQXDH.encodeEC pk) =
      0x05#8 :: gamma interpretation S g pk := by
  unfold DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
  rw [b1_gamma_concat, b1_gamma_lit]
  rfl

private theorem b1_gamma_encodeKEM (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.PQXDH.encodeKEM pk) =
      0x08#8 :: gamma interpretation S g pk := by
  unfold DY.Libsignal.PQXDH.encodeKEM DY.Libsignal.TripleRatchet.litByte
  rw [b1_gamma_concat, b1_gamma_lit]
  rfl

/-! ## `Runs` helpers for `setupTrace` in Composed `ExecTrace` -/

private def b1_Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private theorem b1_Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} {b : β}
    (h1 : b1_Runs x tr a tr1) (h2 : b1_Runs (f a) tr1 b tr2) :
    b1_Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b
  cases h1a
  cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b
  cases h2a
  cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem b1_Runs.pure {α : Type} (a : α) (tr : ExecTrace) :
    b1_Runs (Pure.pure a : Traceful α) tr a tr := by
  simp [b1_Runs, DY.Traceful.run_pure]

attribute [local irreducible] Bind.bind

private theorem b1_Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : b1_Runs (DY.getEntry i : Traceful E) tr e tr := by
  unfold b1_Runs
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  rw [h]
  exact ⟨rfl, rfl⟩

private theorem b1_Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    b1_Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold b1_Runs
  simp only [Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  exact ⟨rfl, rfl⟩

private theorem b1_Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    b1_Runs (_root_.guard p : Traceful Unit) tr () tr := by
  simp only [_root_.guard, h, ↓reduceIte]; exact b1_Runs.pure () tr

abbrev b1_EvE (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent :=
  DY.ProtocolEvent.ExecEntryT.mk ev

abbrev b1_NetE (b : DY.Bytes) : DY.Network.ExecEntryT :=
  DY.Network.ExecEntryT.mk b

abbrev b1_StE (me : DY.Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :=
  DY.PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := me, state := st } :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)

abbrev b1_RndE (n : Nat) : DY.Random.ExecEntryT :=
  DY.Random.ExecEntryT.mk n

private theorem b1_Runs.logEvent (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    b1_Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (b1_EvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact b1_Runs.bind (b1_Runs.appendEntry tr _) (b1_Runs.pure _ _)

private theorem b1_Runs.genRand (tr : ExecTrace) (n : Nat) :
    b1_Runs (DY.Random.genRand n) tr (randTerm tr.length n) (tr.append (b1_RndE n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact b1_Runs.bind (b1_Runs.appendEntry tr _) (b1_Runs.pure _ _)

private theorem b1_Runs.sendMessage (tr : ExecTrace) (b : DY.Bytes) :
    b1_Runs (DY.Network.sendMessage b) tr tr.length (tr.append (b1_NetE b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact b1_Runs.appendEntry _ _

private theorem b1_Runs.storeLocalState (tr : ExecTrace) (me : DY.Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) :
    b1_Runs (DY.PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (b1_StE me st)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact b1_Runs.appendEntry _ _

private theorem b1_Runs.getKey {tr : ExecTrace} {me : DY.Participant} {h : Nat}
    {kind : DY.Libsignal.PQXDH.KeyKind} {sk : DY.Bytes}
    (hst : tr.at? h = some (b1_StE me { kind, sk })) :
    b1_Runs (DY.Libsignal.PQXDH.getKey me h kind) tr sk tr := by
  unfold DY.Libsignal.PQXDH.getKey
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine b1_Runs.bind (b1_Runs.bind (b1_Runs.bind (b1_Runs.getEntry hst) (b1_Runs.pure _ _))
    (b1_Runs.bind (b1_Runs.guard _ rfl) (b1_Runs.pure _ _))) ?_
  exact b1_Runs.bind (b1_Runs.guard _ rfl) (b1_Runs.pure _ _)

private theorem b1_Runs.requireTracePredicate {p : ExecTrace → Bool} {tr : ExecTrace} (h : p tr = true) :
    b1_Runs (DY.Libsignal.PQXDH.guardTrace p) tr () tr := by
  unfold b1_Runs DY.Libsignal.PQXDH.guardTrace
  simp only [Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

def b1_setupTr1 (a : DY.Participant) : ExecTrace :=
  ((((Trace.nil.append (b1_RndE 32)).append
    (b1_EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true))).append
    (b1_NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))).append
    (b1_NetE (DY.Signature.vk (randTerm 0 32)))).append
    (b1_StE a { kind := .identity, sk := randTerm 0 32 })

def b1_setupTr2 (a b : DY.Participant) : ExecTrace :=
  (((((b1_setupTr1 a).append (b1_RndE 32)).append
    (b1_EvE (.IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32))
      (DY.Signature.vk (randTerm 5 32)) true))).append
    (b1_NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))).append
    (b1_NetE (DY.Signature.vk (randTerm 5 32)))).append
    (b1_StE b { kind := .identity, sk := randTerm 5 32 })

def b1_setupTr3 (a b : DY.Participant) : ExecTrace :=
  ((((((b1_setupTr2 a b).append (b1_RndE 32)).append (b1_RndE 64)).append
    (b1_EvE (.SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))))).append
    (b1_StE b { kind := .signedPrekey, sk := randTerm 10 32 })).append
    (b1_NetE (DY.DiffieHellman.dhPk (randTerm 10 32)))).append
    (b1_NetE (DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
      (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32)))))

def b1_setupTr4 (a b : DY.Participant) : ExecTrace :=
  ((((((b1_setupTr3 a b).append (b1_RndE 64)).append (b1_RndE 64)).append
    (b1_EvE (.PQPrekeyPublished b (DY.PQKem.kemPk (randTerm 16 64))))).append
    (b1_StE b { kind := .pqPrekey, sk := randTerm 16 64 })).append
    (b1_NetE (DY.PQKem.kemPk (randTerm 16 64)))).append
    (b1_NetE (DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
      (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))))

def b1_setupTr5 (a b : DY.Participant) : ExecTrace :=
  ((((b1_setupTr4 a b).append (b1_RndE 32)).append
    (b1_EvE (.OneTimePrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 22 32))))).append
    (b1_StE b { kind := .oneTimePrekey, sk := randTerm 22 32 })).append
    (b1_NetE (DY.DiffieHellman.dhPk (randTerm 22 32)))

private theorem b1_runs_registerIdentity_a (a : DY.Participant) :
    b1_Runs (DY.Libsignal.PQXDH.registerIdentity a) Trace.nil 4 (b1_setupTr1 a) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine b1_Runs.bind (b1_Runs.requireTracePredicate
    (by simp [DY.Libsignal.PQXDH.isRegisteredB, DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      Symbolic.DYBridge.DY.Trace.length_eq_1])) ?_
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
  refine b1_Runs.bind (b1_Runs.logEvent _ _) ?_
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  rw [show (4 : Nat) =
    (((((Trace.nil : ExecTrace).append (b1_RndE 32)).append
      (b1_EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
        (DY.Signature.vk (randTerm 0 32)) true))).append
      (b1_NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))).append
      (b1_NetE (DY.Signature.vk (randTerm 0 32)))).length by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]]
  exact b1_Runs.storeLocalState _ _ _

private theorem b1_not_isRegisteredB_setupTr1 {a b : DY.Participant} (hNe : a ≠ b) :
    (!DY.Libsignal.PQXDH.isRegisteredB (b1_setupTr1 a) b) = true := by
  have hbeq : (a == b) = false := beq_false_of_ne hNe
  have h0 : (b1_setupTr1 a).length = 5 := by
    simp [b1_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hat0 : ((b1_setupTr1 a).at? 0 :
    Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
    simp [b1_setupTr1, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    rfl
  have hat1 : ((b1_setupTr1 a).at? 1 :
    Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
    some (b1_EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true)) := by
    simp [b1_setupTr1, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    rfl
  have hat2 : ((b1_setupTr1 a).at? 2 :
    Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
    simp [b1_setupTr1, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    rfl
  have hat3 : ((b1_setupTr1 a).at? 3 :
    Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
    simp [b1_setupTr1, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    rfl
  have hat4 : ((b1_setupTr1 a).at? 4 :
    Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
    simp [b1_setupTr1, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    rfl
  unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [h0]
  simp [List.range_succ, hat0, hat1, hat2, hat3, hat4, hbeq]

private theorem b1_at?_append_of_some {E E' : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E']
    {tr : ExecTrace} {e : E'} {i : Nat} {res : E} (h : tr.at? i = some res) :
    (tr.append e).at? i = some res := by
  have hle := Trace.at?_le (EntryT := E) tr (tr.append e) i (Trace.append_le tr e)
  rw [h] at hle
  exact hle

private theorem b1_setupTr2_idB (a b : DY.Participant) :
    (b1_setupTr2 a b).at? 9 = some (b1_StE b { kind := .identity, sk := randTerm 5 32 }) := by
  unfold b1_setupTr2
  rw [show (9 : Nat) =
    (((((b1_setupTr1 a).append (b1_RndE 32)).append
      (b1_EvE (.IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32))
        (DY.Signature.vk (randTerm 5 32)) true))).append
      (b1_NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))).append
      (b1_NetE (DY.Signature.vk (randTerm 5 32)))).length by
    simp [b1_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]]
  exact Trace.at?_append _ _

private theorem b1_setupTr3_idB (a b : DY.Participant) :
    (b1_setupTr3 a b).at? 9 = some (b1_StE b { kind := .identity, sk := randTerm 5 32 }) := by
  unfold b1_setupTr3
  exact b1_at?_append_of_some (b1_at?_append_of_some (b1_at?_append_of_some
    (b1_at?_append_of_some (b1_at?_append_of_some (b1_at?_append_of_some (b1_setupTr2_idB a b))))))

private theorem b1_runs_registerIdentity_b {a b : DY.Participant} (hNe : a ≠ b) :
    b1_Runs (DY.Libsignal.PQXDH.registerIdentity b) (b1_setupTr1 a) 9 (b1_setupTr2 a b) := by
  have hl1 : (b1_setupTr1 a).length = 5 := by
    simp [b1_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine b1_Runs.bind (b1_Runs.requireTracePredicate (b1_not_isRegisteredB_setupTr1 hNe)) ?_
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [hl1]
  refine b1_Runs.bind (b1_Runs.logEvent _ _) ?_
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  rw [show (9 : Nat) =
    (((((b1_setupTr1 a).append (b1_RndE 32)).append
      (b1_EvE (.IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32))
        (DY.Signature.vk (randTerm 5 32)) true))).append
      (b1_NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))).append
      (b1_NetE (DY.Signature.vk (randTerm 5 32)))).length by
    simp [hl1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]]
  exact b1_Runs.storeLocalState _ _ _

private theorem b1_runs_genSignedPrekey (a b : DY.Participant) :
    b1_Runs (DY.Libsignal.PQXDH.genSignedPrekey b 9) (b1_setupTr2 a b) 13 (b1_setupTr3 a b) := by
  have hl2 : (b1_setupTr2 a b).length = 10 := by
    simp [b1_setupTr2, b1_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl2' : ((b1_setupTr2 a b).append (b1_RndE 32)).length = 11 := by
    simp [hl2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine b1_Runs.bind (b1_Runs.getKey (b1_setupTr2_idB a b)) ?_
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [hl2]
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [hl2']
  refine b1_Runs.bind (b1_Runs.logEvent _ _) ?_
  refine b1_Runs.bind (b1_Runs.storeLocalState _ _ _) ?_
  rw [show ((((b1_setupTr2 a b).append (b1_RndE 32)).append (b1_RndE 64)).append
      (b1_EvE (.SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))))).length = 13 by
    simp [hl2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]]
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  exact b1_Runs.pure _ _

private theorem b1_runs_genPQPrekey (a b : DY.Participant) :
    b1_Runs (DY.Libsignal.PQXDH.genPQPrekey b 9) (b1_setupTr3 a b) 19 (b1_setupTr4 a b) := by
  have hl3 : (b1_setupTr3 a b).length = 16 := by
    simp [b1_setupTr3, b1_setupTr2, b1_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl3' : ((b1_setupTr3 a b).append (b1_RndE 64)).length = 17 := by
    simp [hl3, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine b1_Runs.bind (b1_Runs.getKey (b1_setupTr3_idB a b)) ?_
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [hl3]
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [hl3']
  refine b1_Runs.bind (b1_Runs.logEvent _ _) ?_
  refine b1_Runs.bind (b1_Runs.storeLocalState _ _ _) ?_
  rw [show ((((b1_setupTr3 a b).append (b1_RndE 64)).append (b1_RndE 64)).append
      (b1_EvE (.PQPrekeyPublished b (DY.PQKem.kemPk (randTerm 16 64))))).length = 19 by
    simp [hl3, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]]
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  exact b1_Runs.pure _ _

private theorem b1_runs_genOneTimePrekey (a b : DY.Participant) :
    b1_Runs (DY.Libsignal.PQXDH.genOneTimePrekey b) (b1_setupTr4 a b) 24 (b1_setupTr5 a b) := by
  have hl4 : (b1_setupTr4 a b).length = 22 := by
    simp [b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine b1_Runs.bind (b1_Runs.genRand _ _) ?_
  rw [hl4]
  refine b1_Runs.bind (b1_Runs.logEvent _ _) ?_
  refine b1_Runs.bind (b1_Runs.storeLocalState _ _ _) ?_
  rw [show (((b1_setupTr4 a b).append (b1_RndE 32)).append
      (b1_EvE (.OneTimePrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 22 32))))).length = 24 by
    simp [hl4, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]]
  refine b1_Runs.bind (b1_Runs.sendMessage _ _) ?_
  exact b1_Runs.pure _ _

theorem b1_setupTrace_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupTrace r = if r.withOpk then b1_setupTr5 r.alice r.bob else b1_setupTr4 r.alice r.bob := by
  unfold setupTrace setupAct
  have h : b1_Runs (setupAct r.alice r.bob r.withOpk) Trace.nil ()
      (if r.withOpk then b1_setupTr5 r.alice r.bob else b1_setupTr4 r.alice r.bob) := by
    unfold setupAct
    refine b1_Runs.bind (b1_runs_registerIdentity_a r.alice) ?_
    refine b1_Runs.bind (b1_runs_registerIdentity_b hNe) ?_
    refine b1_Runs.bind (b1_runs_genSignedPrekey r.alice r.bob) ?_
    refine b1_Runs.bind (b1_runs_genPQPrekey r.alice r.bob) ?_
    cases r.withOpk with
    | false => exact b1_Runs.pure () _
    | true => exact b1_Runs.bind (b1_runs_genOneTimePrekey r.alice r.bob) (b1_Runs.pure () _)
  exact h.2

theorem b1_setupRandomsAt_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupRandomsAt r =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] ++
        (if r.withOpk then [(22, 32)] else []) := by
  have hstep : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E),
      (newIndices Trace.nil (tr.append e)).filterMap
        (fun i => ((tr.append e).at? i : Option DY.Random.ExecEntryT).map fun x => (i, x.length)) =
      (newIndices Trace.nil tr).filterMap
        (fun i => (tr.at? i : Option DY.Random.ExecEntryT).map fun x => (i, x.length)) ++
        match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option DY.Random.ExecEntryT) with
        | none => []
        | some entry => [(tr.length, entry.length)] := by
    intro E _ tr e
    have hcongr : ∀ (l : List Nat) (f g : Nat → Option (Nat × Nat)),
        (∀ i ∈ l, f i = g i) → l.filterMap f = l.filterMap g := by
      intro l f g hfg
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filterMap_cons, hfg x (.head _), ih (fun i hi => hfg i (.tail _ hi))]
    have hni : newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
      unfold newIndices
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat, Nat.zero_add, Nat.one_mul]
    rw [hni, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    congr 1
    · refine hcongr _ _ _ fun i hi => ?_
      unfold newIndices at hi
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero, List.mem_range'_1,
        Nat.zero_add] at hi
      have hi2 : i < (tr.append e).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      simp only [DY.Trace.at?, hi.2, hi2, ↓reduceDIte,
        DY.Trace.at_le tr (tr.append e) i hi.2 (DY.Trace.append_le tr e)]
    · simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
        Symbolic.DYBridge.DY.Trace.at_eq_2]
      cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option DY.Random.ExecEntryT) <;> rfl
  have hnil : (newIndices Trace.nil (Trace.nil : ExecTrace)).filterMap
      (fun i => ((Trace.nil : ExecTrace).at? i : Option DY.Random.ExecEntryT).map
        fun x => (i, x.length)) = [] := by
    simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hrnd : ∀ (tr : ExecTrace) (n : Nat),
      (newIndices Trace.nil (tr.append (b1_RndE n))).filterMap
        (fun i => ((tr.append (b1_RndE n)).at? i : Option DY.Random.ExecEntryT).map
          fun x => (i, x.length)) =
      (newIndices Trace.nil tr).filterMap
        (fun i => (tr.at? i : Option DY.Random.ExecEntryT).map fun x => (i, x.length)) ++
        [(tr.length, n)] :=
    fun tr n => hstep tr (b1_RndE n)
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      (newIndices Trace.nil (tr.append (b1_NetE m))).filterMap
        (fun i => ((tr.append (b1_NetE m)).at? i : Option DY.Random.ExecEntryT).map
          fun x => (i, x.length)) =
      (newIndices Trace.nil tr).filterMap
        (fun i => (tr.at? i : Option DY.Random.ExecEntryT).map fun x => (i, x.length)) := by
    intro tr m; rw [hstep]; exact List.append_nil _
  have hev : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent),
      (newIndices Trace.nil (tr.append (b1_EvE ev))).filterMap
        (fun i => ((tr.append (b1_EvE ev)).at? i : Option DY.Random.ExecEntryT).map
          fun x => (i, x.length)) =
      (newIndices Trace.nil tr).filterMap
        (fun i => (tr.at? i : Option DY.Random.ExecEntryT).map fun x => (i, x.length)) := by
    intro tr ev; rw [hstep]; exact List.append_nil _
  have hst : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.PQXDH.PQXDHState),
      (newIndices Trace.nil (tr.append (b1_StE me s))).filterMap
        (fun i => ((tr.append (b1_StE me s)).at? i : Option DY.Random.ExecEntryT).map
          fun x => (i, x.length)) =
      (newIndices Trace.nil tr).filterMap
        (fun i => (tr.at? i : Option DY.Random.ExecEntryT).map fun x => (i, x.length)) := by
    intro tr me s; rw [hstep]; exact List.append_nil _
  rw [setupRandomsAt, b1_setupTrace_eq r hNe]
  cases r.withOpk
  · simp only [Bool.false_eq_true, ↓reduceIte, b1_setupTr4, b1_setupTr3,
      b1_setupTr2, b1_setupTr1, hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append,
      List.append_nil]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  · simp only [↓reduceIte, b1_setupTr5, b1_setupTr4, b1_setupTr3,
      b1_setupTr2, b1_setupTr1, hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem b1_setupSent_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupSent r =
      [DY.DiffieHellman.dhPk (randTerm 0 32),
       DY.Signature.vk (randTerm 0 32),
       DY.DiffieHellman.dhPk (randTerm 5 32),
       DY.Signature.vk (randTerm 5 32),
       DY.DiffieHellman.dhPk (randTerm 10 32),
       DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
         (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))),
       DY.PQKem.kemPk (randTerm 16 64),
       DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
         (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))] ++
        (if r.withOpk then [DY.DiffieHellman.dhPk (randTerm 22 32)] else []) := by
  have hstep : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E),
      (newIndices Trace.nil (tr.append e)).filterMap (fun i => (tr.append e).getMessageSentAt i) =
        (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) ++
          match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
              Option DY.Network.ExecEntryT) with
          | none => []
          | some entry => [entry.msg] := by
    intro E _ tr e
    have hcongr : ∀ (l : List Nat) (f g : Nat → Option DY.Bytes),
        (∀ i ∈ l, f i = g i) → l.filterMap f = l.filterMap g := by
      intro l f g hfg
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filterMap_cons, hfg x (.head _), ih (fun i hi => hfg i (.tail _ hi))]
    have hni : newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
      unfold newIndices
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat, Nat.zero_add, Nat.one_mul]
    rw [hni, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    congr 1
    · refine hcongr _ _ _ fun i hi => ?_
      unfold newIndices at hi
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero, List.mem_range'_1,
        Nat.zero_add] at hi
      have hi2 : i < (tr.append e).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?, hi.2, hi2,
        ↓reduceDIte, DY.Trace.at_le tr (tr.append e) i hi.2 (DY.Trace.append_le tr e)]
    · simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Nat.lt_succ_self, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
      cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option DY.Network.ExecEntryT) <;> rfl
  have hnil : (newIndices Trace.nil (Trace.nil : ExecTrace)).filterMap
      (fun i => (Trace.nil : ExecTrace).getMessageSentAt i) = [] := by
    simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      (newIndices Trace.nil (tr.append (b1_NetE m))).filterMap
        (fun i => (tr.append (b1_NetE m)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) ++ [m] :=
    fun tr m => hstep tr (b1_NetE m)
  have hrnd : ∀ (tr : ExecTrace) (n : Nat),
      (newIndices Trace.nil (tr.append (b1_RndE n))).filterMap
        (fun i => (tr.append (b1_RndE n)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) := by
    intro tr n; rw [hstep]; exact List.append_nil _
  have hev : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent),
      (newIndices Trace.nil (tr.append (b1_EvE ev))).filterMap
        (fun i => (tr.append (b1_EvE ev)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) := by
    intro tr ev; rw [hstep]; exact List.append_nil _
  have hst : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.PQXDH.PQXDHState),
      (newIndices Trace.nil (tr.append (b1_StE me s))).filterMap
        (fun i => (tr.append (b1_StE me s)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) := by
    intro tr me s; rw [hstep]; exact List.append_nil _
  rw [setupSent, b1_setupTrace_eq r hNe]
  cases r.withOpk
  · simp only [Bool.false_eq_true, ↓reduceIte, b1_setupTr4, b1_setupTr3,
      b1_setupTr2, b1_setupTr1, hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append,
      List.append_nil]
  · simp only [↓reduceIte, b1_setupTr5, b1_setupTr4, b1_setupTr3,
      b1_setupTr2, b1_setupTr1, hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]

theorem b1_setupPublic_5 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupPublic r 5 =
      DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))) := by
  rw [setupPublic, b1_setupSent_eq r hNe]
  cases r.withOpk <;> rfl

theorem b1_setupPublic_6 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) := by
  rw [setupPublic, b1_setupSent_eq r hNe]
  cases r.withOpk <;> rfl

theorem b1_setupPublic_7 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupPublic r 7 =
      DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))) := by
  rw [setupPublic, b1_setupSent_eq r hNe]
  cases r.withOpk <;> rfl

/-- `compSemOf interpretation r` is compatible with every ghost that agrees with `r` on the setup's
fresh values (`r.alice ≠ r.bob` version). -/
theorem compSemOf_ready_of_ne (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) :
    SemReady interpretation r (compSemOf interpretation r) := by
  intro g hσ
  refine ⟨hσ, ?_, fun _ => rfl⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  ·
    unfold ProtocolSetup.spkSigTerm
    have h5 := b1_setupPublic_5 r hNe
    conv => lhs; rw [h5, b1_gamma_sign, b1_gamma_encodeEC]
    rfl
  ·
    unfold ProtocolSetup.pqpkPubTerm
    have h6 := b1_setupPublic_6 r hNe
    have h16 : g.σ 16 64 = r.fresh 16 64 := by
      apply hσ (16, 64)
      rw [b1_setupRandomsAt_eq r hNe]
      simp
    conv =>
      lhs
      rw [h6, b1_gamma_kemPk, b1_gamma_rand]
    change (if g.σ 16 64 = r.fresh 16 64 then r.opaqueBytes (setupPublic r 6) else 0xFF#8 :: g.σ 16 64) =
      r.opaqueBytes (setupPublic r 6)
    simp only [h16, ↓reduceIte]
  ·
    unfold ProtocolSetup.pqpkSigTerm
    have h7 := b1_setupPublic_7 r hNe
    conv => lhs; rw [h7, b1_gamma_sign, b1_gamma_encodeKEM]
    rfl

/-- `compSemOf interpretation r` satisfies `SemReady interpretation r` under `ProtocolSetupWF r`. -/
theorem compSemOf_ready (interpretation : ExternInterpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r) :
    SemReady interpretation r (compSemOf interpretation r) :=
  compSemOf_ready_of_ne interpretation r hwf.1

end Symbolic.Swarm.CREF
