/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Preservation of Triple Ratchet Invariants Across Non-Ratchet Transitions

Defines `TrDHS.InertOnNonTR` for composed-trace predicates invariant under network, random, and
PQXDH entries, discharging all non-ratchet branches of `composed_reachable_induction`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (SessionInfo TREvent)
open DY.Libsignal.TripleRatchet.Cheval (StateStoredAt)

end DY.Libsignal.Composed

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse DY.DiffieHellman DY.KdfExtract DY.Literal DY.Concat
open DY.Libsignal.TripleRatchet (SessionInfo createChain kdfCk chainKeyAt)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent BundleHandles BobKeyHandles AliceHandshakeOut
  BobHandshakeOut aliceHandshake bobHandshake guardTrace registerIdentity registerCorruptIdentity
  genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK
  compromiseOPK breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TRState TREvent messageEncrypt messageEncryptAbort messageDecrypt
  messageDecryptSkipped exposeKey exposeSpqr exposeSkipped)
open DY.Libsignal.TripleRatchet.Cheval (StateStoredAt)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompTrace

namespace TrDHS

/-- Trace predicate `Inv` is preserved by appending network, random, PQXDH, or composed-event
entries. -/
structure InertOnNonTR (Inv : ExecTrace → Prop) : Prop where
  append_net : ∀ tr m, Inv tr → Inv (tr.append (NetE m))
  append_rnd : ∀ tr n, Inv tr → Inv (tr.append (RndE n))
  append_pqxEv : ∀ tr ev, Inv tr → Inv (tr.append (PQEvE ev))
  append_cEv : ∀ tr ev, Inv tr → Inv (tr.append (CEvE ev))
  append_pqxSt : ∀ tr p st, Inv tr → Inv (tr.append (PQStE p st))

namespace InertOnNonTR
variable {Inv : ExecTrace → Prop} (hI : InertOnNonTR Inv)
include hI
theorem preserves_sendMessage (m : Bytes) : Preserves Inv (Network.sendMessage m) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hI.append_net tr m h
theorem preserves_genRand (n : Nat) : Preserves Inv (Random.genRand n) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact hI.append_rnd tr n h
theorem preserves_logPQX (ev : PQXDHEvent) : Preserves Inv (ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]
  exact hI.append_pqxEv tr ev h
theorem preserves_storePQX (p : Participant) (st : PQXDHState) :
    Preserves Inv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hI.append_pqxSt tr p st h

omit hI in
theorem preserves_getKey (p : Participant) (stateIdx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves Inv (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
theorem preserves_registerIdentity (p : Participant) : Preserves Inv (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (hI.preserves_genRand 32) fun _ =>
    Preserves.bind (hI.preserves_logPQX _) fun _ => Preserves.bind (hI.preserves_sendMessage _) fun _ =>
    Preserves.bind (hI.preserves_sendMessage _) fun _ => hI.preserves_storePQX p _
theorem preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves Inv (registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ =>
    Preserves.bind (hI.preserves_logPQX _) fun _ => hI.preserves_logPQX _
theorem preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves Inv (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact Preserves.bind (preserves_getKey _ _ _) fun _ => Preserves.bind (hI.preserves_genRand 32) fun _ =>
    Preserves.bind (hI.preserves_genRand 64) fun _ => Preserves.bind (hI.preserves_logPQX _) fun _ =>
    Preserves.bind (hI.preserves_storePQX b _) fun _ => Preserves.bind (hI.preserves_sendMessage _) fun _ =>
    Preserves.bind (hI.preserves_sendMessage _) fun _ => Preserves.pure _
theorem preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves Inv (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact Preserves.bind (preserves_getKey _ _ _) fun _ => Preserves.bind (hI.preserves_genRand 64) fun _ =>
    Preserves.bind (hI.preserves_genRand 64) fun _ => Preserves.bind (hI.preserves_logPQX _) fun _ =>
    Preserves.bind (hI.preserves_storePQX b _) fun _ => Preserves.bind (hI.preserves_sendMessage _) fun _ =>
    Preserves.bind (hI.preserves_sendMessage _) fun _ => Preserves.pure _
theorem preserves_genOneTimePrekey (b : Participant) : Preserves Inv (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact Preserves.bind (hI.preserves_genRand 32) fun _ => Preserves.bind (hI.preserves_logPQX _) fun _ =>
    Preserves.bind (hI.preserves_storePQX b _) fun _ => Preserves.bind (hI.preserves_sendMessage _) fun _ => Preserves.pure _
theorem preserves_compromiseIK (p : Participant) (stateIdx : Nat) : Preserves Inv (compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact Preserves.bind (preserves_getKey _ _ _) fun _ => Preserves.bind (hI.preserves_logPQX _) fun _ => hI.preserves_sendMessage _
theorem preserves_compromiseSPK (b : Participant) (stateIdx : Nat) : Preserves Inv (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact Preserves.bind (preserves_getKey _ _ _) fun _ => Preserves.bind (hI.preserves_logPQX _) fun _ => hI.preserves_sendMessage _
theorem preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) : Preserves Inv (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact Preserves.bind (preserves_getKey _ _ _) fun _ => Preserves.bind (hI.preserves_logPQX _) fun _ => hI.preserves_sendMessage _
theorem preserves_compromiseOPK (b : Participant) (stateIdx : Nat) : Preserves Inv (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact Preserves.bind (preserves_getKey _ _ _) fun _ =>
    Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (hI.preserves_logPQX _) fun _ => hI.preserves_sendMessage _
theorem preserves_breakDH : Preserves Inv breakDH :=
  hI.preserves_logPQX _
theorem preserves_breakKEM : Preserves Inv breakKEM :=
  hI.preserves_logPQX _
theorem preserves_invertDH (pkIdx : Nat) : Preserves Inv (invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact hI.preserves_sendMessage _
  · exact Preserves.failure
theorem preserves_invertKEM (pkIdx : Nat) : Preserves Inv (invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.monadLiftErr _) fun _ => ?_
  exact hI.preserves_sendMessage _
theorem preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves Inv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  exact Preserves.bind (hI.preserves_genRand 32) fun _ => Preserves.failure
theorem bind_aliceHandshake {α : Type}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles)
    {f : AliceHandshakeOut → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ o : AliceHandshakeOut,
      Inv ((f o).run ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    Inv (((aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) :=
  bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hInv (hI.append_rnd tr 32 hInv)
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hf _

omit hI in
theorem bind_bobHandshake {α : Type}
    (b a : Participant) (kh : BobKeyHandles) (regIdxA ekIdx ctIdx : Nat)
    {f : BobHandshakeOut → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ o : BobHandshakeOut, Inv ((f o).run tr).2.val) :
    Inv (((bobHandshake b a kh regIdxA ekIdx ctIdx >>= f).run tr).2.val) :=
  bind_bobHandshake_at b a kh regIdxA ekIdx ctIdx tr hInv
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hf _
theorem reachable_induction
    (hBase : Inv Trace.nil)
    (hAliceStart : ∀ a b idStateIdx regIdxB bh, Preserves Inv (aliceStart a b idStateIdx regIdxB bh))
    (hBobStart : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx,
      Preserves Inv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx))
    (hMsgEnc : ∀ me stH coinsLen pqIdx, Preserves Inv (messageEncrypt me stH coinsLen pqIdx))
    (hMsgDec : ∀ me stH msgH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecrypt me stH msgH pqIdx spqrMsgIdx))
    (hMsgDecSkip : ∀ me stH msgH evH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx))
    (hExpKey : ∀ me stH k, Preserves Inv (exposeKey me stH k))
    (hExpSpqr : ∀ me stH, Preserves Inv (exposeSpqr me stH))
    (hExpSkip : ∀ evH, Preserves Inv (exposeSkipped evH))
    {tr : ExecTrace} (hReach : tr.Reachable DY.Libsignal.Composed.reachability) :
    Inv tr :=
  composed_reachable_induction hBase
    (fun msg t _ hInv => hI.append_net t msg hInv)
    hI.preserves_registerIdentity
    hI.preserves_registerCorruptIdentity
    hI.preserves_genSignedPrekey
    hI.preserves_genPQPrekey
    hI.preserves_genOneTimePrekey
    hAliceStart
    hBobStart
    hMsgEnc
    hI.preserves_messageEncryptAbort
    hMsgDec
    hMsgDecSkip
    hExpKey
    hExpSpqr
    hExpSkip
    hI.preserves_compromiseIK
    hI.preserves_compromiseSPK
    hI.preserves_compromisePQSPK
    hI.preserves_compromiseOPK
    hI.preserves_breakDH
    hI.preserves_breakKEM
    hI.preserves_invertDH
    hI.preserves_invertKEM
    hReach

end InertOnNonTR

end TrDHS

open TrDHS

end Symbolic.Swarm.COMPOSED.CompRatchet
