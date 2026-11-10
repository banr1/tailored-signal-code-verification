/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.Adversary
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.DYBridge.DY.Bytes.Basic
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
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH Secrecy Tightness Witness Traces

Defines the split-compromise witness trace `trR2` (where `compromiseIK "bob"` precedes `BobDone`
and `compromiseSPK "bob"` and `compromisePQSPK "bob"` occur afterward) together with generic
singleton event-index lemmas for PQXDH secrecy tightness tests.
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHSecrecyTraces

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (ak_aliceAgreement_block_of_responderSecrets
  ak_net compIkTr compIkTr_reach compPqTr compPqTr_reach compSpkTr compSpkTr_reach isAnyTRExposure
  not_sessionStateExposed_of_no_trExposure trEvIdx)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (bh1 evIdx ikA ikB isCompromise kh1
  mem_evIdx pqNonce pqskB spkB spkNonce t1 t1_length t2 t2_length t3 t3_length t4 t4_length
  t4_reach t5 t5_noCompromise)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_init_agree)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.aliceStart
  Runs.bobStart Runs.genPQPrekey Runs.genSignedPrekey Runs.messageEncrypt Runs.registerIdentity
  StP StT aliceOut aliceSt aliceStart_reachable aliceTr aliceTrOpt bobAgreement_honest bobSt0
  bobStart_reachable createChain_comm dec_ok encMsg encSig encTr genPQPrekeyTr genSignedPrekeyTr
  mac_ok messageEncrypt_reachable parse_encMsg ratchetState reach_of_runs recvSt registerIdentityTr
  rnd skipTr)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem DY.Literal DY.Concat
open DY.Libsignal.Composed
open TripleRatchet (RecvChain TRState TREvent kdfCk createChain setRecvChain maxReceiverChains
  spqrB2A)
open PQXDH (PQXDHEvent HandshakeKeys PreKeyMsgHandles AliceHandshakeOut IsHandshakeBlock
  LoggedBefore SessionStateExposed)

/-! ## Split-compromise witness trace `trR2` -/

def trR2_1 : ExecTrace := compIkTr t4 "bob" ikB

def trR2_2 : ExecTrace :=
  aliceTr trR2_1 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)

abbrev trR2_out : AliceHandshakeOut :=
  aliceOut trR2_1 ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
abbrev trR2_keys : HandshakeKeys := trR2_out.keys
abbrev trR2_dhsA : Bytes := rnd 26 32
def trR2_stA0 : TRState := aliceSt "bob" trR2_out trR2_dhsA

abbrev trR2_m0 : Bytes := rnd 33 32
abbrev trR2_coins0 : Bytes := rnd 34 32
def trR2_key0 : Bytes := (Spqr.spqrSend trR2_stA0.spqr trR2_coins0).2.1
def trR2_pqm0 : Bytes := (Spqr.spqrSend trR2_stA0.spqr trR2_coins0).2.2
def trR2_3 : ExecTrace := encTr trR2_2 "alice" 32 trR2_stA0 trR2_key0

def trR2_mh : PreKeyMsgHandles := { ek := 27, ct := 28, msg := 39 }
abbrev trR2_dhsB1 : Bytes := rnd 40 32
def trR2_stB00 : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) trR2_keys
    (encSig trR2_stA0 trR2_coins0 trR2_key0 trR2_m0)
def trR2_stB0' : TRState := (ratchetState trR2_stB00 (dhPk trR2_dhsA) trR2_dhsB1).1
def trR2_cB : RecvChain := (ratchetState trR2_stB00 (dhPk trR2_dhsA) trR2_dhsB1).2
def trR2_cB' : RecvChain := { trR2_cB with chainKey := (kdfCk trR2_cB.chainKey).1, index := 1 }
def trR2_seedB0 : Bytes := (kdfCk trR2_cB.chainKey).2
def trR2_stB1 : TRState :=
  { trR2_stB0' with
    recv := [trR2_cB'], spqr := recvSt (Spqr.spqrInit trR2_keys.pqr spqrB2A) trR2_pqm0 }

def trR2_4 : ExecTrace :=
  let tr1 := (trR2_3.append (RndE 32)).append (NetE trR2_key0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none trR2_out.ek trR2_out.ct trR2_keys))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk trR2_dhsA) (dhPk trR2_dhsB1)))).append
      (EvT (.HonestDH (trR2_stB0'.sessionInfo "bob") trR2_dhsB1 0))).append
      (EvC (.HandshakeSession (trR2_stB0'.sessionInfo "bob") 42))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk trR2_dhsA) 0 trR2_m0))).append
    (EvT (.MessageKey (trR2_stB0'.sessionInfo "bob") .receiver trR2_seedB0
      trR2_key0 0 2 48))).append
    (StT "bob" trR2_stB1)

def trR2_5 : ExecTrace := compSpkTr trR2_4 "bob" spkB
def trR2 : ExecTrace := compPqTr trR2_5 "bob" pqskB

theorem trR2_seedB0_eq : (kdfCk trR2_stA0.cks).2 = trR2_seedB0 := by
  show (kdfCk (createChain trR2_keys.rk (dhPk spkB) trR2_dhsA).2).2 =
    (kdfCk (createChain trR2_keys.rk (dhPk trR2_dhsA) spkB).2).2
  rw [createChain_comm trR2_keys.rk trR2_dhsA spkB]

theorem trR2_reach : trR2.Reachable reachability := by
  have hat_here : ∀ {E : Type} [ExecTraceTypes.Has E] {i : Nat} (tr : ExecTrace) (e : E),
      tr.length = i → (tr.append e).at? i = some e :=
    fun tr e hi => hi ▸ DY.Trace.at?_append tr e
  have hunregA : (!PQXDH.isRegisteredB Trace.nil "alice") = true := by
    unfold PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (tr := Trace.nil) (p := "alice") hunregA).2
  have hunregB : (!PQXDH.isRegisteredB t1 "bob") = true := by
    cases hb : (!PQXDH.isRegisteredB t1 "bob")
    · exfalso
      have heq : t2 = t1 := by
        unfold t2 PQXDH.registerIdentity PQXDH.guardTrace
        rw [DY.Traceful.run_bind, DY.Traceful.run_mk]
        simp [hb]
      have hl1 := t1_length
      have hl2 := t2_length
      rw [heq] at hl2
      omega
    · rfl
  have ht2 : t2 = registerIdentityTr t1 "bob" :=
    (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2
  have hat_t2_9 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]; unfold registerIdentityTr; dsimp only; rw [t1_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length])
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey (tr := t2) (b := "bob") (idH := 9) hat_t2_9).2
  have hle_t12 : t1 ≤ t2 := by
    rw [ht2]; unfold registerIdentityTr; dsimp only
    iterate 5 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle_t23 : t2 ≤ t3 := by
    rw [ht3]; unfold genSignedPrekeyTr; dsimp only
    iterate 6 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hat_t3_9 : t3.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) :=
    Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle_t23 hat_t2_9
  have ht4 : t4 = genPQPrekeyTr t3 "bob" ikB :=
    (Runs.genPQPrekey (tr := t3) (b := "bob") (idH := 9) hat_t3_9).2
  have hle_t34 : t3 ≤ t4 := by
    rw [ht4]; unfold genPQPrekeyTr; dsimp only
    iterate 6 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hat_t4_9 : t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) :=
    Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle_t34 hat_t3_9
  have hat_t4_1 : t4.at? 1 =
      some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some
      (DY.Trace.le_trans _ _ _ hle_t12 (DY.Trace.le_trans _ _ _ hle_t23 hle_t34)) ?_
    rw [ht1]; unfold registerIdentityTr; dsimp only
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    iterate 3 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hat_t4_4 : t4.at? 4 = some (StP "alice" { kind := .identity, sk := ikA }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some
      (DY.Trace.le_trans _ _ _ hle_t12 (DY.Trace.le_trans _ _ _ hle_t23 hle_t34)) ?_
    rw [ht1]; unfold registerIdentityTr; dsimp only
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hat_t4_6 : t4.at? 6 =
      some (EvP (.IdentityRegistered "bob" (dhPk ikB) (DY.Signature.vk ikB) true)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some
      (DY.Trace.le_trans _ _ _ hle_t23 hle_t34) ?_
    rw [ht2]; unfold registerIdentityTr; dsimp only; rw [t1_length]
    iterate 3 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length])
  have hat_t4_13 : t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle_t34 ?_
    rw [ht3]; unfold genSignedPrekeyTr; dsimp only; rw [t2_length]
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t2_length])
  have hat_t4_14 : t4.at? 14 = some (NetE (dhPk spkB)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle_t34 ?_
    rw [ht3]; unfold genSignedPrekeyTr; dsimp only; rw [t2_length]
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t2_length])
  have hat_t4_15 : t4.at? 15 =
      some (NetE (DY.Signature.sign ikB spkNonce (PQXDH.encodeEC (dhPk spkB)))) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle_t34 ?_
    rw [ht3]; unfold genSignedPrekeyTr; dsimp only; rw [t2_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t2_length])
  have hat_t4_19 : t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) := by
    rw [ht4]; unfold genPQPrekeyTr; dsimp only; rw [t3_length]
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t3_length])
  have hat_t4_20 : t4.at? 20 = some (NetE (kemPk pqskB)) := by
    rw [ht4]; unfold genPQPrekeyTr; dsimp only; rw [t3_length]
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t3_length])
  have hat_t4_21 : t4.at? 21 =
      some (NetE (DY.Signature.sign ikB pqNonce (PQXDH.encodeKEM (kemPk pqskB)))) := by
    rw [ht4]; unfold genPQPrekeyTr; dsimp only; rw [t3_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t3_length])
  have hlen1 : trR2_1.length = 24 := by
    simp only [trR2_1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have hlen2 : trR2_2.length = 33 := by
    simp only [trR2_2, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1]
  have hlen3 : trR2_3.length = 40 := by
    simp only [trR2_3, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2]
  have hle01 : t4 ≤ trR2_1 := by
    unfold trR2_1 compIkTr
    iterate 2 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle12 : trR2_1 ≤ trR2_2 := by
    unfold trR2_2 aliceTr aliceTrOpt; dsimp only
    iterate 9 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle23 : trR2_2 ≤ trR2_3 := by
    unfold trR2_3 encTr; dsimp only
    iterate 7 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle34 : trR2_3 ≤ trR2_4 := by
    unfold trR2_4; dsimp only
    iterate 9 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle45 : trR2_4 ≤ trR2_5 := by
    unfold trR2_5 compSpkTr
    iterate 2 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle03 : t4 ≤ trR2_3 := DY.Trace.le_trans _ _ _ hle01 (DY.Trace.le_trans _ _ _ hle12 hle23)
  have hv_var : ∀ sk : Bytes, ((dhPk sk).view? DY.X25519.Variant.SubF) = none := fun sk => by
    simp only [dhPk, DY.DiffieHellman.CanDH.dhPk]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
  have hlow_dhPk : ∀ sk : Bytes, TripleRatchet.x25519LowOrder (dhPk sk) = false := fun sk => by
    have hv_lit : ((dhPk sk).view? DY.Literal.Literal.SubF) = none := by
      simp only [dhPk, DY.DiffieHellman.CanDH.dhPk]
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
        ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
    simp only [TripleRatchet.x25519LowOrder, DY.X25519.normalizeX25519Key,
      hv_var, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have r1 : trR2_1.Reachable reachability := compIkTr_reach (idx := 9) t4_reach hat_t4_9
  have r2 : trR2_2.Reachable reachability :=
    reach_of_runs
      (Runs.aliceStart (idH := 4) (regB := 6) (h := bh1) (honest := true)
        (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle01 hat_t4_4)
        (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle01 hat_t4_6)
        (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle01 hat_t4_14)
        (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle01 hat_t4_15)
        (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle01 hat_t4_20)
        (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle01 hat_t4_21)
        (DY.Signature.verify_sign _ _ _) (DY.Signature.verify_sign _ _ _) rfl (hlow_dhPk spkB))
      (aliceStart_reachable r1)
  have hst_a0 : trR2_2.at? 32 = some (StT "alice" trR2_stA0) := by
    unfold trR2_2 aliceTr aliceTrOpt trR2_stA0 trR2_dhsA; dsimp only
    rw [hlen1]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen1])
  have hpq_enc : (((trR2_2.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend trR2_stA0.spqr (rnd (trR2_2.length + 1) 32)).2.1)).at? 35 =
      some (NetE trR2_key0) := by
    rw [hlen2]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen2])
  have r3 : trR2_3.Reachable reachability :=
    reach_of_runs
      (Runs.messageEncrypt (tr := trR2_2) (stH := 32) (pqH := 35) (st := trR2_stA0)
        (pq := trR2_key0) hst_a0 (by decide) hpq_enc)
      (messageEncrypt_reachable r2
        (hcur := by simp only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?, hst_a0, hlen2]; rfl))
  have hset : setRecvChain trR2_stB0'.recv trR2_cB' = [trR2_cB'] := by
    simp [setRecvChain, trR2_stB0', ratchetState, trR2_cB', trR2_cB, trR2_stB00,
      bobSt0, maxReceiverChains]
  have hrs :
      ratchetState
        (bobSt0 "alice" ikB spkB (dhPk ikA) trR2_keys
          (encSig trR2_stA0 trR2_coins0 trR2_key0 trR2_m0))
        (encSig trR2_stA0 trR2_coins0 trR2_key0 trR2_m0).ratchetKey
        (rnd trR2_3.length 32) = (trR2_stB0', trR2_cB) := by
    rw [hlen3]; rfl
  have hrecv : Spqr.spqrRecv trR2_stB0'.spqr trR2_pqm0 1 =
      some (recvSt (Spqr.spqrInit trR2_keys.pqr spqrB2A) trR2_pqm0, trR2_key0) :=
    spqrRecv_init_agree trR2_keys.pqr trR2_coins0 trR2_pqm0 .b2a
      (by
        simp only [trR2_pqm0, Spqr.spqrSend, DY.Literal.bytesToLiteral,
          DY.Literal.CanMkLiteral.bytesToLiteral]
        rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
          ({ st := trR2_stA0.spqr, coins := trR2_coins0 } : Spqr.SendMsg.SubF Bytes)])
  have hek : trR2_3.at? trR2_mh.ek = some (NetE trR2_out.ek) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle23 ?_
    change trR2_2.at? 27 = _
    unfold trR2_2 aliceTr aliceTrOpt; dsimp only
    iterate 5 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen1])
  have hct : trR2_3.at? trR2_mh.ct = some (NetE trR2_out.ct) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle23 ?_
    change trR2_2.at? 28 = _
    unfold trR2_2 aliceTr aliceTrOpt; dsimp only
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen1])
  have hcan : PQXDH.isCanonicalKey trR2_out.ek = true := by
    simp only [PQXDH.isCanonicalKey, trR2_out, aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt, hv_var]
    change (Option.isNone none && !TripleRatchet.x25519LowOrder
      (dhPk (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd trR2_1.length 32))) = true
    rw [hlow_dhPk]; rfl
  have hagree : PQXDH.bobAgreement ikB spkB pqskB none (dhPk ikA) trR2_out.ek trR2_out.ct =
      some trR2_keys := by
    unfold trR2_keys trR2_out aliceOut
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt
    dsimp only
    rw [hlen1]
    exact bobAgreement_honest ikA (rnd 24 32) ikB spkB pqskB (rnd 25 32)
  have hmsg : trR2_3.at? trR2_mh.msg =
      some (NetE (encMsg trR2_stA0 trR2_coins0 trR2_key0 trR2_m0)) := by
    change trR2_3.at? 39 = _
    unfold trR2_3 encTr; dsimp only; rw [hlen2]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen2])
  have hpq_bob : ((trR2_3.append (RndE 32)).append (NetE trR2_key0)).at? 35 =
      some (NetE trR2_key0) := by
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    unfold trR2_3 encTr; dsimp only; rw [hlen2]
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen2])
  have hruns : Runs (Composed.bobStart "bob" "alice" kh1 1 trR2_mh 35 1) trR2_3 48 trR2_4 := by
    have hbs := Runs.bobStart (kh := kh1) (keys := trR2_keys)
      (msg := encSig trR2_stA0 trR2_coins0 trR2_key0 trR2_m0)
      (t := encMsg trR2_stA0 trR2_coins0 trR2_key0 trR2_m0)
      (st' := trR2_stB0') (c := trR2_cB) (c' := trR2_cB') (seed := trR2_seedB0)
      (pq := trR2_key0) (m := trR2_m0)
      (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle03 hat_t4_9)
      (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle03 hat_t4_13)
      (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle03 hat_t4_19)
      rfl
      (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle03 hat_t4_1)
      hek hct hcan hagree hmsg (parse_encMsg _ _ _ _) rfl (hlow_dhPk trR2_dhsA) hrs rfl hrecv
      hpq_bob (mac_ok trR2_seedB0_eq rfl rfl) (dec_ok trR2_seedB0_eq) (stOut := trR2_stB1)
      (by rw [hset]; rfl)
    dsimp -failIfUnchanged only [Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOutOpt] at hbs
    have htr1_len : ((trR2_3.append (RndE 32)).append (NetE trR2_key0)).length = 42 := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3]
    rw [htr1_len] at hbs
    have hskip : ∀ (tr : ExecTrace) (n : Nat),
        skipTr tr (trR2_stB0'.sessionInfo "bob")
          (encSig trR2_stA0 trR2_coins0 trR2_key0 trR2_m0).ratchetKey trR2_cB n
          (encSig trR2_stA0 trR2_coins0 trR2_key0 trR2_m0).counter = tr :=
      fun tr _ => by
        change ((Pure.pure () : DY.Traceful Unit).run tr).2.val = tr
        rw [DY.Traceful.run_pure]
    rw [hskip] at hbs
    let tr5 := (((((trR2_3.append (RndE 32)).append (NetE trR2_key0)).append
      (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
        (kemPk pqskB) none trR2_out.ek trR2_out.ct trR2_keys))).append
        (EvT (.DHRatchet "bob" "alice" (dhPk trR2_dhsA) (dhPk trR2_dhsB1)))).append
        (EvT (.HonestDH (trR2_stB0'.sessionInfo "bob") trR2_dhsB1 0))).append
        (EvC (.HandshakeSession (trR2_stB0'.sessionInfo "bob") 42))
    have htr5_len : tr5.length = 46 := by
      simp [tr5, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen3]
    change Runs (Composed.bobStart "bob" "alice" kh1 1 trR2_mh 35 1) trR2_3 (tr5.length + 2)
      (((tr5.append (EvT (.Received "bob" "alice" (dhPk trR2_dhsA) 0 trR2_m0))).append
        (EvT (.MessageKey (trR2_stB0'.sessionInfo "bob") .receiver trR2_seedB0
          trR2_key0 0 2 (tr5.length + 0 + 2)))).append
        (StT "bob" trR2_stB1)) at hbs
    rw [htr5_len] at hbs
    exact hbs
  have r4 : trR2_4.Reachable reachability := reach_of_runs hruns (bobStart_reachable r3)
  have r5 : trR2_5.Reachable reachability :=
    compSpkTr_reach (idx := 13) r4
      (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some
        (DY.Trace.le_trans _ _ _ hle03 hle34) hat_t4_13)
  exact compPqTr_reach (idx := 19) r5
    (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some
      (DY.Trace.le_trans _ _ _ hle03 (DY.Trace.le_trans _ _ _ hle34 hle45))
      hat_t4_19)

theorem trR2_bobDone :
    trR2.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none trR2_out.ek trR2_out.ct trR2_keys) 42 := by
  have hlen1 : trR2_1.length = 24 := by
    simp only [trR2_1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have hlen2 : trR2_2.length = 33 := by
    simp only [trR2_2, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1]
  have hlen3 : trR2_3.length = 40 := by
    simp only [trR2_3, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2]
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  unfold trR2 compPqTr trR2_5 compSpkTr trR2_4; dsimp only
  iterate 10 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
  have hl : ((trR2_3.append (RndE 32)).append (NetE trR2_key0)).length = 42 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3]
  exact hl ▸ DY.Trace.at?_append _ _

theorem trR2_compIK :
    trR2.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 22 := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  have hle : (t4.append (EvP (.CompromisedIK "bob" (dhPk ikB)))) ≤ trR2 := by
    unfold trR2 compPqTr trR2_5 compSpkTr trR2_4 trR2_3 encTr trR2_2 aliceTr aliceTrOpt trR2_1
      compIkTr
    dsimp only
    iterate 30 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  exact Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle
    (t4_length ▸ DY.Trace.at?_append t4 (EvP (.CompromisedIK "bob" (dhPk ikB))))

theorem trR2_compSPK :
    trR2.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 49 := by
  have hlen4 : trR2_4.length = 49 := by
    simp only [trR2_4, trR2_3, encTr, trR2_2, aliceTr, aliceTrOpt, trR2_1, compIkTr,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  unfold trR2 compPqTr trR2_5 compSpkTr
  iterate 3 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
  exact hlen4 ▸ DY.Trace.at?_append trR2_4 (EvP (.CompromisedSPK "bob" (dhPk spkB)))

theorem trR2_compPQ :
    trR2.EventLoggedAt (PQXDHEvent.CompromisedPQSPK "bob" (kemPk pqskB)) 51 := by
  have hlen5 : trR2_5.length = 51 := by
    simp only [trR2_5, compSpkTr, trR2_4, trR2_3, encTr, trR2_2, aliceTr, aliceTrOpt, trR2_1,
      compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      t4_length]
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  unfold trR2 compPqTr
  refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
  exact hlen5 ▸ DY.Trace.at?_append trR2_5 (EvP (.CompromisedPQSPK "bob" (kemPk pqskB)))

theorem trR2_compromise_indices : evIdx trR2 isCompromise = [22, 49, 51] := by
  have hstep_other : ∀ {E : Type} [ExecTraceTypes.Has E]
      (_ : ∀ x : E, (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
      (tr : ExecTrace) (e : E),
      evIdx (tr.append e) isCompromise = evIdx tr isCompromise := by
    intro E _ hnone tr e
    have hlen : (tr.append e).length = tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hlast : (tr.append e).getEventAt PQXDHEvent tr.length = none := by
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      have hat : ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) =
          none := by
        simp only [DY.Trace.at?, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.at_eq_2, hnone e, dite_eq_ite, ite_self]
      rw [hat]
    simp only [evIdx, hlen, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
      hlast, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    refine List.filter_congr fun i hi => ?_
    have hi' : i < tr.length := List.mem_range.mp hi
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr e hi']
  have hstep_same : ∀ (tr : ExecTrace) (ev : PQXDHEvent),
      evIdx (tr.append (EvP ev)) isCompromise =
        evIdx tr isCompromise ++ (if isCompromise ev then [tr.length] else []) := by
    intro tr ev
    have hlen : (tr.append (EvP ev)).length = tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hlast : (tr.append (EvP ev)).getEventAt PQXDHEvent tr.length = some ev := by
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?_append tr (EvP ev)]
    simp only [evIdx, hlen, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
      hlast]
    congr 1
    refine List.filter_congr fun i hi => ?_
    have hi' : i < tr.length := List.mem_range.mp hi
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr (EvP ev) hi']
  have ht4_idx : evIdx t4 isCompromise = [] := by
    rcases t5_noCompromise with ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
    have hle45 : t4 ≤ t5 := by
      unfold t5 aliceTr aliceTrOpt; dsimp only
      iterate 9 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
      exact DY.Trace.le_refl _
    refine List.eq_nil_iff_forall_not_mem.mpr fun i hi => ?_
    simp only [evIdx, List.mem_filter, List.mem_range] at hi
    rcases hi with ⟨_, hget⟩
    cases he : t4.getEventAt PQXDHEvent i with
    | none => simp [he] at hget
    | some val =>
      simp only [he] at hget
      have hlog5 : t5.EventLogged val :=
        ⟨i, Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_mono hle45
          ((DY.Trace.EventLoggedAt_eq_getEventAt val i t4).mpr he)⟩
      cases val <;> simp [isCompromise] at hget
      · exact hc1 _ _ hlog5
      · exact hc2 _ _ hlog5
      · exact hc3 _ _ hlog5
      · exact hc4 _ _ hlog5
      · exact hc5 hlog5
      · exact hc6 hlog5
  have h1 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.NetEntry) (fun _ => rfl)
  have h2 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.RndEntry) (fun _ => rfl)
  have h3 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.TREntry) (fun _ => rfl)
  have h4 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.CEntry) (fun _ => rfl)
  have h5 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) (fun _ => rfl)
  have hlen4 : trR2_4.length = 49 := by
    simp only [trR2_4, trR2_3, encTr, trR2_2, aliceTr, aliceTrOpt, trR2_1, compIkTr,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have hlen5 : trR2_5.length = 51 := by
    simp only [trR2_5, compSpkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen4]
  have hidx1 : evIdx trR2_1 isCompromise = [22] := by
    simp only [trR2_1, compIkTr, hstep_same, h1, isCompromise, ↓reduceIte, ht4_idx,
      List.nil_append, t4_length]
  have hidx2 : evIdx trR2_2 isCompromise = [22] := by
    simp only [trR2_2, aliceTr, aliceTrOpt, hstep_same, h1, h2, h3, h4, h5, isCompromise,
      Bool.false_eq_true, ↓reduceIte, List.append_nil, hidx1]
  have hidx3 : evIdx trR2_3 isCompromise = [22] := by
    simp only [trR2_3, encTr, h1, h2, h3, h5, hidx2]
  have hidx4 : evIdx trR2_4 isCompromise = [22] := by
    simp only [trR2_4, hstep_same, h1, h2, h3, h4, h5, isCompromise, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, hidx3]
  have hidx5 : evIdx trR2_5 isCompromise = [22, 49] := by
    simp only [trR2_5, compSpkTr, hstep_same, h1, isCompromise, ↓reduceIte, hidx4, hlen4]; rfl
  simp only [trR2, compPqTr, hstep_same, h1, isCompromise, ↓reduceIte, hidx5, hlen5]; rfl

theorem trR2_trExposure_indices : trEvIdx trR2 isAnyTRExposure = [] := by
  have hat_here : ∀ {E : Type} [ExecTraceTypes.Has E] {i : Nat} (tr : ExecTrace) (e : E),
      tr.length = i → (tr.append e).at? i = some e :=
    fun tr e hi => hi ▸ DY.Trace.at?_append tr e
  have hnil : trEvIdx Trace.nil isAnyTRExposure = [] := by
    simp only [trEvIdx, Symbolic.DYBridge.DY.Trace.length_eq_1, List.range_zero, List.filter_nil]
  have hstep_other : ∀ {E : Type} [ExecTraceTypes.Has E]
      (_ : ∀ x : E, (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT TREvent)) = none)
      (tr : ExecTrace) (e : E),
      trEvIdx (tr.append e) isAnyTRExposure = trEvIdx tr isAnyTRExposure := by
    intro E _ hnone tr e
    have hlen : (tr.append e).length = tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hlast : (tr.append e).getEventAt TREvent tr.length = none := by
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      have hat : ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT TREvent)) =
          none := by
        simp only [DY.Trace.at?, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.at_eq_2, hnone e, dite_eq_ite, ite_self]
      rw [hat]
    simp only [trEvIdx, hlen, List.range_succ, List.filter_append, List.filter_cons,
      List.filter_nil, hlast, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    refine List.filter_congr fun i hi => ?_
    have hi' : i < tr.length := List.mem_range.mp hi
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr e hi']
  have hstep_same : ∀ (tr : ExecTrace) (ev : TREvent),
      trEvIdx (tr.append (EvT ev)) isAnyTRExposure =
        trEvIdx tr isAnyTRExposure ++ (if isAnyTRExposure ev then [tr.length] else []) := by
    intro tr ev
    have hlen : (tr.append (EvT ev)).length = tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hlast : (tr.append (EvT ev)).getEventAt TREvent tr.length = some ev := by
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?_append tr (EvT ev)]
    simp only [trEvIdx, hlen, List.range_succ, List.filter_append, List.filter_cons,
      List.filter_nil, hlast]
    congr 1
    refine List.filter_congr fun i hi => ?_
    have hi' : i < tr.length := List.mem_range.mp hi
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr (EvT ev) hi']
  have hunregA : (!PQXDH.isRegisteredB Trace.nil "alice") = true := by
    unfold PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (tr := Trace.nil) (p := "alice") hunregA).2
  have hunregB : (!PQXDH.isRegisteredB t1 "bob") = true := by
    cases hb : (!PQXDH.isRegisteredB t1 "bob")
    · exfalso
      have heq : t2 = t1 := by
        unfold t2 PQXDH.registerIdentity PQXDH.guardTrace
        rw [DY.Traceful.run_bind, DY.Traceful.run_mk]; simp [hb]
      have hl1 := t1_length; have hl2 := t2_length; rw [heq] at hl2; omega
    · rfl
  have ht2 : t2 = registerIdentityTr t1 "bob" :=
    (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2
  have hat_t2_9 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]; unfold registerIdentityTr; dsimp only; rw [t1_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length])
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey (tr := t2) (b := "bob") (idH := 9) hat_t2_9).2
  have hat_t3_9 : t3.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht3]; unfold genSignedPrekeyTr; dsimp only
    iterate 6 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_t2_9
  have ht4 : t4 = genPQPrekeyTr t3 "bob" ikB :=
    (Runs.genPQPrekey (tr := t3) (b := "bob") (idH := 9) hat_t3_9).2
  have h1 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.NetEntry) (fun _ => rfl)
  have h2 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.RndEntry) (fun _ => rfl)
  have h3 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.PQXDHEntry) (fun _ => rfl)
  have h4 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.CEntry) (fun _ => rfl)
  have h5 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) (fun _ => rfl)
  have h6 := hstep_other (E := Symbolic.Swarm.COMPOSED.CompTrace.PQXDHStEntry) (fun _ => rfl)
  have ht4_idx : trEvIdx t4 isAnyTRExposure = [] := by
    rw [ht4, ht3, ht2, ht1]
    simp only [genPQPrekeyTr, genSignedPrekeyTr, registerIdentityTr, h1, h2, h3, h6, hnil]
  simp only [trR2, compPqTr, trR2_5, compSpkTr, trR2_4, trR2_3, encTr, trR2_2, aliceTr,
    aliceTrOpt, trR2_1, compIkTr, hstep_same, h1, h2, h3, h4, h5, isAnyTRExposure,
    Bool.false_eq_true, ↓reduceIte, List.append_nil, ht4_idx]

theorem trR2_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trR2 trR2_keys k :=
  not_sessionStateExposed_of_no_trExposure trR2_trExposure_indices _ k

theorem trR2_knows_block {k : Bytes} (hk : IsHandshakeBlock trR2_keys k) :
    k.AttackerKnows trR2 := by
  have hat_here : ∀ {E : Type} [ExecTraceTypes.Has E] {i : Nat} (tr : ExecTrace) (e : E),
      tr.length = i → (tr.append e).at? i = some e :=
    fun tr e hi => hi ▸ DY.Trace.at?_append tr e
  have hunregA : (!PQXDH.isRegisteredB Trace.nil "alice") = true := by
    unfold PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (tr := Trace.nil) (p := "alice") hunregA).2
  have hlen1 : trR2_1.length = 24 := by
    simp only [trR2_1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have hlen4 : trR2_4.length = 49 := by
    simp only [trR2_4, trR2_3, encTr, trR2_2, aliceTr, aliceTrOpt,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1]
  have hlen5 : trR2_5.length = 51 := by
    simp only [trR2_5, compSpkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen4]
  have hle_t1_t4 : t1 ≤ t4 :=
    DY.Trace.le_trans _ _ _ ((PQXDH.registerIdentity "bob").run t1).2.property
      (DY.Trace.le_trans _ _ _ ((PQXDH.genSignedPrekey "bob" 9).run t2).2.property
        ((PQXDH.genPQPrekey "bob" 9).run t3).2.property)
  have hle16 : trR2_1 ≤ trR2 := by
    unfold trR2 compPqTr trR2_5 compSpkTr trR2_4 trR2_3 encTr trR2_2 aliceTr aliceTrOpt
    dsimp only
    iterate 29 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle26 : trR2_2 ≤ trR2 := by
    unfold trR2 compPqTr trR2_5 compSpkTr trR2_4 trR2_3 encTr
    dsimp only
    iterate 20 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have hle06 : t4 ≤ trR2 := by
    refine DY.Trace.le_trans _ _ _ ?_ hle16
    unfold trR2_1 compIkTr
    iterate 2 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.le_refl _
  have h2 : trR2.at? 2 = some (NetE (dhPk ikA)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some
      (DY.Trace.le_trans _ _ _ hle_t1_t4 hle06) ?_
    rw [ht1]; unfold registerIdentityTr; dsimp only
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h27 : trR2.at? 27 = some (NetE trR2_out.ek) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle26 ?_
    unfold trR2_2 aliceTr aliceTrOpt; dsimp only
    iterate 5 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen1])
  have h23 : trR2.at? 23 = some (NetE ikB) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle16 ?_
    unfold trR2_1 compIkTr
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t4_length])
  have h50 : trR2.at? 50 = some (NetE spkB) := by
    unfold trR2 compPqTr
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    unfold trR2_5 compSpkTr
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen4])
  have h52 : trR2.at? 52 = some (NetE pqskB) := by
    unfold trR2 compPqTr
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen5])
  have h28 : trR2.at? 28 = some (NetE trR2_out.ct) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle26 ?_
    unfold trR2_2 aliceTr aliceTrOpt; dsimp only
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        hlen1])
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net h2) (ak_net h27) (ak_net h23) (ak_net h50) (ak_net h52) trivial (ak_net h28) hk

/-! ## Singleton event-index lemmas -/

theorem not_gap_lt_of_singleton {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {g i j k : Nat} (hj : tr.EventLoggedAt e j) (hidx : evIdx tr p = [k])
    (hp : p e = true) (hg : i - k ≤ g) : ¬ j + g < i := by
  have hm := mem_evIdx hj hp
  rw [hidx, List.mem_singleton] at hm
  omega

theorem not_atOrAfter_of_singleton {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {i j k : Nat} (hj : tr.EventLoggedAt e j) (hidx : evIdx tr p = [k])
    (hp : p e = true) (hki : k < i) : ¬ i ≤ j := by
  have hm := mem_evIdx hj hp
  rw [hidx, List.mem_singleton] at hm
  omega

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHSecrecyTraces
