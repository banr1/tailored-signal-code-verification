/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepRatchetDHAtPureA
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrHonestPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSendBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# DH-Ratchet Single-Explanation Receive Step

Proves non-collision disjunction and decrypt-witness lemmas at a fixed explanation `(g, ms)`
for the DH-ratchet whisper receive branch.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir findRecvChain chainKeyAt kdfCk computeMac
  messageVersion createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (aesCbcDecryptSymbol ExternCryptoLawsHold canonicalVariation)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3 Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec (at?_append_of_lt)
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry StEntry
open Symbolic.Swarm.CREF.TR.G1 (TermShapeId)

section AliceCoinsLen32
open Symbolic.Swarm.CREF.XplSteps
theorem noAliceDone_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (r src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), NoAliceDone (DY.Libsignal.TripleRatchet.logSkippedKeys s pk r src ck n k)
  | 0, _, _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | k + 1, ck, n => by
    rw [DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact noAliceDone_bind (noAliceDone_logEvent_tr _) fun _ => noAliceDone_logSkippedKeys s pk r src k _ _

theorem noAliceDone_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat) (st : TRState) :
    NoAliceDone (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact noAliceDone_bind (noAliceDone_logEvent_tr _) fun _ => noAliceDone_storeTR _ _

local macro "nad_step_1" : tactic =>
  `(tactic| first
    | with_reducible refine noAliceDone_bind ?_ fun _ => ?_
    | with_reducible exact noAliceDone_logEvent_tr _
    | with_reducible refine noAliceDone_logEvent_pq _ ?_
    | with_reducible exact noAliceDone_logEvent_c _
    | with_reducible exact noAliceDone_storeTR _ _
    | with_reducible exact noAliceDone_storePQ _ _)

local macro "nad_step_2" : tactic =>
  `(tactic| first
    | with_reducible exact noAliceDone_logSkippedKeys _ _ _ _ _ _ _
    | with_reducible exact noAliceDone_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    | with_reducible exact noAliceDone_of_quiet (xquiet_bobHandshake _ _ _ _ _ _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_receiveSignalMsg _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_ensureReceiverChain _ _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_verifyMacAndDecrypt _ _ _ _))

local macro "nad_step_3" : tactic =>
  `(tactic| first
    | with_reducible exact noAliceDone_of_quiet (xquiet_genRand _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_sendMessage _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_receiveMessage _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_getLocalState _ _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_getEntry _)))

local macro "nad_step_4" : tactic =>
  `(tactic| first
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_guard _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix xfix_traceLength)
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_guardTrace _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix xfix_failure)
    | split)

local macro "nad_step" : tactic =>
  `(tactic| first | nad_step_1 | nad_step_2 | nad_step_3 | nad_step_4)

theorem noAliceDone_setup (a b : Participant) (w : Bool) :
    NoAliceDone (Move.setup a b w).act := by
  dsimp only [Move.act]
  unfold setupAct
    DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.genSignedPrekey
    DY.Libsignal.PQXDH.genPQPrekey DY.Libsignal.PQXDH.genOneTimePrekey
  repeat' nad_step
  all_goals rfl

private theorem noAliceDone_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (r : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32) :
    NoAliceDone (DY.Libsignal.Composed.bobStart b a kh r mh pq sp) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  dsimp only
  repeat' nad_step
  all_goals rfl

private theorem noAliceDone_messageEncrypt (me : Participant) (si cl pq : Nat) :
    NoAliceDone (DY.Libsignal.TripleRatchet.messageEncrypt me si cl pq) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  repeat' nad_step

private theorem noAliceDone_messageDecrypt (me : Participant) (si mi pq : Nat) (sp : UInt32) :
    NoAliceDone (DY.Libsignal.TripleRatchet.messageDecrypt me si mi pq sp) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  repeat' nad_step

private theorem noAliceDone_messageDecryptSkipped (me : Participant) (si mi k pq : Nat) (sp : UInt32) :
    NoAliceDone (DY.Libsignal.TripleRatchet.messageDecryptSkipped me si mi k pq sp) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  repeat' nad_step

theorem noAliceDone_nonAlice {m : Move}
    (hnotA : ∀ a b i r h s, m ≠ .aliceStart a b i r h s) :
    NoAliceDone m.act := by
  cases m with
  | setup a b w => exact noAliceDone_setup a b w
  | aliceStart a b i r h s => exact absurd rfl (hnotA a b i r h s)
  | bobStart b a kh r mh pq sp sh =>
    exact noAliceDone_bind (noAliceDone_bobStart b a kh r mh pq sp) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | encrypt me si cl pq wr =>
    exact noAliceDone_bind (noAliceDone_messageEncrypt me si cl pq) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | encryptAbort me si =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
    repeat' nad_step
  | encryptFail me si cl =>
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix xfix_traceLength)) fun _ =>
      noAliceDone_bind (noAliceDone_messageEncrypt me si cl _) fun _ =>
        noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | decrypt me si mi pq sp wr =>
    exact noAliceDone_bind (noAliceDone_messageDecrypt me si mi pq sp) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | decryptSkipped me si mi k pq sp wr =>
    exact noAliceDone_bind (noAliceDone_messageDecryptSkipped me si mi k pq sp) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | compromiseIK p si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromiseIK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | compromiseSPK b si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromiseSPK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | compromiseOPK b si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromiseOPK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | compromisePQSPK b si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromisePQSPK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | exposeKey me si k =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeKey
    repeat' nad_step
  | exposeSpqr me si =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeSpqr
    repeat' nad_step
  | exposeSkipped k =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeSkipped
    repeat' nad_step
  | attackerSend msg =>
    dsimp only [Move.act]
    repeat' nad_step
  | brkDH =>
    exact noAliceDone_logEvent_pq .BrokenDH rfl
  | brkKEM =>
    exact noAliceDone_logEvent_pq .BrokenKEM rfl
  | reject dr =>
    dsimp only [Move.act]
    repeat' nad_step

theorem pqEv_at?_append_other {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i = tr.length)
    (he : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none) :
    ((tr.append e).at? i :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
  subst hi; rw [Symbolic.Swarm.CREF.at?_append_length, he]

theorem aliceStart_aliceDone_step {tr : ExecTrace}
    {a b : Participant} {idH regB : Nat} {bh : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat}
    (hanc : (Move.aliceStart a b idH regB bh shown).LogsSessionCompletion tr)
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hi : tr.length ≤ i)
    (hev : ((Move.aliceStart a b idH regB bh shown).next tr).getEventAt
      DY.Libsignal.PQXDH.PQXDHEvent i = some ev)
    (had : DY.Libsignal.Composed.Refinement.isAliceDone ev = true) :
    i = tr.length + 5 ∧
      ⟨.rng, [randTerm (tr.length + 1) 32], .kyberCoin 0, none⟩ ∈
        (Move.aliceStart a b idH regB bh shown).vis tr := by
  let m := Move.aliceStart a b idH regB bh shown
  let Inv : ExecTrace → Prop := fun tr' =>
    NoAliceDoneFrom tr.length tr' ∨
      ∃ (hs : DY.Libsignal.PQXDH.AliceHandshakeOut) (dhsA : DY.Bytes) (stA : TRState),
        tr' = ((((((((tr.append (Symbolic.Swarm.COMPOSED.CompInv.RndE 32)).append
          (Symbolic.Swarm.COMPOSED.CompInv.RndE 32)).append
          (Symbolic.Swarm.COMPOSED.CompInv.RndE 32)).append
          (Symbolic.Swarm.COMPOSED.CompInv.NetE hs.ek)).append
          (Symbolic.Swarm.COMPOSED.CompInv.NetE hs.ct)).append
          (Symbolic.Swarm.COMPOSED.CompInv.EvE
            (.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))).append
          (Symbolic.Swarm.COMPOSED.CompInv.TREvE (.InitSession a b (DY.DiffieHellman.dhPk dhsA) hs.spk))).append
          (Symbolic.Swarm.COMPOSED.CompInv.CEvE (.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append
          (Symbolic.Swarm.COMPOSED.CompInv.TRStE a stA)
  have hshape : Inv (m.next tr) := by
    change Inv (((DY.Libsignal.Composed.aliceStart a b idH regB bh >>= fun _ => Pure.pure ()).run tr).2.val)
    rw [xrun_bind_unit]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine Symbolic.Swarm.COMPOSED.CompPresPQXDH.bind_aliceHandshake_at a b idH regB bh tr
      (Or.inl (by
        have hq := noAliceDone_of_quiet (xquiet_of_fix (xfix_pure ())) tr
        rwa [Symbolic.DYBridge.DY.Traceful.run_eq_1] at hq))
      (Or.inl (by
        have hq := noAliceDone_of_quiet (xquiet_genRand 32) tr
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
          Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1] at hq
        exact hq))
      fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ =>
        let hs := Symbolic.Swarm.COMPOSED.CompPresPQXDH.aliceOut tr ikA ikBPk spkPk pqPk opk
        let dhsA := randTerm (tr.length + 2) 32
        let stA : TRState :=
          { peer := b, myIk := PQXDH.serializedIk hs.ikA, peerIk := PQXDH.serializedIk hs.ikB,
            rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA,
            cks := (createChain hs.keys.rk hs.spk dhsA).2, ns := 0, pn := 0,
            sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
            initiator := true, rIdx := 1,
            recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
            spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
        Or.inr ⟨hs, dhsA, stA, by
          simp only [DY.Libsignal.TripleRatchet.traceLength,
            Symbolic.DYBridge.DY.Random.genRand_eq_1,
            Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
            Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
            Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
            Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
            Symbolic.DYBridge.DY.appendEntry_eq_1,
            DY.Traceful.run_bind,
            DY.Traceful.run_pure,
            DY.Traceful.run_mk,
            Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Nat.add_assoc]; rfl⟩
  rcases hshape with hno | ⟨hs, dhsA, stA, htr'⟩
  · rw [hno.elim hi hev] at had; cases had
  · have hlen35 : 35 ≤ (m.vis tr).length := by
      by_contra hlt35
      have hneff := noSessionEffect_aliceStart_short' hanc (Nat.lt_of_not_le hlt35)
      have hmem : i ∈ newIndices tr (m.next tr) := xpl_mem_newIndices hi (xlt_of_getEventAt hev)
      have hn := (hneff i hmem).2.1
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
      rcases hat : (((Move.aliceStart a b idH regB bh shown).next tr).at? i :
          Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | e
      · rw [hat] at hev; cases hev
      · rw [hat] at hev
        cases hev
        have hf := Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_pred_eq_false hn hat
          (p := DY.Libsignal.Composed.Refinement.isAliceDone)
        rw [had] at hf; cases hf
    have hex : exposures tr (m.next tr) = [] :=
      exposures_nil_of_not_leakKind' rfl (fun h => nomatch h)
    have hvis_eq : m.vis tr = (aliceVis tr (m.next tr) bh).take shown := by
      rw [xpl_vis_eq, hex, List.append_nil]; rfl
    have hshown : 35 ≤ shown := by
      rw [hvis_eq, List.length_take] at hlen35; omega
    have hnr : newRandoms tr (m.next tr) =
        [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32),
         (randTerm (tr.length + 2) 32, 32)] := by
      rw [htr']
      have h0 : tr.length ≤ tr.length := Nat.le_refl _
      rw [Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_rnd (by simp only [Symbolic.Swarm.CREF.length_append']; omega),
          Symbolic.Swarm.CREF.newRandoms_append_rnd (by simp only [Symbolic.Swarm.CREF.length_append']; omega),
          Symbolic.Swarm.CREF.newRandoms_append_rnd h0,
          Symbolic.Swarm.CREF.newRandoms_self]
      simp only [Symbolic.Swarm.CREF.length_append', List.nil_append, List.cons_append, Nat.add_assoc]
    have hi_eq : i = tr.length + 5 := by
      by_contra hne
      have hnone : ((m.next tr).at? i :
          Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
        rw [htr']
        rcases Nat.lt_or_ge i (tr.length + 9) with hlt9 | hge9
        · have : i = tr.length ∨ i = tr.length + 1 ∨ i = tr.length + 2 ∨
              i = tr.length + 3 ∨ i = tr.length + 4 ∨ i = tr.length + 6 ∨
              i = tr.length + 7 ∨ i = tr.length + 8 := by omega
          rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            · repeat (rw [Symbolic.Swarm.COMPOSED.CompPresPQXDH.at?_append_of_lt _ _
                (by simp only [Symbolic.Swarm.CREF.length_append']; omega)])
              exact pqEv_at?_append_other _ _
                (by simp only [Symbolic.Swarm.CREF.length_append']; try omega) rfl
        · exact (xnone_of_ge (by simp only [Symbolic.Swarm.CREF.length_append']; omega)).2.1
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev; rw [hnone] at hev; cases hev
    refine ⟨hi_eq, ?_⟩
    rw [hvis_eq]
    unfold aliceVis
    rw [hnr]
    dsimp only [List.map, aliceDraws, List.take]
    rw [List.take_of_length_le (by simp [kyberCoinEntries]; omega)]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
    unfold kyberCoinEntries
    exact List.mem_map.mpr ⟨0, by simp, rfl⟩

theorem movesAnchored_snoc_at {ms : List Move} {m : Move} {tr : ExecTrace}
    (h : MovesAnchored (ms ++ [m]) tr) :
    MovesAnchored ms tr ∧ m.LogsSessionCompletion (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact ⟨trivial, h.1⟩
  | cons m₀ ms ih =>
    obtain ⟨h₀, hrest⟩ := h
    obtain ⟨hms, hm⟩ := ih hrest
    exact ⟨⟨h₀, hms⟩, hm⟩

theorem aliceDone_kyberCoin0_mem_runMoves
    (tr₀ : ExecTrace) (hno₀ : NoAliceDoneFrom 0 tr₀)
    (ms : List Move) (hanc : MovesAnchored ms tr₀)
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hev : (runMoves ms tr₀).1.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev)
    (had : DY.Libsignal.Composed.Refinement.isAliceDone ev = true) :
    ∃ t, i = t + 5 ∧
      ⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ ∈ (runMoves ms tr₀).2 := by
  induction ms using List.reverseRecOn generalizing i ev with
  | nil =>
    dsimp only [runMoves] at hev
    rw [hno₀.elim (Nat.zero_le _) hev] at had; cases had
  | append_singleton ms₀ m ih =>
    obtain ⟨hanc₀, hm_anc⟩ := movesAnchored_snoc_at hanc
    have hfst : (runMoves (ms₀ ++ [m]) tr₀).1 = m.next (runMoves ms₀ tr₀).1 := by
      rw [Symbolic.Swarm.CREF.b5_runMoves_append_fst]; rfl
    have hsnd : (runMoves (ms₀ ++ [m]) tr₀).2 =
        (runMoves ms₀ tr₀).2 ++ m.vis (runMoves ms₀ tr₀).1 := by
      rw [Symbolic.Swarm.CREF.b5_runMoves_append_snd]
      dsimp only [runMoves]
      rw [List.append_nil]
    rw [hfst] at hev
    by_cases hlt : i < (runMoves ms₀ tr₀).1.length
    · have hev₀ : (runMoves ms₀ tr₀).1.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev ⊢
        rwa [← xat?_le_eq (xrun_le m.act (runMoves ms₀ tr₀).1) hlt]
      obtain ⟨t, rfl, hmem⟩ := ih hanc₀ hev₀ had
      exact ⟨t, rfl, hsnd ▸ List.mem_append_left _ hmem⟩
    · have hge : (runMoves ms₀ tr₀).1.length ≤ i := Nat.le_of_not_lt hlt
      by_cases hmA : ∃ a b idH regB bh shown, m = .aliceStart a b idH regB bh shown
      · obtain ⟨a, b, idH, regB, bh, shown, rfl⟩ := hmA
        obtain ⟨hi_eq, hmem⟩ := aliceStart_aliceDone_step hm_anc hge hev had
        exact ⟨(runMoves ms₀ tr₀).1.length, hi_eq, hsnd ▸ List.mem_append_right _ hmem⟩
      · have hno := noAliceDone_nonAlice
          (fun a b idH regB bh shown heq => hmA ⟨a, b, idH, regB, bh, shown, heq⟩)
          (runMoves ms₀ tr₀).1
        rw [hno.elim hge hev] at had; cases had

theorem noAliceDoneFrom_next {m : Move} (hm : NoAliceDone m.act) (tr : ExecTrace) :
    NoAliceDoneFrom tr.length (m.next tr) :=
  hm tr

theorem noAliceDoneFrom_setupTrace (r₀ : ProtocolSetup) :
    NoAliceDoneFrom 0 (setupTrace r₀) := by
  rw [← setupMove_next_nil, ← Symbolic.DYBridge.DY.Trace.length_eq_1]
  exact noAliceDoneFrom_next (noAliceDone_setup r₀.alice r₀.bob r₀.withOpk) DY.Trace.nil

theorem aliceDone_kyberCoin0_mem_runVis
    (r₀ : ProtocolSetup) (ms : List Move)
    (hanc : MovesAnchored ms (setupTrace r₀))
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hev : (runTraceMoves r₀ ms).getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev)
    (had : DY.Libsignal.Composed.Refinement.isAliceDone ev = true) :
    ∃ t, i = t + 5 ∧
      ⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ ∈ runVis r₀ ms := by
  rw [Symbolic.Swarm.CREF.b5_runTrace_eq] at hev
  obtain ⟨t, ht, hmem⟩ :=
    aliceDone_kyberCoin0_mem_runMoves (setupTrace r₀) (noAliceDoneFrom_setupTrace r₀) ms hanc hev had
  rw [Symbolic.Swarm.CREF.b5_runVis_eq]
  exact ⟨t, ht, List.mem_append_right _ hmem⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hxy hrest ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.Mem.head _, hxy⟩
    · obtain ⟨x, hx, hr⟩ := ih hy'
      exact ⟨x, List.Mem.tail _ hx, hr⟩

theorem aliceSlot_sigma_len32_of_explains
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    {who : List Participant} {ok : Nat → Bool}
    (g : Ghost) (ms : List Move) {τ₁ : List MachineEvent}
    (hEx : ExplainsMoves interpretation r₀ S who ok g ms τ₁) :
    ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot (runTraceMoves r₀ ms) t →
      (g.σ (t + 1) 32).length = 32 := by
  intro t hSlot
  obtain ⟨_, _, _, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, _, _, hevA⟩ := hSlot
  have hev : (runTraceMoves r₀ ms).getEventAt DY.Libsignal.PQXDH.PQXDHEvent (t + 5) =
      some (.AliceDone a b ikA ikB spk pqpk opk ek ct keys) := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hevA
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [hevA]
  obtain ⟨t', ht_eq, hmem⟩ :=
    aliceDone_kyberCoin0_mem_runVis r₀ ms hEx.1.2.1.2.2.1.2.1 hev rfl
  have ht : t' = t := by omega
  subst ht
  obtain ⟨e, _, hmatch⟩ := forall₂_mem_right hEx.1.2.2.2.2.2 hmem
  obtain ⟨_, _, t₀, ht₀_eq, hlen32, _⟩ := hmatch
  injection ht₀_eq with ht₀_hd
  subst ht₀_hd
  rwa [gamma_randTerm32_at] at hlen32

end AliceCoinsLen32

/-- On a non-colliding DH-ratchet receive representation under `ExplainsMoves` and
`G1cAttackerBuiltSeedExcl'`, the message MAC is either authentic or derived from an
attacker-known `RkSwap` seed. -/
theorem recv_mac_authentic_or_rkSwap_seed_known_of_not_collision_explains'
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) {who : List Participant} {ok : Nat → Bool}
    (g : Ghost) (ms : List Move) {τ₁ : List MachineEvent}
    (b ptext : HwBytes) (parsed : SignalMessage)
    (hEx : ExplainsMoves interpretation r₀ S who ok g ms τ₁)
    (hABS' : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = none)
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (k_own : DY.Bytes) (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext, gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    (∃ theirPk_c : DY.Bytes,
      let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk theirPk_c st₀.dhs).2 msg₀.counter.toNat)).2
      Symbolic.Swarm.CREF.TR.G1.TermShapeId theirPk_c ∧ theirPk_c.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g theirPk_c = gamma interpretation S g msg₀.ratchetKey ∧
      seed_c.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g seed_c = gamma interpretation S g mkSeed) ∨
    (∃ salt₁ ∈ honestSalts r₀ ms, Symbolic.Swarm.CREF.TR.G1.TermShapeId msg₀.ratchetKey ∧
      Symbolic.Swarm.CREF.TR.G1.AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed salt₁ ∧
      gamma interpretation S g (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) =
        b.drop (b.length - 8) ∧
      interpretation aesCbcDecryptSymbol
        [parsed.ciphertext, gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey,
         (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv).take 16] = some ptext) := by
  have hrkK := Symbolic.Swarm.CREF.TR.G1.ratchetKey_attackerKnows_of_recvRepresentations
    interpretation r₀ S g ms b ht₀ hparse₀
  have hIk := Symbolic.Swarm.CREF.TR.G1.Ik.availableIkShapeId_all r₀ ms
  have hDisj : mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
      Symbolic.Swarm.CREF.TR.G1.AuthenticDecryptRepB3_g1 interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own := by
    rcases Symbolic.Swarm.CREF.TR.G1.g1a_case_split interpretation r₀ S g ms b t₀ msg₀ hreach ht₀ hparse₀
        hNotCol st₀ hst₀ mkSeed hseed k_own hk_own hMacBytes with
      hSeedKnows | hCaseB | hCaseC
    · exact Or.inl hSeedKnows
    · obtain ⟨salt₁, hsalt₁, hTripleEq, pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s,
        ns_s, pn_s, hmac_eq, htrunc_ak, hsh_inp⟩ := hCaseB
      let wire_s := trHonestWireMsg (DY.DiffieHellman.dhPk a_s) ns_s pn_s
        (DY.SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
      let inp₀ := DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt_s seed_s).macKey
        (DY.Concat.concat myIk_s (DY.Concat.concat peerIk_s wire_s))
      have hDecOk_salt₁ : interpretation aesCbcDecryptSymbol
          [parsed.ciphertext, gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv).take 16] = some ptext := by
        rw [hTripleEq.1, hTripleEq.2.2]; exact hDecOk
      rcases Symbolic.Swarm.CREF.TR.G1.macKdfSafe_c_trunc8_inv_strong r₀ ms inp₀ hreach htrunc_ak with
        hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a', ns', pn', m', pqMsg', t_s, st_s,
          hinp_eq, hpq_ak, ht'_ak, ha_eq, hst_s, hmyIk_s, hpeerIk_s, hseed_s⟩
      · exact Symbolic.Swarm.CREF.TR.G1.g1c_own_key_branch' interpretation r₀ S g ms b ptext hABS' hreach
          t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ mkSeed hseed k_own
          ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_ak, hsh_inp⟩
      · right; refine ⟨salt₁, hsalt₁, hTripleEq, ?_⟩
        have hmac_eq' : msg₀.mac = computeMac (trMsgKeys pqSalt' seed').macKey myIk' peerIk'
            (trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
              (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg') := by
          unfold DY.Libsignal.TripleRatchet.computeMac; rw [← hinp_eq]; exact hmac_eq
        have hsh_inp' : (gamma' interpretation S g
            (DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt' seed').macKey
              (DY.Concat.concat myIk' (DY.Concat.concat peerIk'
                (trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
                  (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg'))))).shape =
            (gamma' interpretation S g
              (DY.Libsignal.TripleRatchet.hmac (trMsgKeys salt₁ mkSeed).macKey
                (DY.Concat.concat st₀.peerIk (DY.Concat.concat st₀.myIk msg₀.wire)))).shape := by
          rw [← hinp_eq]; exact hsh_inp
        have ht'_kn' : (DY.Concat.concat (trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
            (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg')
            msg₀.mac).AttackerKnows (runTraceMoves r₀ ms) := by rw [hmac_eq]; exact ht'_ak
        obtain ⟨_, hseed_sh, hmyIk_sh, hpeerIk_sh, hwire_sh⟩ :=
          Symbolic.Swarm.CREF.TR.G1.shape_inp_honest_inj interpretation S g hsh_inp'
        obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ :=
          Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_eq_some_inv hparse₀
        have hwire_sh' : (gamma' interpretation S g
            (DY.TrWire.trWireMsg messageVersion (DY.DiffieHellman.dhPk a')
              ns' pn'
              (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
              pqMsg' DY.Libsignal.Refinement.canonicalVariation)).shape =
            (gamma' interpretation S g
              (DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀)).shape := by
          rw [← hwire₀_eq]; exact hwire_sh
        obtain ⟨_, _, hrk_sh, _, _, _, _, _⟩ :=
          Symbolic.Swarm.CREF.TR.G1.trWire_shape_eq_imp_addr_eq interpretation interpretation S S g g
            messageVersion (DY.DiffieHellman.dhPk a')
            ns' pn'
            (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
            pqMsg' DY.Libsignal.Refinement.canonicalVariation
            v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀ hwire_sh'
        have hrk_eq : DY.DiffieHellman.dhPk a' = msg₀.ratchetKey := by
          rw [ha_eq] at hrk_sh ⊢
          exact Symbolic.Swarm.CREF.TR.G1.eq_dhPk_randTerm32_of_shape_eq interpretation S g t_s hrk_sh
        have hseed_eq : seed' = mkSeed := by
          rw [← hseed_s] at hseed_sh ⊢
          exact honestSkelUniq_of_reachable_compat interpretation r₀ S g ms hreach
            (aliceSlot_sigma_len32_of_explains interpretation r₀ S g ms hEx)
            hst_s hst₀ hseed hseed_sh
        have hmyIk_eq : myIk' = st₀.peerIk := by
          rw [← hmyIk_s] at hmyIk_sh ⊢
          exact Symbolic.Swarm.CREF.TR.G1.eq_of_shape_eq_of_shapeId (hIk st_s hst_s).1 (hIk st₀ hst₀).2 hmyIk_sh
        have hpeerIk_eq : peerIk' = st₀.myIk := by
          rw [← hpeerIk_s] at hpeerIk_sh ⊢
          exact Symbolic.Swarm.CREF.TR.G1.eq_of_shape_eq_of_shapeId (hIk st_s hst_s).2 (hIk st₀ hst₀).1 hpeerIk_sh
        exact Symbolic.Swarm.CREF.TR.G1.g1b_honest_send_branch_core interpretation hEq r₀ S g ms b ptext parsed hTryFrom
          t₀ msg₀ ht₀ hparse₀ st₀ mkSeed hseed salt₁ hDecOk_salt₁
          salt₁ pqSalt' seed' myIk' peerIk' a' m' pqMsg' ns' pn'
          rfl hmac_eq' hsh_inp' hpq_ak ht'_kn' hrk_eq hseed_eq hmyIk_eq hpeerIk_eq
    · exact Symbolic.Swarm.CREF.TR.G1.g1c_own_key_branch' interpretation r₀ S g ms b ptext hABS' hreach
        t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ mkSeed hseed k_own hCaseC
  rcases hDisj with hmk_ak | ⟨salt₁, hsalt₁, ⟨hck_eq, hmk_eq, hiv_eq⟩, hAuth_salt₁⟩
  · exact Or.inl (Symbolic.Swarm.CREF.TR.G1.ratchetDH_rkSwap_seed_known_of_seed_attackerKnows
      interpretation hEq r₀ S g ms msg₀ st₀ mkSeed hreach hst₀ hfind hrkK hseed hmk_ak)
  · rcases Symbolic.Swarm.CREF.TR.G1.seed_attackerKnows_or_termShapeId_of_authenticDecryptRep
        interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed salt₁ hreach hseed hAuth_salt₁ with
      hmk_ak | ⟨hrk_sid, hAuth⟩
    · exact Or.inl (Symbolic.Swarm.CREF.TR.G1.ratchetDH_rkSwap_seed_known_of_seed_attackerKnows
        interpretation hEq r₀ S g ms msg₀ st₀ mkSeed hreach hst₀ hfind hrkK hseed hmk_ak)
    · refine Or.inr ⟨salt₁, hsalt₁, hrk_sid, hAuth, ?_, by rw [hck_eq, hiv_eq]; exact hDecOk⟩
      rw [hMacBytes]
      unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
      rw [Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.gamma_trunc8_tr,
          Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.gamma_trunc8_tr,
          Symbolic.Swarm.CREF.TR.G1.gamma_kdfExtract_tr,
          Symbolic.Swarm.CREF.TR.G1.gamma_kdfExtract_tr, hmk_eq]

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
