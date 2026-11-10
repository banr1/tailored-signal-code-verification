/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
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
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieRec
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptRecRelPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
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
# Record Relation Core for Pre-Key Session Start

Proves `RpkRecRel` between Bob's post-handshake symbolic state `rpkR_finalSt w` and the serialized
session record `sm.state` from `AcceptTieD` and the bundled model glue `RpkT1Glue`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF.TR (RndE)

/-- The TR DH ratchet step from Bob's initial state on the peer's ratchet key `rt` is Bob's
ratcheted state and chain. -/
theorem rpkT1_trDh_bobInitSt (a : Participant) (ikB ikA : DY.Bytes)
    (keys : PQXDH.HandshakeKeys) (sS rt : DY.Bytes) (n : Nat) :
    TR.RecvDec.trDhRatchetState (bobInitSt a ikB ikA keys sS rt) rt n =
      (bobRatchetedSt a ikB ikA keys sS rt (randTerm n 32), bobRatchetedChain keys rt sS) := rfl

private theorem rpkT1_flatten_map_lenField_length_ge {α : Type} (tag : Nat)
    (f : α → List (BitVec 8)) (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem rpkT1_encReceiverChain_length_le_encSession
    (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (rc : CryptoGames.LibsignalSession.ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := rpkT1_flatten_map_lenField_length_ge 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega

theorem rpkT1_recordBytes_of_binSessionInv
    {st' : CryptoGames.LibsignalSession.SessionState HwBytes}
    {aliceBaseBytes : HwBytes} {f248 regIdB : BitVec 32} {smState : HwBytes}
    (hbin : TR.Pure.BinSessionInv
      (bobNewSession st' aliceBaseBytes f248 regIdB))
    (hsm : smState = CryptoVerification.E2E.Record.encodeRecord
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩) :
    smState = recordBytes (sessionToRecordRec (bobNewSession st' aliceBaseBytes f248 regIdB)) := by
  obtain ⟨_hwf, _hrc_len, hrc_mk, halice_lt, _hkyb, hpq_lt, henc_lt⟩ := hbin
  have hsess_lt : (CryptoVerification.E2E.Record.encSession
      (bobNewSession st' aliceBaseBytes f248 regIdB)).length < 2 ^ 64 := by
    have h62 : (CryptoVerification.E2E.Record.encSession
        (bobNewSession st' aliceBaseBytes f248 regIdB)).length < 2 ^ 62 := henc_lt
    omega
  have hseeds : ∀ rc ∈ (bobNewSession st' aliceBaseBytes f248 regIdB).state.receiverChains,
      ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk
    have h32 := (hrc_mk rc hrc).2 mk hmk
    omega
  have htr := Swarm.Phase0WholeFunctionBridge.recordBytes_sessionToRecordRec_eq_encodeRecord
    (bobNewSession st' aliceBaseBytes f248 regIdB) rfl rfl
    (by omega) (by omega) hseeds
    (fun rc hrc' => Nat.lt_of_le_of_lt (rpkT1_encReceiverChain_length_le_encSession _ rc hrc') hsess_lt)
    hsess_lt
  exact hsm.trans htr.symm

/-- Proves `RpkRecRel` between `rpkR_finalSt w` and `sm.state` from `AcceptTieD`, the initial
`StateRel` on `bobInitSt`, and pre-start skipped-key freshness. -/
theorem rpkT1_core {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {p : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    (hD : AcceptD.AcceptTieD interpretation r p d pt sm)
    (_hsmLen : sm.state.length < 2 ^ 64)
    {ms : List Move} {a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (shown : Nat)
    (w : BobStartOk (runTraceMoves r ms) r.bob a kh regA mh pqIdx spqrMsgIdx)
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hrel0 : ∀ s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)),
      AcceptSt0ModelInvs interpretation r p s.state →
      TR.StateRel interpretation S g
        (bobInitSt a w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey)
        (sessionToRecordRec (RpkDHa.rpkSessionNorm (rpkSpkPub interpretation r) s)))
    (hRkLen : (gamma interpretation S g w.keys.rk).length = 32)
    (hDhsLen : (gamma interpretation S g w.spk).length = 32)
    (hTheir : p.inner.senderRatchetKey =
      ⟨DY.Libsignal.TripleRatchet.Refinement.vec32 (gamma interpretation S g w.msg.ratchetKey)⟩)
    (hPkLen : (gamma interpretation S g w.msg.ratchetKey).length = 32)
    (hRng : g.σ (runTraceMoves r ms).length 32 = d) (hdLen : d.length = 32)
    (hCtr : UInt32.ofBitVec p.inner.counter = w.msg.counter)
    (hSpqr : ∀ (st0 : CryptoGames.LibsignalSession.SessionState HwBytes) (newPqr : HwBytes)
      (key : CryptoGames.HKDF.Salt),
      AcceptSt0ModelInvs interpretation r p st0 →
      (pureSpqrEmptyAsNone
          (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation)).recv
        st0.pqRatchetState p.inner.pqRatchet = Except.ok (newPqr, key) →
      gamma interpretation S g w.spqr' = newPqr)
    (hfresh : ∀ j < w.msg.counter.toNat,
      DY.Libsignal.TripleRatchet.receiverKeyUsedB (runTraceMoves r ms)
        ((rpkR_finalSt w).sessionInfo r.bob)
        (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt
          (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2
        (UInt32.ofNat j) 2 = false) :
    RpkRecRel interpretation S g
      (runTraceMoves r (ms ++ [.bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown]))
      r.bob (rpkR_finalSt w) sm.state := by
  obtain ⟨st0, st', _expected, ⟨_, f248, _hscope, hbin, hsm⟩, hinv, _hsk, hdec⟩ := hD
  have hrc0 : st0.receiverChains = [] := by
    obtain ⟨_, _, h, -⟩ := hinv; exact h
  obtain ⟨_remIk, tr_out, _hRem, hTr, hSt2⟩ :=
    Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hdec
  obtain ⟨ck0, r1_0, r2, mkGen, newPqrState, pqrKey,
      hEnsure, hConsume, hspqr, hMac, _hDec, hTrOut⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv hTr
  have hst' : st' = { st0 with
      rootKey := r2.rootKey, previousCounter := r2.previousCounter,
      senderChain := r2.senderChain, receiverChains := r2.receiverChains,
      pqRatchetState := newPqrState, pendingPreKey := false } := by
    rw [hSt2, hTrOut]
  have ⟨ck, ck_adv, ck_next, r1, r_adv, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet⟩ :
      ∃ ck ck_adv ck_next r1 r_adv,
        (Proofs.libsignal.RngG.R3.ratchetStateOf st0).findReceiverChainKey
          p.inner.senderRatchetKey = .ok none ∧
        Mut.exec (CryptoGames.LibsignalSession.RatchetState.dhRatchetStep
          (Proofs.libsignal.Hooks2.cryptoOf' interpretation)
          p.inner.senderRatchetKey
          (RpkCli.pureCoinsOf d))
          (Proofs.libsignal.RngG.R3.ratchetStateOf st0) = (.ok ck, r1) ∧
        ¬ (p.inner.counter < ck.index) ∧
        (p.inner.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps ∧
        Mut.exec (CryptoGames.LibsignalSession.RatchetState.advanceChain
          (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
          p.inner.senderRatchetKey p.inner.counter
          (p.inner.counter - ck.index).toNat ck) r1 = (.ok ck_adv, r_adv) ∧
        ck_adv.nextChainKey (DY.Libsignal.Refinement.sha256CompressFunction interpretation) =
          .ok ck_next ∧
        Mut.exec (CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey
          p.inner.senderRatchetKey ck_next) r_adv = (.ok (), r2) := by
    cases Proofs.libsignal.RngG.R3.decryptOkBranch_of_ensure_consume hEnsure hConsume hMac with
    | skipped ck' hFind _ _ _ =>
      obtain ⟨_, rc', _, hrc', _, _⟩ :=
        Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
      have hmem : rc' ∈ st0.receiverChains := List.mem_of_getElem? hrc'
      rw [hrc0] at hmem; cases hmem
    | existing ck' _ _ _ hFind _ _ _ _ _ _ _ =>
      obtain ⟨_, rc', _, hrc', _, _⟩ :=
        Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
      have hmem : rc' ∈ st0.receiverChains := List.mem_of_getElem? hrc'
      rw [hrc0] at hmem; cases hmem
    | ratchet ck ck_adv ck_next r1 r_adv hFind hDh hNotLt hJump hAdv hNext hSet _ _ =>
      obtain ⟨_, _, _, _, _, _, _, hr1_eq⟩ := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
      have hJump' : (p.inner.counter - ck.index).toNat ≤
          CryptoGames.LibsignalSession.maxForwardJumps := by
        have hmfj : r1.maxForwardJumps = CryptoGames.LibsignalSession.maxForwardJumps := by
          rw [hr1_eq]
        omega
      exact ⟨ck, ck_adv, ck_next, r1, r_adv, hFind, hDh, hNotLt, hJump', hAdv, hNext, hSet⟩
  let s0 : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)) :=
    { state := st0, pendingPreKey := none, pendingKyberPreKey := none,
      aliceBaseKey := p.baseKey.take 33, remoteRegistrationId := f248,
      localRegistrationId := r.regIdB }
  have h := RpkDHa.rpkD_stateRel_and_consumeMessageKey_of_dhRatchetStep interpretation S g hEq
    (s := s0) (P := rpkSpkPub interpretation r) (hrel := hrel0 s0 hinv) (hRkLen := hRkLen)
    (hDhsLen := hDhsLen) (hCkLens := by intro c hc; simp [bobInitSt] at hc) (hTheir := hTheir)
    (hPkLen := hPkLen) (hRng := hRng) (hRngLen := hdLen)
    (hspqr' := hSpqr st0 newPqrState pqrKey hinv hspqr) (hFindNone := hFind) (hStep := hDh)
    (hNotLt := hNotLt) (hJump := hJump) (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  rw [rpkT1_trDh_bobInitSt] at h
  dsimp only at h
  obtain ⟨-, mks', seed, c', hcons, -, -, -, -, -, -, -, hRel, hRcMem, hMks'⟩ := h
  rw [hCtr] at hcons
  have hc2 : some (seed, c') = some (w.seed, w.c') := hcons.symm.trans w.hcons
  simp only [Option.some.injEq, Prod.mk.injEq] at hc2
  obtain ⟨rfl, rfl⟩ := hc2
  let s1 : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)) :=
    bobNewSession st' (p.baseKey.take 33) f248 r.regIdB
  have hs1_eq : s1 = { s0 with
      state := { s0.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter,
        senderChain := r2.senderChain, receiverChains := r2.receiverChains,
        pqRatchetState := newPqrState, pendingPreKey := false }
      pendingPreKey := none, pendingKyberPreKey := none } := by
    dsimp only [s1, bobNewSession, s0]
    rw [hst']
  have hbytes : sm.state = recordBytes (sessionToRecordRec s1) :=
    rpkT1_recordBytes_of_binSessionInv hbin hsm
  have hRc1 : ∀ rc ∈ s1.state.receiverChains,
      rc = ⟨p.inner.senderRatchetKey, some ck_next, mks'⟩ := by
    intro rc hrc
    rw [hs1_eq] at hrc
    rcases hRcMem rc hrc with h | h
    · have h' : rc ∈ st0.receiverChains := h
      rw [hrc0] at h'; simp at h'
    · exact h
  have hidx : (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).index = 0 := rfl
  refine ⟨sessionToRecordRec s1, hbytes, by rw [hs1_eq]; exact hRel, ?_, ?_⟩
  · intro c hc k hk
    change c ∈ s1.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec
      at hc
    obtain ⟨rc, hrc, rfl⟩ := List.mem_map.1 hc
    obtain rfl := hRc1 rc hrc
    change k ∈ mks'.map (fun mk => (mk.counter, mk.seed)) at hk
    obtain ⟨mk, hmk, rfl⟩ := List.mem_map.1 hk
    obtain ⟨j, hj, -, hctr, -, hseed, -⟩ := hMks' mk hmk
    have hctr' : UInt32.ofBitVec mk.counter = UInt32.ofNat j := by
      rw [hctr, hidx]; simp
    have hj' : j < w.msg.counter.toNat := by
      rw [hCtr, hidx] at hj; simpa using hj
    obtain ⟨skIdx, srcIdx, hlog, hsk, hrk⟩ :=
      rpkRR_skipped_T3_run shown w hreach hj' (hfresh j hj')
    refine ⟨w.msg.ratchetKey, 2, srcIdx, skIdx,
      (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt
        (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hctr'] using hlog
    · simp [hsk]
    · simp [hctr', hrk]
    · exact hseed.symm
    · show p.inner.senderRatchetKey.serialize = _
      rw [hTheir]
      unfold CryptoGames.LibsignalSession.PublicKey.serialize TR.serializedKey
      congr 1
      exact Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hPkLen
    · dsimp only [rpkR_finalSt, bobRatchetedSt, bobRatchetedChain,
        DY.Libsignal.TripleRatchet.setRecvChain, DY.Libsignal.TripleRatchet.findRecvChain, List.map]
      by_cases h : (w.msg.ratchetKey == w.c'.ratchetKey) = true
      · have heq : w.c'.ratchetKey = w.msg.ratchetKey := (beq_iff_eq.mp h).symm
        simp [heq]
      · simp [h]
  · exact TR.RecvDecStep.nodup_and_lt_of_dhRatchetStep_tr (s := s0) (s' := s1) hFind hDh hNotLt
      hAdv hNext hSet (congrArg (fun x => x.state.receiverChains) hs1_eq)
      (by
        refine ⟨?_, ?_, ?_⟩ <;>
          simp [s0, hrc0, sessionToRecordRec, Swarm.Phase0WholeFunctionBridge.sessionToSessionRec])

/-- Bundled model-to-binary glue hypotheses for `rpkT1_core` on a successful `BobStartOk` witness. -/
structure RpkT1Glue (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (p : PreKeyFields) (d : HwBytes) (ms : List Move) (a : Participant)
    (kh : PQXDH.BobKeyHandles) (regA : Nat) (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat)
    (spqrMsgIdx : UInt32) (w : BobStartOk (runTraceMoves r ms) r.bob a kh regA mh pqIdx spqrMsgIdx) :
    Prop where
  reach : (runTraceMoves r ms).Reachable reachability
  rel0 : ∀ s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)),
    AcceptSt0ModelInvs interpretation r p s.state →
    TR.StateRel interpretation S g
      (bobInitSt a w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey)
      (sessionToRecordRec (RpkDHa.rpkSessionNorm (rpkSpkPub interpretation r) s))
  rkLen : (gamma interpretation S g w.keys.rk).length = 32
  dhsLen : (gamma interpretation S g w.spk).length = 32
  their : p.inner.senderRatchetKey =
    ⟨DY.Libsignal.TripleRatchet.Refinement.vec32 (gamma interpretation S g w.msg.ratchetKey)⟩
  pkLen : (gamma interpretation S g w.msg.ratchetKey).length = 32
  rng : g.σ (runTraceMoves r ms).length 32 = d
  dLen : d.length = 32
  ctr : UInt32.ofBitVec p.inner.counter = w.msg.counter
  spqr : ∀ (st0 : CryptoGames.LibsignalSession.SessionState HwBytes) (newPqr : HwBytes)
      (key : CryptoGames.HKDF.Salt),
    AcceptSt0ModelInvs interpretation r p st0 →
    (pureSpqrEmptyAsNone
        (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
        (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
        (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation)).recv
      st0.pqRatchetState p.inner.pqRatchet = Except.ok (newPqr, key) →
    gamma interpretation S g w.spqr' = newPqr
  fresh : ∀ j < w.msg.counter.toNat,
    DY.Libsignal.TripleRatchet.receiverKeyUsedB (runTraceMoves r ms)
      ((rpkR_finalSt w).sessionInfo r.bob)
      (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt
        (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2
      (UInt32.ofNat j) 2 = false

theorem rpkT1_of_glue {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {p : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    (hD : AcceptD.AcceptTieD interpretation r p d pt sm)
    (hsmLen : sm.state.length < 2 ^ 64)
    {ms : List Move} {a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (shown : Nat)
    {w : BobStartOk (runTraceMoves r ms) r.bob a kh regA mh pqIdx spqrMsgIdx}
    (G : RpkT1Glue interpretation r S g p d ms a kh regA mh pqIdx spqrMsgIdx w) :
    RpkRecRel interpretation S g
      (runTraceMoves r (ms ++ [.bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown]))
      r.bob (rpkR_finalSt w) sm.state :=
  rpkT1_core hEq hD hsmLen shown w G.reach G.rel0 G.rkLen G.dhsLen G.their G.pkLen G.rng G.dLen
    G.ctr G.spqr G.fresh

/-- Relates `p.inner.senderRatchetKey` and `p.inner.counter` to the `gamma` image and counter of a
parsed `TRSignalMsg` satisfying `FaithfulInner`. -/
theorem rpkT1_msgTie_of_faithfulInner {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {t : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {p : PreKeyFields}
    (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg)
    (hF : FaithfulInner interpretation S g t p) :
    gamma interpretation S g msg.ratchetKey = p.inner.senderRatchetKey.bytes.toList ∧
      p.inner.senderRatchetKey =
        ⟨DY.Libsignal.TripleRatchet.Refinement.vec32 (gamma interpretation S g msg.ratchetKey)⟩ ∧
      (gamma interpretation S g msg.ratchetKey).length = 32 ∧
      UInt32.ofBitVec p.inner.counter = msg.counter := by
  obtain ⟨msg', hp', _, _, _, _, hrk, _, hctr, _⟩ := hF
  rw [hparse] at hp'
  cases hp'
  have hlen : (gamma interpretation S g msg.ratchetKey).length = 32 := by
    rw [hrk]; exact p.inner.senderRatchetKey.bytes.2
  refine ⟨hrk, ?_, hlen, ?_⟩
  · cases hmk : p.inner.senderRatchetKey with
    | mk b =>
      have hb : b.toList =
          (DY.Libsignal.TripleRatchet.Refinement.vec32
            (gamma interpretation S g msg.ratchetKey)).toList := by
        rw [hmk] at hrk
        exact hrk.symm.trans
          (Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hlen).symm
      exact congrArg _ (Subtype.ext hb)
  · apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofBitVec]
    exact hctr.symm

private theorem rpkT1_newIndices_trans {tr₀ tr₁ tr₂ : ExecTrace} (h01 : tr₀ ≤ tr₁)
    (h12 : tr₁ ≤ tr₂) :
    newIndices tr₀ tr₂ = newIndices tr₀ tr₁ ++ newIndices tr₁ tr₂ := by
  unfold newIndices
  have hlen01 := DY.Trace.length_le tr₀ tr₁ h01
  have hlen12 := DY.Trace.length_le tr₁ tr₂ h12
  have hadd : tr₂.length - tr₀.length = (tr₁.length - tr₀.length) + (tr₂.length - tr₁.length) := by
    omega
  have hmid : tr₀.length + (tr₁.length - tr₀.length) = tr₁.length := by omega
  rw [hadd, ← List.range'_append_1, hmid]

private theorem rpkT1_mem_newIndices_lt {tr₀ tr₁ : ExecTrace} {i : Nat}
    (hi : i ∈ newIndices tr₀ tr₁) : i < tr₁.length := by
  unfold newIndices at hi; rw [List.mem_range'] at hi; rcases hi with ⟨k, hk, rfl⟩; omega

private theorem rpkT1_newIndices_append_singleton {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) : newIndices tr (tr.append e) = [tr.length] := by
  unfold newIndices
  have hlen : (tr.append e).length - tr.length = 1 := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen]; rfl

private theorem rpkT1_at?_append_self_proj {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.snoc (DY.TraceEntryHas.inj e)).length := by simp [Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

theorem rpkT1_newRandoms_trans {tr₀ tr₁ tr₂ : ExecTrace} (h01 : tr₀ ≤ tr₁)
    (h12 : tr₁ ≤ tr₂) :
    newRandoms tr₀ tr₂ = newRandoms tr₀ tr₁ ++ newRandoms tr₁ tr₂ := by
  unfold newRandoms; rw [rpkT1_newIndices_trans h01 h12, List.filterMap_append]; congr 1
  exact List.filterMap_congr fun i hi => by rw [at?_of_le h12 (rpkT1_mem_newIndices_lt hi)]

theorem rpkT1_newRandoms_append_rnd_self (tr : ExecTrace) (n : Nat) :
    newRandoms tr (tr.append (RndE n)) = [(randTerm tr.length n, n)] := by
  unfold newRandoms
  rw [rpkT1_newIndices_append_singleton, List.filterMap_cons, List.filterMap_nil,
    rpkT1_at?_append_self_proj, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq]; rfl

theorem rpkT1_newRandoms_append_other {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none := by rfl) :
    newRandoms tr (tr.append e) = [] := by
  unfold newRandoms
  rw [rpkT1_newIndices_append_singleton, List.filterMap_cons, List.filterMap_nil,
    rpkT1_at?_append_self_proj, hnone]; rfl

end Symbolic.Swarm.CREF.CliPure
