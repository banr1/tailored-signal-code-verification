/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3ChainsWFPresPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PinCoinsPure
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.RngG.R3SetRecv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# DH Ratchet and Forward-Jump Step Bridge

Bridges model execution of `dhRatchetStep`, `advanceChain`, `nextChainKey`, and
`setReceiverChainKey` to symbolic `trDhRatchetState` and `consumeMessageKey`, and proves
preservation of `x25519LowOrder = false`, `TRKeyShape`, and `RecordChainsWF3`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr
open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet
  (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte hkdfBlock1 hkdfBlock2)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (x25519AgreementSymbol sha256CompressFunction ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2
open Symbolic.Swarm.CREF.CliPure.RpkCli (pinCoins)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec
  receiverChainToChainRec)
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState)
open Symbolic.Swarm.CREF.TR.FreshSigma

/-- Relates model `dhRatchetStep`, `advanceChain`, `nextChainKey`, and `setReceiverChainKey` to
symbolic `trDhRatchetState`, `consumeMessageKey`, post-state `StateRel`, and cached skipped keys. -/
theorem stateRel_and_consumeMessageKey_of_dhRatchetStep_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEquations : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hRkLen : (gamma interpretation S g st.rk).length = 32)
    (hDhsLen : (gamma interpretation S g st.dhs).length = 32)
    (hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32)
    {their : PublicKey} {pk : DY.Bytes} {counter : BitVec 32}
    (hTheir : their = ⟨vec32 (gamma interpretation S g pk)⟩)
    (hPkLen : (gamma interpretation S g pk).length = 32)
    {rngIdx : Nat} {rngBytes : List (BitVec 8)}
    (hRng : g.σ rngIdx 32 = rngBytes) (hRngLen : rngBytes.length = 32)
    {spqr' : DY.Bytes} {newPqrState : List (BitVec 8)}
    (hspqr' : gamma interpretation S g spqr' = newPqrState)
    {ck_r ck_adv ck_next : ChainKey} {r1 r_adv r2 : RatchetState}
    (hFindNone : (ratchetStateOf s.state).findReceiverChainKey their = .ok none)
    (hStep :
      Mut.exec
        (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their (pinCoins (some rngBytes)))
        (ratchetStateOf s.state) = (.ok ck_r, r1))
    (hNotLt : ¬ (counter < ck_r.index))
    (hJump : (counter - ck_r.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps)
    (hAdv :
      Mut.exec
        (RatchetState.advanceChain (sha256CompressFunction interpretation)
          their counter (counter - ck_r.index).toNat ck_r)
        r1 = (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey (sha256CompressFunction interpretation) = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2)) :
    let F := sha256CompressFunction interpretation
    let msgCounter := UInt32.ofBitVec counter
    let (st1, c) := trDhRatchetState st pk rngIdx
    findRecvChain st.recv pk = none ∧
    ∃ (mks' : List MessageKeyGenerator) (seed : DY.Bytes) (c' : RecvChain),
      consumeMessageKey c msgCounter = some (seed, c') ∧
      (ck_adv.messageKeys F).seed = gamma interpretation S g seed ∧
      (ck_adv.messageKeys F).counter = counter ∧
      c'.ratchetKey = pk ∧
      c'.rIdx = st.rIdx + 2 ∧
      c.index = 0 ∧
      c.rIdx = st.rIdx + 2 ∧
      r2 = { r1 with
        receiverChains := r1.receiverChains.set (r1.receiverChains.length - 1)
          { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' } } ∧
      StateRel interpretation S g { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
        (sessionToRecordRec
          { s with
            state :=
              { s.state with
                rootKey := r2.rootKey, previousCounter := r2.previousCounter,
                senderChain := r2.senderChain, receiverChains := r2.receiverChains,
                pqRatchetState := newPqrState, pendingPreKey := false }
            pendingPreKey := none, pendingKyberPreKey := none }) ∧
      (∀ rc ∈ r2.receiverChains,
        rc ∈ s.state.receiverChains ∨
        rc = { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' }) ∧
      (∀ k ∈ mks',
        ∃ j < msgCounter.toNat - c.index.toNat,
          k.counter = c.index.toBitVec + BitVec.ofNat 32 j ∧
          UInt32.ofBitVec k.counter = c.index + UInt32.ofNat j ∧
          UInt32.ofBitVec k.counter ≠ msgCounter ∧
          k.seed = gamma interpretation S g (kdfCk (chainKeyAt c.chainKey j)).2 ∧
          k.seed.length = 32) := by
  intro F msgCounter
  let st1 := (trDhRatchetState st pk rngIdx).1
  let c := (trDhRatchetState st pk rngIdx).2
  have hMap0 : (ratchetStateOf s.state).receiverChains.map eraseRecvChain =
      st.recv.map (modelRecvChainOfTr interpretation S g) :=
    recvMap_of_stateRel_tr interpretation S g hrel hCkLens
  obtain ⟨hNoR0, hFindSym⟩ := findReceiverChainKey_none_of_map_erase_tr hMap0 hFindNone hTheir
  obtain ⟨hCkR, hCkLen, hRk2Len, hCksLen, hR1Root, hR1RootBytes, hR1Prev, hR1Send, hR1SendRec,
      hR1RcEvict, hR1Len, hR1Last, hR1Prefix, hR1Map⟩ :=
    dhRatchetStep_ok_eq_gamma_trDhRatchetState interpretation S g hEquations E D hrel
      hRkLen hDhsLen hCkLens hTheir hPkLen hRng hRngLen hStep
  obtain ⟨hLe, hNeAllOnes, hCkAdvEq, hCkAdvIdx, hCkNextEq, hCkNextIdx,
      ci, ch, mks', hci, hch, hsrk, hR2Eq, hMksSub⟩ :=
    advanceChain_setReceiverChainKey_ok_inv hNotLt hAdv hNext hSet
  have hCiLt : ci < r1.receiverChains.length := by
    by_contra hGe; rw [List.getElem?_eq_none (Nat.not_lt.mp hGe)] at hch; cases hch
  have hCiEqLast : ci = r1.receiverChains.length - 1 := by
    by_contra hNe; have hOldAt := hR1Prefix ci (by omega); rw [hch] at hOldAt
    exact hNoR0 ch (List.mem_of_getElem? hOldAt.symm) hsrk
  subst hCiEqLast; rw [hR1Last] at hch; injection hch with hChEq
  have hChRewrite :
      { ch with chainKey := some ck_next, messageKeys := mks' } =
        ({ senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' } : ReceiverChain) := by
    cases ch; dsimp only at hsrk ⊢; rw [hsrk]
  have hChMksNil : ch.messageKeys = [] := by rw [← hChEq]; rfl
  have hCIdx0 : c.index = 0 := rfl
  have hCkIdx : ck_r.index = c.index.toBitVec := by rw [hCkR]; rfl
  have hIdxLe : c.index ≤ msgCounter := by rw [uint32_ofBitVec_le_iff, ← hCkIdx]; exact hLe
  have hn_eq : (counter - ck_r.index).toNat = msgCounter.toNat - c.index.toNat := by
    have hadd := index_toNat_add_sub_eq ck_r counter hLe
    change ck_r.index.toNat + (counter - ck_r.index).toNat = msgCounter.toNat at hadd
    have hck_nat : ck_r.index.toNat = c.index.toNat := by rw [hCkIdx]; rfl
    omega
  have hJumpSym : msgCounter.toNat - c.index.toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps := by
    rw [← hn_eq]; exact hJump
  have hNeU32Max : msgCounter ≠ u32Max := uint32_ofBitVec_ne_u32Max_of_ne_allOnes hNeAllOnes
  let n := msgCounter.toNat - c.index.toNat
  let seed : DY.Bytes := (kdfCk (chainKeyAt c.chainKey n)).2
  let c' : RecvChain :=
    { ratchetKey := c.ratchetKey, chainKey := (kdfCk (chainKeyAt c.chainKey n)).1,
      index := msgCounter + 1, rIdx := c.rIdx }
  have hNotLtSym : ¬ msgCounter < c.index := by
    intro h; rw [UInt32.lt_iff_toNat_lt] at h; rw [UInt32.le_iff_toNat_le] at hIdxLe; omega
  have hConsSym : consumeMessageKey c msgCounter = some (seed, c') :=
    (consumeMessageKey_eq_some_iff_tr c msgCounter seed c').mpr ⟨hNotLtSym, hJumpSym, hNeU32Max, rfl, rfl⟩
  have hSeedEq : (ck_adv.messageKeys F).seed = gamma interpretation S g seed := by
    rw [hCkAdvEq, hn_eq, hCkR]
    exact chainStepN_messageKeys_seed_eq_gamma_tr interpretation S g c.chainKey c.index.toBitVec n hCkLen
  have hCntEq : (ck_adv.messageKeys F).counter = counter := hCkAdvIdx
  have hCkNextVal :
      ck_next = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c'.chainKey), c'.index.toBitVec⟩ := by
    have hAdvKey : ck_adv.key = CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (chainKeyAt c.chainKey n)) := by
      rw [hCkAdvEq, hn_eq, hCkR]
      exact chainStepN_eq_gamma_chainKeyAt_tr interpretation S g c.chainKey c.index.toBitVec n hCkLen
    have hAdvFull : ck_adv =
        ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (chainKeyAt c.chainKey n)), counter⟩ := by
      rcases ck_adv with ⟨k_a, i_a⟩; dsimp only at hAdvKey hCkAdvIdx; rw [hAdvKey, hCkAdvIdx]
    rw [hCkNextEq, hAdvFull,
      step1_key_eq_gamma_kdfCk_fst_tr interpretation S g (chainKeyAt c.chainKey n) counter
        (length_gamma_chainKeyAt_tr interpretation S g c.chainKey n hCkLen)]; rfl
  have hEraseCh' :
      eraseRecvChain { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' } =
        modelRecvChainOfTr interpretation S g c' := by
    unfold eraseRecvChain modelRecvChainOfTr; dsimp only; rw [hTheir, hCkNextVal]; rfl
  have hNoMatchStRecv : ∀ y ∈ st.recv, y.ratchetKey ≠ pk := by
    intro y hy hEq; unfold findRecvChain at hFindSym
    have hNone2 := List.find?_eq_none.mp hFindSym y hy; simp [hEq] at hNone2
  have hSetRecvSt1 : setRecvChain st1.recv c' = st1.recv.set (st1.recv.length - 1) c' := by
    have hk_recv : (st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains ≤ st.recv.length := by
      change (st.recv.length + 1) - 5 ≤ st.recv.length; omega
    have hRecvDrop :
        (st.recv ++ [c]).drop ((st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) =
          st.recv.drop ((st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) ++ [c] :=
      drop_append_singleton_of_le hk_recv
    have hNoDrop :
        ∀ y ∈ st.recv.drop ((st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains),
          y.ratchetKey ≠ c'.ratchetKey := fun y hy => hNoMatchStRecv y (List.mem_of_mem_drop hy)
    change setRecvChain ((st.recv ++ [c]).drop ((st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains)) c' =
      ((st.recv ++ [c]).drop ((st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains)).set
        (((st.recv ++ [c]).drop ((st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains)).length - 1) c'
    rw [hRecvDrop, setRecvChain_append_singleton_of_forall_ne_tr _ c c' hNoDrop rfl, set_append_singleton_last]
  have hR2RcErase :
      r2.receiverChains.map eraseRecvChain =
        (setRecvChain st1.recv c').map (modelRecvChainOfTr interpretation S g) := by
    rw [hR2Eq, hChRewrite]; dsimp only
    rw [List.map_set, hR1Map, hEraseCh', hR1Len, ← List.map_set]
    exact congrArg (List.map (modelRecvChainOfTr interpretation S g)) hSetRecvSt1.symm
  have hRkLens0 : ∀ c0 ∈ st.recv, (gamma interpretation S g c0.ratchetKey).length = 32 :=
    rkLens_of_stateRel_tr hrel
  have hRkLens1 : ∀ c0 ∈ setRecvChain st1.recv c', (gamma interpretation S g c0.ratchetKey).length = 32 := by
    intro c0 hc0; unfold setRecvChain at hc0
    rcases List.mem_map.mp hc0 with ⟨d0, hd0, hd_eq⟩
    split at hd_eq
    · subst hd_eq; exact hPkLen
    · subst hd_eq
      have hd0_mem := List.mem_of_mem_drop hd0
      rw [List.mem_append, List.mem_singleton] at hd0_mem
      rcases hd0_mem with hd0_old | rfl
      · exact hRkLens0 d0 hd0_old
      · exact hPkLen
  have hCkLens1 : ∀ c0 ∈ setRecvChain st1.recv c', (gamma interpretation S g c0.chainKey).length = 32 := by
    intro c0 hc0; unfold setRecvChain at hc0
    rcases List.mem_map.mp hc0 with ⟨d0, hd0, hd_eq⟩
    split at hd_eq
    · subst hd_eq; exact length_gamma_kdfCk_fst_tr interpretation S g (chainKeyAt c.chainKey n)
    · subst hd_eq
      have hd0_mem := List.mem_of_mem_drop hd0
      rw [List.mem_append, List.mem_singleton] at hd0_mem
      rcases hd0_mem with hd0_old | rfl
      · exact hCkLens d0 hd0_old
      · exact hCkLen
  have hRel' :
      StateRel interpretation S g { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
        (sessionToRecordRec
          { s with
            state :=
              { s.state with
                rootKey := r2.rootKey, previousCounter := r2.previousCounter,
                senderChain := r2.senderChain, receiverChains := r2.receiverChains,
                pqRatchetState := newPqrState, pendingPreKey := false }
            pendingPreKey := none, pendingKyberPreKey := none }) := by
    have heq0 := (stateRel_sessionToRecordRec_iff_tr interpretation S g st s).mp hrel
    rw [stateRel_sessionToRecordRec_iff_tr]
    have hrc' : (r2.receiverChains.map eraseRecvChain).map recChainOfErased =
        (setRecvChain st1.recv c').map fun c0 =>
          ({ senderRatchetKey := Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g c0.ratchetKey)
             senderRatchetKeyPrivate := []
             chainKey := some (c0.index.toBitVec, gamma interpretation S g c0.chainKey)
             messageKeys := [] } : ChainRec) := by
      rw [hR2RcErase, List.map_map]
      exact List.map_congr_left fun c0 hc0 =>
        recChainOfErased_modelRecvChainOfTr interpretation S g c0 (hRkLens1 c0 hc0) (hCkLens1 c0 hc0)
    have hrc'' :
        r2.receiverChains.map (fun rc => { receiverChainToChainRec rc with messageKeys := [] }) =
          (setRecvChain st1.recv c').map fun c0 =>
            ({ senderRatchetKey := Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g c0.ratchetKey)
               senderRatchetKeyPrivate := []
               chainKey := some (c0.index.toBitVec, gamma interpretation S g c0.chainKey)
               messageKeys := [] } : ChainRec) := by
      rw [← hrc', List.map_map]; rfl
    have hR2Root : r2.rootKey = r1.rootKey := by rw [hR2Eq]
    have hR2Prev : r2.previousCounter = r1.previousCounter := by rw [hR2Eq]
    have hR2Send : r2.senderChain = r1.senderChain := by rw [hR2Eq]
    have hRootBytes : CryptoGames.HMAC.keyToBytes32 r2.rootKey = gamma interpretation S g st1.rk := by
      rw [hR2Root]; exact hR1RootBytes
    have hSendRec : r2.senderChain.map senderChainToChainRec =
        (sessionOf interpretation (gamma interpretation S g) st1).senderChain := by
      rw [hR2Send]; exact hR1SendRec
    simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, List.map_map] at heq0 ⊢
    unfold sessionOf at heq0 hSendRec ⊢; dsimp only at heq0 hSendRec ⊢
    injection heq0 with h1 h2 h3 _ _ _ _ _ _ _ _ _ _
    rw [Function.comp_def, hrc'', h1, h2, h3, hRootBytes, hR2Prev, hR1Prev, hSendRec, hspqr']; rfl
  have hR2Eq' :
      r2 = { r1 with
        receiverChains := r1.receiverChains.set (r1.receiverChains.length - 1)
          { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' } } := by
    rw [hR2Eq, hChRewrite]
  have hRcMem :
      ∀ rc ∈ r2.receiverChains,
        rc ∈ s.state.receiverChains ∨
        rc = { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' } := by
    intro rc hrc; rw [hR2Eq'] at hrc; dsimp only at hrc
    obtain ⟨i, hiLt, hiEq⟩ := List.getElem_of_mem hrc
    rw [List.length_set] at hiLt
    by_cases hLast : i = r1.receiverChains.length - 1
    · right
      have hAt : (r1.receiverChains.set (r1.receiverChains.length - 1)
          { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' })[i]? = some rc := by
        rw [List.getElem?_eq_getElem (by rw [List.length_set]; exact hiLt), hiEq]
      rw [hLast, List.getElem?_set_self hCiLt] at hAt
      injection hAt with hEq; exact hEq.symm
    · left
      have hLtLast : i < r1.receiverChains.length - 1 := by omega
      have hAt : (r1.receiverChains.set (r1.receiverChains.length - 1)
          { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' })[i]? = some rc := by
        rw [List.getElem?_eq_getElem (by rw [List.length_set]; exact hiLt), hiEq]
      rw [List.getElem?_set_ne (Ne.symm hLast), hR1Prefix i hLtLast] at hAt
      exact List.mem_of_getElem? hAt
  refine ⟨hFindSym, mks', seed, c', hConsSym, hSeedEq, hCntEq,
    rfl, rfl, hCIdx0, rfl, hR2Eq', hRel', hRcMem, ?_⟩
  intro k hk
  rcases hMksSub k hk with hSkip | hOld
  · rw [hn_eq, hCkR] at hSkip
    obtain ⟨j, hjLt, hjCnt, hjSeed⟩ :=
      skippedKeys_mem_gamma_kdfCk_tr interpretation S g c.chainKey c.index.toBitVec n hCkLen k hSkip
    have hjU32 : UInt32.ofBitVec k.counter = c.index + UInt32.ofNat j := by
      rw [hjCnt, uint32_ofBitVec_add_ofNat]
    have hjNe : UInt32.ofBitVec k.counter ≠ msgCounter := by
      intro hEqCnt
      have h1 : (c.index.toBitVec + BitVec.ofNat 32 j).toNat = counter.toNat :=
        congrArg UInt32.toNat (hjU32.symm.trans hEqCnt)
      have hadd : c.index.toBitVec.toNat + n = counter.toNat := by
        have h := index_toNat_add_sub_eq ck_r counter hLe; rwa [hn_eq, hCkIdx] at h
      have hlt32 : c.index.toBitVec.toNat + j < 2 ^ 32 := by have := counter.isLt; omega
      have htoNat : (c.index.toBitVec + BitVec.ofNat 32 j).toNat = c.index.toBitVec.toNat + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      omega
    have hjLen : k.seed.length = 32 := by
      rw [hjSeed]; exact length_gamma_kdfCk_snd_tr interpretation S g (chainKeyAt c.chainKey j)
    exact ⟨j, hjLt, hjCnt, hjU32, hjNe, hjSeed, hjLen⟩
  · rw [hChMksNil] at hOld; cases hOld

private theorem map_toNat_ofByteArray_data (ba : ByteArray) :
    (ofByteArray ba).map BitVec.toNat = ba.data.toList.map UInt8.toNat := by
  unfold ofByteArray; rw [List.map_map]; rfl

theorem x25519LowOrder_false_of_dhRatchetStep_ok_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {their : PublicKey} {coins : BitVec 256} {pk : DY.Bytes}
    (hTheir : their.bytes.toList = gamma interpretation S g pk)
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hDh :
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their coins) r0 =
        (.ok ck, r1)) :
    x25519LowOrder pk = false := by
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, hsc, hrc1, hrc2, hr1⟩ := dhRatchetStep_ok_inv hDh
  unfold x25519LowOrder
  rcases hb : DY.Literal.bytesToLiteral (DY.X25519.normalizeX25519Key pk) with _ | b
  · rfl
  · dsimp only
    cases hlow : DY.X25519.isLowOrderKey (b.data.toList.map (·.toNat))
    · rfl
    · exfalso
      have hlit : DY.X25519.normalizeX25519Key pk = DY.Literal.literalToBytes b := by
        have := DY.Literal.literalToBytes_bytesToLiteral (DY.X25519.normalizeX25519Key pk); rwa [hb] at this
      have hγ_key : gamma interpretation S g (DY.X25519.normalizeX25519Key pk) = ofByteArray b := by
        rw [hlit, gamma_literalToBytes_tr]
      have hlow_len : (b.data.toList.map (·.toNat)).length = 32 := by
        unfold DY.X25519.isLowOrderKey at hlow; simp only [Bool.and_eq_true] at hlow
        exact beq_iff_eq.mp hlow.1
      have hlen_of : (ofByteArray b).length = 32 := by
        unfold ofByteArray; rw [List.length_map]; simpa [List.length_map] using hlow_len
      have hlow_of : DY.X25519.isLowOrderKey ((ofByteArray b).map BitVec.toNat) = true := by
        rw [map_toNat_ofByteArray_data]; exact hlow
      have hsec_len := (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList_length
      have hiff := hEq.x25519_agreement_zero_iff_low_order
        (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList
        (ofByteArray b) hsec_len hlen_of
      have hz0 := hiff.mpr hlow_of
      have hagr := agreement_gamma_x25519Key_tr interpretation S g hEq
        (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList pk
      rw [hγ_key, ← hTheir] at hagr
      have hz :
          (interpretation x25519AgreementSymbol
            [(CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList,
              their.bytes.toList]).getD [] = List.replicate 32 0#8 := by
        rw [← hagr]; exact hz0
      have hlen := hEq.x25519_agreement_length
        (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList their.bytes.toList
      have hz' :
          ((cryptoOf' interpretation E D).X
            (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes) their.bytes).toList =
            List.replicate 32 0#8 := by
        dsimp only [cryptoOf']
        rw [Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hlen]; exact hz
      unfold rootCreateChain CryptoGames.Ratchet.createChain at hrc1
      simp only [hz', ite_true] at hrc1; nomatch hrc1

theorem trKeyShape_trDhRatchetState_recv_spqr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {pk : DY.Bytes} {rngIdx : Nat} {c' : RecvChain} {spqr' : DY.Bytes}
    (hks : TRKeyShape interpretation S g st)
    (hRngLen : (g.σ rngIdx 32).length = 32) :
    let (st1, _) := trDhRatchetState st pk rngIdx
    TRKeyShape interpretation S g
      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } := by
  obtain ⟨hdhs, hcks, hmy, hpeer⟩ := hks
  dsimp only [trDhRatchetState]
  refine ⟨?_, ?_, hmy, hpeer⟩
  · rw [gamma_randTerm32]; exact hRngLen
  · exact length_gamma_createChain_snd_tr interpretation S g
      (createChain st.rk pk st.dhs).1 pk (randTerm rngIdx 32)

theorem nodup_and_lt_of_dhRatchetStep_tr
    {C : Crypto} {their : PublicKey} {coins : BitVec 256} {counter : BitVec 32}
    {ck ck_adv ck_next : ChainKey} {r1 r_adv r2 : RatchetState}
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hFind : (ratchetStateOf s.state).findReceiverChainKey their = .ok none)
    (hDh : Mut.exec (RatchetState.dhRatchetStep C their coins) (ratchetStateOf s.state) = (.ok ck, r1))
    (hNotLt : ¬ (counter < ck.index))
    (hAdv :
      Mut.exec (RatchetState.advanceChain C.F their counter (counter - ck.index).toNat ck) r1 =
        (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey C.F = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2))
    (hs' : s'.state.receiverChains = r2.receiverChains)
    (hwf : RecordChainsWF3 (sessionToRecordRec s)) :
    RecordChainsWF3 (sessionToRecordRec s') := by
  apply recordChainsWF3_of_chainsWFm
  rw [hs']
  exact chainsWFm_ratchet hFind hDh hNotLt hAdv hNext hSet (chainsWFm_of_recordChainsWF3 hwf)

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
