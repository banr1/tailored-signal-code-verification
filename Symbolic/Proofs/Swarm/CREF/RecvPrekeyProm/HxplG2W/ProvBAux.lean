/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.CaseSplit
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.KdfExtract
import Symbolic.Specifications.Model.EquationalTheory.Trunc
public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepMacTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.NotOpaqueMac
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Skipped-Seed Case Split and HMAC KDF Inversion Helpers

Proves the skipped-seed case split `g1a_case_split_skippedSeed` (and its MAC shape helper
`noSelfMemo_skipped`) under `¬ RecvCollision`, together with the three-stage KDF shape inversion
`hmac_wire_attackerKnows_inv_memo_kdf` for seeds of the form `kdfExtract ck₁ (litByte 0x01)`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg trMsgKeys computeMac
  hmac messageVersion lit litByte)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR.G1

private theorem memo_mem_of_kdfExtract_left_pba (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g a).memo) :
    e ∈ (gamma' i S g (KdfExtract.kdfExtract a b)).memo := by
  unfold gamma'
  show e ∈ (((({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec
    (concretizeAll i S g))).memo
  rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ he)

private theorem memo_mem_of_kdfExtract_right_pba (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g b).memo) :
    e ∈ (gamma' i S g (KdfExtract.kdfExtract a b)).memo := by
  unfold gamma' at he ⊢
  rw [show KdfExtract.kdfExtract a b =
        ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  simp [concretizeKdf, node, he]

private theorem memo_mem_of_parse_mac_pba (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg} {inp₀ : DY.Bytes}
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hmac₀ : msg₀.mac = Trunc.trunc8 inp₀)
    {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g inp₀).memo) :
    e ∈ (gamma' i S g t₀).memo := by
  have hcat : t₀ = Concat.concat msg₀.wire msg₀.mac := parseTrSignalMsg_eq_concat hparse₀
  have hin_mac : e ∈ (gamma' i S g msg₀.mac).memo := by
    rw [hmac₀]
    unfold gamma' at he ⊢
    rw [show Trunc.trunc8 inp₀ = ({ input := inp₀ } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
        DY.Bytes.rec_eq concretizeTrunc (concretizeAll i S g)]
    simp [concretizeTrunc, node, he]
  rw [hcat]
  exact memo_rhs_subset_memo_concat i S g msg₀.wire msg₀.mac hin_mac

theorem noSelfMemo_skipped
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hver₀ : msg₀.version = messageVersion)
    (hns : notSpqrHeaded msg₀.mac) (hno : notOpaqueHeaded msg₀.mac)
    (hNotMemo : ¬ MemoCollisionOn interpretation r₀ S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (runTraceMoves r₀ ms) (runVis r₀ ms)
      (t₀ :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
        (trialTerms (honestSalts r₀ ms) msg₀)) [])
    (p₀ : Participant) (st₁ : TRState) (hst₁ : st₁ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (salt₁ : DY.Bytes) (hsalt₁ : salt₁ ∈ honestSalts r₀ ms)
    (pk₁ seed₁ : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hfind : (TripleRatchet.findRecvChain st₁.toDRState.recv pk₁).isSome = true)
    (hγ_pk : gamma interpretation S g pk₁ = gamma interpretation S g msg₀.ratchetKey)
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st₁.sessionInfo p₀) pk₁ msg₀.counter seed₁ rIdx srcIdx) skIdx)
    (hpt : msg₀.mac ∉ plaintextTerms (runVis r₀ ms))
    (hMacEq : gamma interpretation S g msg₀.mac =
      gamma interpretation S g
        (computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire)) :
    (gamma' interpretation S g msg₀.mac).shape =
      (gamma' interpretation S g
        (computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire)).shape := by
  by_contra hne
  apply hNotMemo
  unfold MemoCollisionOn
  dsimp only
  let cmac := computeMac (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire
  have ht₀_cat : t₀ = Concat.concat msg₀.wire msg₀.mac := parseTrSignalMsg_eq_concat hparse₀
  have hmac_ne_nil : gamma interpretation S g msg₀.mac ≠ [] := by
    rw [hMacEq]
    exact gamma_computeMac_ne_nil interpretation S g _ _ _ _
  have hmac_mem_mac :
      (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape,
        gamma interpretation S g msg₀.mac) ∈ (gamma' interpretation S g msg₀.mac).memo :=
    self_mem_memo_of_notSpqrHeaded interpretation S g msg₀.mac hmac_ne_nil hns hno
  have hmac_mem_t₀ :
      (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape,
        gamma interpretation S g msg₀.mac) ∈ (gamma' interpretation S g t₀).memo := by
    rw [ht₀_cat]
    exact memo_rhs_subset_memo_concat interpretation S g msg₀.wire msg₀.mac hmac_mem_mac
  have hcmac_mem :
      (cmac, (gamma' interpretation S g cmac).shape, gamma interpretation S g cmac) ∈
        (gamma' interpretation S g cmac).memo :=
    self_mem_memo_computeMac_tr interpretation S g _ _ _ _
  have hcmac_wt : cmac ∈ (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
      (trialTerms (honestSalts r₀ ms) msg₀) :=
    Stage1Trials.computeMac_mem_whisperTrialTerms_of_skippedKeyStored
      hver₀ hst₁ hfind hlog hγ_pk hsalt₁
  have hinj : assumedInjective cmac = true := by
    have hv : (cmac.view? DY.Trunc.Trunc8.SubF).isSome = true := by
      dsimp only [cmac, computeMac, DY.Trunc.trunc8, DY.Trunc.CanTrunc8.trunc8]
      rw [DY.BytesView.view_pack]; rfl
    unfold assumedInjective
    rw [hv]
    simp
  have hcmac_not_pt : cmac ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
    rw [List.append_nil]
    have h := computeMac_not_mem_ptAtoms r₀ ms [] (fun _ h => absurd h List.not_mem_nil)
      (trMsgKeys salt₁ seed₁).macKey st₁.peerIk st₁.myIk msg₀.wire
    rwa [List.append_nil] at h
  let x₁ : DY.Bytes × DY.Bytes × HwBytes :=
    (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape, gamma interpretation S g msg₀.mac)
  let x₂ : DY.Bytes × DY.Bytes × HwBytes :=
    (cmac, (gamma' interpretation S g cmac).shape, gamma interpretation S g cmac)
  let recvTerms := t₀ :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
    (trialTerms (honestSalts r₀ ms) msg₀)
  have hx₁_new : x₁ ∈ recvTerms.flatMap
      (fun u => (gamma' interpretation S g u).memo) := by
    rw [List.mem_flatMap]
    exact ⟨t₀, List.mem_cons_self .., hmac_mem_t₀⟩
  have hx₂_new : x₂ ∈ recvTerms.flatMap
      (fun u => (gamma' interpretation S g u).memo) := by
    rw [List.mem_flatMap]
    exact ⟨cmac, List.mem_cons_of_mem _ hcmac_wt, hcmac_mem⟩
  refine ⟨x₁, hx₁_new, x₂, List.mem_append_right _ hx₂_new,
    hne, Or.inr hinj, ?_, fun h2 => False.elim (hcmac_not_pt h2), hMacEq⟩
  intro h1
  rw [List.append_nil] at h1
  exact False.elim (hpt h1)

/-- Case split for a `SkippedKeyStored` seed `mkSeed` under `¬ RecvCollision`: either the attacker
knows `mkSeed`, or `G1bHonestSendCaseB3` holds, or `G1cOwnKeyCaseB3` holds. -/
theorem g1a_case_split_skippedSeed
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hNotCol : ¬ RecvCollision interpretation r₀ S g ms t₀)
    (p₀ : Participant) (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hfind₀ : (TripleRatchet.findRecvChain st₀.toDRState.recv msg₀.ratchetKey).isSome = true)
    (mkSeed : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p₀) msg₀.ratchetKey msg₀.counter mkSeed rIdx srcIdx) skIdx)
    (k_own : DY.Bytes) (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire)) :
    mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
    G1bHonestSendCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own ∨
    G1cOwnKeyCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own := by
  have hno : notOpaqueHeaded msg₀.mac := notOpaqueHeaded_mac_of_parseTrSignalMsg hparse₀
  have hNotMemo := not_memoCollisionOn_of_not_recvCollision interpretation r₀ S g ms t₀ msg₀
    hparse₀ hNotCol
  have hNotOwn := not_ownSaltMacCollision_of_not_recvCollision interpretation r₀ S g ms t₀ msg₀
    hparse₀ hNotCol
  obtain ⟨hns_mac, hpt_mac⟩ :=
    g1_rep_of_recvRepresentations interpretation r₀ S g ms b t₀ msg₀ ht₀ hparse₀
  by_cases hSeedKnows : mkSeed.AttackerKnows (runTraceMoves r₀ ms)
  · exact Or.inl hSeedKnows
  · have ht₀_knows : t₀.AttackerKnows (runTraceMoves r₀ ms) := ht₀.1
    have hmac₀_gamma : gamma interpretation S g msg₀.mac = b.drop (b.length - 8) :=
      (ht₀.2.2.2 msg₀ hparse₀).2.1
    have hmac₀_knows : msg₀.mac.AttackerKnows (runTraceMoves r₀ ms) :=
      attackerKnows_mac_of_parseTrSignalMsg ht₀_knows hparse₀
    let ctx : TrialCtx :=
      { peerIk := st₀.peerIk, myIk := st₀.myIk, extra := [],
        ownSalts := ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀, seed? := some mkSeed }
    have hctx : ctx ∈ whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀ :=
      Stage1Trials.whisperTrials_mem_of_skippedKeyStored_owner
        hver₀ hst₀ hfind₀ ⟨p₀, rfl⟩ hlog
        (rfl : gamma interpretation S g msg₀.ratchetKey = gamma interpretation S g msg₀.ratchetKey)
    have hmac_ctx : gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey ctx.peerIk ctx.myIk msg₀.wire) =
      gamma interpretation S g msg₀.mac := by
      change gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) =
        gamma interpretation S g msg₀.mac
      rw [← hMacBytes, hmac₀_gamma]
    obtain ⟨salt₁, hsalt₁, hTripleEq⟩ :=
      Stage1Trials.exists_honestSalt_of_not_ownSaltMacCollision
        hctx rfl hk_own hSeedKnows hmac_ctx hNotOwn
    have hmk_eq : gamma interpretation S g (trMsgKeys salt₁ mkSeed).macKey =
        gamma interpretation S g (trMsgKeys k_own mkSeed).macKey := hTripleEq.2.1
    have hcmac_eq : gamma interpretation S g
        (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) =
        gamma interpretation S g
          (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) :=
      gamma_computeMac_congr_macKey interpretation S g _ _ _ _ _ hmk_eq
    have hMacEq : gamma interpretation S g msg₀.mac =
        gamma interpretation S g
          (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) :=
      hmac₀_gamma.trans (hMacBytes.trans hcmac_eq.symm)
    have hShMac : (gamma' interpretation S g msg₀.mac).shape =
        (gamma' interpretation S g
          (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire)).shape :=
      noSelfMemo_skipped interpretation r₀ S g ms t₀ msg₀ hparse₀ hver₀ hns_mac hno hNotMemo
        p₀ st₀ hst₀ salt₁ hsalt₁ msg₀.ratchetKey mkSeed rIdx srcIdx skIdx hfind₀ rfl hlog hpt_mac hMacEq
    let rhsHmac := hmac (trMsgKeys salt₁ mkSeed).macKey
      (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire))
    have hview : DY.Bytes.view? (gamma' interpretation S g msg₀.mac).shape DY.Trunc.Trunc8.SubF =
        some { input := (gamma' interpretation S g rhsHmac).shape } := by
      rw [hShMac]
      unfold computeMac
      rw [shape_trunc8_tr]
      exact DY.BytesView.view_pack (SubF := DY.Trunc.Trunc8.SubF) _
    obtain ⟨inp₀, hmac_eq, hshape_eq⟩ :=
      (view?_trunc8_shape_eq_some_iff interpretation S g msg₀.mac
        (gamma' interpretation S g rhsHmac).shape).mp hview
    have hmac_knows : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms) := by
      rwa [hmac_eq] at hmac₀_knows
    rcases macKdfSafe_c_trunc8_inv r₀ ms inp₀ hreach hmac_knows with
      hinp_knows | ⟨pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, ns_s, pn_s, m_s, pqMsg_s, hinp_eq⟩
    · exact Or.inr (Or.inr ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_knows, hshape_eq⟩)
    · subst hinp_eq
      exact Or.inr (Or.inl ⟨salt₁, hsalt₁, hTripleEq,
        pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s, ns_s, pn_s,
        hmac_eq, hmac_knows, hshape_eq⟩)

/-- Three-stage KDF shape and memo-inclusion inversion for an attacker-known HMAC input over a seed
of the form `KdfExtract.kdfExtract ck₁ (litByte 0x01)`. -/
theorem hmac_wire_attackerKnows_inv_memo_kdf
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (salt₁ seed₁ peerIk myIk inp₀ : DY.Bytes)
    (hseed_kdf : ∃ ck₁ : DY.Bytes, seed₁ = KdfExtract.kdfExtract ck₁ (litByte 0x01))
    (hmac₀ : msg₀.mac = Trunc.trunc8 inp₀)
    (hinp_ak : inp₀.AttackerKnows (runTraceMoves r₀ ms))
    (hsh : (gamma' interpretation S g inp₀).shape =
      (gamma' interpretation S g (hmac (trMsgKeys salt₁ seed₁).macKey
        (Concat.concat peerIk (Concat.concat myIk msg₀.wire)))).shape) :
    ∃ salt₀ seed₀ : DY.Bytes,
      salt₀.AttackerKnows (runTraceMoves r₀ ms) ∧ seed₀.AttackerKnows (runTraceMoves r₀ ms) ∧
      (gamma' interpretation S g salt₀).shape = (gamma' interpretation S g salt₁).shape ∧
      (gamma' interpretation S g seed₀).shape = (gamma' interpretation S g seed₁).shape ∧
      (∀ e ∈ (gamma' interpretation S g (KdfExtract.kdfExtract salt₀ seed₀)).memo,
        e ∈ (gamma' interpretation S g t₀).memo) ∧
      (∀ e ∈ (gamma' interpretation S g seed₀).memo, e ∈ (gamma' interpretation S g t₀).memo) := by
  let T := runTraceMoves r₀ ms
  have hmemo_inp : ∀ e ∈ (gamma' interpretation S g inp₀).memo,
      e ∈ (gamma' interpretation S g t₀).memo :=
    fun _ he => memo_mem_of_parse_mac_pba interpretation S g hparse₀ hmac₀ he
  obtain ⟨x₀, _hsplit, _hx₀, hpack, _hrk_eq, _hct_eq, _hpq_eq⟩ := parseTrSignalMsg_unpack_c hparse₀
  have hpack_wire : msg₀.wire = DY.TrWire.trWireMsg x₀.version x₀.senderRatchetKey
      x₀.counter x₀.previousCounter x₀.ciphertext x₀.pqRatchet x₀.encodingVariation := hpack
  obtain ⟨s₀, i₀, hs₀_sh, hi₀_sh, hinp_eq⟩ := kdfExtract_shape_eq_inv_c interpretation S g hsh
  have hinp_kdf_ak : (KdfExtract.kdfExtract s₀ i₀).AttackerKnows T := hinp_eq ▸ hinp_ak
  rw [shape_concat_tr, shape_concat_tr] at hi₀_sh
  have hs₀_ak : s₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms s₀ i₀ hreach hinp_kdf_ak with
      ⟨hs₀_ak, _⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hs₀_ak
    · rw [h01] at hi₀_sh; unfold litByte at hi₀_sh; rw [shape_literalToBytes] at hi₀_sh
      exact False.elim (literal_ne_concat _ _ _ hi₀_sh)
    · rw [h02] at hi₀_sh; unfold litByte at hi₀_sh; rw [shape_literalToBytes] at hi₀_sh
      exact False.elim (literal_ne_concat _ _ _ hi₀_sh)
    · rw [hwr1, shape_concat_tr] at hi₀_sh
      have h2 := (concat_injective hi₀_sh).2
      unfold litByte at h2; rw [shape_literalToBytes] at h2
      exact False.elim (literal_ne_concat _ _ _ h2)
    · rcases hwr2 with hwr2 | hwr2 | hwr2 <;> {
        rw [hwr2, shape_concat_tr, shape_concat_tr] at hi₀_sh
        have h3 := (concat_injective (concat_injective hi₀_sh).2).2
        unfold litByte at h3; rw [shape_literalToBytes, hpack_wire, shape_trWireMsg_tr] at h3
        exact False.elim (literal_ne_trWireMsg _ _ _ _ _ _ _ _ h3)
      }
  obtain ⟨prk₀, info₂₀, hprk₀_sh, hinfo₂₀_sh, hs₀_eq⟩ :=
    kdfExtract_shape_eq_inv_c interpretation S g hs₀_sh
  have hs₀_kdf_ak : (KdfExtract.kdfExtract prk₀ info₂₀).AttackerKnows T := hs₀_eq ▸ hs₀_ak
  rw [shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
  have hprk₀_ak : prk₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms prk₀ info₂₀ hreach hs₀_kdf_ak with
      ⟨hprk₀_ak, _⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hprk₀_ak
    · rw [h01] at hinfo₂₀_sh; unfold litByte at hinfo₂₀_sh; rw [shape_literalToBytes] at hinfo₂₀_sh
      exact False.elim (literal_ne_concat _ _ _ hinfo₂₀_sh)
    · rw [h02] at hinfo₂₀_sh; unfold litByte at hinfo₂₀_sh; rw [shape_literalToBytes] at hinfo₂₀_sh
      exact False.elim (literal_ne_concat _ _ _ hinfo₂₀_sh)
    · rw [hwr1, shape_concat_tr] at hinfo₂₀_sh
      have h2 := (concat_injective hinfo₂₀_sh).2
      unfold litByte at h2; rw [shape_literalToBytes] at h2
      exact False.elim (literal_ne_concat _ _ _ h2)
    · have hwmk_sh : (gamma' interpretation S g (lit "WhisperMessageKeys")).shape =
          lit "WhisperMessageKeys" :=
        shape_literalToBytes interpretation S g _
      have hpq_sh : (gamma' interpretation S g DY.Libsignal.PQXDH.pqxdhLabel).shape =
          DY.Libsignal.PQXDH.pqxdhLabel :=
        shape_literalToBytes interpretation S g _
      rcases hwr2 with hwr2 | hwr2 | hwr2
      · rw [hwr2, shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
        have h2 := (concat_injective (concat_injective hinfo₂₀_sh).2).1
        have hwr_sh : (gamma' interpretation S g (lit "WhisperRatchet")).shape =
            lit "WhisperRatchet" :=
          shape_literalToBytes interpretation S g _
        rw [hwr_sh, hwmk_sh] at h2
        exact False.elim (lit_whisperRatchet_ne_whisperMessageKeys h2)
      · rw [hwr2, shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
        have h2 := (concat_injective (concat_injective hinfo₂₀_sh).2).1
        rw [hpq_sh, hwmk_sh] at h2
        exact False.elim (pqxdhLabel_ne_whisperMessageKeys h2)
      · rw [hwr2, shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
        have h2 := (concat_injective (concat_injective hinfo₂₀_sh).2).1
        rw [hpq_sh, hwmk_sh] at h2
        exact False.elim (pqxdhLabel_ne_whisperMessageKeys h2)
  obtain ⟨salt₀, seed₀, hsalt₀_sh, hseed₀_sh, hprk₀_eq⟩ :=
    kdfExtract_shape_eq_inv_c interpretation S g hprk₀_sh
  have hprk₀_kdf_ak : (KdfExtract.kdfExtract salt₀ seed₀).AttackerKnows T := hprk₀_eq ▸ hprk₀_ak
  obtain ⟨ck₁, hseed₁_eq⟩ := hseed_kdf
  have hseed₀_sh_kdf : (gamma' interpretation S g seed₀).shape =
      KdfExtract.kdfExtract (gamma' interpretation S g ck₁).shape
        (gamma' interpretation S g (litByte 0x01)).shape := by
    rw [hseed₀_sh, hseed₁_eq, shape_kdfExtract_tr]
  have hsalt_seed_ak : salt₀.AttackerKnows T ∧ seed₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms salt₀ seed₀ hreach hprk₀_kdf_ak with
      hboth | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hboth
    · rw [h01] at hseed₀_sh_kdf; unfold litByte at hseed₀_sh_kdf
      rw [shape_literalToBytes] at hseed₀_sh_kdf
      exact False.elim (literal_ne_kdfExtract _ _ _ hseed₀_sh_kdf)
    · rw [h02] at hseed₀_sh_kdf; unfold litByte at hseed₀_sh_kdf
      rw [shape_literalToBytes] at hseed₀_sh_kdf
      exact False.elim (literal_ne_kdfExtract _ _ _ hseed₀_sh_kdf)
    · rw [hwr1, shape_concat_tr] at hseed₀_sh_kdf
      exact False.elim (concat_ne_kdfExtract _ _ _ _ hseed₀_sh_kdf)
    · rcases hwr2 with hwr2 | hwr2 | hwr2 <;> {
        rw [hwr2, shape_concat_tr] at hseed₀_sh_kdf
        exact False.elim (concat_ne_kdfExtract _ _ _ _ hseed₀_sh_kdf)
      }
  have hmemo_prk : ∀ e ∈ (gamma' interpretation S g (KdfExtract.kdfExtract salt₀ seed₀)).memo,
      e ∈ (gamma' interpretation S g t₀).memo := by
    intro e he
    rw [← hprk₀_eq] at he
    apply hmemo_inp
    rw [hinp_eq, hs₀_eq]
    exact memo_mem_of_kdfExtract_left_pba interpretation S g _ _
      (memo_mem_of_kdfExtract_left_pba interpretation S g _ _ he)
  exact ⟨salt₀, seed₀, hsalt_seed_ak.1, hsalt_seed_ak.2, hsalt₀_sh, hseed₀_sh, hmemo_prk,
    fun e he => hmemo_prk e (memo_mem_of_kdfExtract_right_pba interpretation S g _ _ he)⟩

end Symbolic.Swarm.CREF
