/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Trials -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepMacTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.NotOpaqueMac
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac

/-!
# Case Split on Received Triple Ratchet MACs

Proves `g1a_case_split`: under `¬RecvCollision` at a received representation `t₀`, either the
receiver's seed `mkSeed` is attacker-known, or `msg₀.mac = Trunc.trunc8 inp₀` where `inp₀` is
either an honest send's `hmac` (`G1bHonestSendCaseB3`) or attacker-known (`G1cOwnKeyCaseB3`), in
each case matching the receiver's `hmac` shape under an honest salt.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys trHonestWireMsg)

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (computeMac hmac)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvDecStep

/-! ## MAC `trunc8` inversion -/

/-- Valid preimages of an attacker-known `Trunc.trunc8 inp` on a reachable trace `T`: either `inp`
is attacker-known or `inp` is an honest send's `hmac`. -/
def TruncInputValidC (T : ExecTrace) (inp : DY.Bytes) : Prop :=
  inp.AttackerKnows T ∨
  ∃ (pqSalt seed myIk peerIk a : DY.Bytes) (ns pn : UInt32) (m pqMsg : DY.Bytes),
    inp = hmac (trMsgKeys pqSalt seed).macKey
      (Concat.concat myIk (Concat.concat peerIk
        (trHonestWireMsg (dhPk a) ns pn
          (SymEnc.symEnc (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv m) pqMsg)))

theorem macKdfSafe_c_trunc8_inv (r₀ : ProtocolSetup) (ms : List Move) (inp₀ : DY.Bytes)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hknows : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms)) :
    TruncInputValidC (runTraceMoves r₀ ms) inp₀ :=
  macKdfSafe_tr_trunc8_inv r₀ ms inp₀ hreach hknows

/-! ## Branch definitions -/

/-- Existence of an honest salt `salt₁ ∈ honestSalts r₀ ms` whose `(cipherKey, macKey, iv)` triple
on `mkSeed` agrees with `k_own` under `gamma` and at which `AuthenticDecryptRep` holds. -/
def AuthenticDecryptRepB3_g1
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes) (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed k_own : DY.Bytes) : Prop :=
  ∃ salt₁ ∈ honestSalts r₀ ms,
    ((gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey =
      gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ mkSeed).macKey =
      gamma interpretation S g (trMsgKeys k_own mkSeed).macKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv =
      gamma interpretation S g (trMsgKeys k_own mkSeed).iv)) ∧
    AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed salt₁

/-- Honest-send MAC branch: `msg₀.mac = Trunc.trunc8 inp₀` where `inp₀` is an honest `hmac` over
`trHonestWireMsg` whose shape matches the receiver's `hmac` under an honest salt matching `k_own`
on `mkSeed`. -/
def G1bHonestSendCaseB3
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed k_own : DY.Bytes) : Prop :=
  ∃ (salt₁ : DY.Bytes),
    salt₁ ∈ honestSalts r₀ ms ∧
    ((gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey =
      gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ mkSeed).macKey =
      gamma interpretation S g (trMsgKeys k_own mkSeed).macKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv =
      gamma interpretation S g (trMsgKeys k_own mkSeed).iv)) ∧
    ∃ (pqSalt_s seed_s myIk_s peerIk_s a_s m_s pqMsg_s : DY.Bytes) (ns_s pn_s : UInt32),
      let wire_s := trHonestWireMsg (dhPk a_s) ns_s pn_s
        (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
      let inp₀ := hmac (trMsgKeys pqSalt_s seed_s).macKey
        (Concat.concat myIk_s (Concat.concat peerIk_s wire_s))
      msg₀.mac = Trunc.trunc8 inp₀ ∧
      (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms) ∧
      (gamma' interpretation S g inp₀).shape =
        (gamma' interpretation S g
          (hmac (trMsgKeys salt₁ mkSeed).macKey
            (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire)))).shape

/-- Attacker-known MAC-input branch: `msg₀.mac = Trunc.trunc8 inp₀` with `inp₀` attacker-known and
shape-matching the receiver's `hmac` under an honest salt matching `k_own` on `mkSeed`. -/
def G1cOwnKeyCaseB3
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed k_own : DY.Bytes) : Prop :=
  ∃ (salt₁ inp₀ : DY.Bytes),
    salt₁ ∈ honestSalts r₀ ms ∧
    ((gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey =
      gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ mkSeed).macKey =
      gamma interpretation S g (trMsgKeys k_own mkSeed).macKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv =
      gamma interpretation S g (trMsgKeys k_own mkSeed).iv)) ∧
    msg₀.mac = Trunc.trunc8 inp₀ ∧
    inp₀.AttackerKnows (runTraceMoves r₀ ms) ∧
    (gamma' interpretation S g inp₀).shape =
      (gamma' interpretation S g
        (hmac (trMsgKeys salt₁ mkSeed).macKey
          (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg₀.wire)))).shape

/-! ## Helper lemmas for `parseTrSignalMsg`, `recvSeed`, and `trMsgKeys` -/

unseal DY.Bytes in
private instance subKdf0CS (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance subTrunc0CS (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_trunc8_cs (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (x : DY.Bytes) :
    gamma interpretation S g (Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold Trunc.trunc8 gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]
  rfl

private theorem gamma_kdfExtract_cs (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) :
    gamma interpretation S g (KdfExtract.kdfExtract salt ikm) =
      CryptoGames.HMAC.hmacWith
        (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
        (gamma interpretation S g salt) (gamma interpretation S g ikm) := by
  unfold KdfExtract.kdfExtract gamma gamma'
  show ((({salt := salt, ikm := ikm} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]
  rfl

theorem attackerKnows_mac_of_parseTrSignalMsg
    {tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : t.AttackerKnows tr)
    (hparse : parseTrSignalMsg t = some msg) :
    msg.mac.AttackerKnows tr := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  obtain ⟨⟨wire, mac⟩, hsp, f, _hwf, rfl⟩ := hparse
  dsimp only
  have hkn := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht
  rw [hsp] at hkn
  exact hkn.2

theorem gamma_computeMac_congr_macKey
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (mk₁ mk₂ peerIk myIk wire : DY.Bytes)
    (hmk : gamma interpretation S g mk₁ = gamma interpretation S g mk₂) :
    gamma interpretation S g (computeMac mk₁ peerIk myIk wire) =
      gamma interpretation S g (computeMac mk₂ peerIk myIk wire) := by
  unfold computeMac hmac
  rw [gamma_trunc8_cs, gamma_trunc8_cs, gamma_kdfExtract_cs, gamma_kdfExtract_cs, hmk]

/-! ## Consequences of `¬RecvCollision` -/

theorem not_memoCollisionOn_of_not_recvCollision
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀) :
    ¬MemoCollisionOn interpretation r₀ S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (runTraceMoves r₀ ms) (runVis r₀ ms)
      (t₀ :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀).flatMap
        (trialTerms (honestSalts r₀ ms) msg₀)) [] := by
  intro h
  apply hNotCol
  unfold RecvCollision
  rw [hparse₀]
  exact Or.inl h

theorem not_ownSaltMacCollision_of_not_recvCollision
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀) :
    ¬MacTagForgeryOrCollision interpretation S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (honestSalts r₀ ms) msg₀
      (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg₀) := by
  intro h
  apply hNotCol
  unfold RecvCollision
  rw [hparse₀]
  exact Or.inr h

private theorem exists_trialCtx_of_recvSeed
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) {st₀ : TRState} {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hst₀ : st₀ ∈ availableStates r₀ tr)
    (hseed : recvSeed st₀ msg₀ = some mkSeed) :
    ∃ ctx ∈ whisperTrials interpretation r₀ S g tr msg₀,
      ctx.peerIk = st₀.peerIk ∧ ctx.myIk = st₀.myIk ∧
      ctx.ownSalts = ownKeys r₀ tr st₀ msg₀ ∧ ctx.seed? = some mkSeed := by
  unfold recvSeed at hseed
  split at hseed
  · next hver =>
    split at hseed
    · cases hseed
    · next c fresh hrc =>
      simp only [Option.map_eq_some_iff] at hseed
      obtain ⟨⟨s, c'⟩, hcmk, rfl⟩ := hseed
      exact ⟨_, Symbolic.Swarm.CREF.Stage1Trials.whisperTrials_mem_of_recvChainFor_some
        hver hst₀ hrc hcmk, rfl, rfl, rfl, rfl⟩
  · cases hseed

/-! ## Main case split -/

/-- Under `¬RecvCollision` at the representation `t₀`, either `mkSeed` is attacker-known, or
`msg₀.mac` is the `trunc8` of an honest send's `hmac` or of an attacker-known term, in each case
shape-matching the receiver's `hmac` under an honest salt whose key triple on `mkSeed` matches
`k_own`. -/
theorem g1a_case_split
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
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
    obtain ⟨ctx, hctx, hpeer, hmy, hsalts, hctx_seed⟩ :=
      exists_trialCtx_of_recvSeed interpretation r₀ S g (runTraceMoves r₀ ms) hst₀ hseed
    have hk_ctx : k_own ∈ ctx.ownSalts := hsalts ▸ hk_own
    have hmac_ctx : gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey ctx.peerIk ctx.myIk msg₀.wire) =
      gamma interpretation S g msg₀.mac := by
      rw [hpeer, hmy, ← hMacBytes, hmac₀_gamma]
    obtain ⟨salt₁, hsalt₁, hTripleEq⟩ :=
      Symbolic.Swarm.CREF.Stage1Trials.exists_honestSalt_of_not_ownSaltMacCollision
        hctx hctx_seed hk_ctx hSeedKnows hmac_ctx hNotOwn
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
      g1_noSelfMemo_len8_of_notSpqrHeaded interpretation r₀ S g ms b t₀ msg₀
        ht₀ hparse₀ hns_mac hno hNotMemo st₀ hst₀ salt₁ hsalt₁ mkSeed hseed (Or.inl hpt_mac) hMacEq
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

end Symbolic.Swarm.CREF.TR.G1
