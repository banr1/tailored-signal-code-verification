/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Concrete Byte-Level State Agreement and `gamma` Step Congruence

Defines `SpqrStateAgree` and `StateBytesAgree` and proves concrete byte-level `gamma` congruence
across `aliceStart`, `messageEncrypt`, `bobStart`, and `messageDecrypt` under `evictedI0`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.PQXDH (serializedIk pqxdhKdf pqxdhIkm agree)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg kdfCk createChain setRecvChain trMsgKeys computeMac trHonestWireMsg
   spqrA2B spqrB2A messageVersion)
open DY.Libsignal.Refinement (aesCbcEncryptSymbol canonicalVariation)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost gamma gamma' concretizeAll
   concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey
   concretizeSpqrSendMsg concretizeSpqrRecvState
   trWireBytes spqrKeyBytes clamp)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encSig encMsg aliceOut aliceOutOpt aliceSt bobSt0 ratchetState)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t4 t4_length ikA ikB spkB pqskB dhsA o1 keys1 stA0)
open Symbolic.Swarm.CREF.TR
  (gamma_lit gamma_concat gamma_hmac gamma_dhPk
   gamma_kemEncap_fst gamma_kemEncap_snd gamma_spqrChainKey gamma_serializedIk
   gamma_trMsgKeys_cipherKey gamma_trMsgKeys_iv gamma_trMsgKeys_macKey gamma_computeMac
   gamma_agree gamma_pqxdhIkm gamma_pqxdhKdf gamma_createChain_snd gamma_kdfCk_fst gamma_kdfCk_snd
   gamma_hkdfBlock1 gamma_whisperRatchet gamma_spqrParams_a2b gamma_spqrIdx)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound (ms_pack_trWire ms_pack_sym)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedI0_cryptoEquationsHold)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (coins1Clean coins2Clean stB3Clean bobStartSpqrKey0 bytesToLiteral_spqrSendMsg)

theorem gamma_spqrInitE (S : OpaqueSymbolSemantics) (g : Ghost) (a p : Bytes) :
    gamma evictedI0 S g (DY.Spqr.spqrInit a p) =
      S.init (gamma evictedI0 S g a) (gamma evictedI0 S g p) := by
  unfold gamma gamma' DY.Spqr.spqrInit
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll evictedI0 S g)]; rfl

theorem gamma_spqrSendStateE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma evictedI0 S g (({ st, coins := c } : DY.Spqr.SendState.SubF Bytes).pack) =
      S.sendState (gamma evictedI0 S g st) (gamma evictedI0 S g c) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll evictedI0 S g)]; rfl

theorem gamma_spqrSendKeyE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma evictedI0 S g (({ st, coins := c } : DY.Spqr.SendKey.SubF Bytes).pack) =
      spqrKeyBytes (S.sendKey (gamma evictedI0 S g st) (gamma evictedI0 S g c)) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll evictedI0 S g)]; rfl

theorem gamma_spqrSendMsgE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma evictedI0 S g (({ st, coins := c } : DY.Spqr.SendMsg.SubF Bytes).pack) =
      S.sendMsg (gamma evictedI0 S g st) (gamma evictedI0 S g c) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll evictedI0 S g)]; rfl

theorem gamma_spqrRecvStateE (S : OpaqueSymbolSemantics) (g : Ghost) (st m : Bytes) :
    gamma evictedI0 S g (({ st, msg := m } : DY.Spqr.RecvState.SubF Bytes).pack) =
      S.recvState (gamma evictedI0 S g st) (gamma evictedI0 S g m) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll evictedI0 S g)]; rfl

theorem gamma_symEncE (S : OpaqueSymbolSemantics) (g : Ghost) (k iv m : Bytes) :
    gamma evictedI0 S g (DY.SymEnc.symEnc k iv m) =
      (evictedI0 aesCbcEncryptSymbol
        [gamma evictedI0 S g m, gamma evictedI0 S g k, (gamma evictedI0 S g iv).take 16]).getD [] := by
  unfold gamma
  have hpack : DY.SymEnc.symEnc k iv m =
      (({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF Bytes).pack) := rfl
  rw [hpack, ms_pack_sym evictedI0 S g ⟨k, iv, m⟩]; rfl

theorem gamma_trHonestWireMsgE (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk : Bytes) (ns pn : UInt32) (ct pq : Bytes) :
    let w := trHonestWireMsg rk ns pn ct pq
    gamma evictedI0 S g w =
      trWireBytes (g.addr w) canonicalVariation
        { version := 4, ratchetKey := gamma evictedI0 S g rk,
          counter := ns.toNat, previousCounter := pn.toNat,
          ciphertext := gamma evictedI0 S g ct }
        (gamma evictedI0 S g pq) := by
  intro w
  have hpack : w =
      (({ version := messageVersion, senderRatchetKey := rk, counter := ns,
          previousCounter := pn, ciphertext := ct, pqRatchet := pq,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) := rfl
  unfold gamma
  rw [hpack, ms_pack_trWire evictedI0 S g ⟨messageVersion, rk, ns, pn, ct, pq, canonicalVariation⟩]
  rfl

/-- Byte-level `gamma` agreement between SPQR state terms under `g` and `g'`, tracking whether both
are initial `spqrInit` terms or both are post-step terms (`view? = none`). -/
def SpqrStateAgree (S : OpaqueSymbolSemantics) (g g' : Ghost) (spqr spqr' : Bytes) : Prop :=
  gamma evictedI0 S g spqr = gamma evictedI0 S g' spqr' ∧
    ((∃ k k' p, spqr = DY.Spqr.spqrInit k p ∧ spqr' = DY.Spqr.spqrInit k' p ∧
        gamma evictedI0 S g k = gamma evictedI0 S g' k' ∧
        gamma evictedI0 S g p = gamma evictedI0 S g' p) ∨
     (spqr.view? DY.Spqr.InitState.SubF = none ∧ spqr'.view? DY.Spqr.InitState.SubF = none))

/-- Concrete byte-level `gamma` agreement between two `TRState` snapshots under `g` and `g'` on
identity keys, root/sending chain keys, DH secret, SPQR state, and sending counters. -/
structure StateBytesAgree (S : OpaqueSymbolSemantics) (g g' : Ghost)
    (st st' : TRState) : Prop where
  myIk_eq : gamma evictedI0 S g st.myIk = gamma evictedI0 S g' st'.myIk
  peerIk_eq : gamma evictedI0 S g st.peerIk = gamma evictedI0 S g' st'.peerIk
  rk_eq : gamma evictedI0 S g st.rk = gamma evictedI0 S g' st'.rk
  cks_eq : gamma evictedI0 S g st.cks = gamma evictedI0 S g' st'.cks
  dhs_eq : gamma evictedI0 S g st.dhs = gamma evictedI0 S g' st'.dhs
  spqr_agree : SpqrStateAgree S g g' st.spqr st'.spqr
  ns_eq : st.ns = st'.ns
  pn_eq : st.pn = st'.pn

theorem spqrStateAgree_init {S : OpaqueSymbolSemantics} {g g' : Ghost} {k k' : Bytes} (p : Bytes)
    (hk : gamma evictedI0 S g k = gamma evictedI0 S g' k')
    (hp : gamma evictedI0 S g p = gamma evictedI0 S g' p) :
    SpqrStateAgree S g g' (DY.Spqr.spqrInit k p) (DY.Spqr.spqrInit k' p) := by
  refine ⟨?_, Or.inl ⟨k, k', p, rfl, rfl, hk, hp⟩⟩
  rw [gamma_spqrInitE, gamma_spqrInitE, hk, hp]

theorem spqrSend_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {spqr spqr' c c' : Bytes}
    (hsp : SpqrStateAgree S g g' spqr spqr')
    (hc : gamma evictedI0 S g c = gamma evictedI0 S g' c') :
    SpqrStateAgree S g g' (DY.Spqr.spqrSend spqr c).1 (DY.Spqr.spqrSend spqr' c').1 ∧
    gamma evictedI0 S g (DY.Spqr.spqrSend spqr c).2.1 =
      gamma evictedI0 S g' (DY.Spqr.spqrSend spqr' c').2.1 ∧
    gamma evictedI0 S g (DY.Spqr.spqrSend spqr c).2.2 =
      gamma evictedI0 S g' (DY.Spqr.spqrSend spqr' c').2.2 := by
  have hst1 : gamma evictedI0 S g (DY.Spqr.spqrSend spqr c).1 =
      gamma evictedI0 S g' (DY.Spqr.spqrSend spqr' c').1 := by
    unfold DY.Spqr.spqrSend
    rw [gamma_spqrSendStateE, gamma_spqrSendStateE, hsp.1, hc]
  have hmsg : gamma evictedI0 S g (DY.Spqr.spqrSend spqr c).2.2 =
      gamma evictedI0 S g' (DY.Spqr.spqrSend spqr' c').2.2 := by
    unfold DY.Spqr.spqrSend
    rw [gamma_spqrSendMsgE, gamma_spqrSendMsgE, hsp.1, hc]
  have hnone1 : (DY.Spqr.spqrSend spqr c).1.view? DY.Spqr.InitState.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr, coins := c } : DY.Spqr.SendState.SubF Bytes)
  have hnone2 : (DY.Spqr.spqrSend spqr' c').1.view? DY.Spqr.InitState.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr', coins := c' } : DY.Spqr.SendState.SubF Bytes)
  refine ⟨⟨hst1, Or.inr ⟨hnone1, hnone2⟩⟩, ?_, hmsg⟩
  rcases hsp.2 with ⟨k, k', p, rfl, rfl, hk, hp⟩ | ⟨hn1, hn2⟩
  · unfold DY.Spqr.spqrSend DY.Spqr.spqrInit
    rw [DY.BytesView.view_pack, DY.BytesView.view_pack]
    dsimp only
    rw [gamma_spqrChainKey, gamma_spqrChainKey, hk, hp, gamma_spqrIdx, gamma_spqrIdx]
  · unfold DY.Spqr.spqrSend
    rw [hn1, hn2]
    dsimp only
    rw [gamma_spqrSendKeyE, gamma_spqrSendKeyE, hsp.1, hc]

theorem spqrRecv_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {spqr spqr' msg msg' spqrOut key spqrOut' key' : Bytes} {idx idx' : UInt32}
    (hsp : SpqrStateAgree S g g' spqr spqr')
    (hmsg : gamma evictedI0 S g msg = gamma evictedI0 S g' msg')
    (hr1 : DY.Spqr.spqrRecv spqr msg idx = some (spqrOut, key))
    (hr2 : DY.Spqr.spqrRecv spqr' msg' idx' = some (spqrOut', key')) :
    SpqrStateAgree S g g' spqrOut spqrOut' := by
  have hout1 : spqrOut = ({ st := spqr, msg } : DY.Spqr.RecvState.SubF Bytes).pack := by
    unfold DY.Spqr.spqrRecv at hr1
    split at hr1
    · cases hr1
    · dsimp only at hr1
      split at hr1
      · split at hr1
        · injection hr1 with hp; exact (congrArg Prod.fst hp).symm
        · cases hr1
      · injection hr1 with hp; exact (congrArg Prod.fst hp).symm
  have hout2 : spqrOut' = ({ st := spqr', msg := msg' } : DY.Spqr.RecvState.SubF Bytes).pack := by
    unfold DY.Spqr.spqrRecv at hr2
    split at hr2
    · cases hr2
    · dsimp only at hr2
      split at hr2
      · split at hr2
        · injection hr2 with hp; exact (congrArg Prod.fst hp).symm
        · cases hr2
      · injection hr2 with hp; exact (congrArg Prod.fst hp).symm
  subst hout1; subst hout2
  refine ⟨?_, Or.inr ⟨
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr, msg } : DY.Spqr.RecvState.SubF Bytes),
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr', msg := msg' } : DY.Spqr.RecvState.SubF Bytes)⟩⟩
  rw [gamma_spqrRecvStateE, gamma_spqrRecvStateE, hsp.1, hmsg]

theorem createChain_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {rk rk' theirPk theirPk' ourSk ourSk' : Bytes}
    (hrk : gamma evictedI0 S g rk = gamma evictedI0 S g' rk')
    (hpk : gamma evictedI0 S g theirPk = gamma evictedI0 S g' theirPk')
    (hsk : gamma evictedI0 S g ourSk = gamma evictedI0 S g' ourSk') :
    gamma evictedI0 S g (createChain rk theirPk ourSk).1 =
      gamma evictedI0 S g' (createChain rk' theirPk' ourSk').1 ∧
    gamma evictedI0 S g (createChain rk theirPk ourSk).2 =
      gamma evictedI0 S g' (createChain rk' theirPk' ourSk').2 := by
  have hEq := evictedI0_cryptoEquationsHold
  refine ⟨?_, ?_⟩
  · have h1a : (createChain rk theirPk ourSk).1 =
        DY.Libsignal.TripleRatchet.hkdfBlock1
          (DY.Libsignal.TripleRatchet.hmac rk (agree theirPk ourSk))
          (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
    have h1b : (createChain rk' theirPk' ourSk').1 =
        DY.Libsignal.TripleRatchet.hkdfBlock1
          (DY.Libsignal.TripleRatchet.hmac rk' (agree theirPk' ourSk'))
          (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
    rw [h1a, h1b, gamma_hkdfBlock1, gamma_hkdfBlock1, gamma_hmac, gamma_hmac,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq,
        gamma_whisperRatchet, gamma_whisperRatchet, hrk, hpk, hsk]
  · rw [gamma_createChain_snd evictedI0 hEq, gamma_createChain_snd evictedI0 hEq, hrk, hpk, hsk]

theorem o1_ek_eq : o1.ek = dhPk (rnd 22 32) := by
  dsimp only [o1, aliceOut, aliceOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
  rw [t4_length]; rfl

theorem o1_ct_eq :
    o1.ct = (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).1 := by
  dsimp only [o1, aliceOut, aliceOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
    DY.Libsignal.PQXDH.aliceAgreement]
  rw [t4_length]; rfl

theorem keys1_eq :
    keys1 = pqxdhKdf (pqxdhIkm (agree (dhPk spkB) ikA)
      (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) := by
  dsimp only [keys1, o1, aliceOut, aliceOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
    DY.Libsignal.PQXDH.aliceAgreement]
  rw [t4_length]; rfl

theorem stateBytesAgree_aliceStart {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {tr : ExecTrace} {ik_a ik_b_pk spk_pk pq_pk dhs_a : Bytes}
    (hikA : gamma evictedI0 S g ik_a = gamma evictedI0 S g' ikA)
    (hikB : gamma evictedI0 S g ik_b_pk = gamma evictedI0 S g' (dhPk ikB))
    (hspk : gamma evictedI0 S g spk_pk = gamma evictedI0 S g' (dhPk spkB))
    (hpq : gamma evictedI0 S g pq_pk = gamma evictedI0 S g' (DY.PQKem.kemPk pqskB))
    (hek : gamma evictedI0 S g (rnd tr.length 32) = gamma evictedI0 S g' (rnd 22 32))
    (he : gamma evictedI0 S g (rnd (tr.length + 1) 32) = gamma evictedI0 S g' (rnd 23 32))
    (hdhs : gamma evictedI0 S g dhs_a = gamma evictedI0 S g' dhsA) :
    let o_ss := aliceOut tr ik_a ik_b_pk spk_pk pq_pk
    gamma evictedI0 S g o_ss.ek = gamma evictedI0 S g' o1.ek ∧
    gamma evictedI0 S g o_ss.ct = gamma evictedI0 S g' o1.ct ∧
    StateBytesAgree S g g' (aliceSt "bob" o_ss dhs_a) stA0 := by
  intro o_ss
  have hEq := evictedI0_cryptoEquationsHold
  have hek_pk : gamma evictedI0 S g o_ss.ek = gamma evictedI0 S g' o1.ek := by
    rw [o1_ek_eq]
    show gamma evictedI0 S g (dhPk (rnd tr.length 32)) = gamma evictedI0 S g' (dhPk (rnd 22 32))
    rw [gamma_dhPk, gamma_dhPk, hek]
  have hct_eq : gamma evictedI0 S g o_ss.ct = gamma evictedI0 S g' o1.ct := by
    rw [o1_ct_eq]
    show gamma evictedI0 S g (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).1 =
      gamma evictedI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).1
    rw [gamma_kemEncap_fst, gamma_kemEncap_fst, hpq, he]
  have hss_eq : gamma evictedI0 S g (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2 =
      gamma evictedI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 := by
    rw [gamma_kemEncap_snd, gamma_kemEncap_snd, hpq, he]
  have hikm : gamma evictedI0 S g
      (pqxdhIkm (agree spk_pk ik_a)
        (agree ik_b_pk (rnd tr.length 32)) (agree spk_pk (rnd tr.length 32)) none
        (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2) =
      gamma evictedI0 S g'
      (pqxdhIkm (agree (dhPk spkB) ikA)
        (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) := by
    rw [gamma_pqxdhIkm, gamma_pqxdhIkm,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq,
        hikA, hikB, hspk, hek, hss_eq]
    rfl
  have hkdf1 := gamma_pqxdhKdf evictedI0 S g
    (pqxdhIkm (agree spk_pk ik_a)
      (agree ik_b_pk (rnd tr.length 32)) (agree spk_pk (rnd tr.length 32)) none
      (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2)
  have hkdf2 := gamma_pqxdhKdf evictedI0 S g'
    (pqxdhIkm (agree (dhPk spkB) ikA)
      (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
  rw [hikm] at hkdf1
  have hrk0 : gamma evictedI0 S g o_ss.keys.rk = gamma evictedI0 S g' keys1.rk := by
    rw [keys1_eq]; exact hkdf1.1.trans hkdf2.1.symm
  have hpqr0 : gamma evictedI0 S g o_ss.keys.pqr = gamma evictedI0 S g' keys1.pqr := by
    rw [keys1_eq]; exact hkdf1.2.2.trans hkdf2.2.2.symm
  have hcc := createChain_gamma_congr hrk0 hspk hdhs
  refine ⟨hek_pk, hct_eq, ?_⟩
  refine ⟨?_, ?_, hcc.1, hcc.2, hdhs, ?_, rfl, rfl⟩
  · show gamma evictedI0 S g (serializedIk (dhPk ik_a)) =
      gamma evictedI0 S g' (serializedIk (dhPk ikA))
    rw [gamma_serializedIk, gamma_serializedIk, gamma_dhPk, gamma_dhPk, hikA]
  · show gamma evictedI0 S g (serializedIk ik_b_pk) =
      gamma evictedI0 S g' (serializedIk (dhPk ikB))
    rw [gamma_serializedIk, gamma_serializedIk, hikB]
  · refine spqrStateAgree_init spqrA2B hpqr0 ?_
    unfold spqrA2B
    rw [gamma_spqrParams_a2b, gamma_spqrParams_a2b]

theorem stateBytesAgree_encrypt {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {st st' : TRState} {coins coins' pt pt' : Bytes}
    (hst : StateBytesAgree S g g' st st')
    (hc : gamma evictedI0 S g coins = gamma evictedI0 S g' coins')
    (hpt : gamma evictedI0 S g pt = gamma evictedI0 S g' pt')
    (haddr : g.addr (encSig st coins (DY.Spqr.spqrSend st.spqr coins).2.1 pt).wire =
             g'.addr (encSig st' coins' (DY.Spqr.spqrSend st'.spqr coins').2.1 pt').wire) :
    StateBytesAgree S g g' (encSt st coins) (encSt st' coins') ∧
    gamma evictedI0 S g (encMsg st coins (DY.Spqr.spqrSend st.spqr coins).2.1 pt) =
      gamma evictedI0 S g' (encMsg st' coins' (DY.Spqr.spqrSend st'.spqr coins').2.1 pt') := by
  obtain ⟨hsp1, hpqKey, hpqMsg⟩ := spqrSend_gamma_congr hst.spqr_agree hc
  have hck1 : gamma evictedI0 S g (kdfCk st.cks).1 = gamma evictedI0 S g' (kdfCk st'.cks).1 := by
    rw [gamma_kdfCk_fst, gamma_kdfCk_fst, hst.cks_eq]
  have hseed : gamma evictedI0 S g (kdfCk st.cks).2 = gamma evictedI0 S g' (kdfCk st'.cks).2 := by
    rw [gamma_kdfCk_snd, gamma_kdfCk_snd, hst.cks_eq]
  have hstNext : StateBytesAgree S g g' (encSt st coins) (encSt st' coins') :=
    ⟨hst.myIk_eq, hst.peerIk_eq, hst.rk_eq, hck1, hst.dhs_eq, hsp1,
     congrArg (· + 1) hst.ns_eq, hst.pn_eq⟩
  refine ⟨hstNext, ?_⟩
  let pq1 := (DY.Spqr.spqrSend st.spqr coins).2.1
  let pq2 := (DY.Spqr.spqrSend st'.spqr coins').2.1
  have hckey : gamma evictedI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).cipherKey =
      gamma evictedI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).cipherKey := by
    rw [gamma_trMsgKeys_cipherKey, gamma_trMsgKeys_cipherKey, hpqKey, hseed]
  have hiv : gamma evictedI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).iv =
      gamma evictedI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).iv := by
    rw [gamma_trMsgKeys_iv, gamma_trMsgKeys_iv, hpqKey, hseed]
  have hmkey : gamma evictedI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).macKey =
      gamma evictedI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).macKey := by
    rw [gamma_trMsgKeys_macKey, gamma_trMsgKeys_macKey, hpqKey, hseed]
  have hct : gamma evictedI0 S g
      (DY.SymEnc.symEnc (trMsgKeys pq1 (kdfCk st.cks).2).cipherKey
        (trMsgKeys pq1 (kdfCk st.cks).2).iv pt) =
      gamma evictedI0 S g'
      (DY.SymEnc.symEnc (trMsgKeys pq2 (kdfCk st'.cks).2).cipherKey
        (trMsgKeys pq2 (kdfCk st'.cks).2).iv pt') := by
    rw [gamma_symEncE, gamma_symEncE, hckey, hiv, hpt]
  have hrk : gamma evictedI0 S g (dhPk st.dhs) = gamma evictedI0 S g' (dhPk st'.dhs) := by
    rw [gamma_dhPk, gamma_dhPk, hst.dhs_eq]
  have hwire : gamma evictedI0 S g (encSig st coins pq1 pt).wire =
      gamma evictedI0 S g' (encSig st' coins' pq2 pt').wire := by
    dsimp only [encSig]
    rw [gamma_trHonestWireMsgE, gamma_trHonestWireMsgE]
    change trWireBytes (g.addr (encSig st coins pq1 pt).wire) canonicalVariation _ _ =
      trWireBytes (g'.addr (encSig st' coins' pq2 pt').wire) canonicalVariation _ _
    rw [haddr, hrk, hst.ns_eq, hst.pn_eq, hct, hpqMsg]
  unfold encMsg
  rw [gamma_concat, gamma_concat]
  change gamma evictedI0 S g (encSig st coins pq1 pt).wire ++
      gamma evictedI0 S g (computeMac (trMsgKeys pq1 (kdfCk st.cks).2).macKey
        st.myIk st.peerIk (encSig st coins pq1 pt).wire) =
    gamma evictedI0 S g' (encSig st' coins' pq2 pt').wire ++
      gamma evictedI0 S g' (computeMac (trMsgKeys pq2 (kdfCk st'.cks).2).macKey
        st'.myIk st'.peerIk (encSig st' coins' pq2 pt').wire)
  rw [gamma_computeMac, gamma_computeMac, hmkey, hst.myIk_eq, hst.peerIk_eq, hwire]

theorem stateBytesAgree_bobStart {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {cls : Nat → Nat}
    {ik_b spk_b ik_a_pk ek_w ss_kem dhs_b pq_msg spqrOut key : Bytes}
    {msg_b : TRSignalMsg} {c' : DY.Libsignal.TripleRatchet.RecvChain} {idx : UInt32}
    (hikB : gamma evictedI0 S g ik_b = gamma evictedI0 S g' ikB)
    (hspkB : gamma evictedI0 S g spk_b = gamma evictedI0 S g' spkB)
    (hikA : gamma evictedI0 S g ik_a_pk = gamma evictedI0 S g' (dhPk ikA))
    (hek : gamma evictedI0 S g ek_w = gamma evictedI0 S g' o1.ek)
    (hss : gamma evictedI0 S g ss_kem =
           gamma evictedI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
    (hrkMsg : gamma evictedI0 S g msg_b.ratchetKey = gamma evictedI0 S g' (dhPk dhsA))
    (hdhsB : gamma evictedI0 S g dhs_b = gamma evictedI0 S g' (rnd 45 32))
    (hpqMsg : gamma evictedI0 S g pq_msg =
              gamma evictedI0 S g' (DY.Spqr.spqrSend (encSt stA0 (coins1Clean cls)).spqr (coins2Clean cls)).2.2)
    (hspRecv : DY.Spqr.spqrRecv
      (DY.Spqr.spqrInit
        (pqxdhKdf (pqxdhIkm (agree ik_a_pk spk_b)
          (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)).pqr spqrB2A)
      pq_msg idx = some (spqrOut, key)) :
    let keys_b := pqxdhKdf (pqxdhIkm (agree ik_a_pk spk_b)
      (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)
    let (stB_r, _) := ratchetState (bobSt0 "alice" ik_b spk_b ik_a_pk keys_b msg_b)
      msg_b.ratchetKey dhs_b
    StateBytesAgree S g g'
      { stB_r with recv := setRecvChain stB_r.recv c', spqr := spqrOut } (stB3Clean cls) := by
  intro keys_b
  have hEq := evictedI0_cryptoEquationsHold
  have hikm : gamma evictedI0 S g
      (pqxdhIkm (agree ik_a_pk spk_b)
        (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem) =
      gamma evictedI0 S g'
      (pqxdhIkm (agree (dhPk spkB) ikA)
        (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) := by
    rw [gamma_pqxdhIkm, gamma_pqxdhIkm,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq,
        gamma_agree evictedI0 hEq, gamma_agree evictedI0 hEq]
    have hc1 := hEq.x25519_agreement_commutes
      (clamp (gamma evictedI0 S g spk_b)) (clamp (gamma evictedI0 S g' ikA))
    have hc2 := hEq.x25519_agreement_commutes
      (clamp (gamma evictedI0 S g ik_b)) (clamp (gamma evictedI0 S g' (rnd 22 32)))
    have hc3 := hEq.x25519_agreement_commutes
      (clamp (gamma evictedI0 S g spk_b)) (clamp (gamma evictedI0 S g' (rnd 22 32)))
    have hek' : gamma evictedI0 S g ek_w = gamma evictedI0 S g' (dhPk (rnd 22 32)) := by
      rwa [o1_ek_eq] at hek
    rw [hikA, hek', gamma_dhPk, gamma_dhPk, hc1, hc2, hc3]
    simp only [Option.map, gamma_dhPk, hikB, hspkB, hss]
  have hkdf1 := gamma_pqxdhKdf evictedI0 S g
    (pqxdhIkm (agree ik_a_pk spk_b)
      (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)
  have hkdf2 := gamma_pqxdhKdf evictedI0 S g'
    (pqxdhIkm (agree (dhPk spkB) ikA)
      (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
  rw [hikm] at hkdf1
  have hrk0 : gamma evictedI0 S g keys_b.rk = gamma evictedI0 S g' keys1.rk := by
    rw [keys1_eq]; exact hkdf1.1.trans hkdf2.1.symm
  have hpqr0 : gamma evictedI0 S g keys_b.pqr = gamma evictedI0 S g' keys1.pqr := by
    rw [keys1_eq]; exact hkdf1.2.2.trans hkdf2.2.2.symm
  have hcc1 := createChain_gamma_congr hrk0 hrkMsg hspkB
  have hcc2 := createChain_gamma_congr hcc1.1 hrkMsg hdhsB
  have hspInit : SpqrStateAgree S g g'
      (DY.Spqr.spqrInit keys_b.pqr spqrB2A) (DY.Spqr.spqrInit keys1.pqr spqrB2A) := by
    refine spqrStateAgree_init spqrB2A hpqr0 ?_
    unfold spqrB2A DY.Spqr.encodeSpqrDirectionParams
    rw [gamma_lit, gamma_lit]
  have hspClean : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys1.pqr spqrB2A)
      (DY.Spqr.spqrSend (encSt stA0 (coins1Clean cls)).spqr (coins2Clean cls)).2.2 2 =
      some ((({ st := DY.Spqr.spqrInit keys1.pqr spqrB2A,
                msg := (DY.Spqr.spqrSend (encSt stA0 (coins1Clean cls)).spqr (coins2Clean cls)).2.2 } :
              DY.Spqr.RecvState.SubF Bytes).pack),
            bobStartSpqrKey0) := by
    unfold DY.Spqr.spqrRecv DY.Spqr.spqrEmptyMsg DY.Spqr.spqrInit spqrB2A
      DY.Spqr.spqrParamsDir? DY.Spqr.encodeSpqrDirectionParams
    rw [bytesToLiteral_spqrSendMsg, DY.BytesView.view_pack]
    dsimp only
    rw [DY.Literal.bytesToLiteral_literalToBytes]
    simp [bobStartSpqrKey0, spqrA2B, DY.Spqr.encodeSpqrDirectionParams,
          DY.Spqr.Direction.toByte, DY.Spqr.Direction.flip]
  have hspOut := spqrRecv_gamma_congr hspInit hpqMsg hspRecv hspClean
  refine ⟨?_, ?_, hcc2.1, hcc2.2, hdhsB, hspOut, rfl, rfl⟩
  · show gamma evictedI0 S g (serializedIk (dhPk ik_b)) =
      gamma evictedI0 S g' (serializedIk (dhPk ikB))
    rw [gamma_serializedIk, gamma_serializedIk, gamma_dhPk, gamma_dhPk, hikB]
  · show gamma evictedI0 S g (serializedIk ik_a_pk) =
      gamma evictedI0 S g' (serializedIk (dhPk ikA))
    rw [gamma_serializedIk, gamma_serializedIk, hikA]

theorem stateBytesAgree_decrypt_ratchet {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {st st' : TRState} {rk_msg rk_msg' dhsNew dhsNew' pq_msg pq_msg' spqrOut key spqrOut' key' : Bytes}
    {c' c'' : DY.Libsignal.TripleRatchet.RecvChain} {idx idx' : UInt32}
    (hst : StateBytesAgree S g g' st st')
    (hrkMsg : gamma evictedI0 S g rk_msg = gamma evictedI0 S g' rk_msg')
    (hdhsNew : gamma evictedI0 S g dhsNew = gamma evictedI0 S g' dhsNew')
    (hpqMsg : gamma evictedI0 S g pq_msg = gamma evictedI0 S g' pq_msg')
    (hr1 : DY.Spqr.spqrRecv st.spqr pq_msg idx = some (spqrOut, key))
    (hr2 : DY.Spqr.spqrRecv st'.spqr pq_msg' idx' = some (spqrOut', key')) :
    let (st_r, _) := ratchetState st rk_msg dhsNew
    let (st'_r, _) := ratchetState st' rk_msg' dhsNew'
    StateBytesAgree S g g'
      { st_r with recv := setRecvChain st_r.recv c', spqr := spqrOut }
      { st'_r with recv := setRecvChain st'_r.recv c'', spqr := spqrOut' } := by
  have hcc1 := createChain_gamma_congr hst.rk_eq hrkMsg hst.dhs_eq
  have hcc2 := createChain_gamma_congr hcc1.1 hrkMsg hdhsNew
  have hspOut := spqrRecv_gamma_congr hst.spqr_agree hpqMsg hr1 hr2
  exact ⟨hst.myIk_eq, hst.peerIk_eq, hcc2.1, hcc2.2, hdhsNew, hspOut, rfl,
         congrArg (fun n => if n = 0 then 0 else n - 1) hst.ns_eq⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
