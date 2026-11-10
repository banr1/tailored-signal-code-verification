/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptRecRelPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.OooRpkPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedFreshPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBobHistPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecCanonPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecRelT1Pure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecSizePure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPureB
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach

/-!
# `PureCRel` Preservation for Pre-Key Accept

Proves `rpk_accept_cRel_ps` and `rpk_accept_cRel`, showing that `PureCRel` holds after Bob accepts a
fresh pre-key message `[.recv b, .rng d, .accept pt]` without a collision, with or without archived
previous session bytes `ps`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure.RpkCli
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement (u32Field bytesField msgField chainBytes)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)

private def rpkRel_sessionFieldsBytes (s : SessionRec) : HwBytes :=
  u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
    bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
    u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
    s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
    ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
    u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId ++
    bytesField 13 s.aliceBaseKey ++
    ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
    bytesField 15 s.pqRatchetState

private theorem rpkRel_recordBytes_eq_fields (rr : RecordRec) :
    recordBytes rr =
      msgField 1 (rpkRel_sessionFieldsBytes rr.current) ++ rr.previous.flatMap (msgField 2) :=
  rfl

private theorem rpkRel_state_eq {rr₀ : RecordRec} (h0 : rr₀.previous = []) {smNs : HwBytes}
    (hN : smNs = recordBytes rr₀) (ps : List HwBytes) :
    smNs ++ ps.flatMap (msgField 2) = recordBytes { rr₀ with previous := ps } := by
  rw [hN, rpkRel_recordBytes_eq_fields, rpkRel_recordBytes_eq_fields, h0]; simp

private theorem rpkRel_record_current {pf : PreKeyFields} {smN : StateAndMessage}
    (hBin : RpkAcceptBin pf smN) (hlenA : (pf.baseKey.take 33).length = 33) :
    ∃ rr₀ : RecordRec, smN.state = recordBytes rr₀ ∧ rr₀.previous = [] ∧
      rr₀.current.aliceBaseKey = pf.baseKey.take 33 ∧
      rr₀.current.pendingKyberPreKey = none := by
  obtain ⟨st', f248, regIdB, hscope, hinv, hclamp, hsm⟩ := hBin.record
  obtain ⟨rr₀, hsm₀, hprev₀, hcur₀, -, hkyb₀⟩ :=
    recvPrekey_accept_record hscope hinv hlenA hclamp hsm
  exact ⟨rr₀, hsm₀, hprev₀, by rw [hcur₀]; rfl, hkyb₀⟩

private theorem rpkRel_current_fields {pf : PreKeyFields} {smN : StateAndMessage}
    (hBin : RpkAcceptBin pf smN) (hlenA : (pf.baseKey.take 33).length = 33)
    (ps : List HwBytes) {rr : RecordRec}
    (hrr : smN.state ++ ps.flatMap (msgField 2) = recordBytes rr) :
    rr.current.aliceBaseKey = pf.baseKey.take 33 ∧ rr.current.pendingKyberPreKey = none := by
  obtain ⟨rr₀, hN, h0, hbk₀, hkyb₀⟩ := rpkRel_record_current hBin hlenA
  rw [rpkRel_state_eq h0 hN ps] at hrr
  have hcur : TR.normPendingS rr.current = TR.normPendingS rr₀.current :=
    congrArg RecordRec.current (TR.recordBytes_injective hrr.symm)
  have hbk : rr.current.aliceBaseKey = rr₀.current.aliceBaseKey := by
    simpa [TR.normPendingS] using congrArg SessionRec.aliceBaseKey hcur
  have hkyb : (rr.current.pendingKyberPreKey.map fun p => (p.1 ++ p.2, ([] : HwBytes))) = none := by
    have h := congrArg SessionRec.pendingKyberPreKey hcur
    simp only [TR.normPendingS] at h; rw [h, hkyb₀]; rfl
  refine ⟨hbk.trans hbk₀, ?_⟩
  cases hk : rr.current.pendingKyberPreKey with
  | none => rfl
  | some _ => rw [hk] at hkyb; simp at hkyb

theorem rpk_accept_cRel_ps {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc : List MachineEvent}
    {b : HwBytes} {sm smN : StateAndMessage} {pf : PreKeyFields} {d ct_wire pt : HwBytes}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hA : RpkAcceptHypsPure interpretation r S who ok records sent accepted opkUsed acc b sm pf d ct_wire pt)
    (hBin : RpkAcceptBin pf smN) (hTie : AcceptD.AcceptTieD interpretation r pf d pt smN)
    (ps : List HwBytes) (hst : sm.state = smN.state ++ ps.flatMap (msgField 2))
    (hcol : ¬ CollisionAt interpretation r S who ok (acc ++ [.recv b, .rng d, .accept pt])) :
    PureCRel interpretation r S who ok
      (fun q => if q = r.bob then some sm.state else records q)
      sent
      (accepted ++ [pf.baseKey.take 33])
      (acc ++ [.recv b, .rng d, .accept pt]) := by
  have hrel := hA.ready.2.1
  have hlenA : (pf.baseKey.take 33).length = 33 := by
    have h := hA.contract.baseKey_ok.1; simp only [List.length_drop] at h; omega
  obtain ⟨rr₀, hN₀, h0₀, -, -⟩ := rpkRel_record_current hBin hlenA
  have hooo' : COooAll (fun q => if q = r.bob then some sm.state else records q) := by
    refine cOOO_step_update hrel.oooAll ?_
    rw [hst, rpkRel_state_eq h0₀ hN₀ ps, pqStateOf_recordBytes, ← pqStateOf_recordBytes rr₀, ← hN₀]
    exact AcceptD.newOoo_of_acceptTieD hext.1 hwf hA.contract.baseKey_ok.1 hTie
  have hbka' : BobRecordBaseKeyInAccepted r
      (fun q => if q = r.bob then some sm.state else records q)
      (accepted ++ [pf.baseKey.take 33]) := by
    intro rr hrr; simp only [↓reduceIte, Option.some.injEq] at hrr
    rw [(rpkRel_current_fields hBin hlenA ps (hst ▸ hrr)).1]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hbkn' : PureBobKyberNone r (fun q => if q = r.bob then some sm.state else records q) := by
    intro rr hrr; simp only [↓reduceIte, Option.some.injEq] at hrr
    exact (rpkRel_current_fields hBin hlenA ps (hst ▸ hrr)).2
  have hcanon : smN.state.length < 2 ^ 32 - 2 ^ 20 → TR.PureTRRecordCanon r r.bob smN.state :=
    AcceptD.recCanon_of_acceptTieD hext.1 hwf r.bob hA.contract.baseKey_ok.1 hTie
  have hsmLen : smN.state.length < 2 ^ 64 := by
    have h := hA.state_lt; rw [hst, List.length_append] at h; omega
  obtain ⟨hlen0, hlow0⟩ := rpkBH_senderRatchetKey_len_notLow hext.1 hTie
  have hwho_cs : who[(callStarts acc).length]? = some r.bob := hA.who_cs
  refine ⟨hooo', TR.sendsFit_append hrel.sendsFit (rpk_accept_sendsFit b d pt), hbka', hbkn',
    fun g ms hc => ?_⟩
  have hmp := hc.matched
  obtain ⟨ms₀, δ, rfl, hpre₀, hmatch⟩ :=
    matchedPrefix_split hmp (rpkA2_blockHead b d pt) (matchedPrefix_prefix_reachable hmp)
  have hc₀ : Clean interpretation r S who ok g ms₀ acc := clean_prefix hpre₀.2.2.2.2.2.length_eq hc
  obtain ⟨⟨hrecs₀, ⟨hs₀, hns₀, ha1₀, ha2₀⟩, hch₀, hrole₀⟩, -⟩ := hrel.clean g ms₀ hc₀
  have hB : XplBlock interpretation r S who g ms₀ δ acc [.recv b, .rng d, .accept pt] :=
    ⟨hpre₀, hmp.2.1, hmatch⟩
  have hdf := rpk_deltaFaithful_of_roleFaithful rfl hB hmp.2.2.1 hwho_cs
  have hrole' := rpk_roleSnapshots_accept hwf hB hdf hrole₀
  obtain ⟨pre, m, post, rfl, hpre, ⟨_, _, hacc⟩, hpost⟩ :=
    xplInv_rpk hB hdf (rpkA2_blockShape b d pt)
  have hnodec := rpk_noDecrypt_of_pathFaithful hA.contract.parse hA.fresh hB hpre hpost
    hmp.2.2.2.1 ⟨hs₀, hns₀, ha1₀, ha2₀⟩
  have hbs : BobStartBy r.bob m := (hacc (rpkA2_blockAccept b d pt)).resolve_right hnodec
  have hbob : ∀ a kh regA mh pqIdx spqrMsgIdx shown,
      m = .bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown →
      ∃ w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob a kh regA mh pqIdx spqrMsgIdx,
        RpkRecRel interpretation S g (runTraceMoves r ((ms₀ ++ pre) ++ [m])) r.bob (rpkR_finalSt w)
          smN.state ∧
        TR.TRKeyShape interpretation S g (rpkR_finalSt w) ∧
        gamma interpretation S g w.msg.ratchetKey = pf.inner.senderRatchetKey.bytes.toList := by
    intro a kh regA mh pqIdx spqrMsgIdx shown hm
    subst hm
    have ha : a = r.alice := rpk_peer_eq_of_peerFaithful hmp.2.1.2.2.2.2.2.1
    subst ha
    obtain ⟨_, ⟨w⟩⟩ := rpkT_bobStart_block hB hpre
    have hrep := rpk_rep_of_readFaithful hB hpre hpost w hmp.2.2.2.2.1
    have hkm := rpk_not_kyberMismatch_of_not_collisionAt hc.1 hB hpre hA.contract.parse hA.fresh
      ⟨hs₀, hns₀, ha1₀, ha2₀⟩ hrep hcol
    have hG := rpkT1_glue_of_rep hext.1 hwf hSeq hA.contract.parse hA.contract.d_len
      hA.contract.opk_ok hkm hB hpre w hrep
      (rpk_skipped_fresh hB hpre w ha2₀ hA.contract.parse (hA.fresh pf hA.contract.parse))
    have hrecRel := rpkT1_of_glue hext.1 hTie hsmLen shown hG
    have hdhs : (gamma interpretation S g (randTerm (runTraceMoves r (ms₀ ++ pre)).length 32)).length = 32 := by
      rw [(rpkT1_rng_eq hB hpre).2]; exact hA.contract.d_len
    have hks : TR.TRKeyShape interpretation S g (rpkR_finalSt w) := by
      refine ⟨hdhs, ?_, ?_, ?_⟩
      · dsimp only [rpkR_finalSt, bobRatchetedSt]
        unfold DY.Libsignal.TripleRatchet.createChain DY.X25519.agree DY.Libsignal.TripleRatchet.kdfRk DY.Libsignal.TripleRatchet.hkdfBlock1 DY.Libsignal.TripleRatchet.hkdfBlock2
        dsimp only; rw [TR.gamma_hmac]; exact TR.length_hmacWith _ _ _
      · dsimp only [rpkR_finalSt, bobRatchetedSt]; rw [TR.gamma_serializedIk]; rfl
      · dsimp only [rpkR_finalSt, bobRatchetedSt]; rw [TR.gamma_serializedIk]; rfl
    have hrk_eq : gamma interpretation S g w.msg.ratchetKey =
        pf.inner.senderRatchetKey.bytes.toList := by
      rw [hG.their]
      exact (Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hG.pkLen).symm
    exact ⟨w, hrecRel, hks, hrk_eq⟩
  have htieRec : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre ++ [m])
      (fun q => if q = r.bob then some smN.state else none) :=
    rpkR_pureTieRec_reduce hbs hcanon fun a kh regA mh pqIdx spqrMsgIdx shown hm => by
      obtain ⟨w, hrr, hks, -⟩ := hbob a kh regA mh pqIdx spqrMsgIdx shown hm
      exact ⟨w, hrr, hks⟩
  have hch_step : TR.CHistStep.CHist interpretation r S g (ms₀ ++ pre ++ [m]) := by
    have hch_pre := XplQuiet.quiet_cHist (b2_quietPre hpre) hch₀
    cases m with
    | bobStart p a kh regA mh pqIdx spqrMsgIdx shown =>
      have hp_bob : p = r.bob := hbs; subst hp_bob
      obtain ⟨w, ⟨rec', _, hrel', _, hnd', -⟩, -, hrk_eq⟩ := hbob a kh regA mh pqIdx spqrMsgIdx shown rfl
      have ha : a = r.alice := rpk_peer_eq_of_peerFaithful hmp.2.1.2.2.2.2.2.1; subst ha
      exact rpkBH_cHist_bobStart shown w hch_pre hrel' hnd'
        (by rw [hrk_eq]; exact hlen0) (by rw [hrk_eq]; exact hlow0)
    | _ => exact False.elim hbs
  have hch' := XplQuiet.quiet_cHist (b2_quietPost hpost) hch_step
  obtain ⟨ek, hek, hγ⟩ := rpkT_tie_baseKey hA.contract.parse hB hpre hbs
  have hkeys : bobDoneBaseKeys (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) =
      bobDoneBaseKeys (runTraceMoves r ms₀) ++ [ek] := by
    rw [XplQuiet.quiet_bobDoneBaseKeys (b2_quietPost hpost), hek,
      XplQuiet.quiet_bobDoneBaseKeys (b2_quietPre hpre)]
  have hns' : TR.TRNsBound r (ms₀ ++ (pre ++ m :: post)) sent :=
    rpkA2_nsBound hB hpre hpost hbs hns₀
  have hbks' : BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ (pre ++ m :: post))
      (fun q => if q = r.bob then some sm.state else records q) := by
    intro rr hrr; simp only [↓reduceIte, Option.some.injEq] at hrr
    rw [(rpkRel_current_fields hBin hlenA ps (hst ▸ hrr)).1]
    exact bks_bobStart hwf hA.contract.parse hB hpre hpost hbs hrole'
  refine ⟨⟨fun p bs hpb => ?_, ⟨?_, hns', ?_, ?_⟩, ⟨hch', hrole'⟩⟩, hbks'⟩
  · by_cases hp : p = r.bob
    · subst hp; simp only [ite_true, Option.some.injEq] at hpb; subst hpb
      refine ⟨Or.inr rfl, ?_, ?_⟩
      · rw [hst]; intro h
        obtain ⟨_, _, _, _, _, _, hstN⟩ := hBin.record
        exact b2_encodeRecord_ne_nil _ (hstN ▸ (List.append_eq_nil_iff.1 h).1)
      · rw [hst]
        have hN_rel : PureCRecRel interpretation r S g (ms₀ ++ (pre ++ m :: post)) r.bob smN.state :=
          XplQuiet.quiet_pureCRecRel (b2_quietPost hpost) (Or.inl htieRec)
        cases ps with
        | nil => simp only [List.flatMap_nil, List.append_nil]; exact Or.inl hN_rel
        | cons x xs =>
          rw [rpkRel_state_eq h0₀ hN₀ (x :: xs)]
          exact Or.inr (rpk_pureCPrevRel_append (hN₀ ▸ hN_rel) h0₀ (List.cons_ne_nil x xs))
    · simp only [hp, ite_false] at hpb
      obtain ⟨hmem, hne, hcr⟩ := hrecs₀ p bs hpb
      exact ⟨hmem, hne, rpk_pureCRecRelH_mono (fun _ => rpkA2_frame hwf hB hpre hpost hbs hp) hcr⟩
  · rw [hs₀, rpkA2_sentBodies]
  · rw [hkeys]; intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · obtain ⟨ek', hmem, rfl⟩ := ha1₀ k hk
      exact ⟨ek', List.mem_append_left _ hmem, rfl⟩
    · rw [List.mem_singleton] at hk
      exact ⟨ek, List.mem_append_right _ (List.mem_singleton_self _), hk.trans hγ.symm⟩
  · rw [hkeys]; intro ek' hek'
    rcases List.mem_append.1 hek' with hm | hm
    · exact List.mem_append_left _ (ha2₀ ek' hm)
    · rw [List.mem_singleton] at hm; subst hm; rw [hγ]
      exact List.mem_append_right _ (List.mem_singleton_self _)

theorem rpk_accept_cRel {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc : List MachineEvent}
    {b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields} {d ct_wire pt : HwBytes}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hA : RpkAcceptHypsPure interpretation r S who ok records sent accepted opkUsed acc b sm pf d ct_wire pt)
    (hBin : RpkAcceptBin pf sm) (hTie : AcceptD.AcceptTieD interpretation r pf d pt sm)
    (hcol : ¬ CollisionAt interpretation r S who ok (acc ++ [.recv b, .rng d, .accept pt])) :
    PureCRel interpretation r S who ok
      (fun q => if q = r.bob then some sm.state else records q)
      sent
      (accepted ++ [pf.baseKey.take 33])
      (acc ++ [.recv b, .rng d, .accept pt]) :=
  rpk_accept_cRel_ps hext hwf hSeq hA hBin hTie [] (by simp) hcol

end Symbolic.Swarm.CREF.CliPure
