/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPureA
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CHistStepPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyTR
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptFramePure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptRelPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.HistHwPure
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach

/-!
# `PureRcvAcceptCall` Step Obligations and `PureCRel` Assembly

Proves post-call `SpqrOooBounded`, Bob base-key and `PureBobKyberNone` preservation, output
`RecRecvRkOk`, and the combined `PureCRel ∧ COpkRelC` step across an accepting whisper receive
block.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

theorem rcv_recordBytes_ne_nil₂ (rr : RecordRec) : recordBytes rr ≠ [] := by
  intro h
  dsimp only [recordBytes, msgField,
    DY.Libsignal.Refinement.encodeField] at h
  rw [Swarm.Phase0WholeFunctionBridge.paddedVarint_zero_of_lt_128 (by omega : 1 * 8 + 2 < 128)] at h
  nomatch h

theorem rcv_bks_rec_of_same_baseKey {r : ProtocolSetup} {records : Participant → Option HwBytes}
    {p : Participant} {rec st' : HwBytes} {rr₀ rr₁ : RecordRec}
    (hrec : records p = some rec)
    (hrr₀ : rec = recordBytes rr₀)
    (hrr₁ : st' = recordBytes rr₁)
    (hbase : rr₁.current.aliceBaseKey = rr₀.current.aliceBaseKey) :
    ∀ rr, (fun q => if q = p then some st' else records q) r.bob = some (recordBytes rr) →
      ∃ rr_old, records r.bob = some (recordBytes rr_old) ∧
        rr.current.aliceBaseKey = rr_old.current.aliceBaseKey := by
  intro rr hrr
  by_cases hp : r.bob = p
  · simp only [hp, ↓reduceIte, Option.some.injEq] at hrr
    refine ⟨rr₀, by rw [hp, hrec, hrr₀], ?_⟩
    rw [← hbase]
    exact aliceBaseKey_eq_of_recordBytes_eq (hrr.symm.trans hrr₁)
  · simp only [hp, ↓reduceIte] at hrr
    exact ⟨rr, hrr, rfl⟩

variable (interpretation : ExternInterpretation)

theorem rcv_pending_callEnd_of_pureAccept {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r₀ S who ok j p records sent accepted opkUsed acc mid rec body sm) :
    (sm.state.length < 2 ^ 32 - 2 ^ 20 → TR.Pure.TRRecordCanon r₀ p sm.state) ∧
    ∃ (g_rw : RecvWireGhost) (coins : BitVec 256),
      g_rw.who = (if p = r₀.alice then 0 else 1) ∧
      g_rw.wireBytes = wireWhisperTag :: body ∧
      TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess ∧
      ((coins = 0#256 ∧ mid = [] ∧
          Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.recvWireMissFact (cryptoOf' interpretation)
            (Proofs.libsignal.SR.interpW interpretation)
            (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
            g_rw) ∨
        (∃ rngBytes : List (BitVec 8), mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧
          coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
          (∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
            TR.PureRecvEval.pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey = true))) ∧
      (∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
        TR.PureRecvEval.PureDecryptCoinsOk (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey coins) ∧
      TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
        g_rw coins = some (sm.state, sm.message) :=
  ⟨hC.hcanon_out, hC.heval⟩

theorem rcv_oooOK_of_pureAccept {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r S who ok j p records sent accepted opkUsed acc mid rec body sm) :
    SpqrOooBounded (pqStateOf sm.state) := by
  obtain ⟨g, coins, _, _, hrcq, _, _, hev⟩ := hC.heval
  obtain ⟨hooo, hpqlen⟩ := ooo_of_trRecordCanonPend hC.hcanonP hrcq
  obtain ⟨_body, msg, role, _hw, _hm, _hopen, henc⟩ :=
    TR.PureRecvEval.pureEvalRecvWireWithCoinsW_some_inv hev
  rw [TR.PureRecvEval.pqStateOf_eq_of_pureWireRecCanon hC.hwc henc]
  exact Symbolic.Swarm.TRREF.GrowthRecordPure.spqrOooBounded_recvWire_storedSession (cryptoOf' interpretation)
    (Proofs.libsignal.SR.interpW interpretation) interpretation TR.PureRecvEval.pureSerializeRole msg role.peer role
    coins g.sess hooo hpqlen

/-- Preserves `BobRecordBaseKeyInAccepted`, `PureBobKyberNone`, and `aliceBaseKey` across an
accepting `pureEvalRecvWireWithCoinsW` step. -/
theorem bobNewBaseKeyOk_of_whisper_accept_eval {r : ProtocolSetup}
    {p : Participant} {records : Participant → Option HwBytes} {accepted : List HwBytes}
    {rec_in rec_out pt : HwBytes} {g_rw : RecvWireGhost} {coins : BitVec 256}
    (hrec : records p = some rec_in)
    (hrec4 : ∃ rr : RecordRec, rec_in = recordBytes rr ∧ rr.current.sessionVersion = 4#32)
    (hrcq : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec_in g_rw.sess)
    (hwc : TR.Pure.WireRecCanon rec_out)
    (hev : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
      g_rw coins = some (rec_out, pt))
    (hbka₀ : BobRecordBaseKeyInAccepted r records accepted)
    (hbkn₀ : PureBobKyberNone r records) :
    BobRecordBaseKeyInAccepted r (fun q => if q = p then some rec_out else records q) accepted ∧
    PureBobKyberNone r (fun q => if q = p then some rec_out else records q) ∧
    (∀ rr' : RecordRec,
      (fun q => if q = p then some rec_out else records q) r.bob = some (recordBytes rr') →
      ∃ rr : RecordRec, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey) := by
  obtain ⟨rr₀, hrec_rr₀, _⟩ := hrec4
  obtain ⟨rr', hsm_rr', hbk_eq⟩ :=
    rcv_evalRecvWireWithCoinsW_out_recordBytes interpretation hrec_rr₀ hrcq hwc hev
  refine ⟨rcv_bka_of_same_baseKey hrec hrec_rr₀ hsm_rr' hbk_eq hbka₀,
    fun rr hrr => ?_,
    rcv_bks_rec_of_same_baseKey hrec hrec_rr₀ hsm_rr' hbk_eq⟩
  by_cases hbp : r.bob = p
  · subst hbp
    simp only [↓reduceIte, Option.some.injEq] at hrr
    obtain ⟨_body, msg, role, _hw, _hm, _hopen, henc⟩ :=
      TR.PureRecvEval.pureEvalRecvWireWithCoinsW_some_inv hev
    dsimp only at henc
    have ⟨_, hbs_in⟩ := TR.PureRecvEval.recordBytes_sessionToRecordRecPending_of_pureCanonical_Q hrcq
    have hkyb0 : g_rw.sess.pendingKyberPreKey = none :=
      (sessionToRecordRecPending_pendingKyberPreKey_eq_none_iff g_rw.sess).mp
        (hbkn₀ (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) (hbs_in ▸ hrec))
    obtain ⟨_, _, _, _, _, h62, _⟩ := hwc
    rcases storedSession_decryptW_post_hw
        (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
        TR.PureRecvEval.pureSerializeRole msg role.peer role coins g_rw.sess with heq | ⟨_, _, heq, _, _⟩
    · exact pendingKyberPreKey_eq_none_of_encodeRecord_lt henc (by omega)
        ((congrArg (fun s => s.pendingKyberPreKey) heq).trans hkyb0) hrr
    · exact pendingKyberPreKey_eq_none_of_encodeRecord_lt henc (by omega)
        (congrArg (fun s => s.pendingKyberPreKey) heq) hrr
  · simp only [hbp, ↓reduceIte] at hrr
    exact hbkn₀ rr hrr

theorem rcv_bkaOK_of_pureAccept {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r S who ok j p records sent accepted opkUsed acc mid rec body sm) :
    BobRecordBaseKeyInAccepted r (fun q => if q = p then some sm.state else records q) accepted ∧
    PureBobKyberNone r (fun q => if q = p then some sm.state else records q) ∧
    (∀ rr' : RecordRec,
      (fun q => if q = p then some sm.state else records q) r.bob = some (recordBytes rr') →
      ∃ rr : RecordRec, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey) := by
  obtain ⟨g_rw, coins, _, _, hrcq, _, _, hev⟩ := hC.heval
  exact bobNewBaseKeyOk_of_whisper_accept_eval interpretation hC.hrec hC.hrec4 hrcq hC.hwc hev
    hC.hrel.bka hC.hrel.bkn

theorem rcv_state_ne_nil_of_pureAccept {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r S who ok j p records sent accepted opkUsed acc mid rec body sm) :
    sm.state ≠ [] := by
  obtain ⟨rr₀, hrec_rr₀, _⟩ := hC.hrec4
  obtain ⟨g_rw, coins, _, _, hrcq, _, _, hev⟩ := hC.heval
  obtain ⟨rr', hsm_rr', _⟩ :=
    rcv_evalRecvWireWithCoinsW_out_recordBytes interpretation hrec_rr₀ hrcq hC.hwc hev
  rw [hsm_rr']
  exact rcv_recordBytes_ne_nil₂ rr'

/-- From `PureRcvAcceptCall`, `CHist`, and `PureCRecRel`, any `RecordRec` decoding `sm.state`
satisfies `RecRecvRkOk`. -/
theorem rcv_recRecvRkOk_of_pureAccept
    (hEq : ExternCryptoLawsHold interpretation) {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    {g₀ : Ghost} {ms₀ : List Move}
    (hC : PureRcvAcceptCall interpretation r S who ok j p records sent accepted opkUsed acc mid rec body sm)
    (hch₀ : CHist interpretation r S g₀ ms₀)
    (hcr₀ : PureCRecRel interpretation r S g₀ ms₀ p rec) :
    ∀ rec' : RecordRec, sm.state = recordBytes rec' → TR.CHistStep.RecRecvRkOk rec' := by
  obtain ⟨rr₀, hrec_rr₀, _, hok₀⟩ := rcv_recRecvRkOk_entry_of_cRecRel hch₀ hcr₀
  obtain ⟨g_rw, coins, _, _, hrcq, _, _, hev⟩ := hC.heval
  exact recRecvRkOk_of_evalRecvWireWithCoinsW interpretation hEq
    (fun _ b => b) (fun _ b => b)
    (Proofs.libsignal.SR.interpW interpretation)
    (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
    hrec_rr₀ hok₀ hrcq hC.hwc hev

/-- Assembles `PureCRel` and `COpkRelC` across an accepting whisper block `rcvAccBlk body mid sm`. -/
theorem rcv_accept_pureCRel_of_parts {r : ProtocolSetup} (_hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hopk : COpkRelC interpretation r S who ok opkUsed acc)
    (hwho : who[j]? = some p) (hj : (callStarts acc).length = j)
    (hp : p = r.alice ∨ p = r.bob) (hrec : records p = some rec) (hss : SingleSession rec)
    (hmid : mid = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid = [.rng rb])
    (hooo' : SpqrOooBounded (pqStateOf sm.state))
    (hbka' : BobRecordBaseKeyInAccepted r (fun q => if q = p then some sm.state else records q) accepted ∧
      PureBobKyberNone r (fun q => if q = p then some sm.state else records q) ∧
      ∀ rr' : RecordRec,
        (fun q => if q = p then some sm.state else records q) r.bob = some (recordBytes rr') →
        ∃ rr : RecordRec, records r.bob = some (recordBytes rr) ∧
          rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (hnew : ∀ g ms₀ δ,
      CleanBy interpretation r S who ok g (ms₀ ++ δ) (acc ++ rcvAccBlk body mid sm) →
      XplBlock interpretation r S who g ms₀ δ acc (rcvAccBlk body mid sm) →
      OneMove (RecvStep p (rcvAccBlk body mid sm)) (runTraceMoves r ms₀) δ →
      CHistBy interpretation r S g ms₀ → PureCRecRel interpretation r S g ms₀ p rec →
      TR.TRNsBound r ms₀ sent →
      sm.state ≠ [] ∧ PureCRecRel interpretation r S g (ms₀ ++ δ) p sm.state ∧
        TR.TRNsBound r (ms₀ ++ δ) sent)
    (hhist : ∀ g ms₀ δ,
      CleanBy interpretation r S who ok g (ms₀ ++ δ) (acc ++ rcvAccBlk body mid sm) →
      XplBlock interpretation r S who g ms₀ δ acc (rcvAccBlk body mid sm) →
      OneMove (RecvStep p (rcvAccBlk body mid sm)) (runTraceMoves r ms₀) δ →
      CHistBy interpretation r S g ms₀ → PureCRecRel interpretation r S g ms₀ p rec →
      TR.TRNsBound r ms₀ sent → PureCRecRel interpretation r S g (ms₀ ++ δ) p sm.state →
      CHist interpretation r S g (ms₀ ++ δ)) :
    PureCRel interpretation r S who ok
        (fun q => if q = p then some sm.state else records q) sent accepted
        (acc ++ rcvAccBlk body mid sm) ∧
      COpkRelC interpretation r S who ok opkUsed (acc ++ rcvAccBlk body mid sm) := by
  have hwho_cs : who[(callStarts acc).length]? = some p := by rw [hj, hwho]
  have hhead : ∀ e ∈ (rcvAccBlk body mid sm).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [rcvAccBlk, List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hmid_kinds : ∀ e ∈ mid ++ [MachineEvent.accept sm.message],
      eventKind e = .rng ∨ eventKind e = .accept := rcv_accMid_kinds hmid
  have hshape : RecvBlockShape (rcvAccBlk body mid sm) := rcv_accBlk_shape hmid
  refine ⟨{
    oooAll := cOOO_step_update hrel.oooAll hooo'
    sendsFit := rcv_blk_sendsFit_pure hrel.sendsFit hmid_kinds
    bka := hbka'.1
    bkn := hbka'.2.1
    clean := fun g ms hc_ext => ?_
  }, ?_⟩
  · have hmp := hc_ext.matched
    obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ :=
      matchedPrefix_split hmp hhead (matchedPrefix_prefix_reachable hmp)
    have hc₀ : Clean interpretation r S who ok g ms₀ acc :=
      clean_prefix hpre.2.2.2.2.2.length_eq hc_ext
    obtain ⟨⟨hrecs₀, hbook₀, hch₀, hrole₀⟩, hbks₀⟩ := hrel.clean g ms₀ hc₀
    have hB : XplBlock interpretation r S who g ms₀ δ acc (rcvAccBlk body mid sm) :=
      ⟨hpre, hmp.2.1, hmatch⟩
    have hdf : DeltaFaithful p (runTraceMoves r ms₀) δ :=
      rcv_deltaFaithful_of_roleFaithful interpretation hB hshape hc_ext.matched.2.2.1 hwho_cs
    have h1 : OneMove (RecvStep p (rcvAccBlk body mid sm)) (runTraceMoves r ms₀) δ :=
      xplInv_recv hB hdf hshape
    obtain ⟨_, _, hrrH₀⟩ := hrecs₀ p rec hrec
    have hrr₀ := pureCRecRelH_single hrrH₀ hss
    obtain ⟨hst, hrel', hns'⟩ := hnew g ms₀ δ hc_ext hB h1 ⟨hch₀, hrole₀⟩ hrr₀ hbook₀.2.1
    refine ⟨⟨fun q b hb => ?_, rcv_book h1 hmid_kinds hbook₀ hns',
      hhist g ms₀ δ hc_ext hB h1 ⟨hch₀, hrole₀⟩ hrr₀ hbook₀.2.1 hrel',
      by
        rw [TR.runTrace_append]
        exact roleSnapshots_of_oneMove (fun _ _ hm h0 => roleSnapshots_of_recvMove hm.2.1 h0) h1 hrole₀⟩,
      bks_xplBlock_recv hB hdf hshape hbka'.2.2 hbks₀⟩
    by_cases hq : q = p
    · subst hq
      simp only [↓reduceIte, Option.some.injEq] at hb
      subst hb
      exact ⟨hp, hst, Or.inl hrel'⟩
    · simp only [hq, ↓reduceIte] at hb
      obtain ⟨hq', hb', hrq⟩ := hrecs₀ q b hb
      exact ⟨hq', hb', pureCRecRelH_mono (fun _ => rcv_frame_other h1 hq) hrq⟩
  · refine cOpkRelC_of_no_opkNamed_recv hopk id
      (fun e he => .inl (by cases he; rfl))
      (fun _ _ hmp => matchedPrefix_prefix_reachable hmp) ?_
    intro b hb
    have hb_eq : b = wireWhisperTag :: body := by
      rcases hmid with rfl | ⟨rb, _, rfl⟩ <;>
        simp [rcvAccBlk, List.mem_cons] at hb <;> exact hb
    subst hb_eq
    exact not_opkNamed_true_of_parsePreKeyWire_none rfl

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
