/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Defs
public import Symbolic.BugInjection.Proofs.Common443.Census443Close
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
public import Symbolic.BugInjection.Proofs.Common443.CompC3Census38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3KdfChild38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances

namespace Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Memo

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle (aliceStartTrOfOut)
open Symbolic.Swarm.COMPOSED.CompTrace (NetMsgAt aliceOut)
open Symbolic.Swarm.CREF.TR.RecvRep (gamma_litOf knows_litOf length_litOf)
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire (aliceVis_dhs_coin single_eq_inv)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (IsKdf)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge (evInit evSend)
open Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Defs

theorem memo_litOf (S : Sem) (g : Ghost) (bs : HwBytes) :
    (gamma' compI0 S g (litOf bs)).memo = [(litOf bs, litOf bs, bs)] := by
  have hγ : (gamma' compI0 S g (litOf bs)).bytes = bs := gamma_litOf compI0 S g bs
  unfold gamma' litOf at hγ ⊢
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S g)] at hγ ⊢
  exact congrArg (fun v => [(_, _, v)]) hγ

theorem assumedInjective_litOf (bs : HwBytes) : assumedInjective (litOf bs) = false := by
  unfold assumedInjective litOf
  simp (disch := decide) only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.view_pack_none,
    Option.map_none, Option.getD_none, Option.isSome_none, Bool.or_self]

theorem spqrHeaded_litOf (bs : HwBytes) : spqrHeaded (litOf bs) = false := by
  unfold spqrHeaded litOf
  simp (disch := decide) only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.view_pack_none,
    Option.isSome_none, Bool.or_self]

theorem zeros8_len : zeros8.length = 8 := by decide

private theorem msg38IrFast_len : msg38IrFast.length < 2 ^ 63 := by decide +kernel

theorem msg38_ir_len : msg38_ir.length < 2 ^ 63 := by
  rw [msg38_ir_eq_fast]
  exact msg38IrFast_len

def xIrMsg (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes :=
  DY.Concat.concat (CompPrefixInvEnc.encWire tr₂ stA cl pq) (litOf zeros8)

def msgIr (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) :
    DY.Libsignal.TripleRatchet.TRSignalMsg :=
  { CompRFaithfulInner.encParsedMsg tr₂ stA cl pq with mac := litOf zeros8 }

def xIr (r : Records) (tr₁ tr₂ : ExecTrace) (cl : Nat) : PreKeyRep :=
  let o := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o
  ⟨o.ek, o.ct, xIrMsg tr₂ stA cl (tr₂.length + 2)⟩

theorem parseTrSignalMsg_xIrMsg (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) :
    DY.Libsignal.TripleRatchet.parseTrSignalMsg (xIrMsg tr₂ stA cl pq) =
      some (msgIr tr₂ stA cl pq) := by
  have hl :
      (DY.Concat.concat (CompPrefixInvEnc.encWire tr₂ stA cl pq) (litOf zeros8)).length -
          DY.Trunc.trunc8Length =
        (CompPrefixInvEnc.encWire tr₂ stA cl pq).length := by
    rw [DY.Concat.length_concat, length_litOf, zeros8_len,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.trunc8Length_eq_8,
      Nat.add_sub_cancel]
  simp only [DY.Libsignal.TripleRatchet.parseTrSignalMsg, xIrMsg, hl, DY.Concat.split_concat]
  simp only [CompPrefixInvEnc.encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg,
    bind, Option.bind, DY.TrWire.trWireMsgFields?_trWireMsg]
  rfl

theorem take_sub_eight_append {a b : HwBytes} (hb : b.length = 8) :
    (a ++ b).take ((a ++ b).length - 8) = a := by
  rw [List.length_append, hb, Nat.add_sub_cancel, List.take_left' rfl]

def InnerFieldsEq (a b : CryptoGames.LibsignalSession.SignalMessage) : Prop :=
  a.ciphertext = b.ciphertext ∧
  a.senderRatchetKey = b.senderRatchetKey ∧
  a.counter = b.counter ∧
  a.messageVersion = b.messageVersion ∧
  a.pqRatchet = b.pqRatchet

def checkWirePairIr (w₀ w₁ : HwBytes) : Bool :=
  match parsePreKeyWire w₀, parsePreKeyWire w₁ with
  | some q₀, some p =>
    decide (p.baseKey = q₀.baseKey) &&
    decide (p.kyberCiphertext = q₀.kyberCiphertext) &&
    decide (p.inner.ciphertext = q₀.inner.ciphertext) &&
    decide (p.inner.senderRatchetKey = q₀.inner.senderRatchetKey) &&
    decide (p.inner.counter = q₀.inner.counter) &&
    decide (p.inner.messageVersion = q₀.inner.messageVersion) &&
    decide (p.inner.pqRatchet = q₀.inner.pqRatchet) &&
    decide (p.message = q₀.message.take (q₀.message.length - 8) ++ zeros8) &&
    decide (p.preKeyId = none) &&
    decide (preKeySpqrIndex p = 1)
  | _, _ => false

private theorem checkWirePairIr_fast :
    checkWirePairIr CompRPlantWire.sentWireFast msg38IrFast = true := by
  decide +kernel

theorem wirePairIr_spec {q₀ p : PreKeyFields}
    (hq₀ : parsePreKeyWire CompRPlantWire.sentWireBytes = some q₀)
    (hp : parsePreKeyWire msg38_ir = some p) :
    p.baseKey = q₀.baseKey ∧
    p.kyberCiphertext = q₀.kyberCiphertext ∧
    InnerFieldsEq p.inner q₀.inner ∧
    p.message = q₀.message.take (q₀.message.length - 8) ++ zeros8 ∧
    p.preKeyId = none ∧
    preKeySpqrIndex p = 1 := by
  have h := checkWirePairIr_fast
  rw [CompRPlantWire.sentWireBytes_eq] at hq₀
  change parsePreKeyWire CompRPlantWire.sentWireFast = some q₀ at hq₀
  rw [msg38_ir_eq_fast] at hp
  unfold checkWirePairIr at h
  rw [hq₀, hp] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
  exact ⟨h1, h2, ⟨h3, h4, h5, h6, h7⟩, h8, h9, h10⟩

private theorem checkOuter_ir_fast :
    CompFitsNames.checkPreKeyOuter Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 msg38IrFast = true := by
  decide +kernel

theorem outer_ir {r : Records} {p : PreKeyFields}
    (hfits : compFits Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hp : parsePreKeyWire msg38_ir = some p) :
    CompRPreKeyWire.PreKeyOuterMatches compI0 r msg38_ir p := by
  refine CompFitsNames.preKeyOuterMatches_of_check hfits hp ?_
  rw [msg38_ir_eq_fast]
  exact checkOuter_ir_fast

theorem attackerKnows_xIrMsg {tr tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat}
    (hk : (CompPrefixInvEnc.encOut tr₂ stA cl pq).AttackerKnows tr) :
    (xIrMsg tr₂ stA cl pq).AttackerKnows tr := by
  have hsp := DY.Concat.attacker_knows_split (CompPrefixInvEnc.encOut tr₂ stA cl pq)
    (CompPrefixInvEnc.encWire tr₂ stA cl pq).length tr hk
  rw [CompPrefixInvEnc.encOut, DY.Concat.split_concat] at hsp
  exact DY.Concat.attacker_knows_concat _ _ tr hsp.1 (knows_litOf zeros8 tr)

theorem faithfulInner_xIrMsg {S : Sem} {g : Ghost} {tr₂ : ExecTrace}
    {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {q₀ p : PreKeyFields}
    (hfi₀ : FaithfulInner compI0 S g (CompPrefixInvEnc.encOut tr₂ stA cl pq) q₀)
    (hinner : InnerFieldsEq p.inner q₀.inner)
    (hpm : p.message = q₀.message.take (q₀.message.length - 8) ++ zeros8) :
    FaithfulInner compI0 S g (xIrMsg tr₂ stA cl pq) p ∧
      p.message = gamma compI0 S g (xIrMsg tr₂ stA cl pq) := by
  obtain ⟨hct_eq, hrk_eq, hcnt_eq, hver_eq, hpq_eq⟩ := hinner
  obtain ⟨m₀, hp₀, hwire₀, _, _, hct₀, hrk₀, hpq₀, hcnt₀, hver₀⟩ := hfi₀
  change DY.Libsignal.TripleRatchet.parseTrSignalMsg (Census443Defs.encOut tr₂ stA cl pq) = some m₀ at hp₀
  rw [CompRFaithfulInner.parseTrSignalMsg_encOut] at hp₀
  injection hp₀ with hm₀_eq; subst hm₀_eq
  have htake : p.message.take (p.message.length - 8) = q₀.message.take (q₀.message.length - 8) := by
    rw [hpm, take_sub_eight_append zeros8_len]
  have hdrop : p.message.drop (p.message.length - 8) = zeros8 := by
    rw [hpm, drop_sub_eight_append zeros8_len]
  have hγmsg : p.message = gamma compI0 S g (xIrMsg tr₂ stA cl pq) := by
    rw [xIrMsg, CompFreshDistinct.gamma_concat_eq, gamma_litOf, hpm]
    have hw : (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).wire =
        CompPrefixInvEnc.encWire tr₂ stA cl pq := rfl
    rw [← hw, hwire₀]
  refine ⟨⟨msgIr tr₂ stA cl pq, parseTrSignalMsg_xIrMsg tr₂ stA cl pq, ?_⟩, hγmsg⟩
  refine ⟨?_, ?_, spqrHeaded_litOf zeros8, ?_, ?_, ?_, ?_, ?_⟩
  · change gamma compI0 S g (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).wire = _
    rw [htake]; exact hwire₀
  · change gamma compI0 S g (litOf zeros8) = _
    rw [gamma_litOf, hdrop]
  · change gamma compI0 S g (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).ciphertext = _
    rw [hct_eq]; exact hct₀
  · change gamma compI0 S g (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).ratchetKey = _
    rw [hrk_eq]; exact hrk₀
  · change gamma compI0 S g (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).pqRatchet = _
    rw [hpq_eq]; exact hpq₀
  · change (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).counter.toNat = _
    rw [hcnt_eq]; exact hcnt₀
  · change (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).version.toNat = _
    rw [hver_eq]; exact hver₀

private theorem ecKey_b0_take33 :
    (ecKey (compLookupPub (clamp CompRX0SS38.b0Bytes))).take 33 =
      ecKey (compLookupPub (clamp CompRX0SS38.b0Bytes)) := by
  decide +kernel

theorem swap_and_mem_ir {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {τ₁ : List MachineEvent} {p q₀ : PreKeyFields}
    {pre mid post : List Move} {m₀ : Move} {me : Participant} {s cl e c' : Nat}
    {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    {stA : DY.Libsignal.TripleRatchet.TRState}
    (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1)
    (htr₂ : tr₂ = (runMoves mid (m₀.next tr₁)).1)
    (hek : NetMsgAt o.ek (tr₁.length + 3) tr₂)
    (hct : NetMsgAt o.ct (tr₁.length + 4) tr₂)
    (hsm : CompRPreKeyWire.SendMatchesMoves compI0 r S g CompRPlantWire.sentWireBytes
      (received tr₂ [e, c'] ++ [CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)]))
    (hns : stA.ns = 0) (hpn : stA.pn = 0)
    (hq₀ : parsePreKeyWire CompRPlantWire.sentWireBytes = some q₀)
    (hcan₀ : CompRFaithfulInner.InnerWireCanonical q₀)
    (hbk₀ : q₀.baseKey = ecKey (gamma compI0 S g o.ek))
    (hkc₀ : q₀.kyberCiphertext = some (kyberKey (gamma compI0 S g o.ct)))
    (hp : parsePreKeyWire msg38_ir = some p)
    (hbk_take : p.baseKey.take 33 = ecKey (gamma compI0 S g o.ek))
    (hout : CompRPreKeyWire.PreKeyOuterMatches compI0 r msg38_ir p)
    (hex : ExplainsMoves compI0 r S who ok g
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post) τ₁)
    (hkek : o.ek.AttackerKnows (runTraceMoves r
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post)))
    (hkct : o.ct.AttackerKnows (runTraceMoves r
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post)))
    (hkmsg : (CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post))) :
    ExplainsMoves compI0 r S who ok g
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) τ₁ ∧
    (⟨o.ek, o.ct, xIrMsg tr₂ stA cl (tr₂.length + 2)⟩ : PreKeyRep) ∈
      preKeyRepresentations compI0 r S g
        (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post)
        msg38_ir := by
  subst htr₁
  have hlen := CompRX0SS38.sentWireBytes_len
  have hγ := CompRX0Mem.hγ_of_sendMatches hsm hlen hq₀ hbk₀ hkc₀
  obtain ⟨_, _, _, _, _, hmsg₀⟩ := CompRX0Mem.sendMatches_append_inv hsm hlen hq₀
  have hfi₀ := CompRFaithfulInner.faithfulInner_of_gamma_encOut S g tr₂ stA cl _ q₀ hns hpn hmsg₀.symm hcan₀
  obtain ⟨_, hkc_p, hinner_p, hpm_p, _, _⟩ := wirePairIr_spec hq₀ hp
  obtain ⟨hfi, hγmsg⟩ := faithfulInner_xIrMsg hfi₀ hinner_p hpm_p
  have hmem := CompRX0Mem.x0_mem_of_parts hkek hkct (attackerKnows_xIrMsg hkmsg)
    hp hbk_take (hkc_p.trans hkc₀) hγmsg hout hfi
  have hk : (pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post)[(pre ++ m₀ :: mid).length]? =
      some (.encrypt me s cl (tr₂.length + 2) (some (e, c'))) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have htake : (pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).take
      (pre ++ m₀ :: mid).length = pre ++ m₀ :: mid := List.take_left
  have hrt : runTraceMoves r (pre ++ m₀ :: mid) = tr₂ := by
    have h := CompPrefixInvStruct.runTrace_append r [] (pre ++ m₀ :: mid)
    rw [List.nil_append] at h; rw [h, htr₂, CompPrefixInvStruct.runMoves_append_fst]; rfl
  have hset : (pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).set
      (pre ++ m₀ :: mid).length
      (.encrypt me s cl (tr₂.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))) =
      pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2)
        (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post := by
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl
  have hγ' :
      (received (runTraceMoves r ((pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).take (pre ++ m₀ :: mid).length)) [e, c']).map (gamma compI0 S g) =
      (received (runTraceMoves r ((pre ++ m₀ :: mid ++ Move.encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post).take (pre ++ m₀ :: mid).length)) [(runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4]).map
        (gamma compI0 S g) := by
    rw [htake, hrt, hγ, CompRX0Assembly.received_pair_of_netMsgAt hek hct]; rfl
  have hex' := CompPrefixInvSwap.explains_set_wrap hk hγ' hex
  have htr_eq := CompPrefixInvSwap.runTrace_set_wrap
    (r := r)
    (w₂ := some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) hk
  rw [hset] at hex' htr_eq
  refine ⟨hex', ?_⟩
  unfold preKeyRepresentations at hmem ⊢
  rw [htr_eq]; exact hmem

theorem split38_decomp_swap_rep_ir {who : List Participant} {ok : Nat → Bool}
    {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex_cli : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire msg38_ir = some p) :
    ∃ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let ms₀ := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
      ms = ms₀ ∧ Compat compI0 r S g ∧ ModelRun r ms₀ ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g)
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) (runVis r ms₀) ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      bobDoneBaseKeys (runTraceMoves r ms₀) = [] ∧
      ExplainsCli compI0 r S who ok σ₁
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms' ∧
      xIr r tr₁ tr₂ cl ∈ preKeyRepresentations compI0 r S g ms' msg38_ir := by
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb_s, hs_s, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by
    rw [hb_s]; exact CompRX0SS38.highBitComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by
    rw [hs_s]; exact CompRX0SS38.highBitComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, hcan₀⟩ := CompRPlantWire.sentWireBytes_innerWireCanonical.1
  obtain ⟨hpbk, _, _, _, _, _⟩ := wirePairIr_spec hq₀ hp
  have hex : ExplainsMoves compI0 r S who ok g ms
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) :=
    ⟨hex_cli.2.1, hex_cli.2.2.1.1⟩
  obtain ⟨pre, a, idS, hb, shown, mid, cl, e, c', post, ikA, tr₁, tr₂, o, stA,
    htr₁, ho, hstA, htr₂, hms, hdisj, hek, hct, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀, hpre, hmid, hpost⟩ :=
    CliCoinSplit.pia_x0_decomp_split hwf.1 hnb hcs hex.1 (by simp [CompRX0SS38.rsT_len])
      CompRX0SS38.rsT_kind CompRX0SS38.bunBytes_getElem4_ne CompRX0SS38.sentWireBytes_head_ne
  have hc : Compat compI0 r S g := hex.1.1
  have hmr : ModelRun r ms := hex.1.2.1
  have hvis := hex.1.2.2.2.2.2
  rcases hdisj with ⟨hidS, ha, hikA⟩ | ⟨hidS, ha, hikA⟩
  · subst hidS ha hikA ho hstA htr₂ htr₁ hms
    rw [hm₀] at hvis₀
    obtain ⟨hγek, hγe⟩ := CompRX0Gamma.aliceVis_rng_coins hvis₀
    have hek_γ := CompRX0Gamma.gamma_iniAliceOut_ek_compI0 (S := S) (g := g)
      (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none hγek
    have hcoins : (CompRX0Gamma.coinHeads (CompRX0SS38.rsT.take 32)).length = 32 := by
      simp [CompRX0Gamma.coinHeads, CompRX0SS38.rsT_len]
    have hct_γ := CompRX0Gamma.gamma_iniAliceOut_ct (i := compI0) (S := S) (g := g)
      (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      (by rw [hγe]; exact hcoins)
    rw [hγe] at hct_γ
    have hbk₀ : q₀.baseKey = ecKey (gamma compI0 S g
        (aliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2)
          (setupPublic r 4) (setupPublic r 6) none).ek) := by
      rw [CompRX0Join.aliceOut_eq_iniAliceOut, hek_γ]
      exact CompRX0SS38.sentWireBytes_baseKey hq₀
    have hkc₀ : q₀.kyberCiphertext = some (kyberKey (gamma compI0 S g
        (aliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2)
          (setupPublic r 4) (setupPublic r 6) none).ct)) := by
      rw [CompRX0Join.aliceOut_eq_iniAliceOut, hct_γ,
        CompRX0SS38.sentWireBytes_kyberCiphertext hq₀, CompRX0SS38.compI0_kyberEncaps_rsT]
    have hbk_take : p.baseKey.take 33 = ecKey (gamma compI0 S g
        (aliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2)
          (setupPublic r 4) (setupPublic r 6) none).ek) := by
      rw [hpbk, CompRX0SS38.sentWireBytes_baseKey hq₀, ecKey_b0_take33,
        CompRX0Join.aliceOut_eq_iniAliceOut, hek_γ]
    obtain ⟨hex', hmem'⟩ := swap_and_mem_ir rfl rfl hek hct hsm rfl rfl hq₀ hcan₀ hbk₀ hkc₀
      hp hbk_take (outer_ir hfits.1 hp) hex hekK hctK hencK
    exact ⟨pre, mid, post, hb, shown, cl, e, c', rfl, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil,
      CliCoinSplitClose.explainsCli_of_explains_mid_encrypt_swap hex_cli hex', hmem'⟩
  · exfalso
    subst hidS ha hikA ho hstA
    obtain ⟨ek', ct', hL, -⟩ := CompRX0Mem.sendMatches_append_inv hsm CompRX0SS38.sentWireBytes_len hq₀
    rw [hL] at hsm
    exact CompRX0Bytes.not_sendMatches_bobSelf hwf.1 hEq hc hs1 hs2 CompRPlantWire.sentWireBytes
      CompRX0SS38.sentWireBytes_hasTag4 tr₁ tr₂ r.bob _ _ ek' ct' cl _ hsm

private theorem mem_memo_ek_sub_variant (S : Sem) (g : Ghost) {k : DY.Bytes}
    (hk : DY.X25519.x25519Key k = k)
    {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g k).memo) :
    x ∈ (gamma' compI0 S g (DY.X25519.x25519TorsionVariant k 1 0)).memo := by
  have hv : DY.X25519.x25519TorsionVariant k 1 0 =
      ({ key := k, variation := 1, torsion := 0 } : DY.X25519.Variant.SubF DY.Bytes).pack := by
    unfold DY.X25519.x25519TorsionVariant
    unfold DY.X25519.x25519Key at hk
    split_ifs with h
    · exfalso; revert h; decide
    · rw [hk]
  rw [hv, CompRPreMemoSound.ms_pack_variant compI0 S g { key := k, variation := 1, torsion := 0 }]
  simp only [gVariant0, concretizeVariant, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons]
  exact Or.inr hx

private theorem mem_memo_xIrMsg_cases (S : Sem) (g : Ghost) (tr₂ : ExecTrace)
    (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat)
    {x : DY.Bytes × DY.Bytes × HwBytes}
    (hx : x ∈ (gamma' compI0 S g (xIrMsg tr₂ stA cl pq)).memo) :
    x ∈ (gamma' compI0 S g (CompPrefixInvEnc.encOut tr₂ stA cl pq)).memo ∨
      (assumedInjective x.1 = false ∧
        (x.2.2 = zeros8 ∨ x.2.2 = gamma compI0 S g (CompPrefixInvEnc.encWire tr₂ stA cl pq) ++ zeros8)) := by
  rcases CompRX0NBSC38Hmc.mem_memo_concat_cases hx with hcat | hw | hz
  · right
    refine ⟨?_, Or.inr ?_⟩
    · rw [hcat]
      exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _
    · rw [(CompRPreMemoSound.memo_sound compI0 S g _ hx).2, hcat,
        CompFreshDistinct.gamma_concat_eq, gamma_litOf]
  · exact Or.inl (CompRX0NBSC38Hmc.mem_memo_concat_left hw)
  · right
    rw [memo_litOf, List.mem_singleton] at hz
    subst hz
    exact ⟨assumedInjective_litOf zeros8, Or.inl rfl⟩

private def checkHighBitIdx1 (b : HwBytes) : Bool :=
  match parsePreKeyWire b with
  | some q => decide (preKeySpqrIndex q = 1)
  | none => false

private theorem checkHighBitIdx1_fast : checkHighBitIdx1 CompRPlantWire.highBitWireFast = true := by
  decide +kernel

private theorem highBitWireBytes_spqrIdx1 {q : PreKeyFields}
    (hq : parsePreKeyWire CompRPlantWire.highBitWireBytes = some q) :
    preKeySpqrIndex q = 1 := by
  have h := checkHighBitIdx1_fast
  rw [CompRPlantWire.highBitWireBytes_eq] at hq
  change parsePreKeyWire CompRPlantWire.highBitWireFast = some q at hq
  unfold checkHighBitIdx1 at h
  rw [hq, decide_eq_true_eq] at h
  exact h

private theorem bobTrials_flatMap_xIr_sub {r : Records} {tr : ExecTrace} {p q_hb : PreKeyFields}
    {tr₁ tr₂ : ExecTrace} {cl : Nat} (salts : List DY.Bytes)
    (hopk : p.preKeyId = none) (hopk_hb : q_hb.preKeyId = none)
    (hidx : preKeySpqrIndex p = preKeySpqrIndex q_hb) :
    let o := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o
    let pq := tr₂.length + 2
    let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek 1 0, o.ct, CompPrefixInvEnc.encOut tr₂ stA cl pq⟩
    (bobTrials r tr p (xIr r tr₁ tr₂ cl) (msgIr tr₂ stA cl pq)).flatMap
        (trialTerms salts (msgIr tr₂ stA cl pq)) ⊆
      bobTerms r salts q_hb x₀ := by
  intro o stA pq x₀
  rcases CompExcuse.bobTrials_eq_nil_or_raw r tr p (xIr r tr₁ tr₂ cl) (msgIr tr₂ stA cl pq) with hnil | hraw
  · rw [hnil]; simp
  · rw [hraw]
    suffices h : (CompExcuse.bobTrialsRaw r p (xIr r tr₁ tr₂ cl) (msgIr tr₂ stA cl pq)).flatMap
        (trialTerms salts (msgIr tr₂ stA cl pq)) = bobTerms r salts q_hb x₀ by
      rw [h]
    rw [← CompExcuse.bobTrialsRaw_flatMap_trialTerms_eq_bobTerms r salts q_hb x₀
      (CompRFaithfulInner.parseTrSignalMsg_encOut tr₂ stA cl pq)]
    unfold CompExcuse.bobTrialsRaw bobKeys bobChain xIr
    dsimp only [x₀, spqrIdx]
    rw [hopk, hopk_hb, hidx]
    simp only [Pure.pure, Bind.bind, Option.bind_some, Option.map_none]
    rw [CompExcuse.agree_torsionVariant_of_ne o.ek (setupSecret r 1) 1 0 (by decide),
      CompExcuse.agree_torsionVariant_of_ne o.ek (setupSecret r 2) 1 0 (by decide)]
    have hrat : (msgIr tr₂ stA cl pq).ratchetKey = (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).ratchetKey := rfl
    have hcnt : (msgIr tr₂ stA cl pq).counter = (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).counter := rfl
    have hpqr : (msgIr tr₂ stA cl pq).pqRatchet = (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).pqRatchet := rfl
    have hw : (msgIr tr₂ stA cl pq).wire = (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).wire := rfl
    have hct : (msgIr tr₂ stA cl pq).ciphertext = (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).ciphertext := rfl
    rw [hrat, hcnt, hpqr]
    rcases DY.Libsignal.TripleRatchet.consumeMessageKey _ (CompRFaithfulInner.encParsedMsg tr₂ stA cl pq).counter with _ | ⟨seed, c'⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, trialTerms]; rfl
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, trialTerms, hw, hct]; rfl

private theorem not_zVal_zeros8 : ¬ CompRNonInj38Census.ZVal zeros8 := by
  rintro (⟨hL, _⟩ | ⟨_, htag | hrow⟩)
  · rw [zeros8_len] at hL; cases hL
  · exact compTag4_ne_zeros4 htag.symm
  · obtain ⟨d, hd, htake⟩ := List.mem_map.mp hrow
    exact rowDigests_take8_ne_zeros8 d hd htake

private theorem not_rv38HB_zeros8 : ¬ CompC3RestFn38HBA.Rv38HB zeros8 := by
  decide +kernel

private theorem restFnEntry_rv38HB_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    {r : Records} {S : Sem} {g : Ghost} {q_hb : PreKeyFields}
    (hfitsP : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hopk : q_hb.preKeyId = none)
    (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let o := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let pq := tr₂.length + 2
    let stA := Census443Defs.iniAliceStartState tr₁ r.bob o
    let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post
    let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post
    let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek 1 0, o.ct, Census443Defs.encOut tr₂ stA cl pq⟩
    Compat compI0 r S g → ModelRun r ms →
    List.Forall₂ (EventMatchesEntry compI0 r S g)
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) (runVis r ms) →
    Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre →
    Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid →
    Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = CompPrefixInvAlice.iniAliceStartTr tr₁ r.alice r.bob o →
    let memo := fun u => (gamma' compI0 S g u).memo
    let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo
    let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') q_hb x₀).flatMap memo
    69 ≤ (gamma compI0 S g (CompPrefixInvEnc.encWire tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl pq)).length ∧
    (gamma compI0 S g (CompPrefixInvEnc.encWire tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl pq)).length ≤ 1400 ∧
    (∀ y ∈ preMemo ++ newMemo,
      CompC2RestFn.RestFnEntry
        (CompC3RestFn38HBA.lookupShape S g (CompC3RestFn38HB.allTerms38 tr₁ tr₂ r.bob o cl))
        CompC3RestFn38HBA.Rv38HB S g y) := by
  intro tr₁ o m₀ tr₂ pq stA ms ms' x₀ hc hmr hvis hpre hmid hpost hm₀ memo preMemo newMemo
  have hfits : compFits Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r :=
    CompFitsNames.compFits_base hfitsP
  have hNe : r.alice ≠ r.bob := hfits.1.1
  have hA : r.alice = "alice" := CompFitsNames.compFits_alice hfitsP
  have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfitsP
  obtain ⟨hvis₀, hm₁⟩ := CompC3RestPre38HB.split38_forall2_vis_inv_split hNe rfl hpre hmid hpost hm₀
    CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind' hvis
  obtain ⟨hb0_s, hcoins, hdhs_s⟩ := aliceVis_dhs_coin CompRX0SS38.rsT_len
    CompC3RestFn38HBA.rsT_drop32 hvis₀
  obtain ⟨q₀, hq₀, _⟩ := CompRPlantWire.sentWireBytes_innerWireCanonical.1
  obtain ⟨hpt_s, hc_in, hmsg⟩ := CompC3RestPre38HB.encVis_split38_pins_split hcs CompRX0SS38.sentWireBytes_len hq₀ hm₁
  obtain ⟨_, ⟨n, hn_le, hcl_iff, hc_eq, _⟩, _⟩ := CliCoinSplit.encVis_of_coinSplit_send hcs hm₁
  have hc_eq' : gamma compI0 S g (randTerm (tr₂.length + 1) cl) = CompRX0SS38.cB.take n := hc_eq
  have h0 : gamma compI0 S g (randTerm 0 32) = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId := by
    rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRWSBobChain.gamma_setupSecret_0 hNe hc, hfits.2.2.2.2.2.2.1]
  have h5 : gamma compI0 S g (randTerm 5 32) = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId := by
    rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.2.2.2.2.2.2.2.1]
  have h10 : gamma compI0 S g (randTerm 10 32) = Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk := by
    rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.2.2.2.2.2.2.2.2.1]
  have h16 : gamma compI0 S g (randTerm 16 64) = fillFresh 16 64 :=
    (CompC3RestFn38HB.gamma_randTerm_16 hNe hc).trans (CompFitsNames.compFits_secretBytes_fresh hfitsP).2.1
  have hb0 : gamma compI0 S g (randTerm tr₁.length 32) = CompRX0SS38.b0Bytes :=
    single_eq_inv hb0_s
  have he0 : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE0 :=
    (CompRX0Gamma.gamma_of_kyberCoins hcoins).trans CompRX0SS38.rsT_coinHeads_eq
  have hdhs : gamma compI0 S g (randTerm (tr₁.length + 2) 32) = CompC3RestFn38HBA.ssDhsBytes :=
    single_eq_inv hdhs_s
  have hpt : gamma compI0 S g (randTerm tr₂.length 32) = CompRX0SS38.ptB :=
    single_eq_inv hpt_s
  have hc_tail : cl ≠ 0 → CompRX0SS38.cB.take n ∈ (List.inits CompRX0SS38.cB).tail :=
    fun hcl => CompC3RestFn38HB.mem_inits_tail_of_take CompRX0SS38.cB (fun hn0 => hcl (hcl_iff.mpr hn0)) hn_le
  obtain ⟨hk, hP, _, _, _, _⟩ := CompC3RestPre38HB.split38_encMac_chain_split (r := r) (S := S) (g := g)
    hNe hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind'
    CompRX0SS38.sentWireBytes_len CompRNbsc38MacKey.wireMacChainOk_sentWire hcs hvis
  have hct : gamma compI0 S g (DY.SymEnc.symEnc
      (CompRNbsc38MacKey.encKeys tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)).cipherKey
      (CompRNbsc38MacKey.encKeys tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)).iv
      (randTerm tr₂.length 32)) = compAesCt0 :=
    CompC3RestFn38HBA.gamma_symEnc_encKeys_hb hk hP hpt
  have hmac_val : gamma compI0 S g
      (CompPrefixInvEnc.encMac tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)) =
      CompC3RestFn38HBA.sentMac8 :=
    (CompRNbsc38VT.gamma_encWire_mac_of_encOut hmsg).2.trans (CompC3RestFn38HBA.sentWireBytes_msgMac8 hq₀)
  have hzmac_val : gamma compI0 S g
      (DY.Trunc.trunc8 (CompRSplit38ZVals.zfullT tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2))) =
      CompC3Nbsc38HB.zfull0SS.take 8 := by
    rw [CompFreshDistinct.gamma_trunc8_eq]
    exact congrArg (fun v => v.take 8) (CompC3Nbsc38HB.split38_zpins_ss_split hNe hpre hmid hpost hm₀ hcs hvis).2
  have hag1 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 h0 CompC3RestFn38HB.hb_dh_comm.1
  have hag2 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h5 hb0 CompC3RestFn38HB.hb_dh_comm.2.1
  have hag3 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hb0 CompC3RestFn38HB.hb_dh_comm.2.2.1
  have hag4 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hdhs CompC3RestFn38HB.hb_dh_comm.2.2.2
  have hkct : gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1 =
      compKyberCt0 := CompC3RestFn38HB.gamma_kemEncap_fst_of_e0 he0
  have hkss : gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 =
      compKyberSs0 := CompC3RestFn38HB.gamma_kemEncap_snd_of_e0 he0
  have hmapR : (CompC3RestFn38HB.rTerms38 tr₁ tr₂ r.bob o cl).map (gamma compI0 S g) =
      CompC3RestFn38HBA.rVals38HBOf (CompRX0SS38.cB.take n) := by
    simp only [CompC3RestFn38HB.rTerms38, CompC3RestFn38HBA.rVals38HBOf, List.map_cons, List.map_nil,
      h0, h5, h10, h16, hb0, he0, hdhs, hpt, hc_eq', hct, hkct, hkss]
  have hmapA : (CompC3RestFn38HB.allTerms38 tr₁ tr₂ r.bob o cl).map (gamma compI0 S g) =
      CompC3RestFn38HBA.allVals38HBOf (CompRX0SS38.cB.take n) := by
    simp only [CompC3RestFn38HB.allTerms38, CompC3RestFn38HBA.allVals38HBOf, List.map_append, hmapR,
      List.map_cons, List.map_nil, CompFreshDistinct.gamma_dhPk_compI0, h0, h5, h10, hb0, hdhs,
      hag1, hag2, hag3, hag4, hmac_val, hzmac_val]
  have hnd : ((CompC3RestFn38HB.allTerms38 tr₁ tr₂ r.bob o cl).map (gamma compI0 S g)).Nodup :=
    hmapA ▸ CompC3RestFn38HBA.allVals38HBOf_nodup (hc_eq ▸ hc_in)
  have hentL : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [he0]; decide +kernel
  have hwL : 69 ≤ (gamma compI0 S g
      (CompPrefixInvEnc.encWire tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl pq)).length := by
    have h1 : gamma compI0 S g
        (CompPrefixInvEnc.encWire tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl pq) =
        q₀.message.take (q₀.message.length - 8) :=
      (CompRNbsc38VT.gamma_encWire_mac_of_encOut hmsg).1
    have h2 := CompC3RestFn38HBA.sentWireBytes_msg_ge77 hq₀
    rw [h1, List.length_take]; omega
  have hwU : (gamma compI0 S g
      (CompPrefixInvEnc.encWire tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl pq)).length ≤ 1400 := by
    have h1 : gamma compI0 S g
        (CompPrefixInvEnc.encWire tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o) cl pq) =
        q₀.message.take (q₀.message.length - 8) :=
      (CompRNbsc38VT.gamma_encWire_mac_of_encOut hmsg).1
    have h2 := CompC3RestFn38HBA.sentWireBytes_msg_le1400 hq₀
    rw [h1, List.length_take]; omega
  have hstA := CompC3RestFn38HB.trStateNRC_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl hentL
  have ho_out := CompC3RestFn38HB.nrcensus_aliceOut (S := S) (g := g) hNe tr₁ tr₂ r.bob o cl hentL
  have henc := CompC3RestFn38HB.nrcensus_enc hstA (CompC3RestFn38HB.nrcensus_encSalt_stA hNe tr₁ tr₂ cl hentL) hwL hwU
  have htr_eq : runTraceMoves r ms = runTraceMoves r ms' :=
    CompRVariantFree38.runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl pq
      (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  have hpost' : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := by
    rwa [CompC3RestFn38HB.encrypt_next_wrap_eq r.alice (tr₁.length + 8) cl pq
      (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4)) tr₂] at hpost
  have hpt_r : CompC3RestFn38HB.FnCensus38 tr₁ tr₂ r.bob o cl S g (randTerm tr₂.length 32) :=
    CompC3RestFn38HB.nrcensus_randTerm38 (by simp only [CompC3RestFn38HB.rTerms38, List.mem_cons, true_or, or_true])
  have hpreTerms : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'),
      CompC3RestFn38HB.FnCensus38 tr₁ tr₂ r.bob o cl S g u := by
    refine CompC3RestFn38HB.nrcensus_prefixTerms (fun v hv hkind u hu_v => ?_) (fun ls hls => ?_)
      (htr_eq ▸ CompC3RestFn38HB.nrcensus_storedSecrets_hb hfitsP hc hmr.2.1 hmr.2.2.1.1) (fun v hv hkind u hu_v => ?_)
    · rcases CompRVariantFree38.send_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v with rfl | rfl | rfl <;>
        [exact ho_out.2.2.2.1; exact ho_out.2.2.2.2.1; exact henc.2.1]
    · rcases CompRX0NBSC38Parts.storedStates_split38_cases rfl hpre hmid hpost' hm₀ hls with hls_eq | hls_eq <;>
        rw [hls_eq] <;>
        [exact CompC3RestFn38HB.nrcensus_serialize_local_tr (Or.inl hA) hstA;
         exact CompC3RestFn38HB.nrcensus_serialize_local_tr (Or.inl hA) (CompC3RestFn38HB.trStateNRC_encSt cl rfl hstA)]
    · rw [CompRX0NBSC38Parts.pt_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v]
      exact hpt_r
  have hek_key : DY.X25519.x25519Key x₀.ek = o.ek :=
    CompRNoBSC.x25519Key_torsionVariant_aliceOut_ek tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none 1 0
  have ho_ek : DY.X25519.x25519Key o.ek = o.ek := CompPlant.x25519Key_dhPk (randTerm tr₁.length 32)
  have hek_val : gamma compI0 S g (DY.X25519.x25519Key o.ek) = CompC3RestFn38HBA.hbEkAPub := by
    rw [ho_ek]
    change gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = CompC3RestFn38HBA.hbEkAPub
    rw [CompFreshDistinct.gamma_dhPk_compI0, hb0]; rfl
  have hnewTerms : ∀ u ∈ [x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') q_hb x₀,
      CompC3RestFn38HB.FnCensus38 tr₁ tr₂ r.bob o cl S g u := by
    have henc_step := CompRVariantFree38.encrypt_next_split38_eq (cl := cl) (some (tr₁.length + 3, tr₁.length + 4)) hm₀ hmid rfl
    have hsalts := CompRNoBSC.honestSalts_split_eq rfl rfl hpre hmid hpost' henc_step
    intro u hu
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
    rcases hu with rfl | rfl | rfl | hu_bob
    · exact CompC3RestFn38HBA.nrcensus_variant_ek 1 0 hek_val (ho_ek.symm ▸ ho_out.2.2.2.1)
    · exact ho_out.2.2.2.2.1
    · exact henc.2.1
    · rw [hsalts] at hu_bob
      have hu_cases := CompRNoBSC.mem_bobTerms_x0_iff (tr₁ := tr₁) (tr₂ := tr₂) (cl := cl) hNe hopk hek_key rfl rfl u hu_bob
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_cases
      rcases hu_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ho_out.2.2.2.2.2.1
      · exact ho_out.2.2.2.2.2.2.1
      · exact ho_out.2.2.2.2.2.2.2
      · exact hstA.cks
      · exact (CompC3RestFn38HB.trStateNRC_encSt cl rfl hstA).cks
      · exact henc.2.2.2.2.1.1
      · exact henc.2.2.2.2.1.2.1
      · exact henc.2.2.2.2.1.2.2
      · exact henc.2.2.1
      · exact hpt_r
      · exact henc.2.2.2.2.2.1
      · exact henc.2.2.2.2.2.2.1
      · exact henc.2.2.2.2.2.2.2
      · exact henc.2.2.2.1
  refine ⟨hwL, hwU, fun y hy => ?_⟩
  rcases List.mem_append.mp hy with hy_pre | hy_new
  · obtain ⟨u, hu, hyu⟩ := List.mem_flatMap.mp hy_pre
    exact CompC3RestFn38HB.restFnEntry_of_fnOK hc_eq' hc_tail hmapR hnd
      (CompRPreMemoSound.memo_sound compI0 S g u hyu).2 (hpreTerms u hu y hyu)
  · obtain ⟨u, hu, hyu⟩ := List.mem_flatMap.mp hy_new
    exact CompC3RestFn38HB.restFnEntry_of_fnOK hc_eq' hc_tail hmapR hnd
      (CompRPreMemoSound.memo_sound compI0 S g u hyu).2 (hnewTerms u hu y hyu)

private theorem not_inj_hb_eq_ir_extra {S : Sem} {g : Ghost} {F : HwBytes → DY.Bytes}
    {y : DY.Bytes × DY.Bytes × HwBytes} {w_bytes : HwBytes}
    (hy_ai : assumedInjective y.1 = true)
    (hy_val : y.2.2 = gamma compI0 S g y.1)
    (hy_re : CompC2Rest38.RestEntry S g y)
    (hy_rfn : CompC2RestFn.RestFnEntry F CompC3RestFn38HBA.Rv38HB S g y)
    (hwL : 69 ≤ w_bytes.length) (hwU : w_bytes.length ≤ 1400)
    (hextra : y.2.2 = zeros8 ∨ y.2.2 = w_bytes ++ zeros8) : False := by
  have hextra_len : y.2.2.length = 8 ∨ (77 ≤ y.2.2.length ∧ y.2.2.length ≤ 1408) := by
    rcases hextra with h | h
    · exact Or.inl (by rw [h, zeros8_len])
    · refine Or.inr ?_
      rw [h, List.length_append, zeros8_len]
      omega
  by_cases hK : IsKdf y.1
  · obtain ⟨k, m, hkdf⟩ := hK
    have hL : y.2.2.length = 32 := by
      rw [hy_val, hkdf]
      exact CompFreshDistinct.gamma_hmac_length S g k m
    rcases hextra_len with h8 | ⟨hge, _⟩ <;> omega
  · by_cases hX : CompRSplit38UntaggedShape.IsX y.1
    · have hL : y.2.2.length = 32 := by
        rw [hy_val]
        rcases hX with ⟨s, hpk⟩ | ⟨pk, sk, hdh⟩
        · rw [hpk]; exact CompFreshDistinct.gamma_dhPk_length S g s
        · rw [hdh]; exact CompFreshDistinct.gamma_dh_pack_length S g pk sk
      rcases hextra_len with h8 | ⟨hge, _⟩ <;> omega
    · by_cases hT : CompRSplit38UntaggedShape.IsTrunc8 y.1
      · have hz := hy_re.2.1 hT
        rcases hextra with hz8 | hmsg
        · rw [hz8] at hz; exact not_zVal_zeros8 hz
        · rcases hz with ⟨hL, _⟩ | ⟨hL, _⟩
          · rcases hextra_len with h8 | ⟨hge, _⟩ <;> omega
          · rcases hextra_len with h8 | ⟨hge, _⟩
            · rw [hmsg, List.length_append, zeros8_len] at h8; omega
            · omega
      · have hrv := hy_rfn.2.1 hy_ai hK hX hT
        rcases hextra with hz8 | hmsg
        · rw [hz8] at hrv; exact not_rv38HB_zeros8 hrv
        · rw [hmsg] at hrv
          exact CompC3RestFn38HBA.not_rv38HB_of_len_gt68
            (by rw [List.length_append, zeros8_len]; omega)
            (by rw [List.length_append, zeros8_len]; omega) hrv

theorem noBsc_ir_cli_swap {who : List Participant} {ok : Nat → Bool} {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire msg38_ir = some p) :
    ∃ (pre mid post : List Move) (hb_eq : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
      ms = pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g ms' msg38_ir,
        ¬ BobStartCollision compI0 r S g ms' p x := by
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, _, hxIr⟩ :=
    split38_decomp_swap_rep_ir hcs r S g ms p hfits hnb hex hp
  obtain ⟨q₀, hq₀, _⟩ := CompRPlantWire.sentWireBytes_innerWireCanonical.1
  obtain ⟨_, _, _, _, hopk, hidx_p⟩ := wirePairIr_spec hq₀ hp
  obtain ⟨q_hb, hq_hb, _⟩ := CompRPlantWire.highBitWireBytes_innerWireCanonical.1
  obtain ⟨hopk_hb, _⟩ := CompRNbsc38VT.highBitWireBytes_hopk_hidx' hq_hb
  let tr₁ := (runMoves pre (setupTrace r)).1
  let o := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let pq := tr₂.length + 2
  let stA := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o
  let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post
  have hm₀_a : m₀.next tr₁ = CompPrefixInvAlice.iniAliceStartTr tr₁ r.alice r.bob o := hm₀
  have hvt := Census443Close.nbsc38At_of_leaves_split
    (CompC3Nbsc38HB.split38CtxPairsAt_qZNodup5_of_split hcs rfl)
    (CompC3RestPre38HB.split38CtxPairsHB_qPreUntaggedNX_split hcs)
    (CompC3Census38HB.nonInj38CensusXZ_highBitComp_split CompRPlantWire.highBitWireBytes hcs)
    (CompC3Census38HB.split38PairsHB_qKdfInjRest_split hcs)
    (CompC3RestPre38HB.restPre38HB_split hcs)
    (CompC3RestFn38HB.rest38Fn_of_wirePairOk_split rfl rfl rfl hcs)
    (CompC3KdfChild38HB.split38PairsAt_qKdfChild2_of_sentPrefix_split hcs)
  have hhmc_hb := CompRNbsc38VT.hmcAt38_of_classVT hvt hfits hq_hb hopk_hb
    pre mid post hb_eq shown cl e c' hc hmr hvis hpre hmid hpost hm₀_a hnil
  have hre_hb := CompC2RestEntry38.rest38EntryAt_of_pre (CompC3RestPre38HB.restPre38HB_split hcs)
    r S g q_hb hfits hq_hb hopk_hb pre mid post hb_eq shown cl e c' hc hmr hvis hpre hmid hpost hm₀_a hnil
  obtain ⟨hwL, hwU, hrfn_hb⟩ := restFnEntry_rv38HB_split hcs hfits hopk_hb
    pre mid post hb_eq shown cl e c' hc hmr hvis hpre hmid hpost hm₀_a
  refine ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, xIr r tr₁ tr₂ cl, hxIr, ?_⟩
  unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects
  dsimp only
  have hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg (xIr r tr₁ tr₂ cl).msg =
      some (msgIr tr₂ stA cl pq) :=
    parseTrSignalMsg_xIrMsg tr₂ stA cl pq
  rw [hparse]
  dsimp only
  have hmac_z : gamma compI0 S g (msgIr tr₂ stA cl pq).mac = zeros8 :=
    gamma_litOf compI0 S g zeros8
  rintro (hmc | hforg)
  · let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek 1 0, o.ct, CompPrefixInvEnc.encOut tr₂ stA cl pq⟩
    have hbt_sub := bobTrials_flatMap_xIr_sub (r := r) (tr := runTraceMoves r ms') (p := p) (q_hb := q_hb)
      (tr₁ := tr₁) (tr₂ := tr₂) (cl := cl) (honestSalts r ms') hopk hopk_hb
      (hidx_p.trans (highBitWireBytes_spqrIdx1 hq_hb).symm)
    have hmc := CompExcuse.memoCollisionOn_mono_new
      (List.append_subset.mpr ⟨List.subset_append_left _ _,
        List.Subset.trans hbt_sub (List.subset_append_right _ _)⟩) hmc
    let memo := fun t => (gamma' compI0 S g t).memo
    let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo
    let newMemo_hb := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') q_hb x₀).flatMap memo
    have hsub_ir : ∀ z ∈ ([(xIr r tr₁ tr₂ cl).ek, (xIr r tr₁ tr₂ cl).ct, (xIr r tr₁ tr₂ cl).msg] ++
        bobTerms r (honestSalts r ms') q_hb x₀).flatMap memo,
        z ∈ newMemo_hb ∨
          (assumedInjective z.1 = false ∧
            (z.2.2 = zeros8 ∨ z.2.2 = gamma compI0 S g (CompPrefixInvEnc.encWire tr₂ stA cl pq) ++ zeros8)) := by
      intro z hz
      obtain ⟨u, hu, hzu⟩ := List.mem_flatMap.mp hz
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
      rcases hu with rfl | rfl | rfl | hu_bt
      · exact Or.inl (List.mem_flatMap.mpr ⟨x₀.ek, List.mem_cons_self,
          mem_memo_ek_sub_variant S g
            (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) hzu⟩)
      · exact Or.inl (List.mem_flatMap.mpr ⟨x₀.ct, List.mem_cons_of_mem _ List.mem_cons_self, hzu⟩)
      · rcases mem_memo_xIrMsg_cases S g tr₂ stA cl pq hzu with hmem_out | hextra
        · exact Or.inl (List.mem_flatMap.mpr ⟨x₀.msg,
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hmem_out⟩)
        · exact Or.inr hextra
      · exact Or.inl (List.mem_flatMap.mpr ⟨u,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu_bt)), hzu⟩)
    have hpost' : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := hpost
    have hkill : ∀ y ∈ preMemo ++ newMemo_hb, assumedInjective y.1 = true →
        y.2.2 = zeros8 ∨ y.2.2 = gamma compI0 S g (CompPrefixInvEnc.encWire tr₂ stA cl pq) ++ zeros8 → False := by
      intro y hy hy_ai hextra
      have hy_val : y.2.2 = gamma compI0 S g y.1 := by
        rcases List.mem_append.mp hy with hy_p | hy_n
        · obtain ⟨u, _, hyu⟩ := List.mem_flatMap.mp hy_p
          exact (CompRPreMemoSound.memo_sound compI0 S g u hyu).2
        · obtain ⟨u, _, hyu⟩ := List.mem_flatMap.mp hy_n
          exact (CompRPreMemoSound.memo_sound compI0 S g u hyu).2
      have hy_cls := CompRNbsc38VT.split38MemoClass_of_preOrNewMemo (v := 1) (t := 0)
        hfits.1.1.1 hopk_hb hpre hmid hpost' hm₀_a hy
      exact not_inj_hb_eq_ir_extra hy_ai hy_val (hre_hb y hy hy_cls) (hrfn_hb y hy) hwL hwU hextra
    obtain ⟨x₁, hx₁, x₂, hx₂, hne_sh, hai, hpts₁, hpts₂, hbytes⟩ := hmc
    rcases hsub_ir x₁ hx₁ with hx₁_hb | ⟨hai₁_f, hextra₁⟩
    · rcases List.mem_append.mp hx₂ with hx₂_pre | hx₂_new
      · exact hhmc_hb ⟨x₁, hx₁_hb, x₂, List.mem_append_left _ hx₂_pre, hne_sh, hai, hpts₁, hpts₂, hbytes⟩
      · rcases hsub_ir x₂ hx₂_new with hx₂_hb | ⟨hai₂_f, hextra₂⟩
        · exact hhmc_hb ⟨x₁, hx₁_hb, x₂, List.mem_append_right _ hx₂_hb, hne_sh, hai, hpts₁, hpts₂, hbytes⟩
        · have hai₁ : assumedInjective x₁.1 = true := by
            rcases hai with h | h
            · exact h
            · rw [hai₂_f] at h; cases h
          exact hkill x₁ (List.mem_append_right _ hx₁_hb) hai₁ (hbytes ▸ hextra₂)
    · have hai₂ : assumedInjective x₂.1 = true := by
        rcases hai with h | h
        · rw [hai₁_f] at h; cases h
        · exact h
      have hx₂_hb : x₂ ∈ preMemo ++ newMemo_hb := by
        rcases List.mem_append.mp hx₂ with hx₂_pre | hx₂_new
        · exact List.mem_append_left _ hx₂_pre
        · rcases hsub_ir x₂ hx₂_new with h | ⟨hai₂_f, _⟩
          · exact List.mem_append_right _ h
          · rw [hai₂_f] at hai₂; cases hai₂
      exact hkill x₂ hx₂_hb hai₂ (hbytes.symm ▸ hextra₁)
  · exact not_macTagForgeryOrCollision_of_mac_zeros8 hmac_z hforg

end Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Memo
