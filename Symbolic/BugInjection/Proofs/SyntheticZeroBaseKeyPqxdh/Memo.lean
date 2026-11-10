/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticZeroBaseKeyPqxdh.Defs
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

namespace Symbolic.BugInjection.Proofs.SyntheticZeroBaseKeyPqxdh.Memo

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (canonicalVariation WireFields)
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
open Symbolic.BugInjection.Proofs.SyntheticZeroBaseKeyPqxdh.Defs

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

theorem macZbk8_len : macZbk8.length = 8 := by decide
theorem ctZbk16_len : ctZbk16.length = 16 := by decide
theorem zeroDh_len : CompRI0Census.zeroDh.length = 32 := by decide

def zbkVariation : DY.TrWire.EncodingVariation :=
  ⟨4, [], 0, 0,
    [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0,
     .known 5 0 0, .extra 6 (.bytes addrZbk36) 0 0]⟩

def wireZbkBytesOf (rk pq : HwBytes) : HwBytes :=
  trWireBytes [] zbkVariation ⟨4, rk, 0, 0, ctZbk16⟩ pq

theorem trWireBytes_zbkVariation (addr : HwBytes) (f : WireFields) (pq : HwBytes) :
    trWireBytes addr zbkVariation f pq = trWireBytes [] zbkVariation f pq := rfl

def wireZbkBytes : HwBytes :=
  match parsePreKeyWire msg38ZbkFast with
  | some p => p.message.take (p.message.length - 8)
  | none => []

def zbkMsgBytes : HwBytes := wireZbkBytes ++ macZbk8
theorem wireZbkBytes_len : wireZbkBytes.length = 135 := by decide +kernel
theorem zbkMsgBytes_len : zbkMsgBytes.length = 143 := by decide +kernel

def wireZbk (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : DY.Bytes :=
  DY.TrWire.trWireMsg 4 (DY.DiffieHellman.dhPk stA.dhs) 0 0 (litOf ctZbk16)
    (CompRNoBSC.encPqMsg tr₂ stA cl) zbkVariation

def xZbkMsg (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : DY.Bytes :=
  DY.Concat.concat (wireZbk tr₂ stA cl) (litOf macZbk8)

def msgZbk (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) :
    DY.Libsignal.TripleRatchet.TRSignalMsg :=
  { wire := wireZbk tr₂ stA cl, mac := litOf macZbk8, version := 4,
    ratchetKey := DY.DiffieHellman.dhPk stA.dhs, counter := 0,
    ciphertext := litOf ctZbk16, pqRatchet := CompRNoBSC.encPqMsg tr₂ stA cl }

def xZbk (r : Records) (tr₁ tr₂ : ExecTrace) (cl : Nat) : PreKeyRep :=
  let o := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o
  ⟨litOf CompRI0Census.zeroDh, o.ct, xZbkMsg tr₂ stA cl⟩

theorem parseTrSignalMsg_xZbkMsg (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) :
    DY.Libsignal.TripleRatchet.parseTrSignalMsg (xZbkMsg tr₂ stA cl) = some (msgZbk tr₂ stA cl) := by
  have hl : (DY.Concat.concat (wireZbk tr₂ stA cl) (litOf macZbk8)).length - DY.Trunc.trunc8Length =
      (wireZbk tr₂ stA cl).length := by
    rw [DY.Concat.length_concat, length_litOf, macZbk8_len,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.trunc8Length_eq_8, Nat.add_sub_cancel]
  simp only [DY.Libsignal.TripleRatchet.parseTrSignalMsg, xZbkMsg, hl, DY.Concat.split_concat]
  simp only [wireZbk, bind, Option.bind, DY.TrWire.trWireMsgFields?_trWireMsg]; rfl

theorem take_sub_eight_append {a b : HwBytes} (hb : b.length = 8) :
    (a ++ b).take ((a ++ b).length - 8) = a := by
  rw [List.length_append, hb, Nat.add_sub_cancel, List.take_left' rfl]

def checkWirePairZbk (w₀ w₁ : HwBytes) : Bool :=
  match parsePreKeyWire w₀, parsePreKeyWire w₁ with
  | some q₀, some p =>
    decide (p.baseKey = 0x05#8 :: CompRI0Census.zeroDh) &&
    decide (p.kyberCiphertext = q₀.kyberCiphertext) &&
    decide (p.inner.ciphertext = ctZbk16) &&
    decide (p.inner.senderRatchetKey = q₀.inner.senderRatchetKey) &&
    decide (p.inner.counter = 0) &&
    decide (p.inner.messageVersion = 4) &&
    decide (p.inner.pqRatchet = q₀.inner.pqRatchet) &&
    decide (wireZbkBytesOf q₀.inner.senderRatchetKey.bytes.toList q₀.inner.pqRatchet = wireZbkBytes) &&
    decide (p.message = wireZbkBytes ++ macZbk8) &&
    decide (p.preKeyId = none)
  | _, _ => false

private theorem checkWirePairZbk_fast :
    checkWirePairZbk CompRPlantWire.sentWireFast msg38ZbkFast = true := by
  decide +kernel

theorem wirePairZbk_spec {q₀ p : PreKeyFields}
    (hq₀ : parsePreKeyWire CompRPlantWire.sentWireBytes = some q₀)
    (hp : parsePreKeyWire msg38_zbk = some p) :
    p.baseKey = 0x05#8 :: CompRI0Census.zeroDh ∧
    p.kyberCiphertext = q₀.kyberCiphertext ∧
    p.inner.ciphertext = ctZbk16 ∧
    p.inner.senderRatchetKey = q₀.inner.senderRatchetKey ∧
    p.inner.counter = 0 ∧
    p.inner.messageVersion = 4 ∧
    p.inner.pqRatchet = q₀.inner.pqRatchet ∧
    wireZbkBytesOf q₀.inner.senderRatchetKey.bytes.toList q₀.inner.pqRatchet = wireZbkBytes ∧
    p.message = wireZbkBytes ++ macZbk8 ∧
    p.preKeyId = none := by
  have h := checkWirePairZbk_fast
  rw [CompRPlantWire.sentWireBytes_eq] at hq₀
  change parsePreKeyWire CompRPlantWire.sentWireFast = some q₀ at hq₀
  rw [msg38_zbk_eq_fast] at hp
  unfold checkWirePairZbk at h
  rw [hq₀, hp] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

private theorem checkOuter_zbk_fast :
    CompFitsNames.checkPreKeyOuter Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 msg38ZbkFast = true := by
  decide +kernel

theorem outer_zbk {r : Records} {p : PreKeyFields}
    (hfits : compFits Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hp : parsePreKeyWire msg38_zbk = some p) :
    CompRPreKeyWire.PreKeyOuterMatches compI0 r msg38_zbk p := by
  refine CompFitsNames.preKeyOuterMatches_of_check hfits hp ?_
  rw [msg38_zbk_eq_fast]
  exact checkOuter_zbk_fast

theorem attackerKnows_xZbkMsg {tr tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat}
    (hk : (CompPrefixInvEnc.encOut tr₂ stA cl pq).AttackerKnows tr) :
    (xZbkMsg tr₂ stA cl).AttackerKnows tr := by
  have hsp := DY.Concat.attacker_knows_split (CompPrefixInvEnc.encOut tr₂ stA cl pq)
    (CompPrefixInvEnc.encWire tr₂ stA cl pq).length tr hk
  rw [CompPrefixInvEnc.encOut, DY.Concat.split_concat] at hsp
  have hsp1 := hsp.1
  dsimp only [CompPrefixInvEnc.encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg] at hsp1
  have hargs := DY.TrWire.attacker_knows_trWireMsg_args _ _ _ _ _ _ _ tr hsp1
  have hw : (wireZbk tr₂ stA cl).AttackerKnows tr :=
    DY.TrWire.attacker_knows_trWireMsg 4 (DY.DiffieHellman.dhPk stA.dhs) 0 0
      (litOf ctZbk16) (CompRNoBSC.encPqMsg tr₂ stA cl) zbkVariation tr
      hargs.1 (knows_litOf ctZbk16 tr) hargs.2.2
  exact DY.Concat.attacker_knows_concat _ _ tr hw (knows_litOf macZbk8 tr)

theorem faithfulInner_xZbkMsg {S : Sem} {g : Ghost} {tr₂ : ExecTrace}
    {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {q₀ p : PreKeyFields}
    (hfi₀ : FaithfulInner compI0 S g (CompPrefixInvEnc.encOut tr₂ stA cl pq) q₀)
    (hct_p : p.inner.ciphertext = ctZbk16)
    (hrk_p : p.inner.senderRatchetKey = q₀.inner.senderRatchetKey)
    (hcnt_p : p.inner.counter = 0) (hver_p : p.inner.messageVersion = 4)
    (hpq_p : p.inner.pqRatchet = q₀.inner.pqRatchet)
    (hwire_of : wireZbkBytesOf q₀.inner.senderRatchetKey.bytes.toList q₀.inner.pqRatchet = wireZbkBytes)
    (hpm : p.message = wireZbkBytes ++ macZbk8) :
    FaithfulInner compI0 S g (xZbkMsg tr₂ stA cl) p ∧
      p.message = gamma compI0 S g (xZbkMsg tr₂ stA cl) ∧
      gamma compI0 S g (wireZbk tr₂ stA cl) = wireZbkBytes := by
  obtain ⟨m₀, hp₀, _, _, _, _, hrk₀, hpq₀, _, _⟩ := hfi₀
  change DY.Libsignal.TripleRatchet.parseTrSignalMsg (Census443Defs.encOut tr₂ stA cl pq) = some m₀ at hp₀
  rw [CompRFaithfulInner.parseTrSignalMsg_encOut] at hp₀
  injection hp₀ with hm₀_eq; subst hm₀_eq
  have hrk_γ : gamma compI0 S g (DY.DiffieHellman.dhPk stA.dhs) = q₀.inner.senderRatchetKey.bytes.toList := hrk₀
  have hpq_γ : gamma compI0 S g (CompRNoBSC.encPqMsg tr₂ stA cl) = q₀.inner.pqRatchet := hpq₀
  have hγwire : gamma compI0 S g (wireZbk tr₂ stA cl) = wireZbkBytes := by
    unfold wireZbk
    rw [CompRFaithfulInner.gamma_trWire_eq, trWireBytes_zbkVariation, hrk_γ, gamma_litOf, hpq_γ]
    exact hwire_of
  have htake : p.message.take (p.message.length - 8) = wireZbkBytes := by rw [hpm, take_sub_eight_append macZbk8_len]
  have hdrop : p.message.drop (p.message.length - 8) = macZbk8 := by rw [hpm, drop_sub_eight_append macZbk8_len]
  have hγmsg : p.message = gamma compI0 S g (xZbkMsg tr₂ stA cl) := by
    rw [xZbkMsg, CompFreshDistinct.gamma_concat_eq, hγwire, gamma_litOf, hpm]
  refine ⟨⟨msgZbk tr₂ stA cl, parseTrSignalMsg_xZbkMsg tr₂ stA cl, ?_⟩, hγmsg, hγwire⟩
  refine ⟨?_, ?_, spqrHeaded_litOf macZbk8, ?_, ?_, ?_, ?_, ?_⟩
  · change gamma compI0 S g (wireZbk tr₂ stA cl) = _; rw [htake]; exact hγwire
  · change gamma compI0 S g (litOf macZbk8) = _; rw [gamma_litOf, hdrop]
  · change gamma compI0 S g (litOf ctZbk16) = _; rw [gamma_litOf, hct_p]
  · change gamma compI0 S g (DY.DiffieHellman.dhPk stA.dhs) = _; rw [hrk_p]; exact hrk_γ
  · change gamma compI0 S g (CompRNoBSC.encPqMsg tr₂ stA cl) = _; rw [hpq_p]; exact hpq_γ
  · change (0 : UInt32).toNat = p.inner.counter.toNat; rw [hcnt_p]; rfl
  · change (4 : UInt8).toNat = p.inner.messageVersion.toNat; rw [hver_p]; rfl

theorem swap_and_mem_zbk {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool}
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
    (hp : parsePreKeyWire msg38_zbk = some p)
    (hout : CompRPreKeyWire.PreKeyOuterMatches compI0 r msg38_zbk p)
    (hex : ExplainsMoves compI0 r S who ok g
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post) τ₁)
    (hkct : o.ct.AttackerKnows (runTraceMoves r
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post)))
    (hkmsg : (CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post))) :
    ExplainsMoves compI0 r S who ok g
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) τ₁ ∧
    (⟨litOf CompRI0Census.zeroDh, o.ct, xZbkMsg tr₂ stA cl⟩ : PreKeyRep) ∈
      preKeyRepresentations compI0 r S g
        (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post)
        msg38_zbk ∧
    gamma compI0 S g (wireZbk tr₂ stA cl) = wireZbkBytes := by
  subst htr₁
  have hlen := CompRX0SS38.sentWireBytes_len
  have hγ := CompRX0Mem.hγ_of_sendMatches hsm hlen hq₀ hbk₀ hkc₀
  obtain ⟨_, _, _, _, _, hmsg₀⟩ := CompRX0Mem.sendMatches_append_inv hsm hlen hq₀
  have hfi₀ := CompRFaithfulInner.faithfulInner_of_gamma_encOut S g tr₂ stA cl _ q₀ hns hpn hmsg₀.symm hcan₀
  obtain ⟨hpbk, hkc_p, hct_p, hrk_p, hcnt_p, hver_p, hpq_p, hwire_of, hpm_p, _⟩ :=
    wirePairZbk_spec hq₀ hp
  obtain ⟨hfi, hγmsg, hγwire⟩ :=
    faithfulInner_xZbkMsg hfi₀ hct_p hrk_p hcnt_p hver_p hpq_p hwire_of hpm_p
  have hbk_take : p.baseKey.take 33 = ecKey (gamma compI0 S g (litOf CompRI0Census.zeroDh)) := by
    rw [gamma_litOf, hpbk]
    decide +kernel
  have hkek : (litOf CompRI0Census.zeroDh).AttackerKnows (runTraceMoves r
      (pre ++ m₀ :: mid ++ .encrypt me s cl (tr₂.length + 2) (some (e, c')) :: post)) :=
    knows_litOf CompRI0Census.zeroDh _
  have hmem := CompRX0Mem.x0_mem_of_parts hkek hkct (attackerKnows_xZbkMsg hkmsg)
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
  refine ⟨hex', ?_, hγwire⟩
  unfold preKeyRepresentations at hmem ⊢
  rw [htr_eq]; exact hmem

theorem split38_decomp_swap_rep_zbk {who : List Participant} {ok : Nat → Bool}
    {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex_cli : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire msg38_zbk = some p) :
    ∃ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let stA := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob
        (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
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
      xZbk r tr₁ tr₂ cl ∈ preKeyRepresentations compI0 r S g ms' msg38_zbk ∧
      gamma compI0 S g (wireZbk tr₂ stA cl) = wireZbkBytes := by
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb_s, hs_s, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by
    rw [hb_s]; exact CompRX0SS38.highBitComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by
    rw [hs_s]; exact CompRX0SS38.highBitComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, hcan₀⟩ := CompRPlantWire.sentWireBytes_innerWireCanonical.1
  have hex : ExplainsMoves compI0 r S who ok g ms
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) :=
    ⟨hex_cli.2.1, hex_cli.2.2.1.1⟩
  obtain ⟨pre, a, idS, hb, shown, mid, cl, e, c', post, ikA, tr₁, tr₂, o, stA,
    htr₁, ho, hstA, htr₂, hms, hdisj, hek, hct, _, hctK, hencK, hnil, hvis₀, hsm, hm₀, hpre, hmid, hpost⟩ :=
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
    obtain ⟨hex', hmem', hγwire⟩ := swap_and_mem_zbk rfl rfl hek hct hsm rfl rfl hq₀ hcan₀ hbk₀ hkc₀
      hp (outer_zbk hfits.1 hp) hex hctK hencK
    exact ⟨pre, mid, post, hb, shown, cl, e, c', rfl, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil,
      CliCoinSplitClose.explainsCli_of_explains_mid_encrypt_swap hex_cli hex', hmem', hγwire⟩
  · exfalso
    subst hidS ha hikA ho hstA
    obtain ⟨ek', ct', hL, -⟩ := CompRX0Mem.sendMatches_append_inv hsm CompRX0SS38.sentWireBytes_len hq₀
    rw [hL] at hsm
    exact CompRX0Bytes.not_sendMatches_bobSelf hwf.1 hEq hc hs1 hs2 CompRPlantWire.sentWireBytes
      CompRX0SS38.sentWireBytes_hasTag4 tr₁ tr₂ r.bob _ _ ek' ct' cl _ hsm

private theorem isLowOrderKey_zeroDh_baseKey :
    DY.X25519.isLowOrderKey ((((0x05#8 :: CompRI0Census.zeroDh).take 33).drop 1).map BitVec.toNat) =
      true := by
  decide

theorem bobTrials_zeroDh_nil (r : ProtocolSetup) (tr : ExecTrace) (p : PreKeyFields)
    (x : PreKeyRep) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (hopk : p.preKeyId = none) (hbk : p.baseKey = 0x05#8 :: CompRI0Census.zeroDh) :
    bobTrials r tr p x msg = [] := by
  unfold bobTrials; rw [hopk, hbk]; dsimp only; rw [isLowOrderKey_zeroDh_baseKey]; simp

private theorem mem_memo_trWire_rk {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes}
    {ev : DY.TrWire.EncodingVariation} {x : DY.Bytes × DY.Bytes × HwBytes}
    (hx : x ∈ (gamma' i S g rk).memo) :
    x ∈ (gamma' i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev)).memo := by
  unfold gamma' at hx ⊢
  dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]
  rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]
  simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]
  exact Or.inr (Or.inl hx)

private theorem mem_memo_trWire_cases {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes}
    {ev : DY.TrWire.EncodingVariation} {x : DY.Bytes × DY.Bytes × HwBytes}
    (hx : x ∈ (gamma' i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev)).memo) :
    x.1 = DY.TrWire.trWireMsg v rk c pc ct pq ev ∨ x ∈ (gamma' i S g rk).memo ∨
      x ∈ (gamma' i S g ct).memo ∨ x ∈ (gamma' i S g pq).memo := by
  unfold gamma' at hx
  dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes] at hx
  rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)] at hx
  simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll] at hx
  rcases hx with rfl | hrk | hct | hpq
  exacts [Or.inl rfl, Or.inr (Or.inl hrk), Or.inr (Or.inr (Or.inl hct)), Or.inr (Or.inr (Or.inr hpq))]

def ZbkExtra (v : HwBytes) : Prop :=
  v = CompRI0Census.zeroDh ∨ v = ctZbk16 ∨ v = macZbk8 ∨ v = wireZbkBytes ∨ v = zbkMsgBytes

private theorem mem_memo_xZbkMsg_cases (S : Sem) (g : Ghost) (tr₂ : ExecTrace)
    (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat)
    (hγwire : gamma compI0 S g (wireZbk tr₂ stA cl) = wireZbkBytes)
    {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (xZbkMsg tr₂ stA cl)).memo) :
    x ∈ (gamma' compI0 S g (CompPrefixInvEnc.encOut tr₂ stA cl pq)).memo ∨
      (assumedInjective x.1 = false ∧ ZbkExtra x.2.2) := by
  rcases CompRX0NBSC38Hmc.mem_memo_concat_cases hx with hcat | hw | hm
  · right; refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    · rw [hcat]; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _
    · rw [(CompRPreMemoSound.memo_sound compI0 S g _ hx).2, hcat, CompFreshDistinct.gamma_concat_eq, hγwire, gamma_litOf]
      rfl
  · rcases mem_memo_trWire_cases hw with htr | hrk | hct | hpq
    · right; refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      · rw [htr]; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_eq _ _ _ _ _ _ _
      · rw [(CompRPreMemoSound.memo_sound compI0 S g _ hw).2, htr]; exact hγwire
    · exact Or.inl (CompRX0NBSC38Hmc.mem_memo_encWire_of_encOut (mem_memo_trWire_rk hrk))
    · right; rw [memo_litOf, List.mem_singleton] at hct; subst hct
      exact ⟨assumedInjective_litOf ctZbk16, Or.inr (Or.inl rfl)⟩
    · exact Or.inl (CompRX0NBSC38Hmc.mem_memo_encPqMsg_of_encOut hpq)
  · right; rw [memo_litOf, List.mem_singleton] at hm; subst hm
    exact ⟨assumedInjective_litOf macZbk8, Or.inr (Or.inr (Or.inl rfl))⟩

private theorem nonInjOff_of_zbkExtra {v : HwBytes} (hv : ZbkExtra v) :
    CompRNonInj38Census.NonInjOff v := by
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun _ => CompRI0TermInj.kdfFree_of_mem_x25519Vals (by simp [CompRI0TermInj.x25519Vals]),
      fun h => ?_⟩
    rw [zeroDh_len] at h; cases h
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> (rw [ctZbk16_len] at h; cases h)
  · refine ⟨fun h => ?_, fun _ => ⟨compTag4_ne_macZbk4.symm, fun hrow => ?_⟩⟩
    · rw [macZbk8_len] at h; cases h
    · obtain ⟨d, hd, htake⟩ := List.mem_map.mp hrow
      exact rowDigests_take8_ne_macZbk8 d hd htake
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> (rw [wireZbkBytes_len] at h; cases h)
  · refine ⟨fun h => ?_, fun h => ?_⟩ <;> (rw [zbkMsgBytes_len] at h; cases h)

private theorem zbkExtra_not_mem_rVals38HB :
    CompRI0Census.zeroDh ∉ CompC3RestFn38HBA.rVals38HB ∧
    ctZbk16 ∉ CompC3RestFn38HBA.rVals38HB ∧
    macZbk8 ∉ CompC3RestFn38HBA.rVals38HB ∧
    wireZbkBytes ∉ CompC3RestFn38HBA.rVals38HB ∧
    zbkMsgBytes ∉ CompC3RestFn38HBA.rVals38HB := by
  decide +kernel

private theorem not_rv38HB_of_zbkExtra {v : HwBytes} (hv : ZbkExtra v) :
    ¬ CompC3RestFn38HBA.Rv38HB v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := zbkExtra_not_mem_rVals38HB
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption

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
    ∀ y ∈ preMemo ++ newMemo,
      CompC2RestFn.RestFnEntry
        (CompC3RestFn38HBA.lookupShape S g (CompC3RestFn38HB.allTerms38 tr₁ tr₂ r.bob o cl))
        CompC3RestFn38HBA.Rv38HB S g y := by
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
  intro y hy
  rcases List.mem_append.mp hy with hy_pre | hy_new
  · obtain ⟨u, hu, hyu⟩ := List.mem_flatMap.mp hy_pre
    exact CompC3RestFn38HB.restFnEntry_of_fnOK hc_eq' hc_tail hmapR hnd
      (CompRPreMemoSound.memo_sound compI0 S g u hyu).2 (hpreTerms u hu y hyu)
  · obtain ⟨u, hu, hyu⟩ := List.mem_flatMap.mp hy_new
    exact CompC3RestFn38HB.restFnEntry_of_fnOK hc_eq' hc_tail hmapR hnd
      (CompRPreMemoSound.memo_sound compI0 S g u hyu).2 (hnewTerms u hu y hyu)

private theorem not_inj_hb_eq_zbk_extra {S : Sem} {g : Ghost} {F : HwBytes → DY.Bytes}
    {y : DY.Bytes × DY.Bytes × HwBytes}
    (hy_ai : assumedInjective y.1 = true)
    (hy_val : y.2.2 = gamma compI0 S g y.1)
    (hy_re : CompC2Rest38.RestEntry S g y)
    (hy_rfn : CompC2RestFn.RestFnEntry F CompC3RestFn38HBA.Rv38HB S g y)
    (hextra : ZbkExtra y.2.2) : False := by
  by_cases hK : IsKdf y.1
  · obtain ⟨k, m, hkdf⟩ := hK
    have hz : CompRNonInj38Census.ZVal y.2.2 := by
      rw [hy_val, hkdf]
      exact CompRNonInj38Census.zVal_kdfExtract k m
    exact CompRNonInj38Census.not_zVal_of_nonInjOff (nonInjOff_of_zbkExtra hextra) hz
  · by_cases hX : CompRSplit38UntaggedShape.IsX y.1
    · have hL : y.2.2.length = 32 := by
        rw [hy_val]
        rcases hX with ⟨s, hpk⟩ | ⟨pk, sk, hdh⟩
        · rw [hpk]; exact CompFreshDistinct.gamma_dhPk_length S g s
        · rw [hdh]; exact CompFreshDistinct.gamma_dh_pack_length S g pk sk
      rcases hextra with h0 | h16 | h8 | h135 | h143
      · exact CompC2RestCore.gamma_x_ne_zeroDh hX hy_re.1 (hy_val.symm.trans h0)
      · rw [h16, ctZbk16_len] at hL; cases hL
      · rw [h8, macZbk8_len] at hL; cases hL
      · rw [h135, wireZbkBytes_len] at hL; cases hL
      · rw [h143, zbkMsgBytes_len] at hL; cases hL
    · by_cases hT : CompRSplit38UntaggedShape.IsTrunc8 y.1
      · exact CompRNonInj38Census.not_zVal_of_nonInjOff (nonInjOff_of_zbkExtra hextra) (hy_re.2.1 hT)
      · exact not_rv38HB_of_zbkExtra hextra (hy_rfn.2.1 hy_ai hK hX hT)

theorem noBsc_zbk_cli_swap {who : List Participant} {ok : Nat → Bool} {σ₁ blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli compI0 r S who ok σ₁
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms)
    (hp : parsePreKeyWire msg38_zbk = some p) :
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
      ∃ x ∈ preKeyRepresentations compI0 r S g ms' msg38_zbk,
        ¬ BobStartCollision compI0 r S g ms' p x := by
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, _, hxZbk, hγwire⟩ :=
    split38_decomp_swap_rep_zbk hcs r S g ms p hfits hnb hex hp
  obtain ⟨q₀, hq₀, _⟩ := CompRPlantWire.sentWireBytes_innerWireCanonical.1
  obtain ⟨hpbk, _, _, _, _, _, _, _, _, hopk⟩ := wirePairZbk_spec hq₀ hp
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
  have hrfn_hb := restFnEntry_rv38HB_split hcs hfits hopk_hb
    pre mid post hb_eq shown cl e c' hc hmr hvis hpre hmid hpost hm₀_a
  refine ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, xZbk r tr₁ tr₂ cl, hxZbk, ?_⟩
  unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects
  dsimp only
  have hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg (xZbk r tr₁ tr₂ cl).msg =
      some (msgZbk tr₂ stA cl) := parseTrSignalMsg_xZbkMsg tr₂ stA cl
  have hbt_nil : bobTrials r (runTraceMoves r ms') p (xZbk r tr₁ tr₂ cl) (msgZbk tr₂ stA cl) = [] :=
    bobTrials_zeroDh_nil r (runTraceMoves r ms') p (xZbk r tr₁ tr₂ cl) (msgZbk tr₂ stA cl) hopk hpbk
  rw [hparse]; dsimp only; rw [hbt_nil]
  rintro (hmc | ⟨_, ⟨⟩, _⟩ | ⟨_, ⟨⟩, _⟩)
  let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek 1 0, o.ct, CompPrefixInvEnc.encOut tr₂ stA cl pq⟩
  rw [List.flatMap_nil, List.append_nil] at hmc
  let memo := fun t => (gamma' compI0 S g t).memo
  let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo
  let newMemo_hb := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') q_hb x₀).flatMap memo
  have hsub_zbk : ∀ z ∈ [(xZbk r tr₁ tr₂ cl).ek, (xZbk r tr₁ tr₂ cl).ct, (xZbk r tr₁ tr₂ cl).msg].flatMap memo,
      z ∈ newMemo_hb ∨ (assumedInjective z.1 = false ∧ ZbkExtra z.2.2) := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := List.mem_flatMap.mp hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · right
      change z ∈ (gamma' compI0 S g (litOf CompRI0Census.zeroDh)).memo at hzu
      rw [memo_litOf, List.mem_singleton] at hzu
      subst hzu
      exact ⟨assumedInjective_litOf CompRI0Census.zeroDh, Or.inl rfl⟩
    · exact Or.inl (List.mem_flatMap.mpr ⟨x₀.ct, List.mem_cons_of_mem _ List.mem_cons_self, hzu⟩)
    · rcases mem_memo_xZbkMsg_cases S g tr₂ stA cl pq hγwire hzu with hmem_out | hextra
      · exact Or.inl (List.mem_flatMap.mpr ⟨x₀.msg,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hmem_out⟩)
      · exact Or.inr hextra
  have hpost' : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := hpost
  have hkill : ∀ y ∈ preMemo ++ newMemo_hb, assumedInjective y.1 = true → ZbkExtra y.2.2 → False := by
    intro y hy hy_ai hextra
    have hy_val : y.2.2 = gamma compI0 S g y.1 := by
      rcases List.mem_append.mp hy with hy_p | hy_n
      · obtain ⟨u, _, hyu⟩ := List.mem_flatMap.mp hy_p
        exact (CompRPreMemoSound.memo_sound compI0 S g u hyu).2
      · obtain ⟨u, _, hyu⟩ := List.mem_flatMap.mp hy_n
        exact (CompRPreMemoSound.memo_sound compI0 S g u hyu).2
    have hy_cls := CompRNbsc38VT.split38MemoClass_of_preOrNewMemo (v := 1) (t := 0)
      hfits.1.1.1 hopk_hb hpre hmid hpost' hm₀_a hy
    exact not_inj_hb_eq_zbk_extra hy_ai hy_val (hre_hb y hy hy_cls) (hrfn_hb y hy) hextra
  obtain ⟨x₁, hx₁, x₂, hx₂, hne_sh, hai, hpts₁, hpts₂, hbytes⟩ := hmc
  rcases hsub_zbk x₁ hx₁ with hx₁_hb | ⟨hai₁_f, hextra₁⟩
  · rcases List.mem_append.mp hx₂ with hx₂_pre | hx₂_new
    · exact hhmc_hb ⟨x₁, hx₁_hb, x₂, List.mem_append_left _ hx₂_pre, hne_sh, hai, hpts₁, hpts₂, hbytes⟩
    · rcases hsub_zbk x₂ hx₂_new with hx₂_hb | ⟨hai₂_f, hextra₂⟩
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
      · rcases hsub_zbk x₂ hx₂_new with h | ⟨hai₂_f, _⟩
        · exact List.mem_append_right _ h
        · rw [hai₂_f] at hai₂; cases hai₂
    exact hkill x₂ hx₂_hb hai₂ (hbytes.symm ▸ hextra₁)

end Symbolic.BugInjection.Proofs.SyntheticZeroBaseKeyPqxdh.Memo
