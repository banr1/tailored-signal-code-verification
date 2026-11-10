/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.CBad
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.QuietTransferPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyOverModel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendEvalBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRecordInj
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendSlot
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.ReadVis
import Symbolic.Proofs.Swarm.CREF.SendWire.RecvSimV3SendPure
import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPure
import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureB
import Symbolic.Proofs.Swarm.CREF.SendWire.StateInv
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.Coinsplit.Slots.S3SendCut
import Symbolic.Proofs.Swarm.SHARED.HmacLen
import Symbolic.Proofs.Swarm.TRREF.MacFormBridge

/-!
# Cut-Polymorphic `send` Slot Refinement

Proves `SlotSendCliSpec`, lifting `slot_send_d3_pqModelRel` from single-cut `CliLiveAt` to
cut-polymorphic `CliLiveAtCli` across all `CoinSplit` cuts `sendCutOfLen`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L08

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX CryptoVerification.SignalSession
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.SndPure
open Symbolic.Swarm.CREF.Cli Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.SendWire (sendGhost sendPendingGhost setSendAddr pqHarnessAddrBytes)
open Symbolic.Swarm.Coinsplit.S1 (NoAdjRng)
open Symbolic.Swarm.Coinsplit.S3 (sendCutOfLen send_exit0_cut_eq_of_move)
open Symbolic.Swarm.Coinsplit.Lift
open Symbolic.Proofs.Swarm.UA.Defs (CliSlotPostW)

private theorem coinSplit_split_append {σ₁ σ₂ τ : List MachineEvent} (h : CoinSplit (σ₁ ++ σ₂) τ) :
    ∃ τ₁ τ₂, τ = τ₁ ++ τ₂ ∧ CoinSplit σ₁ τ₁ ∧ CoinSplit σ₂ τ₂ := by
  induction σ₁ generalizing τ with
  | nil => exact ⟨[], τ, rfl, .nil, h⟩
  | cons e tl ih =>
    by_cases hrng : ∃ bs, e = .rng bs
    · obtain ⟨bs, rfl⟩ := hrng
      rw [List.cons_append, Symbolic.Swarm.Coinsplit.S1.coinSplit_cons_rng_iff] at h
      obtain ⟨pieces, τ', hne, hpref, rfl, hcs'⟩ := h
      obtain ⟨τ₁', τ₂, rfl, h1, h2⟩ := ih hcs'
      exact ⟨pieces.map MachineEvent.rng ++ τ₁', τ₂, by simp [List.append_assoc], .split hne hpref h1, h2⟩
    · have hne : eventKind e ≠ .rng := by
        cases e with | rng bs => exact absurd ⟨bs, rfl⟩ hrng | _ => simp [eventKind]
      rw [List.cons_append, Symbolic.Swarm.Coinsplit.S1.coinSplit_cons_nonRng_iff hne] at h
      obtain ⟨τ', rfl, hcs'⟩ := h
      obtain ⟨τ₁', τ₂, rfl, h1, h2⟩ := ih hcs'
      exact ⟨e :: τ₁', τ₂, rfl, .keep (fun b hb => hrng ⟨b, hb⟩) h1, h2⟩

private theorem outcomeFaithfulCli_prefix {r : ProtocolSetup} {ok : Nat → Bool} {ms₀ δ : List Move}
    (h : OutcomeFaithfulCli r ok (ms₀ ++ δ)) : OutcomeFaithfulCli r ok ms₀ := by
  refine ⟨fun i m hm => ?_, fun i m hm => ?_⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hm).1
    have htake : (ms₀ ++ δ).take i = ms₀.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
    simpa [htake] using h.1 i m (by rwa [List.getElem?_append_left hlt])
  · have hlt := (List.getElem?_eq_some_iff.mp hm).1
    have htake : (ms₀ ++ δ).take i = ms₀.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
    simpa [htake] using h.2 i m (by rwa [List.getElem?_append_left hlt])

private theorem rngLengthsFaithfulCli_prefix {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₀ δ : List Move} (h : RngLengthsFaithfulCli interp r S g (ms₀ ++ δ)) :
    RngLengthsFaithfulCli interp r S g ms₀ := by
  intro i m hm
  have hlt := (List.getElem?_eq_some_iff.mp hm).1
  have htake : (ms₀ ++ δ).take i = ms₀.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
  simpa [htake] using h i m (by rwa [List.getElem?_append_left hlt])

private theorem explainsCli_prefix_of_split {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {σ_pre blk_cli τ_pre blk' : List MachineEvent}
    {g : Ghost} {ms : List Move} (hcs_pre : CoinSplit σ_pre τ_pre)
    (hhead : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hex : ExplainsCli interp r S who ok (σ_pre ++ blk_cli) (τ_pre ++ blk') g ms)
    (hnrc : ¬ ReadCollision interp r S g ms (τ_pre ++ blk')) :
    ∃ ms₀ δ, ms = ms₀ ++ δ ∧ ExplainsCli interp r S who ok σ_pre τ_pre g ms₀ ∧
      ¬ ReadCollision interp r S g ms₀ τ_pre ∧ XplBlock interp r S who g ms₀ δ τ_pre blk' := by
  have hc := explainsCli_toClean hex hnrc
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ := matchedPrefix_split hc.matched hhead (matchedPrefix_prefix_reachable hc.matched)
  have hc₀ := cleanBy_prefix hc hpre.2.2.2.2.2.length_eq
  exact ⟨ms₀, δ, rfl, ⟨hcs_pre, hpre, outcomeFaithfulCli_prefix hex.2.2.1, rngLengthsFaithfulCli_prefix hex.2.2.2⟩,
    hc₀.2, ⟨hpre, hc.matched.2.1, hmatch⟩⟩

/-! ## SPQR Draw-Size Lower Bound and Prefix Generalization -/

private theorem except_bind_eq_ok {ε α β : Type} {u : Except ε α} {f : α → Except ε β} {b : β}
    (h : (u >>= f) = Except.ok b) : ∃ a, u = Except.ok a ∧ f a = Except.ok b := by
  cases u with | error _ => cases h | ok a => exact ⟨a, rfl, h⟩

private theorem spqrModelOf_send_eq_none_of_lt_draw (interp : ExternInterpretation)
    (pq tape : HwBytes) (hlt : tape.length < Slots.trSendDrawSizeOf interp pq) :
    (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).send pq tape = none := by
  let F := DY.Libsignal.Refinement.sha256CompressFunction interp
  let K := Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf interp
  let mac := Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp
  let D := Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac F K mac
  change tape.length < Slots.trSendDrawSize F K mac pq at hlt; unfold Slots.trSendDrawSize at hlt
  change (CryptoVerification.LibsignalSpqrV1.toSpqrModel D (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F)).send pq tape = none
  unfold CryptoVerification.LibsignalSpqrV1.toSpqrModel CryptoVerification.LibsignalSpqrV1.send; dsimp only
  have hgen (t : List (BitVec 8)) (hne : ¬ (t.take 64).length = 64) :
      CryptoVerification.LibsignalSpqrV1.generate K t = .error (.rngExhausted 64 t.length) := by
    have hrfl : CryptoVerification.LibsignalSpqrV1.generate K t =
        match (if h : (t.take 64).length = 64 then (some ⟨t.take 64, h⟩ : Option (List.Vector (BitVec 8) 64)) else none) with
        | none => Except.error (.rngExhausted 64 t.length)
        | some seed => let (hdr, ek, dk) := K.fromSeed seed; Except.ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, t.drop 64) := rfl
    rw [hrfl, dite_eq_right hne]
  have henc (hdr : CryptoVerification.LibsignalSpqrV1.Header) (t : List (BitVec 8)) (hne : ¬ (t.take 32).length = 32) :
      CryptoVerification.LibsignalSpqrV1.encaps1 K hdr t = .error (.rngExhausted 32 t.length) := by
    have hrfl : CryptoVerification.LibsignalSpqrV1.encaps1 K hdr t =
        match (if h : (t.take 32).length = 32 then (some ⟨t.take 32, h⟩ : Option (List.Vector (BitVec 8) 32)) else none) with
        | none => Except.error (.rngExhausted 32 t.length)
        | some rand => match K.encaps1 hdr rand with
          | none => Except.error .encaps1Failed
          | some (ct1, es, ss) => Except.ok ((ct1.toList, es.toList, ss.toList), t.drop 32) := rfl
    rw [hrfl, dite_eq_right hne]
  dsimp only [D] at *
  rcases hdec : CryptoVerification.LibsignalSpqrV1.decodeState (Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac F K mac) pq with _ | pb
  · rfl
  · rw [hdec] at hlt; dsimp only at hlt ⊢
    rcases hin : pb.inner with _ | v1
    · rw [hin] at hlt; simp at hlt
    · rw [hin] at hlt; dsimp only at hlt ⊢
      rcases hfr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac F K mac).statesFromPb v1 with _ | st0
      · rfl
      · rw [hfr] at hlt; dsimp only [Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac] at hlt ⊢
        cases st0 with
        | keysUnsampled s =>
          simp only [Slots.statesDrawSize] at hlt
          have hne64 : ¬ (tape.take 64).length = 64 := by rw [List.length_take]; omega
          simp [CryptoVerification.LibsignalSpqrV1.States.send, CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.send_hdr_chunk,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.send_header, hgen tape hne64]; rfl
        | headerReceived s =>
          simp only [Slots.statesDrawSize] at hlt
          have hne32 : ¬ (tape.take 32).length = 32 := by rw [List.length_take]; omega
          simp [CryptoVerification.LibsignalSpqrV1.States.send, CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.send_ct1_chunk,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.send_ct1, henc s.uc.hdr tape hne32]; rfl
        | _ => simp [Slots.statesDrawSize] at hlt

private theorem spqrSendMsgOf_eq_nil_of_lt_draw (interp : ExternInterpretation)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interp)
    (pq tape : HwBytes) (hlt : tape.length < Slots.trSendDrawSizeOf interp pq) :
    Symbolic.Swarm.SHARED.SpqrBytes.spqrSendMsgOf interp pq tape = [] := by
  have hlen := Symbolic.Swarm.SHARED.HmacLen.hmacLen_of_ceh hEq
  rw [show Symbolic.Swarm.SHARED.SpqrBytes.spqrSendMsgOf interp pq tape =
      Symbolic.Swarm.SHARED.SpqrBytes.spqrSendMsgB (DY.Libsignal.Refinement.sha256CompressFunction interp)
        (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp) (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) pq tape from rfl,
    ← Symbolic.Swarm.TRREF.MacFormBridge.spqrSendMsgOf_spqrSemOf_eq_spqrBytes interp hlen pq tape]
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendMsgOf Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendMsgB Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendB
  have hnone := spqrModelOf_send_eq_none_of_lt_draw interp pq tape hlt
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf at hnone; rw [hnone]

private theorem spqrModelOf_send_msg_ne_nil_of_draw_pos (interp : ExternInterpretation)
    {pq r_coins pq' pm : HwBytes} {salt : CryptoGames.HKDF.Salt}
    (hpos : 0 < Slots.trSendDrawSizeOf interp pq)
    (hsend : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).send pq r_coins = some (pq', salt, pm)) :
    pm ≠ [] := by
  let F := DY.Libsignal.Refinement.sha256CompressFunction interp
  let K := Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf interp
  let mac := Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp
  let D := Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac F K mac
  change 0 < Slots.trSendDrawSize F K mac pq at hpos; unfold Slots.trSendDrawSize at hpos
  change (CryptoVerification.LibsignalSpqrV1.toSpqrModel D
    (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F)).send pq r_coins = some (pq', salt, pm) at hsend
  unfold CryptoVerification.LibsignalSpqrV1.toSpqrModel at hsend; dsimp only at hsend
  rcases htop : (CryptoVerification.LibsignalSpqrV1.send D (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) pq r_coins).1 with _ | out
  · rw [htop] at hsend; cases hsend
  · rw [htop] at hsend; dsimp only at hsend
    rcases hsalt : CryptoVerification.LibsignalSpqrV1.messageKeyToSalt? out.key with _ | s
    · rw [hsalt] at hsend; cases hsend
    · rw [hsalt] at hsend; injection hsend with htuple
      rcases Prod.mk.inj htuple with ⟨_, hrest⟩; rcases Prod.mk.inj hrest with ⟨_, rfl⟩
      unfold CryptoVerification.LibsignalSpqrV1.send at htop
      rcases hdec : CryptoVerification.LibsignalSpqrV1.decodeState D pq with _ | pb
      · simp [D, hdec] at hpos
      · rcases hin : pb.inner with _ | v1
        · simp [D, hdec, hin] at hpos
        · rcases hfr : D.statesFromPb v1 with _ | st0
          · simp [D, hdec, hin, hfr] at hpos
          · simp only [hdec, hin, hfr] at htop
            rcases hst : (D.8 st0 r_coins).1 with _ | ⟨msg, key, st1⟩
            · rw [hst] at htop; cases htop
            · rw [hst] at htop; dsimp only at htop
              let hkdf := CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F
              have finish (vnOpt : Option CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB)
                  (index : BitVec 32) (msgKey : HwBytes) (chainPb : Option CryptoVerification.LibsignalSpqrV1.ChainPB)
                  (htail : (match D.msgSerialize msg index with
                    | [] => Except.error (CryptoVerification.LibsignalSpqrV1.SpqrApiError.panic .sendMsgEmpty)
                    | b0 :: _ =>
                      if b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8 then
                        Except.error (CryptoVerification.LibsignalSpqrV1.SpqrApiError.panic .sendMsgBadVersion)
                      else Except.ok {
                        state := D.encodeState { inner := some (D.statesIntoPb st1), versionNegotiation := vnOpt, chain := chainPb }
                        msg := D.msgSerialize msg index, key := if msgKey.isEmpty then none else some msgKey
                      }) = Except.ok out) : out.msg ≠ [] := by
                cases hser : D.msgSerialize msg index <;> rw [hser] at htail <;> dsimp only at htail
                · nomatch htail
                · rename_i b0 rest
                  by_cases hb0 : (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true
                  · rw [ite_eq_left hb0] at htail; nomatch htail
                  · rw [ite_eq_right hb0] at htail; injection htail with htail; subst htail; exact List.cons_ne_nil _ _
              have someChain (vnOpt : Option CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB)
                  (chain0 : CryptoVerification.LibsignalSpqrV1.Chain)
                  (hchain : (do
                    let chain1 ← match key with
                      | some es => CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf es)
                      | none => pure chain0
                    let epoch := D.msgEpoch msg
                    if epoch == 0#64 then Except.error (.panic .sendEpochUnderflow)
                    else do
                      let (chain2, (idx, mk)) ← CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult (chain1.sendKey hkdf (epoch - 1#64))
                      let (index, msgKey, chainPb) ← pure (idx, mk, some chain2.intoPb)
                      let msgBytes := D.msgSerialize msg index
                      match msgBytes with
                      | [] => Except.error (.panic .sendMsgEmpty)
                      | b0 :: _ =>
                        if b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8 then
                          Except.error (.panic .sendMsgBadVersion)
                        else Except.ok {
                          state := D.encodeState { inner := some (D.statesIntoPb st1), versionNegotiation := vnOpt, chain := chainPb }
                          msg := msgBytes, key := if msgKey.isEmpty then none else some msgKey
                        }) = Except.ok out) : out.msg ≠ [] := by
                cases key <;> (
                  dsimp only at hchain; obtain ⟨chain1, _, hchain⟩ := except_bind_eq_ok hchain
                  by_cases hep : (D.msgEpoch msg == 0#64) = true
                  · rw [ite_eq_left hep] at hchain; nomatch hchain
                  · rw [ite_eq_right hep] at hchain
                    obtain ⟨⟨chain2, idx, mk⟩, _, hchain⟩ := except_bind_eq_ok hchain
                    obtain ⟨⟨idx', mk', cpb⟩, hp2, hchain⟩ := except_bind_eq_ok hchain
                    injection hp2 with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩
                    rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩
                    exact finish vnOpt idx mk (some chain2.intoPb) hchain)
              unfold CryptoVerification.LibsignalSpqrV1.sendAfterStates at htop
              cases hc : pb.chain <;> rw [hc] at htop <;> dsimp only at htop
              · cases hvn : pb.versionNegotiation <;> rw [hvn] at htop <;> dsimp only at htop
                · nomatch htop
                · rename_i vn
                  by_cases hslt : BitVec.slt CryptoVerification.LibsignalSpqrV1.Version.v0.toI32 vn.minVersion = true
                  · rw [ite_eq_left hslt] at htop; obtain ⟨c, _, htop⟩ := except_bind_eq_ok htop
                    obtain ⟨_, hp, htop⟩ := except_bind_eq_ok htop; injection hp with hp; subst hp
                    exact someChain (some vn) c htop
                  · rw [ite_eq_right hslt] at htop; obtain ⟨_, hp, htop⟩ := except_bind_eq_ok htop
                    injection hp with hp; subst hp; dsimp only at htop
                    by_cases hk : key.isNone = true
                    · rw [ite_eq_left hk] at htop; obtain ⟨⟨idx, mk, cpb⟩, hp2, htop⟩ := except_bind_eq_ok htop
                      injection hp2 with hp2; rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩
                      rcases Prod.mk.inj hp3 with ⟨rfl, rfl⟩; exact finish (some vn) 0#32 [] none htop
                    · rw [ite_eq_right hk] at htop; nomatch htop
              · obtain ⟨c, _, htop⟩ := except_bind_eq_ok htop; obtain ⟨_, hp, htop⟩ := except_bind_eq_ok htop
                injection hp with hp; subst hp; exact someChain pb.versionNegotiation c htop

private theorem messageEncryptW_take_of_draw_le (interp : ExternInterpretation)
    (C : Crypto) (W_aes : Proofs.libsignal.SR.AesW) (codec : SignalMessageProtoCodec) (addrs : Option HwBytes)
    (m : HwBytes) {r_coins : HwBytes} {n : Nat} (hr : r_coins.length = 64) (hn_le : n ≤ 64)
    (st : SessionState HwBytes) (hd_le : Slots.trSendDrawSizeOf interp st.pqRatchetState ≤ n) :
    Proofs.libsignal.SR.SessionState.messageEncryptW C W_aes codec (Slots.pureSpqrOf interp) addrs m (r_coins.take n) st =
      Proofs.libsignal.SR.SessionState.messageEncryptW C W_aes codec (Slots.pureSpqrOf interp) addrs m r_coins st := by
  change Proofs.libsignal.SR.SessionState.messageEncryptW C W_aes codec (Cli.pureSpqrOf interp) addrs m (r_coins.take n) st =
    Proofs.libsignal.SR.SessionState.messageEncryptW C W_aes codec (Cli.pureSpqrOf interp) addrs m r_coins st
  rw [← sessionState_messageEncryptW_sendCoinsOf interp C W_aes codec addrs m hr st]
  unfold Proofs.libsignal.SR.SessionState.messageEncryptW
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨e | otr, taken⟩
  · rfl
  · have hpqr : otr.pqrState = st.pqRatchetState :=
      (TR.SendRetCoinsCliPure.mut_exec_fromSessionState_props st otr taken hfrom).1
    dsimp only
    have hlen_n : Slots.trSendDrawSizeOf interp otr.pqrState ≤ (r_coins.take n).length := by
      rw [hpqr, List.length_take_of_le (by omega)]; exact hd_le
    obtain ⟨hsend, hpan⟩ := send_take_trSendDrawSize_spqrModelOf interp otr.pqrState (r_coins.take n) hlen_n
    have htake_eq : (r_coins.take n).take (Slots.trSendDrawSizeOf interp otr.pqrState) =
        sendCoinsOf interp st.pqRatchetState r_coins := by rw [hpqr, List.take_take, Nat.min_eq_left hd_le]; rfl
    rw [htake_eq] at hsend hpan
    have hpan_eq : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).sendPanics otr.pqrState (r_coins.take n) =
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).sendPanics otr.pqrState
          (sendCoinsOf interp st.pqRatchetState r_coins) := Bool.eq_iff_iff.mpr hpan.symm
    unfold Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW Cli.pureSpqrOf
    simp only [mut_exec_bind, mut_exec_get, hpan_eq, hsend.symm]

private theorem sndWhisperRetOut_of_pqSendModel_take {interp : ExternInterpretation} {W : PEParams}
    (hb : ModelHookBridge interp W) (r : ProtocolSetup) (p : Participant) {st st' : PqParty} {x : RecordExtras}
    {g : GhostState HwBytes} {pt r_coins wire : HwBytes} {n : Nat} (hwf : PqxdhPartyInSpecDomain W st)
    (hsess : st.session = some (x, g)) (hpfalse : g.session.pendingPreKey = false)
    (hooo : SpqrOooBounded g.session.pqRatchetState) (hpt : pt.length < 2 ^ 32)
    (hrcoins : r_coins.length = 64) (hn_le : n ≤ 64)
    (hd_le : Slots.trSendDrawSizeOf interp g.session.pqRatchetState ≤ n)
    (hmodel : pqSendModel W st pt r_coins = some (some (st', wire))) :
    SndWhisperRetOut interp r p (encodeRecordUnderExtras (fun _ => x) g) pt r_coins (sendMidOf (r_coins.take n))
      (encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1) wire := by
  let coins := r_coins.take n
  obtain ⟨msg, s, _, henc, _, _, hsend1, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hmsg_lt := pqSendModel_wire_lt_2_64 hwf hsess hpt hmodel
  have hencW : Proofs.libsignal.SR.SessionState.messageEncryptW (cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) protoSignalCodec (Slots.pureSpqrOf interp)
      ((pqxdhSessionParams W).sendAddrs g.party) pt coins g.session = (.ok msg, s) := by
    dsimp only [coins]; rw [messageEncryptW_take_of_draw_le interp (cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) protoSignalCodec ((pqxdhSessionParams W).sendAddrs g.party) pt hrcoins hn_le g.session hd_le]
    exact (messageEncrypt_eq_messageEncryptW_of_bridge hb ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session).symm.trans henc
  obtain ⟨heval, hs_pend, hs_rc, salt, msgPq, hsend⟩ :=
    pureEvalSendWire_of_messageEncryptW hwf hsess pt coins msg s (fun hp => by rw [hpfalse] at hp; cases hp) hencW
  have hs_pend_false : s.pendingPreKey = false := hs_pend.trans hpfalse
  have hrc₀ := recordCanonical_Q_of_wfPq hwf hsess
  have hlen31 := (reachPqInvPure_of_wfPq hwf hsess).2.2
  have hrec_lt₀ : (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length < 2 ^ 32 - 2 ^ 20 := by
    rw [← encodeRecordX_eq_encodeRecord_pqSession]; omega
  obtain ⟨hooo', hpost32_rec⟩ := TR.SendRetCoinsCliPure.encodeRecord_lt_32_of_send_growth
    interp (pqSession x g) s coins salt msgPq hrc₀.2.2 hooo hrec_lt₀ hs_rc hsend
  have hsess_upd : { pqSession x g with state := s } = pqSession x { g with session := s } := by
    simp [pqSession, hpfalse, hs_pend_false]
  rw [hsess_upd, ← encodeRecordX_eq_encodeRecord_pqSession] at hpost32_rec
  have hret_eq : encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1 =
      encodeRecordUnderExtras (fun _ => x) { g with session := s } := by rw [hsend1]; rfl
  obtain ⟨g₀', hR', _, hs'⟩ := reachPq_afterSend_of_wfPq hwf hsess henc
  obtain ⟨hrc', hscope_in', hscope_q', hrem_some'⟩ := postSend_canon_of_reachPq hR' hs' hpost32_rec
  refine ⟨by rw [hret_eq]; omega, hmsg_lt, fun _ hfit => ?_, fun _ => ?_⟩
  · rw [hret_eq] at hfit ⊢
    exact ⟨pqSession x { g with session := s }, hrc', hscope_in', hscope_q', hrem_some',
      by omega, pqSession_pendingPreKey_of_false x { g with session := s } hs_pend_false, hfit, hooo'⟩
  · refine ⟨pqSession x g, coins, hrc₀, sendMidOf_cases coins, List.take_prefix n r_coins, ?_⟩
    rw [hret_eq, hwire]; simpa [hpfalse] using heval

private theorem sndPendingRetOut_of_pqSendModel_take {interp : ExternInterpretation} {W : PEParams}
    (hb : ModelHookBridge interp W) (r : ProtocolSetup) {st st' : PqParty} {x : RecordExtras}
    {g : GhostState HwBytes} {pt r_coins wire : HwBytes} {n : Nat} (hwf : PqxdhPartyInSpecDomain W st)
    (hsess : st.session = some (x, g)) (hpend : g.session.pendingPreKey = true) (hpartyA : g.party = .A)
    (hpt : pt.length < 2 ^ 32) (hrcoins : r_coins.length = 64) (hn_le : n ≤ 64)
    (hd_le : Slots.trSendDrawSizeOf interp g.session.pqRatchetState ≤ n)
    (hmodel : pqSendModel W st pt r_coins = some (some (st', wire))) :
    SndPendingRetOut interp r (encodeRecordUnderExtras (fun _ => x) g) pt r_coins (sendMidOf (r_coins.take n))
      (encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1) wire := by
  let coins := r_coins.take n
  obtain ⟨msg, s, _, henc, _, _, hsend1, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hmsg_lt := pqSendModel_wire_lt_2_64 hwf hsess hpt hmodel
  have hencW : Proofs.libsignal.SR.SessionState.messageEncryptW (cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) protoSignalCodec (Slots.pureSpqrOf interp)
      ((pqxdhSessionParams W).sendAddrs g.party) pt coins g.session = (.ok msg, s) := by
    dsimp only [coins]; rw [messageEncryptW_take_of_draw_le interp (cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) protoSignalCodec ((pqxdhSessionParams W).sendAddrs g.party) pt hrcoins hn_le g.session hd_le]
    exact (messageEncrypt_eq_messageEncryptW_of_bridge hb ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session).symm.trans henc
  obtain ⟨heval, hs_pend, hs_rc, salt, msgPq, hsend⟩ :=
    pureEvalSendWire_of_messageEncryptW hwf hsess pt coins msg s (fun _ => hpartyA) hencW
  have hs_pend_true : s.pendingPreKey = true := hs_pend.trans hpend
  have hrc₀ := recordCanonical_Q_of_wfPq hwf hsess
  refine ⟨hmsg_lt, fun sess hrc_sess _ _ _ _ hrec_lt hooo_sess => ?_⟩
  have hsess_eq : sess = pqSession x g := recordCanonical_Q_inj hrc_sess hrc₀
  subst hsess_eq
  have hrec_lt₀ : (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length < 2 ^ 32 - 2 ^ 20 := by
    rw [← encodeRecordX_eq_encodeRecord_pqSession]; exact hrec_lt
  obtain ⟨_, hpost32_rec⟩ := TR.SendRetCoinsCliPure.encodeRecord_lt_32_of_send_growth
    interp (pqSession x g) s coins salt msgPq hrc₀.2.2 hooo_sess hrec_lt₀ hs_rc hsend
  have hsess_upd : { pqSession x g with state := s } = pqSession x { g with session := s } := by
    simp [pqSession, hpend, hs_pend_true]
  rw [hsess_upd, ← encodeRecordX_eq_encodeRecord_pqSession] at hpost32_rec
  have hret_eq : encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1 =
      encodeRecordUnderExtras (fun _ => x) { g with session := s } := by rw [hsend1]; rfl
  obtain ⟨g₀', hR', _, hs'⟩ := reachPq_afterSend_of_wfPq hwf hsess henc
  obtain ⟨hrc', hscope_in', hscope_q', hrem_some'⟩ := postSend_canon_of_reachPq hR' hs' hpost32_rec
  have hpwc' : PendingWireRecCanon (encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1) := by
    rw [hret_eq]; exact ⟨pqSession x { g with session := s }, hrc', hscope_in', hscope_q', hrem_some', by omega⟩
  refine ⟨hpwc', coins, sendMidOf_cases coins, List.take_prefix n r_coins, ?_⟩
  rw [hret_eq, hwire]; simpa [hpend] using heval

/-! ## Exit-0 `XplBlock` Draw-Size Lower Bound -/

private theorem aesCbcEncrypt_length_eq (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k₁ k₂ : CryptoGames.CBC.AesKey) (iv₁ iv₂ : CryptoGames.CBC.Block) (pt : HwBytes) :
    (CryptoGames.LibsignalSession.aesCbcEncrypt E k₁ iv₁ pt).length =
      (CryptoGames.LibsignalSession.aesCbcEncrypt E k₂ iv₂ pt).length := by
  have hblk : ∀ l : List (BitVec 128), (l.flatMap CryptoGames.CBC.blockToBytesLE).length = 16 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons b t ih =>
      have hb : (CryptoGames.CBC.blockToBytesLE b).length = 16 := by simp [CryptoGames.CBC.blockToBytesLE]
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]; omega
  unfold CryptoGames.LibsignalSession.aesCbcEncrypt
  rw [hblk, hblk, List.Vector.toList_length, List.Vector.toList_length]

private theorem computeMac_length_eq_8 (interp : ExternInterpretation)
    (localId remote : CryptoGames.LibsignalSession.IdentityKey) (macKey : CryptoGames.CBC.AesKey) (content : HwBytes) :
    (CryptoGames.LibsignalSession.computeMac
      (DY.Libsignal.Refinement.sha256CompressFunction interp) localId remote macKey content).length = 8 := by
  unfold CryptoGames.LibsignalSession.computeMac CryptoGames.HMAC.hmacSha256Trunc8
  simp [CryptoGames.HMAC.hmacWith]

private theorem encodeWith_canonical_length_eq {f₁ f₂ : DY.Libsignal.Refinement.WireFields}
    (hv : f₁.version = f₂.version) (hrk : f₁.ratchetKey = f₂.ratchetKey) (hc : f₁.counter = f₂.counter)
    (hpc : f₁.previousCounter = f₂.previousCounter) (hct : f₁.ciphertext.length = f₂.ciphertext.length) :
    (DY.Libsignal.Refinement.encodeWith DY.TrWire.canonicalVariation f₁).length =
      (DY.Libsignal.Refinement.encodeWith DY.TrWire.canonicalVariation f₂).length := by
  simp [DY.Libsignal.Refinement.encodeWith, DY.TrWire.canonicalVariation, DY.TrWire.FieldItem.encode,
    DY.Libsignal.Refinement.knownValue?, DY.Libsignal.Refinement.encodeField, hv, hrk, hc, hpc, hct]

private theorem pq_not_nil_vs_nil_absurd {p₁ p₂ pq₁ a₁ a₂ mac₁ mac₂ : HwBytes}
    (heq : p₁ ++ (DY.Libsignal.Refinement.encodeField 5 0 0 (.bytes pq₁) ++ a₁ ++ mac₁) = p₂ ++ (a₂ ++ mac₂))
    (hlen_p : p₁.length = p₂.length) (hmac₁ : mac₁.length = 8) (hmac₂ : mac₂.length = 8) (hpq₁ : pq₁ ≠ [])
    (ha₂ : a₂ = [] ∨ ∃ b₂, a₂ = DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes b₂)) : False := by
  have hd := congrArg (List.drop p₁.length) heq
  rw [List.drop_left' rfl, List.drop_left' hlen_p.symm] at hd
  have h42 : DY.Libsignal.Refinement.paddedVarint 42 0 = [42#8] := by unfold DY.Libsignal.Refinement.paddedVarint; decide
  rcases ha₂ with rfl | ⟨b₂, rfl⟩
  · have hlhs := congrArg List.length hd
    have hvn := List.length_pos_of_ne_nil (DY.Libsignal.Refinement.paddedVarint_ne_nil pq₁.length 0)
    have hpq_pos := List.length_pos_of_ne_nil hpq₁
    simp only [DY.Libsignal.Refinement.encodeField, h42, List.nil_append,
      List.length_append, List.length_cons, List.length_nil, hmac₁, hmac₂] at hlhs; omega
  · have h50 : DY.Libsignal.Refinement.paddedVarint 50 0 = [50#8] := by unfold DY.Libsignal.Refinement.paddedVarint; decide
    have hh := congrArg List.head? hd
    simp only [DY.Libsignal.Refinement.encodeField, h42, h50, List.cons_append, List.head?_cons] at hh
    exact absurd hh (by decide)

private theorem snd_encrypt_vis_match_full {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {p : Participant} {stateIdx cLen : Nat} {wrap : Option (Nat × Nat)}
    {pt out coins body : HwBytes} {mid : List MachineEvent}
    (hm : List.Forall₂ (EventMatchesEntry interp r S g) ((.pt pt :: mid) ++ [.send out])
      ((Move.encrypt p stateIdx cLen (tr.length + 2) wrap).vis tr))
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    (hout_lt : out.length < 2 ^ 64) (hsb : sentBody out = some body) :
    ∃ st, ((DY.PersistentLocalState.getLocalState p stateIdx :
        DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run tr).1 = some st ∧
      st.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max ∧
      gamma interp S g (randTerm tr.length 32) = pt ∧
      gamma interp S g (randTerm (tr.length + 1) cLen) = coins ∧
      body = gamma interp S g (Symbolic.Swarm.CREF.SendWire.encMsg st cLen tr.length) := by
  obtain ⟨⟨st, hst, hns⟩, hpt_gam, hcoins_gam⟩ := snd_encrypt_vis_match hm hmid
  let w := Symbolic.Swarm.CREF.SendWire.encMsg st cLen tr.length
  have hsend_m : EventMatchesEntry interp r S g (.send out)
      (wrapVisEntry tr wrap (Symbolic.Swarm.CREF.SendWire.trEntry .send w)) := by
    rw [visOf_encrypt_wrap_eq] at hm
    by_cases hc0 : cLen = 0
    · subst hc0; rw [Symbolic.Swarm.CREF.SendWire.visOf_encrypt_zero hst hns] at hm
      rcases hmid with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
      · simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.forall₂_cons] at hm
        exact hm.2.1
      · have hlen := hm.length_eq; simp at hlen
    · rw [Symbolic.Swarm.CREF.SendWire.visOf_encrypt_ne_zero hst hns hc0] at hm
      rcases hmid with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
      · have hlen := hm.length_eq; simp at hlen
      · simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.forall₂_cons] at hm
        exact hm.2.2.1
  refine ⟨st, hst, hns, hpt_gam, hcoins_gam, ?_⟩
  cases wrap with
  | none =>
    obtain ⟨t, ht_eq, hout_eq⟩ : ∃ t, ([w] : List DY.Bytes) = [t] ∧ out = wireWhisperTag :: gamma interp S g t := hsend_m.2
    have htw : w = t := List.singleton_injective ht_eq; subst htw
    rw [hout_eq] at hsb; simp only [sentBody, ↓reduceIte, Option.some.injEq] at hsb; exact hsb.symm
  | some ec =>
    rcases ec with ⟨e, c⟩
    obtain ⟨ids, hsend⟩ : ∃ ids, SendMatches interp r S g (some ids) out (received tr [e, c] ++ [w]) := hsend_m.2
    rcases hterms : received tr [e, c] ++ [w] with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg_t, _ | _⟩⟩⟩
    · rw [hterms] at hsend; exact False.elim hsend
    · rw [hterms] at hsend; exact False.elim hsend
    · rw [hterms] at hsend; exact False.elim hsend
    · rw [hterms] at hsend; obtain ⟨_, _, _, _, hm_eq⟩ := hsend
      have hlast := congrArg List.getLast? hterms
      simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil w []),
        List.getLast?_singleton, List.getLast?_cons_cons, Option.some.injEq] at hlast
      subst hlast; rw [hm_eq] at hsb hout_lt
      exact Symbolic.Swarm.CREF.TR.SrHonestVer.preKeySend_sentBody_strip_srhv hout_lt hsb
    · rw [hterms] at hsend; exact False.elim hsend

private theorem gamma_encMsg_nil_pq_eq
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {g : Ghost}
    {st : _root_.DY.Libsignal.TripleRatchet.TRState} {cLen ts : Nat} {pt coins : HwBytes}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interp) (hagree : ModelAgree interp P)
    (hpt_gam : gamma interp (compSemOf interp r) g (randTerm ts 32) = pt)
    (hcoins_gam : gamma interp (compSemOf interp r) g (randTerm (ts + 1) cLen) = coins)
    (hlt : coins.length < Slots.trSendDrawSizeOf interp (gamma interp (compSemOf interp r) g st.spqr)) :
    ∃ (ct_mod a_mod mac_mod : HwBytes) (k_mod : CryptoGames.CBC.AesKey) (iv_mod : CryptoGames.CBC.Block),
      gamma interp (compSemOf interp r) g (Symbolic.Swarm.CREF.SendWire.encMsg st cLen ts) =
        DY.Libsignal.Refinement.encodeWith DY.TrWire.canonicalVariation
          ⟨4, gamma interp (compSemOf interp r) g (DY.DiffieHellman.dhPk st.dhs),
            st.ns.toNat, st.pn.toNat, ct_mod⟩ ++ (a_mod ++ mac_mod) ∧
      ct_mod = CryptoGames.LibsignalSession.aesCbcEncrypt P.C.E k_mod iv_mod pt ∧
      (a_mod = [] ∨ ∃ b₂, a_mod = DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes b₂)) ∧
      mac_mod.length = 8 := by
  let S := compSemOf interp r
  let coinsTerm := randTerm (ts + 1) cLen
  let pqTerm := (DY.Spqr.spqrSend st.spqr coinsTerm).2.2
  let keys := _root_.DY.Libsignal.TripleRatchet.trMsgKeys
    (DY.Spqr.spqrSend st.spqr coinsTerm).2.1 (_root_.DY.Libsignal.TripleRatchet.kdfCk st.cks).2
  let ctTerm := DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ts 32)
  let wireTerm := Symbolic.Swarm.CREF.SendWire.encWire st cLen ts
  let macTerm := Symbolic.Swarm.CREF.SendWire.encMac st cLen ts
  have hpq_gam : gamma interp S g pqTerm = [] := by
    have h1 := TR.SendRetCoinsCliPure.gamma_spqrSendMsg interp S g st.spqr coinsTerm
    change gamma interp S g pqTerm = S.sendMsg (gamma interp S g st.spqr) (gamma interp S g coinsTerm) at h1
    rw [h1, hcoins_gam]; exact spqrSendMsgOf_eq_nil_of_lt_draw interp hEq _ coins hlt
  have hlen_ck : (gamma interp S g keys.cipherKey).length = 32 := by
    dsimp only [keys, DY.Libsignal.TripleRatchet.trMsgKeys]
    rw [TR.SendRetCoinsCliPure.gamma_hkdfBlock1_tr]; exact Symbolic.Swarm.CREF.TR.length_hmacWith _ _ _
  have hlen_iv : ((gamma interp S g keys.iv).take 16).length = 16 := by
    have hiv32 : (gamma interp S g keys.iv).length = 32 := by
      dsimp only [keys, DY.Libsignal.TripleRatchet.trMsgKeys]
      rw [TR.SendRetCoinsCliPure.gamma_hkdfBlock3_tr]; exact Symbolic.Swarm.CREF.TR.length_hmacWith _ _ _
    rw [List.length_take]; omega
  have hct_eq : gamma interp S g ctTerm =
      CryptoGames.LibsignalSession.aesCbcEncrypt P.C.E
        (CryptoGames.HKDF.bytesToKey32 (gamma interp S g keys.cipherKey))
        (CryptoGames.CBC.bytesToBlock ((gamma interp S g keys.iv).take 16)) pt := by
    dsimp only [ctTerm]
    rw [TR.SendRetCoinsCliPure.gamma_symEnc_tr, hpt_gam, hagree.2.1 pt _ _ hlen_ck hlen_iv, Option.getD_some]
  have hwire_def : wireTerm =
      DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn ctTerm pqTerm := rfl
  let a_mod : HwBytes :=
    if g.addr wireTerm = [] then [] else DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes (g.addr wireTerm))
  have hwire_eq : gamma interp S g wireTerm =
      DY.Libsignal.Refinement.encodeWith DY.TrWire.canonicalVariation
        ⟨4, gamma interp S g (DY.DiffieHellman.dhPk st.dhs), st.ns.toNat, st.pn.toNat, gamma interp S g ctTerm⟩ ++ a_mod := by
    dsimp only [a_mod]; rw [hwire_def, gamma_trHonestWireMsg_addr,
      DY.Libsignal.TripleRatchet.Refinement.trWireBytes_canonical, hpq_gam]
    simp only [↓reduceIte, List.append_nil]
  have ha_mod : a_mod = [] ∨ ∃ b₂, a_mod = DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes b₂) := by
    dsimp only [a_mod]; split_ifs with h <;> [exact Or.inl rfl; exact Or.inr ⟨_, rfl⟩]
  have hmac_len : (gamma interp S g macTerm).length = 8 := by
    change (gamma interp S g (DY.Trunc.trunc8 (DY.KdfExtract.kdfExtract keys.macKey
      (DY.Concat.concat st.myIk (DY.Concat.concat st.peerIk wireTerm))))).length = 8
    rw [TR.SendRetCoinsCliPure.gamma_trunc8_tr, TR.SendRetCoinsCliPure.gamma_kdfExtract_tr,
      List.length_take, Symbolic.Swarm.CREF.TR.length_hmacWith]; decide
  refine ⟨gamma interp S g ctTerm, a_mod, gamma interp S g macTerm, _, _, ?_, hct_eq, ha_mod, hmac_len⟩
  change gamma interp S g (DY.Concat.concat wireTerm macTerm) = _
  rw [TR.SendRetCoinsCliPure.gamma_concat_tr, hwire_eq, List.append_assoc]

private theorem xplBlock_send_ret_unpack {interp : ExternInterpretation} {r : ProtocolSetup}
    {who : List Participant} {g : Ghost} {ms₀ δ : List Move} {τ_pre : List MachineEvent}
    {p : Participant} {pt coins out : HwBytes}
    (hB : XplBlock interp r (compSemOf interp r) who g ms₀ δ τ_pre ((.pt pt :: sendMidOf coins) ++ [.send out]))
    (hdf : DeltaFaithful p (runTraceMoves r ms₀) δ) (hrole₀ : RoleSnapshots r (runTraceMoves r ms₀)) :
    ∃ pre stateIdx cLen wrap post,
      δ = pre ++ Move.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post ∧
      RpkCli.XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) ∧
      RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) ∧
      List.Forall₂ (EventMatchesEntry interp r (compSemOf interp r) g)
        ((.pt pt :: sendMidOf coins) ++ [.send out])
        ((Move.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap).vis
          (runTraceMoves r (ms₀ ++ pre))) := by
  have hmid := sendMidOf_cases coins
  obtain ⟨pre, m, post, rfl, hpre, ⟨hsb_me, hsend_mv⟩, hpost⟩ :=
    xplInv_send hB hdf (snd_ret_blockShape pt out (sendMidOf coins) ⟨coins, hmid⟩)
  obtain ⟨me, stateIdx, cLen, pqIdx, wrap, rfl⟩ := hsend_mv ⟨.send out, by simp, rfl⟩
  have hme_eq : p = me := hsb_me.symm; subst me
  have hpq_idx : pqIdx = (runTraceMoves r (ms₀ ++ pre)).length + 2 := snd_encrypt_pqIdx hB.run.2.2.2.2.1
  subst hpq_idx
  rw [← Symbolic.Swarm.CREF.TR.runTrace_append r ms₀ pre] at hpost
  refine ⟨pre, stateIdx, cLen, wrap, post, rfl, ?_,
    snd_roleSnapshots_quiet (movesFrom_mono (fun _ _ h => h.2) _ _ hpre) hrole₀, ?_⟩
  · rw [Symbolic.Swarm.CREF.TR.runTrace_append]
    exact RpkCli.XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  · have hfor := hB.matched
    rw [Symbolic.Swarm.CREF.TR.runMoves_append, (snd_invisible_runMoves hpre).1,
      List.nil_append, ← Symbolic.Swarm.CREF.TR.runTrace_append] at hfor
    simpa [runMoves, (snd_invisible_runMoves hpost).1] using hfor

private theorem whisper_exit0_draw_le {interp : ExternInterpretation} {P : PEParams}
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hb : ModelHookBridge interp P)
    {r : ProtocolSetup} {who : List Participant} {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ_pre : List MachineEvent} {p : Participant} {st st' : PqParty} {x : RecordExtras}
    {g_st : GhostState HwBytes} {pt r_coins out : HwBytes} {n : Nat} {g : Ghost} {ms₀ δ : List Move}
    (hwf_st : PqxdhPartyInSpecDomain P st) (hsess : st.session = some (x, g_st)) (hpfalse : g_st.session.pendingPreKey = false)
    (hpt : pt.length < 2 ^ 32) (hmodel : pqSendModel P st pt r_coins = some (some (st', out)))
    (hrec : records p = some (encodeRecordUnderExtras (fun _ => x) g_st))
    (hB : XplBlock interp r (compSemOf interp r) who g ms₀ δ τ_pre ((.pt pt :: sendMidOf (r_coins.take n)) ++ [.send out]))
    (hdf : DeltaFaithful p (runTraceMoves r ms₀) δ)
    (hrel₀ : PureCRelAt interp r (compSemOf interp r) g ms₀ records sent accepted τ_pre) :
    Slots.trSendDrawSizeOf interp g_st.session.pqRatchetState ≤ n := by
  by_contra hnot
  have hlt_n := Nat.lt_of_not_ge hnot
  let S := compSemOf interp r; let recBytes := encodeRecordUnderExtras (fun _ => x) g_st; let coins := r_coins.take n
  obtain ⟨pre, stateIdx, cLen, wrap, post, rfl, hq1, hrole₁, hm_vis⟩ := xplBlock_send_ret_unpack hB hdf hrel₀.2.2.2
  obtain ⟨msg, s, _, henc, _, _, _, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hout_lt := pqSendModel_wire_lt_2_64 hwf_st hsess hpt hmodel
  have hencW₀ : Proofs.libsignal.SR.SessionState.messageEncryptW (cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) protoSignalCodec (Slots.pureSpqrOf interp)
      ((pqxdhSessionParams P).sendAddrs g_st.party) pt r_coins g_st.session = (.ok msg, s) :=
    (messageEncrypt_eq_messageEncryptW_of_bridge hb ((pqxdhSessionParams P).sendAddrs g_st.party) pt r_coins g_st.session).symm.trans henc
  obtain ⟨heval_r, _, _, salt?, pqMsgBytes, hsend_r⟩ :=
    pureEvalSendWire_of_messageEncryptW hwf_st hsess pt r_coins msg s (fun hp => by rw [hpfalse] at hp; cases hp) hencW₀
  simp only [hpfalse, Bool.false_eq_true, ↓reduceIte] at heval_r
  have hwire_w : out = wireWhisperTag :: msg.serialized := by
    have hw0 : out = wireWhisper :: msg.serialized := by simpa [hpfalse] using hwire
    exact hw0
  have hsb_out : sentBody out = some msg.serialized := by rw [hwire_w]; simp [sentBody]
  obtain ⟨st_m, hst_m, hns_m, hpt_gam, hcoins_gam, hbody_gam⟩ :=
    snd_encrypt_vis_match_full hm_vis (sendMidOf_cases coins) hout_lt hsb_out
  have hss : SingleSession recBytes := singleSession_encodeRecordX_of_wfPq hwf_st hsess
  have hnpend : ¬ PureRecPending recBytes := fun hp_pure => by
    have hp_t := (recPending_encodeRecordX_iff hwf_st hsess).mp (recPending_iff_pureRecPending.mpr hp_pure)
    rw [hpfalse] at hp_t; cases hp_t
  have hinv_p₀ : Symbolic.Swarm.CREF.TR.PureTRRecordStateInv interp r S (pureTrSlots r) g ms₀
      (fun q => if q = p then some recBytes else none) :=
    Or.resolve_right (SndPure.pureCRecRelH_single (hrel₀.1 p recBytes hrec).2.2 hss)
      (not_alice_and_aliceInitPending_of_not_recPending hnpend)
  obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀_0, hcur₀_0, hrel_st₀, _, _, hks₀, _⟩ := hinv_p₀ p recBytes (by simp)
  have hcur_m := snd_isCurrentSnapshot_of_encrypt hB.run.2.2.1.1 hst_m hns_m
  have hst₀_1 : ((DY.PersistentLocalState.getLocalState p stateIdx₀ :
      DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r (ms₀ ++ pre))).1 = some st₀ := by
    rwa [RpkCli.XplQuiet.quiet_getLocalState hq1]
  have hcur₀_1 : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r (ms₀ ++ pre)) stateIdx₀ = true := by
    rwa [RpkCli.XplQuiet.quiet_isCurrentSnapshot hq1]
  obtain ⟨rfl, rfl⟩ := isCurrentSnapshot_unique_of_role hrole₁ hst_m hst₀_1 hcur_m hcur₀_1
  let sess := pqSession x g_st
  obtain ⟨hnorm_eq, _, _⟩ := TR.SendRetCoinsCliPure.rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀
    (recordCanonical_Q_of_wfPq hwf_st hsess)
  have hrel_sess : Symbolic.Swarm.CREF.TR.StateRel interp S g st_m
      (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec sess) := by
    rw [← TR.SendRetCoinsCliPure.stateRel_sessionToRecordRecPending_iff, ← TR.SendRetCoinsCliPure.stateRel_normPending_iff,
      ← hnorm_eq, TR.SendRetCoinsCliPure.stateRel_normPending_iff]; exact hrel_st₀
  obtain ⟨hver, hpctr, hpq_gam, _, ⟨remote, hrem, _⟩, ⟨sc, hsc, hpub, _, hidx, _⟩⟩ :=
    TR.SendRetCoinsCliPure.stateRel_sessionToRecordRec_extract_TR interp S g st_m sess hrel_sess
  have hrk_gam := TR.SendRetCoinsCliPure.ratchetKey_publicKey_bytes_eq_gamma_dhPk_tr interp hext.1 S g st_m sc hks₀.dhs_len hpub
  have hppk : sess.pendingPreKey = none := by simp [sess, pqSession, hpfalse]
  have hsend_sess : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).send
      sess.state.pqRatchetState r_coins = some (s.pqRatchetState, salt?, pqMsgBytes) := by rw [pqSession_state]; exact hsend_r
  obtain ⟨_, hout_exec⟩ := TR.SendRetCoinsCliPure.pureEvalSendWire_exec (cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
    (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp) sess none pt r_coins _ sc remote
    s.pqRatchetState pqMsgBytes salt? heval_r hppk hver hsc hrem hsend_sess
  rw [Proofs.libsignal.Hooks2.cryptoOf'_F] at hout_exec; injection hout_exec with _ hmsg_exec
  let F := DY.Libsignal.Refinement.sha256CompressFunction interp
  let mk := (sc.chainKey.messageKeys F).generateKeys F salt?
  let ctext_bin := (Proofs.libsignal.SR.interpW interp).enc mk.cipherKey mk.iv pt
  have hmsg_ser : msg.serialized = (CryptoGames.LibsignalSession.SignalMessage.new F protoSignalCodec 4#8
      mk.macKey none sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter
      ctext_bin sess.state.localIdentity remote pqMsgBytes).serialized := List.tail_eq_of_cons_eq hmsg_exec
  have hw_lt_new : (wireWhisperTag :: (CryptoGames.LibsignalSession.SignalMessage.new F protoSignalCodec 4#8
      mk.macKey none sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter
      ctext_bin sess.state.localIdentity remote pqMsgBytes).serialized).length < 2 ^ 64 := by
    rw [← hmsg_ser, ← hwire_w]; exact hout_lt
  obtain ⟨hct_lt, hpq_lt⟩ := TR.SendRetCoinsCliPure.ctext_and_pq_length_lt_of_serialized F mk.macKey
    sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes sess.state.localIdentity remote hw_lt_new
  have hpq_ne : pqMsgBytes ≠ [] := spqrModelOf_send_msg_ne_nil_of_draw_pos interp (by omega) hsend_r
  have hcoins_lt : coins.length < Slots.trSendDrawSizeOf interp (gamma interp S g st_m.spqr) := by
    have hc_le : coins.length ≤ n := List.length_take_le n r_coins
    have hpq_eq : g_st.session.pqRatchetState = gamma interp S g st_m.spqr := by simpa [sess, pqSession_state] using hpq_gam
    rw [← hpq_eq]; omega
  obtain ⟨ct_mod, a_mod, mac_mod, k_mod, iv_mod, hgam_exp, hct_mod, ha_mod, hmac_mod⟩ :=
    gamma_encMsg_nil_pq_eq hext.1 hagree hpt_gam hcoins_gam hcoins_lt
  have hct_bin_eq : ctext_bin = CryptoGames.LibsignalSession.aesCbcEncrypt P.C.E mk.cipherKey mk.iv pt := by
    dsimp only [ctext_bin]; rw [hb.aesCbc]; rfl
  let mac_bin := CryptoGames.LibsignalSession.computeMac F sess.state.localIdentity remote mk.macKey
    (CryptoGames.LibsignalSession.serializeContent protoSignalCodec 4#8 sc.ratchetKey.publicKey
      sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes none)
  have hbin_exp : msg.serialized = DY.Libsignal.Refinement.encodeWith DY.TrWire.canonicalVariation
      ⟨4, sc.ratchetKey.publicKey.bytes.toList, sc.chainKey.index.toNat, sess.state.previousCounter.toNat, ctext_bin⟩ ++
      (DY.Libsignal.Refinement.encodeField 5 0 0 (.bytes pqMsgBytes) ++ [] ++ mac_bin) := by
    rw [hmsg_ser]; dsimp only [CryptoGames.LibsignalSession.SignalMessage.new]
    change CryptoGames.LibsignalSession.serializeContent protoSignalCodec 4#8 sc.ratchetKey.publicKey
      sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes none ++ mac_bin = _
    rw [TR.SendRetCoinsCliPure.serializeContent_tr_eq_encodeWith _ _ _ _ _ hct_lt hpq_lt]
    simp only [hpq_ne, ↓reduceIte, List.append_nil, List.append_assoc]
  have hlen_p := encodeWith_canonical_length_eq (f₁ := ⟨4, sc.ratchetKey.publicKey.bytes.toList,
      sc.chainKey.index.toNat, sess.state.previousCounter.toNat, ctext_bin⟩)
    (f₂ := ⟨4, gamma interp S g (DY.DiffieHellman.dhPk st_m.dhs), st_m.ns.toNat, st_m.pn.toNat, ct_mod⟩)
    rfl hrk_gam (by rw [hidx]; rfl) (by rw [hpctr]; rfl)
    (by rw [hct_bin_eq, hct_mod]; exact aesCbcEncrypt_length_eq P.C.E _ _ _ _ pt)
  exact pq_not_nil_vs_nil_absurd (hbin_exp.symm.trans (hbody_gam.trans hgam_exp))
    hlen_p (computeMac_length_eq_8 interp _ _ _ _) hmac_mod hpq_ne ha_mod

private theorem pending_exit0_draw_le {interp : ExternInterpretation} {P : PEParams}
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hb : ModelHookBridge interp P)
    {r : ProtocolSetup} {who : List Participant} {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ_pre : List MachineEvent} {p : Participant} {st st' : PqParty} {x : RecordExtras}
    {g_st : GhostState HwBytes} {pt r_coins out : HwBytes} {n : Nat} {g : Ghost} {ms₀ δ : List Move}
    (hwf_st : PqxdhPartyInSpecDomain P st) (hsess : st.session = some (x, g_st)) (hpend : g_st.session.pendingPreKey = true)
    (hpartyA_fn : ∀ x₀ g₀, st.session = some (x₀, g₀) → p = r.alice → g₀.party = .A)
    (hpt : pt.length < 2 ^ 32) (hmodel : pqSendModel P st pt r_coins = some (some (st', out)))
    (hrec : records p = some (encodeRecordUnderExtras (fun _ => x) g_st))
    (hB : XplBlock interp r (compSemOf interp r) who g ms₀ δ τ_pre ((.pt pt :: sendMidOf (r_coins.take n)) ++ [.send out]))
    (hdf : DeltaFaithful p (runTraceMoves r ms₀) δ)
    (hrel₀ : PureCRelAt interp r (compSemOf interp r) g ms₀ records sent accepted τ_pre) :
    Slots.trSendDrawSizeOf interp g_st.session.pqRatchetState ≤ n := by
  by_contra hnot
  have hlt_n := Nat.lt_of_not_ge hnot
  let S := compSemOf interp r; let recBytes := encodeRecordUnderExtras (fun _ => x) g_st
  have hlen31 : recBytes.length < 2 ^ 31 := (reachPqInvPure_of_wfPq hwf_st hsess).2.2
  have hpend_pure : PureRecPending recBytes :=
    recPending_iff_pureRecPending.mp ((recPending_encodeRecordX_iff hwf_st hsess).mpr hpend)
  obtain ⟨hp_alice, hpend₀⟩ := recPending_imp_alice_pending_of_recRel interp r S p recBytes g ms₀
    (by omega) hpend_pure (hrel₀.1 p recBytes hrec).2.2
  subst hp_alice
  have hpartyA : g_st.party = .A := hpartyA_fn x g_st hsess rfl
  let coins := r_coins.take n
  obtain ⟨pre, stateIdx, cLen, wrap, post, rfl, hq1, hrole₁, hm_vis⟩ := xplBlock_send_ret_unpack hB hdf hrel₀.2.2.2
  obtain ⟨sess, sc, remote, items, kpk, st₀, stateIdx₀, _, _, ek, ct,
    hrc, _, _, hget, hcur, _, _, _, _, hreg, hver, hpn, _, hrem, _, hsc, hrk, _, hidx,
    hppk, _, hbk, hkpk, hct_ser, hpq_gam, _, _, _, _, _, _⟩ := RpkCli.XplQuiet.quiet_aliceInitPending hq1 hpend₀
  have hsess_eq : sess = pqSession x g_st := recordCanonical_Q_inj hrc (recordCanonical_Q_of_wfPq hwf_st hsess)
  obtain ⟨msg, s, _, henc, _, _, _, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hout_lt := pqSendModel_wire_lt_2_64 hwf_st hsess hpt hmodel
  have hencW₀ : Proofs.libsignal.SR.SessionState.messageEncryptW (cryptoOf' interp)
      (Proofs.libsignal.SR.interpW interp) protoSignalCodec (Slots.pureSpqrOf interp)
      ((pqxdhSessionParams P).sendAddrs g_st.party) pt r_coins g_st.session = (.ok msg, s) :=
    (messageEncrypt_eq_messageEncryptW_of_bridge hb ((pqxdhSessionParams P).sendAddrs g_st.party) pt r_coins g_st.session).symm.trans henc
  obtain ⟨heval_r, _, _, salt?, pqMsgBytes, hsend_r⟩ :=
    pureEvalSendWire_of_messageEncryptW hwf_st hsess pt r_coins msg s (fun _ => hpartyA) hencW₀
  simp only [hpend, ↓reduceIte] at heval_r; rw [← hsess_eq] at heval_r
  have hsend_sess : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).send
      sess.state.pqRatchetState r_coins = some (s.pqRatchetState, salt?, pqMsgBytes) := by
    rw [hsess_eq, pqSession_state]; exact hsend_r
  obtain ⟨_, hexec⟩ := TR.SendRetCoinsCliPure.pureEvalSendWire_exec_pending (cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
    (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp) sess (some pqHarnessAddrBytes) pt r_coins _ sc remote
    items kpk s.pqRatchetState pqMsgBytes salt? heval_r hver hsc hrem hppk hkpk hsend_sess
  rw [Proofs.libsignal.Hooks2.cryptoOf'_F] at hexec; injection hexec with _ hmsg_eq
  let F := DY.Libsignal.Refinement.sha256CompressFunction interp
  let mk := (sc.chainKey.messageKeys F).generateKeys F salt?
  let ctext_bin := (Proofs.libsignal.SR.interpW interp).enc mk.cipherKey mk.iv pt
  let innerMsg := CryptoGames.LibsignalSession.SignalMessage.new F protoSignalCodec 4#8
    mk.macKey (some pqHarnessAddrBytes) sc.ratchetKey.publicKey sc.chainKey.index
    sess.state.previousCounter ctext_bin sess.state.localIdentity remote pqMsgBytes
  have hout_eq' : out = wirePrekeyTag :: (PreKeySignalMessage.new 4#8 r.regIdA items.preKeyId
      items.signedPreKeyId (some ⟨kpk.preKeyId, kyberKey (gamma interp S g ct)⟩)
      items.baseKey sess.state.localIdentity innerMsg).serialized := by
    have hw_out : out = wirePrekey :: firstMessageBody x g_st.session msg := by simpa [hpend] using hwire
    rw [hw_out, hmsg_eq, hreg, hct_ser]
  obtain ⟨body, hbody_tl⟩ := sentBody_pending_wire F r.regIdA items.preKeyId items.signedPreKeyId
    kpk.preKeyId (gamma interp S g ct) items.baseKey sess.state.localIdentity remote mk.macKey
    sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes (hout_eq' ▸ hout_lt)
  have hsb_some : sentBody out = some body := by
    rw [hout_eq']; cases hs : sentBody _ with
    | none => rw [hs] at hbody_tl; cases hbody_tl
    | some b => rw [hs] at hbody_tl; injection hbody_tl with hb_eq; subst hb_eq; rfl
  obtain ⟨hct_klt, hinner_lt⟩ := psm_field_lengths_lt_of_wire_lt r.regIdA items.preKeyId items.signedPreKeyId
    kpk.preKeyId (kyberKey (gamma interp S g ct)) items.baseKey sess.state.localIdentity innerMsg (hout_eq' ▸ hout_lt)
  have hpkw_eq := preKeySignalMessage_serialized_eq_preKeyWire r.regIdA items.preKeyId items.signedPreKeyId
    kpk.preKeyId items.baseKey.bytes.toList (gamma interp S g ct) items.baseKey sess.state.localIdentity
    (ecKey sess.state.localIdentity.publicKey.bytes.toList) innerMsg rfl rfl hct_klt hinner_lt
  have hbody_inner : body = innerMsg.serialized :=
    Symbolic.Swarm.CREF.TR.SrHonestVer.preKeySend_sentBody_strip_srhv
      (by rw [← hpkw_eq, ← hout_eq']; exact hout_lt) (by rw [← hpkw_eq, ← hout_eq']; exact hsb_some)
  rw [hbody_inner] at hsb_some
  obtain ⟨st_m, hst_m, hns_m, hpt_gam, hcoins_gam, hbody_gam⟩ :=
    snd_encrypt_vis_match_full hm_vis (sendMidOf_cases coins) hout_lt hsb_some
  have hcur_m := snd_isCurrentSnapshot_of_encrypt hB.run.2.2.1.1 hst_m hns_m
  obtain ⟨rfl, rfl⟩ := isCurrentSnapshot_unique_of_role hrole₁ hst_m hget hcur_m hcur
  obtain ⟨hct_lt, hpq_lt⟩ := ctext_and_pq_length_lt_of_inner_lt F mk.macKey
    sc.ratchetKey.publicKey sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes sess.state.localIdentity remote hinner_lt
  have hpq_ne : pqMsgBytes ≠ [] := spqrModelOf_send_msg_ne_nil_of_draw_pos interp (by omega) hsend_r
  have hcoins_lt : coins.length < Slots.trSendDrawSizeOf interp (gamma interp S g st_m.spqr) := by
    have hc_le : coins.length ≤ n := List.length_take_le n r_coins
    have hpq_eq : g_st.session.pqRatchetState = gamma interp S g st_m.spqr := by
      rw [← pqSession_state x g_st, ← hsess_eq]; exact hpq_gam
    rw [← hpq_eq]; omega
  obtain ⟨ct_mod, a_mod, mac_mod, k_mod, iv_mod, hgam_exp, hct_mod, ha_mod, hmac_mod⟩ :=
    gamma_encMsg_nil_pq_eq hext.1 hagree hpt_gam hcoins_gam hcoins_lt
  have hct_bin_eq : ctext_bin = CryptoGames.LibsignalSession.aesCbcEncrypt P.C.E mk.cipherKey mk.iv pt := by
    dsimp only [ctext_bin]; rw [hb.aesCbc]; rfl
  let mac_bin := CryptoGames.LibsignalSession.computeMac F sess.state.localIdentity remote mk.macKey
    (CryptoGames.LibsignalSession.serializeContent protoSignalCodec 4#8 sc.ratchetKey.publicKey
      sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes (some pqHarnessAddrBytes))
  let a_bin := DY.Libsignal.Refinement.encodeField 6 0 0 (.bytes pqHarnessAddrBytes)
  have hbin_exp : innerMsg.serialized = DY.Libsignal.Refinement.encodeWith DY.TrWire.canonicalVariation
      ⟨4, sc.ratchetKey.publicKey.bytes.toList, sc.chainKey.index.toNat, sess.state.previousCounter.toNat, ctext_bin⟩ ++
      (DY.Libsignal.Refinement.encodeField 5 0 0 (.bytes pqMsgBytes) ++ a_bin ++ mac_bin) := by
    dsimp only [innerMsg, CryptoGames.LibsignalSession.SignalMessage.new, a_bin]
    change CryptoGames.LibsignalSession.serializeContent protoSignalCodec 4#8 sc.ratchetKey.publicKey
      sc.chainKey.index sess.state.previousCounter ctext_bin pqMsgBytes (some pqHarnessAddrBytes) ++ mac_bin = _
    rw [serializeContent_pending_eq_trWireBytes _ _ _ _ _ hct_lt hpq_lt, DY.Libsignal.TripleRatchet.Refinement.trWireBytes_canonical]
    have ha_ne : pqHarnessAddrBytes ≠ [] := by decide
    simp only [hpq_ne, ha_ne, ↓reduceIte, List.append_assoc]
  have hlen_p := encodeWith_canonical_length_eq (f₁ := ⟨4, sc.ratchetKey.publicKey.bytes.toList,
      sc.chainKey.index.toNat, sess.state.previousCounter.toNat, ctext_bin⟩)
    (f₂ := ⟨4, gamma interp S g (DY.DiffieHellman.dhPk st_m.dhs), st_m.ns.toNat, st_m.pn.toNat, ct_mod⟩)
    rfl hrk (by rw [hidx]; rfl) (by rw [hpn]; rfl)
    (by rw [hct_bin_eq, hct_mod]; exact aesCbcEncrypt_length_eq P.C.E _ _ _ _ pt)
  exact pq_not_nil_vs_nil_absurd (hbin_exp.symm.trans (hbody_gam.trans hgam_exp))
    hlen_p (computeMac_length_eq_8 interp _ _ _ _) hmac_mod hpq_ne ha_mod

/-! ## Constructive Witnesses, Cut Classification, and `slot_send_cli` -/

private theorem callStarts_eq_of_coinSplit {σ τ : List MachineEvent}
    (h : CoinSplit σ τ) : callStarts σ = callStarts τ := by
  induction h with
  | nil => rfl
  | keep _ _ ih => unfold callStarts at ih ⊢; simp only [List.filter_cons, ih]
  | @split _ pieces _ _ _ _ _ ih =>
    have hp : ∀ ps : List HwBytes, ∀ xs, callStarts (ps.map MachineEvent.rng ++ xs) = callStarts xs := by
      intro ps xs; induction ps with
      | nil => rfl
      | cons _ _ ihp => exact ihp
    exact ih.trans (hp pieces _).symm

private theorem sendGhost_sigma_lt (g : Ghost) (ts₀ : Nat) (pt coins : HwBytes) :
    ∀ ts < ts₀, ∀ sz, (sendGhost g ts₀ pt coins).σ ts sz = g.σ ts sz := by
  intro ts hlt sz
  unfold sendGhost Symbolic.Swarm.CREF.SendWire.clearSendAddr Symbolic.Swarm.CREF.SendWire.updateFreshAt
  dsimp only; split_ifs <;> first | rfl | omega

private theorem sendPendingGhost_sigma_lt (g : Ghost) (ts₀ : Nat) (pt coins : HwBytes) :
    ∀ ts < ts₀, ∀ sz, (sendPendingGhost g ts₀ pt coins).σ ts sz = g.σ ts sz := by
  intro ts hlt sz
  unfold sendPendingGhost setSendAddr Symbolic.Swarm.CREF.SendWire.updateFreshAt
  dsimp only; split_ifs <;> first | rfl | omega

private theorem clean_snoc_encryptAbort {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g₀ : Ghost} {ms₀ : List Move}
    {acc : List MachineEvent} {p : Participant} {pt : HwBytes}
    {st₀ : _root_.DY.Libsignal.TripleRatchet.TRState} {stateIdx₀ : Nat}
    (hc₀ : Clean interp r S who ok g₀ ms₀ acc) (hwho : who[(callStarts acc).length]? = some p)
    (hst₀ : ((DY.PersistentLocalState.getLocalState p stateIdx₀ :
      DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₀)).1 = some st₀)
    (hcur₀ : _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₀) stateIdx₀ = true) :
    Clean interp r S who ok (sendGhost g₀ (runTraceMoves r ms₀).length pt [])
      (ms₀ ++ [.encryptAbort p stateIdx₀]) (acc ++ [.pt pt]) := by
  have hc_sg := clean_sendGhost pt [] hc₀
  have hrun' := Symbolic.Swarm.CREF.SendWire.modelRun_snoc_encryptAbort (p := p) hc₀.matched.2.1 hcur₀
  have hvis := Symbolic.Swarm.CREF.SendWire.visOf_encryptAbort_of_some hst₀
  have hno_alice : (eventIdx isAliceDone (runTraceMoves r ms₀)
      ((Move.encryptAbort p stateIdx₀).next (runTraceMoves r ms₀))).isSome = false := by
    rw [SndPure.sndW_eventIdx_eq_none_of_noSessionEffect isAliceDone
      (SndPure.sndW_move_encryptAbort_noSessionEffect (runTraceMoves r ms₀) p stateIdx₀)]; rfl
  refine snd_clean_snoc (m := .encryptAbort p stateIdx₀) (evs := [.pt pt])
    hc_sg hrun' rfl hwho rfl (fun _ h => by cases h) hno_alice rfl ?_ ?_
    (snd_not_readColMove_encryptAbort (g := sendGhost g₀ (runTraceMoves r ms₀).length pt [])) ?_
  · rw [hvis]; intro v hv; simp only [List.mem_singleton] at hv; subst hv; nofun
  · intro e he q; simp only [List.mem_singleton] at he; subst he; nofun
  · rw [hvis]; refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
    show [gamma interp S (sendGhost g₀ (runTraceMoves r ms₀).length pt [])
      (randTerm (runTraceMoves r ms₀).length 32)] = [pt]
    rw [Symbolic.Swarm.CREF.SendWire.gamma_sendGhost_pt]

private theorem whisper_ret_witness {interp : ExternInterpretation} (hext : ExternContractsHoldCli interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {acc mid : List MachineEvent}
    {p : Participant} {rec pt coins_cli retState retMessage : HwBytes} {g₀ : Ghost} {ms₀ : List Move}
    (hc₀ : Clean interp r (compSemOf interp r) who ok g₀ ms₀ acc)
    (hrel : PureCRel interp r (compSemOf interp r) who ok records sent accepted acc)
    (hwho : who[(callStarts acc).length]? = some p) (hrec : records p = some rec)
    (hss : SingleSession rec) (hnpend : ¬ PureRecPending rec)
    (hreclen : rec.length < 2 ^ 32 - 2 ^ 20) (hsent_lt : sent.length < 2 ^ 32 - 1)
    (hout : SndWhisperRetOut interp r p rec pt coins_cli mid retState retMessage) :
    ∃ coins stateIdx₀, ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      MatchedPrefix interp r (compSemOf interp r) who (sendGhost g₀ (runTraceMoves r ms₀).length pt coins)
        (ms₀ ++ [Move.encrypt p stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) none])
        (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) ∧
      (ok (callStarts acc).length = true → Clean interp r (compSemOf interp r) who ok
        (sendGhost g₀ (runTraceMoves r ms₀).length pt coins)
        (ms₀ ++ [Move.encrypt p stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) none])
        (acc ++ ((.pt pt :: mid) ++ [.send retMessage]))) := by
  let S := compSemOf interp r; have hmp₀ := hc₀.matched
  obtain ⟨hinv₀, hbook₀, _, _⟩ := pureCRel_trRecordStateInv interp r S who ok records sent accepted acc
    g₀ ms₀ p rec hrel hc₀ hrec hss (not_alice_and_aliceInitPending_of_not_recPending hnpend)
  obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel_st₀, _, hcanon0, hks₀, _⟩ := hinv₀ p rec (by simp)
  obtain ⟨_, coins, hmid, _, heval⟩ := snd_ret_eval_clause interp hext r hwf S rfl g₀ ms₀ (hcanon0 hreclen) hnpend hout
  have hst_lt := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_at?_st
    (Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g₀
      (runTraceMoves r ms₀).length hmp₀.2.1.2.2.1.1 (Nat.le_refl _))
    (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨hrel_sg, hks_sg⟩ := snd_stateRel_keyShape_sendGhost (pt := pt) (coins := coins) hst_lt hrel_st₀ hks₀
  obtain ⟨_, _, _, _, hmsg⟩ := heval rec₀ st₀ hrecBytes₀ hrel_sg hks_sg (TR.spqrInitA2BKdf_of_getLocalState hst₀)
  have hm_ext : MatchedPrefix interp r S who (sendGhost g₀ (runTraceMoves r ms₀).length pt coins)
      (ms₀ ++ [Move.encrypt p stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) none])
      (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) := by
    simpa only [List.append_nil, List.nil_append] using matchedPrefix_snoc_encrypt (evs := [])
      (by simpa only [List.append_nil] using hmp₀) (by simpa only [List.append_nil] using hwho)
      hst₀ hcur₀ (ns_ne_u32Max_of_trNsBound hbook₀.2.1 hsent_lt hst₀) hmid hmsg
  refine ⟨coins, stateIdx₀, hmid, hm_ext, fun hok_j => ?_⟩
  have hc_sg := clean_sendGhost pt coins hc₀
  have hcc_ms₀ := Stage1Wire.callCount_of_forall₂_eventMatchesEntry hmp₀.2.2.2.2.2
  refine ⟨⟨hm_ext, Stage1Wire.outcomeFaithful_snoc hc₀.1.2 (fun _ h => by cases h) (fun _ => by rw [hcc_ms₀]; exact hok_j)⟩,
    Symbolic.Swarm.CREF.not_readCollision_append_noAccept hc_sg.not_readCollision
      (fun e he _ heq => snd_ret_noAccept pt retMessage mid ⟨coins, hmid⟩ e he (by subst heq; rfl)) ?_⟩
  intro m' hm' pre e; simp only [List.mem_singleton] at hm'; subst hm'; exact snd_not_readColMove_encrypt pre e

private theorem pending_ret_witness {interp : ExternInterpretation} (hext : ExternContractsHoldCli interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {acc mid : List MachineEvent}
    {p : Participant} {rec pt coins_cli retState retMessage : HwBytes} {g₀ : Ghost} {ms₀ : List Move}
    (hc₀ : Clean interp r (compSemOf interp r) who ok g₀ ms₀ acc)
    (hrel : PureCRel interp r (compSemOf interp r) who ok records sent accepted acc)
    (hwho : who[(callStarts acc).length]? = some p) (hrec : records p = some rec)
    (hpend_rec : PureRecPending rec) (hreclen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hsent_lt : sent.length < 2 ^ 32 - 1)
    (hout : p = r.alice → SndPendingRetOut interp r rec pt coins_cli mid retState retMessage) :
    ∃ coins stateIdx₀ ekIdx₀ ctIdx₀, ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      MatchedPrefix interp r (compSemOf interp r) who (sendPendingGhost g₀ (runTraceMoves r ms₀).length pt coins)
        (ms₀ ++ [Move.encrypt r.alice stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) (some (ekIdx₀, ctIdx₀))])
        (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) ∧
      (ok (callStarts acc).length = true → Clean interp r (compSemOf interp r) who ok
        (sendPendingGhost g₀ (runTraceMoves r ms₀).length pt coins)
        (ms₀ ++ [Move.encrypt r.alice stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) (some (ekIdx₀, ctIdx₀))])
        (acc ++ ((.pt pt :: mid) ++ [.send retMessage]))) := by
  let S := compSemOf interp r; have hmp₀ := hc₀.matched
  obtain ⟨⟨hrecs₀, hbook₀, _, _⟩, _⟩ := hrel.clean g₀ ms₀ hc₀
  obtain ⟨hp_alice, hpend₀⟩ := recPending_imp_alice_pending_of_recRel interp r S p rec g₀ ms₀ hreclen hpend_rec (hrecs₀ p rec hrec).2.2
  subst hp_alice
  obtain ⟨_, _, _, coins, _, hmid, _, _, stateIdx₀, ekIdx₀, ctIdx₀, _, hm_ext⟩ :=
    snd_ret_eval_and_matchedPrefix interp hext r hwf S rfl who records sent accepted rec pt coins_cli
      retState retMessage acc mid g₀ ms₀ hmp₀ hwho hpend₀ hbook₀ hrel.oooAll hrec hreclen hsent_lt (hout rfl)
  refine ⟨coins, stateIdx₀, ekIdx₀, ctIdx₀, hmid, hm_ext, fun hok_j => ?_⟩
  have hc_sg := clean_sendPendingGhost pt coins hc₀
  have hcc_ms₀ := Stage1Wire.callCount_of_forall₂_eventMatchesEntry hmp₀.2.2.2.2.2
  refine ⟨⟨hm_ext, Stage1Wire.outcomeFaithful_snoc hc₀.1.2 (fun _ h => by cases h) (fun _ => by rw [hcc_ms₀]; exact hok_j)⟩,
    Symbolic.Swarm.CREF.not_readCollision_append_noAccept hc_sg.not_readCollision
      (fun e he _ heq => snd_ret_noAccept pt retMessage mid ⟨coins, hmid⟩ e he (by subst heq; rfl)) ?_⟩
  intro m' hm' pre e; simp only [List.mem_singleton] at hm'; subst hm'; exact snd_not_readColMove_encrypt pre e

private theorem cut_send_exit0_shape {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ δ : List Move} {τ_pre blk' : List MachineEvent}
    {p : Participant} {pt r_coins out : HwBytes} (hcoins_ne : r_coins ≠ [])
    (hcs : CoinSplit [.pt pt, .rng r_coins, .send out] blk') (hB : XplBlock interp r S who g ms₀ δ τ_pre blk')
    (hrf : RoleFaithful r who (ms₀ ++ δ)) (hwho : who[(callStarts τ_pre).length]? = some p) :
    ∃ n ≤ r_coins.length, blk' = (.pt pt :: sendMidOf (r_coins.take n)) ++ [.send out] ∧ DeltaFaithful p (runTraceMoves r ms₀) δ := by
  have hcs₀ := hcs
  cases hcs with
  | keep _ hcs1 =>
    cases hcs1 with
    | keep hne _ => exact absurd rfl (hne r_coins)
    | @split _ pieces _ _ _ _ hcs2 =>
      cases hcs2 with
      | keep _ hcs3 =>
        cases hcs3 with
        | nil =>
          have htail : ∀ e ∈ pieces.map MachineEvent.rng ++ [MachineEvent.send out],
              eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
            intro e he; simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
            rcases he with ⟨_, _, rfl⟩ | rfl <;> simp [eventKind]
          have hdf := snd_deltaFaithful_of_roleFaithful hB htail hrf hwho
          have hhead : ∀ e ∈ (MachineEvent.pt pt :: (pieces.map MachineEvent.rng ++ [.send out])).head?,
              eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp at he; subst he; exact Or.inr rfl
          obtain ⟨_, _, _, _, _, ⟨_, _, hm⟩, _⟩ := xpl_oneMove hB hhead (List.cons_ne_nil _ _) htail
          obtain ⟨_, _, _, _, _, n, _, hn_le, _, _, hblk_eq⟩ := send_exit0_cut_eq_of_move hcs₀ hm
          refine ⟨n, hn_le, hblk_eq.trans ?_, hdf⟩
          by_cases hn0 : n = 0
          · subst hn0; rcases sendMidOf_cases ([] : HwBytes) with ⟨_, hm0⟩ | ⟨hne, _⟩
            · simp [sendCutOfLen, hm0]
            · exact absurd rfl hne
          · have htake_ne : r_coins.take n ≠ [] := by
              cases r_coins with
              | nil => exact absurd rfl hcoins_ne
              | cons _ _ => cases n with | zero => exact absurd rfl hn0 | succ _ => simp
            rcases sendMidOf_cases (r_coins.take n) with ⟨heq, _⟩ | ⟨_, hm1⟩
            · exact absurd heq htake_ne
            · simp [sendCutOfLen, hn0, hm1]

private theorem slot_send_cli_core
    (hGood : GoodExit0CutSpec)
    (_hA : BridgeAPtSpec)
    (hB : BridgeBQuietFailSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hp : c.party = r.alice ∨ c.party = r.bob)
    (hcmd : c.cmd = .send (peerOf r c.party))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 64)
    (hsb : c.stdin.length < 2 ^ 32)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hsent : t.sent.length < 2 ^ 32 - 1)
    (hrec_ne : t.records r c.party ≠ none)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    let interp' := interpOfParams interp P
    let S := compSemOf interp' r
    let blk_cli := cliEntryEvents c ++ cliExitEvents c code out
    ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
      PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
      ∀ (who : List Participant) (ok : Nat → Bool),
        who[(callStarts σ_pre).length]? = some c.party →
        CliLiveAtCli interp' r S who ok t_clean accepted σ_pre →
        (∃ τ_out g ms, CoinSplit (σ_pre ++ blk_cli) τ_out ∧
            MatchedPrefix interp' r S who g ms τ_out) ∧
        (ok (callStarts σ_pre).length = decide (code = 0) →
          CliLiveAtCli interp' r S who ok t_clean' accepted' (σ_pre ++ blk_cli)) := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hb' : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  let c1 := toCliCallNone c
  have hcmd1 : c1.cmd = .send (peerOf r c1.party) := hcmd
  obtain ⟨hd_eq, hrec_eq, hbca1⟩ := clean_dirs_caller_eq hwf hsim hbca hp
  have hrec_ne1 : t_clean.records r c1.party ≠ none := by
    change t_clean.records r c.party ≠ none; rwa [hrec_eq]
  have hfb1 : FilesBounded (t_clean.dirs c1.party) := hd_eq.symm ▸ hfb
  have hsent1 : t_clean.sent.length < 2 ^ 32 - 1 := hsim.sent_eq.symm ▸ hsent
  have hnext1 : ValidCall interp' r t_clean c1 := by
    refine ⟨by simpa [c1, toCliCallNone, hcmd, coinsLen] using hcoins,
      by simpa [StdinBounded, c1, toCliCallNone, hcmd] using hsb, hfb1, hbca1, ?_⟩
    dsimp only [c1, toCliCallNone]; rw [hcmd]
    exact ⟨hp, rfl, rfl, hsent1, hrec_ne1⟩
  have hin1 : InputsFor c1 (t_clean.dirs c1.party) i := hd_eq.symm ▸ inputsFor_toCliCallNone hbun hin
  obtain ⟨st, hwf_st, hrec_st, hinvP⟩ := pqDispatch_send_party hsim.dirInv hbca1 hp hfb1
  have hgA : ∀ x g, st.session = some (x, g) → c1.party = r.alice → g.party = .A := fun x g hs hpA =>
    (hwf_st.1 x g hs).2.1.trans (hinvP.party_eq.trans (hpA ▸ partyOf_alice r))
  have hcmd' : c1.cmd = .send (partyAddress st.party.other) := by
    rw [peerOf_eq_addrE_other, ← hinvP.party_eq] at hcmd1; exact hcmd1
  let coinsVec : List.Vector (BitVec 8) 64 := ⟨c1.coins, hcoins⟩
  have hi' : InputsFor c1 (filesOf (encodeDir P st)) i := by rwa [hinvP.dir_eq] at hin1
  have hobs_eq := (PqModelRel.exited_iff.mp hRel).send st c1.stdin coinsVec hwf_st hsb
    (inputsEquiv_pqSendInputs hi' hcmd' rfl rfl)
  have hn3 : ¬ PreKeyNoMatch r t c := fun ⟨_, ⟨_, hc⟩, _⟩ => by rw [hcmd] at hc; cases hc
  have hn1 : ¬ PreKeyNoMatch r t_clean c1 := fun ⟨_, ⟨_, hc⟩, _⟩ => by
    change c.cmd = _ at hc; rw [hcmd] at hc; cases hc
  cases hsess : st.session with
  | none =>
    exfalso; apply hrec_ne1; simpa [hsess] using hrec_st
  | some xg =>
    rcases xg with ⟨x, g_st⟩
    let rec_ := encodeRecordUnderExtras (fun _ => x) g_st
    have hrec_t : t_clean.records r c1.party = some rec_ := by simpa [hsess] using hrec_st
    have hleak_rec : t_clean.leakRecords r c.party = some rec_ :=
      (leakRecords_party_eq_of_cliNextCall hnext1).trans hrec_t
    have hss : SingleSession rec_ := singleSession_encodeRecordX_of_wfPq hwf_st hsess
    have hlen31 : rec_.length < 2 ^ 31 := (reachPqInvPure_of_wfPq hwf_st hsess).2.2
    have hreclen : rec_.length < 2 ^ 32 - 2 ^ 20 := by omega
    rcases Slots.pqObserve_send_exited_cases hobs_eq with ⟨rfl, st', hmod, rfl⟩ | ⟨rfl, rfl, _, rfl⟩
    · have hmod' : pqSendModel P st c.stdin c.coins = some (some (st', out)) := hmod
      obtain ⟨hst', hsub⟩ := pqPartyInv_of_pqSendModel hinvP hwf_st hmod'
      let files₀ := filesOf ((pqSendInputs P st c1.stdin coinsVec).files ++ encodeDir P st')
      have hscr : scrub files₀ = filesOf (encodeDir P st') :=
        scrub_filesOf_pqInputs_accept P st st' _ [] _ _ (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
      have hparty_case : c1.party = r.alice ∨ (c1.party = r.bob ∧ t_clean.bobOff = false) := by
        rcases hp with hpA | hpB
        · exact Or.inl hpA
        · cases hbo : t_clean.bobOff
          · exact Or.inr ⟨hpB, rfl⟩
          · exact absurd hpB (hbca1 hbo)
      have hDir' : PqDirInv interp' P r (t_clean.after r c1 0 out files₀) accepted :=
        pqDirInv_after_accept_same hwf.1 hsim.dirInv hparty_case hn1 hscr hst'
      let retState := encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams P).send g_st c.stdin c.coins).1
      have hrec_after : (t_clean.after r c1 0 out files₀).records r c1.party = some retState := by
        obtain ⟨_, hmap⟩ := pqSendModel_some_session_oneTime hsess hmod'
        have hst'_after : PqPartyInv interp' P r accepted c1.party st'
            ((t_clean.after r c1 0 out files₀).dirs c1.party) := by simpa [CliTurn.after, hscr] using hst'
        exact (records_of_pqPartyInv hst'_after).trans hmap
      have hlr_ok : (t_clean.after r c1 0 out files₀).leakRecords r =
          fun q => if q = c.party then some retState else t_clean.leakRecords r q :=
        after_leakRecords_of_send_ok hnext1 hcmd1 hrec_after
      have hsent_ok : (t_clean.after r c1 0 out files₀).sent = t_clean.sent ++ (sentBody out).toList :=
        after_sent_of_send_ok hcmd1 out files₀
      have hopk_ok : (t_clean.after r c1 0 out files₀).opkUsed r = t_clean.opkUsed r := by
        rcases hparty_case with hpA | ⟨hpB, hbo⟩
        · simp [CliTurn.opkUsed, CliTurn.after, hpA, hwf.1.symm]
        · have hbo' : (t_clean.after r c1 0 out files₀).bobOff = false := by simp [CliTurn.after, hbo, hn1]
          have hB_pre : PqBobInv interp' P r accepted t_clean.bobOff st (t_clean.dirs r.bob) := by
            unfold PqBobInv; rw [hbo]; exact hpB ▸ hinvP
          have hB_post : PqBobInv interp' P r accepted (t_clean.after r c1 0 out files₀).bobOff
              st' ((t_clean.after r c1 0 out files₀).dirs r.bob) := by
            unfold PqBobInv; rw [hbo']; simpa [CliTurn.after, hpB, hscr] using (hpB ▸ hst')
          obtain ⟨hone, _⟩ := pqSendModel_some_session_oneTime hsess hmod'
          exact (opkUsed_eq_of_pqBobInv_oneTime_eq hwf.1 hB_pre hB_post hone.symm).symm
      have hblk_eq : cliEntryEvents c ++ cliExitEvents c 0 out = [.pt c.stdin, .rng c.coins, .send out] := by
        rw [cliEntryEvents_eq_send hcmd, cliExitEvents_eq,
          Slots.cliEntryEvents_of_send hcmd1, Slots.cliExitEvents_of_send_ok hcmd1]; rfl
      refine ⟨t_clean.after r c1 0 out files₀, accepted,
        pqTurnSim1A_caller_after hwf hsim hbca hp hn3 hn1 hDir', fun who ok hwho hlive => ?_⟩
      obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
      have hc₀ := explainsCli_toClean hex₀ hnrc₀
      obtain ⟨hrel₀, _⟩ := hlive.cutRel τ_acc ⟨g₀, ms₀, hex₀, hnrc₀⟩
      have hcs_len₀ : (callStarts τ_acc).length = (callStarts σ_pre).length :=
        congrArg List.length (callStarts_eq_of_coinSplit hex₀.1).symm
      have hwho₀ : who[(callStarts τ_acc).length]? = some c.party := by rwa [hcs_len₀]
      let coins₀ := sendCoinsOf interp' g_st.session.pqRatchetState c.coins
      let mid₀ := sendMidOf coins₀
      let blk_hw := (.pt c.stdin :: mid₀) ++ [.send out]
      have hcs_blk : CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 out) blk_hw := by
        rw [hblk_eq]
        exact SndPure.coinSplit_send_ret_step c.stdin c.coins out
          ⟨coins₀, sendMidOf_cases coins₀, sendCoinsOf_prefix interp' g_st.session.pqRatchetState c.coins⟩
      have hnoAdj : NoAdjRng (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c 0 out)) := by
        rw [hblk_eq]
        exact noAdjRng_append_of_head_nonRng hlive.noAdjRng ⟨Or.inl (by simp [eventKind]), Or.inr (by simp [eventKind]), trivial⟩
          (by intro y hy; simp at hy; subst hy; simp [eventKind])
      have hooo₀ : SpqrOooBounded g_st.session.pqRatchetState := by
        have h0 := hrel₀.oooAll c.party rec_ hleak_rec
        rwa [pqStateOf_of_canonical_Q_pend (recordCanonical_Q_of_wfPq hwf_st hsess)] at h0
      have hwit₀ : ∃ g₁ δ₁,
          MatchedPrefix interp' r S who g₁ (ms₀ ++ δ₁) (τ_acc ++ blk_hw) ∧
          (∀ ts < (runTraceMoves r ms₀).length, ∀ sz, g₁.σ ts sz = g₀.σ ts sz) ∧
          (ok (callStarts τ_acc).length = true → Clean interp' r S who ok g₁ (ms₀ ++ δ₁) (τ_acc ++ blk_hw)) := by
        cases hp_b : g_st.session.pendingPreKey
        · have hnpend_pure : ¬ PureRecPending rec_ := fun hp_p => by
            have hp_t := (recPending_encodeRecordX_iff hwf_st hsess).mp (recPending_iff_pureRecPending.mpr hp_p)
            rw [hp_b] at hp_t; cases hp_t
          have hretOut₀ := sndWhisperRetOut_of_pqSendModel hb' r c.party hwf_st hsess hp_b hooo₀ hsb hcoins hmod'
          obtain ⟨coins_w, stateIdx₀, _, hm_ext, hc_fn⟩ :=
            whisper_ret_witness hext' hwf hc₀ hrel₀ hwho₀ hleak_rec hss hnpend_pure hreclen hsent1 hretOut₀
          exact ⟨_, _, hm_ext, sendGhost_sigma_lt _ _ _ _, hc_fn⟩
        · have hpend_pure : PureRecPending rec_ :=
            recPending_iff_pureRecPending.mp ((recPending_encodeRecordX_iff hwf_st hsess).mpr hp_b)
          have hretOut₀ : c.party = r.alice → SndPendingRetOut interp' r rec_ c.stdin c.coins mid₀ retState out :=
            fun hpA => sndPendingRetOut_of_pqSendModel hb' r hwf_st hsess hp_b (hgA x g_st hsess hpA) hsb hcoins hmod'
          obtain ⟨coins_w, stateIdx₀, ekIdx₀, ctIdx₀, _, hm_ext, hc_fn⟩ :=
            pending_ret_witness hext' hwf hc₀ hrel₀ hwho₀ hleak_rec hpend_pure hreclen hsent1 hretOut₀
          exact ⟨_, _, hm_ext, sendPendingGhost_sigma_lt _ _ _ _, hc_fn⟩
      obtain ⟨g₁, δ₁, hm_ext, hsig_lt, hc_fn⟩ := hwit₀
      refine ⟨⟨τ_acc ++ blk_hw, g₁, ms₀ ++ δ₁, SndPure.coinSplit_append_snd hex₀.1 hcs_blk, hm_ext⟩,
        fun hok => ⟨hnoAdj, ?_, ?_⟩⟩
      · simp only [decide_true] at hok
        have hok₀ : ok (callStarts τ_acc).length = true := by rwa [hcs_len₀]
        have hgood : GoodStepCut ok (callStarts τ_acc).length blk_hw := by
          refine GoodStepCut.callSendOk ?_ rfl hok₀
          dsimp only [mid₀]; rcases sendMidOf_cases coins₀ with ⟨_, h0⟩ | ⟨_, h1⟩
          · simp [h0, eventKind]
          · simp [h1, eventKind]
        obtain ⟨hex₁, hnrc₁⟩ := hGood hex₀ hcs_blk hgood (Or.inl rfl) hsig_lt (hc_fn hok₀)
        exact ⟨_, _, _, hex₁, hnrc₁⟩
      · simp only [decide_true] at hok
        intro τ' ⟨g', ms', hex', hnrc'⟩
        obtain ⟨τ'_pre, blk', rfl, hcs'_pre, hcs'_blk⟩ := coinSplit_split_append hex'.1
        rw [hblk_eq] at hcs'_blk
        have hhead' : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt := by
          cases hcs'_blk with | keep _ _ => intro e he; simp at he; subst he; exact Or.inr rfl
        obtain ⟨ms'_pre, δ', rfl, hex'_pre, hnrc'_pre, hB_blk⟩ :=
          explainsCli_prefix_of_split hcs'_pre hhead' hex' hnrc'
        have hc'_pre := explainsCli_toClean hex'_pre hnrc'_pre
        obtain ⟨hrel'_pre, hopk'_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
        have hcs_len' : (callStarts τ'_pre).length = (callStarts σ_pre).length :=
          congrArg List.length (callStarts_eq_of_coinSplit hcs'_pre).symm
        have hwho'_pre : who[(callStarts τ'_pre).length]? = some c.party := by rwa [hcs_len']
        have hok'_pre : ok (callStarts τ'_pre).length = true := by rwa [hcs_len']
        obtain ⟨n, hn_le, rfl, hdf'⟩ := cut_send_exit0_shape
          (by intro h; simp [h] at hcoins) hcs'_blk hB_blk (explainsCli_toClean hex' hnrc').matched.2.2.1 hwho'_pre
        have hn64 : n ≤ 64 := by omega
        rw [hlr_ok, hsent_ok, hopk_ok]
        cases hp_b : g_st.session.pendingPreKey
        · have hnpend_pure : ¬ PureRecPending rec_ := fun hp_p => by
            have hp_t := (recPending_encodeRecordX_iff hwf_st hsess).mp (recPending_iff_pureRecPending.mpr hp_p)
            rw [hp_b] at hp_t; cases hp_t
          have hdraw_le := whisper_exit0_draw_le hext' hagree' hb' hwf_st hsess hp_b hsb hmod'
            hleak_rec hB_blk hdf' (hrel'_pre.clean g' ms'_pre hc'_pre).1
          have hretOut_n := sndWhisperRetOut_of_pqSendModel_take hb' r c.party hwf_st hsess hp_b
            hooo₀ hsb hcoins hn64 hdraw_le hmod'
          obtain ⟨_, _, _, hcl_n⟩ := SndPure.snd_ret_pure_step interp' hext' r hwf S rfl who ok
            (t_clean.leakRecords r) t_clean.sent accepted (t_clean.opkUsed r) τ'_pre
            (sendMidOf (c.coins.take n)) c.party rec_ c.stdin c.coins retState out
            ⟨g', ms'_pre, hc'_pre⟩ hrel'_pre hopk'_pre hp hwho'_pre hleak_rec hss hnpend_pure
            hreclen hsent1 hretOut_n
          exact ⟨(hcl_n hok'_pre).2.1, (hcl_n hok'_pre).2.2⟩
        · have hpend_pure : PureRecPending rec_ :=
            recPending_iff_pureRecPending.mp ((recPending_encodeRecordX_iff hwf_st hsess).mpr hp_b)
          have hdraw_le := pending_exit0_draw_le hext' hagree' hb' hwf_st hsess hp_b hgA hsb hmod'
            hleak_rec hB_blk hdf' (hrel'_pre.clean g' ms'_pre hc'_pre).1
          have hretOut_n : c.party = r.alice →
              SndPendingRetOut interp' r rec_ c.stdin c.coins (sendMidOf (c.coins.take n)) retState out :=
            fun hpA => sndPendingRetOut_of_pqSendModel_take hb' r hwf_st hsess hp_b
              (hgA x g_st hsess hpA) hsb hcoins hn64 hdraw_le hmod'
          obtain ⟨_, _, _, hcl_n⟩ := SndPure.sndP_ret_pure_step interp' hext' r hwf S rfl who ok
            (t_clean.leakRecords r) t_clean.sent accepted (t_clean.opkUsed r) τ'_pre
            (sendMidOf (c.coins.take n)) c.party rec_ c.stdin c.coins retState out
            ⟨g', ms'_pre, hc'_pre⟩ hrel'_pre hopk'_pre hwho'_pre hleak_rec hpend_pure
            hreclen hsent1 hretOut_n
          exact ⟨(hcl_n hok'_pre).2.1, (hcl_n hok'_pre).2.2⟩
    · let files₁ := filesOf (pqSendInputs P st c1.stdin coinsVec).files
      have hscr : scrub files₁ = t_clean.dirs c1.party := by
        rw [hinvP.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st _ [] _ _ (fun _ h => nomatch h) (fun _ h => nomatch h)
      have hDir' := pqDirInv_after_reject (out := []) hsim.dirInv hscr
      have hdirs_eq : ∀ q, (t_clean.after r c1 1 [] files₁).dirs q = t_clean.dirs q := fun q => by
        by_cases hq : q = c1.party <;> simp [CliTurn.after, hq, hscr]
      have hrec_after : (t_clean.after r c1 1 [] files₁).records r c1.party = t_clean.records r c1.party := by
        simp [CliTurn.records, hdirs_eq c1.party]
      have hlr_fail : (t_clean.after r c1 1 [] files₁).leakRecords r = t_clean.leakRecords r :=
        after_leakRecords_of_send_fail hcmd1 hrec_after
      have hsent_fail : (t_clean.after r c1 1 [] files₁).sent = t_clean.sent :=
        snd_after_sent_of_ne_zero (by decide) [] files₁
      have hopk_fail : (t_clean.after r c1 1 [] files₁).opkUsed r = t_clean.opkUsed r := by
        simp only [CliTurn.opkUsed, hdirs_eq r.bob]
      have hblk_eq : cliEntryEvents c ++ cliExitEvents c 1 [] = [.pt c.stdin, .rng c.coins] := by
        rw [cliEntryEvents_eq_send hcmd, cliExitEvents_eq, Slots.cliEntryEvents_of_send hcmd1]; rfl
      refine ⟨t_clean.after r c1 1 [] files₁, accepted,
        pqTurnSim1A_caller_after hwf hsim hbca hp hn3 hn1 hDir', fun who ok hwho hlive => ?_⟩
      obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
      have hc₀ := explainsCli_toClean hex₀ hnrc₀
      obtain ⟨hrel₀, _⟩ := hlive.cutRel τ_acc ⟨g₀, ms₀, hex₀, hnrc₀⟩
      have hcs_len₀ : (callStarts τ_acc).length = (callStarts σ_pre).length :=
        congrArg List.length (callStarts_eq_of_coinSplit hex₀.1).symm
      have hwho₀ : who[(callStarts τ_acc).length]? = some c.party := by rwa [hcs_len₀]
      have hsnap₀ : ∃ st₀ stateIdx₀,
          ((DY.PersistentLocalState.getLocalState c.party stateIdx₀ :
            DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms₀)).1 = some st₀ ∧
          _root_.DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms₀) stateIdx₀ = true := by
        by_cases hpend : PureRecPending rec_
        · obtain ⟨⟨hrecs₀, _, _, _⟩, _⟩ := hrel₀.clean g₀ ms₀ hc₀
          obtain ⟨hp_alice, hpend₀⟩ := recPending_imp_alice_pending_of_recRel interp' r S c.party rec_
            g₀ ms₀ hreclen hpend (hrecs₀ c.party rec_ hleak_rec).2.2
          rw [hp_alice]
          obtain ⟨_, _, _, _, _, st₀, stateIdx₀, _, _, _, _, _, _, _, hst₀, hcur₀, _⟩ := hpend₀
          exact ⟨st₀, stateIdx₀, hst₀, hcur₀⟩
        · obtain ⟨hinv₀, _, _, _⟩ := pureCRel_trRecordStateInv interp' r S who ok
            (t_clean.leakRecords r) t_clean.sent accepted τ_acc g₀ ms₀ c.party rec_ hrel₀ hc₀
            hleak_rec hss (not_alice_and_aliceInitPending_of_not_recPending hpend)
          obtain ⟨_, _, st₀, stateIdx₀, _, hst₀, hcur₀, _⟩ := hinv₀ c.party rec_ (by simp)
          exact ⟨st₀, stateIdx₀, hst₀, hcur₀⟩
      obtain ⟨st₀, stateIdx₀, hst₀, hcur₀⟩ := hsnap₀
      have hc_ext := clean_snoc_encryptAbort (pt := c.stdin) hc₀ hwho₀ hst₀ hcur₀
      have hcs_blk : CoinSplit (cliEntryEvents c ++ cliExitEvents c 1 []) [.pt c.stdin] := by
        rw [hblk_eq]; exact SndPure.coinSplit_send_fail_step c.stdin c.coins (Or.inl rfl)
      have hnoAdj : NoAdjRng (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c 1 [])) := by
        rw [hblk_eq]
        exact noAdjRng_append_of_head_nonRng hlive.noAdjRng ⟨Or.inl (by simp [eventKind]), trivial⟩
          (by intro y hy; simp at hy; subst hy; simp [eventKind])
      refine ⟨⟨τ_acc ++ [.pt c.stdin], _, _, SndPure.coinSplit_append_snd hex₀.1 hcs_blk, hc_ext.matched⟩,
        fun hok => ⟨hnoAdj, ?_, ?_⟩⟩
      · have hok₀ : ok (callStarts τ_acc).length = false := by
          rw [hcs_len₀]; simpa using hok
        have hgood : GoodStepCut ok (callStarts τ_acc).length [.pt c.stdin] :=
          GoodStepCut.callSendFail (by simp) hok₀
        obtain ⟨hex₁, hnrc₁⟩ := hGood hex₀ hcs_blk hgood (Or.inl rfl) (sendGhost_sigma_lt _ _ _ _) hc_ext
        exact ⟨_, _, _, hex₁, hnrc₁⟩
      · intro τ' ⟨g', ms', hex', hnrc'⟩
        obtain ⟨τ'_pre, blk', rfl, hcs'_pre, hcs'_blk⟩ := coinSplit_split_append hex'.1
        rw [hblk_eq] at hcs'_blk
        have hhead' : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt := by
          cases hcs'_blk with | keep _ _ => intro e he; simp at he; subst he; exact Or.inr rfl
        obtain ⟨ms'_pre, _, _, hex'_pre, hnrc'_pre, _⟩ :=
          explainsCli_prefix_of_split hcs'_pre hhead' hex' hnrc'
        obtain ⟨hrel'_pre, hopk'_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
        have hok'_pre : ok (callStarts τ'_pre).length = false := by
          rw [congrArg List.length (callStarts_eq_of_coinSplit hcs'_pre).symm]; simpa using hok
        obtain ⟨hrel'_post, hopk'_post⟩ := hB hwf (Or.inr rfl) hcs'_blk hok'_pre hrel'_pre hopk'_pre
        rw [hlr_fail, hsent_fail, hopk_fail]; exact ⟨hrel'_post, hopk'_post⟩

/-- Generalized `send` slot refinement with trivial side condition `CliSlotPostW (fun _ _ => True)`. -/
theorem slot_send_cli_gen
    (hGood : GoodExit0CutSpec)
    (hA : BridgeAPtSpec)
    (hB : BridgeBQuietFailSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hp : c.party = r.alice ∨ c.party = r.bob)
    (hcmd : c.cmd = .send (peerOf r c.party))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 64)
    (hsb : c.stdin.length < 2 ^ 32)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hsent : t.sent.length < 2 ^ 32 - 1)
    (hrec_ne : t.records r c.party ≠ none)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    CliSlotPostW (fun _ _ => True) interp P r t t_clean c code out files accepted σ_pre := by
  obtain ⟨t_clean', accepted', hsim', hstep⟩ :=
    slot_send_cli_core hGood hA hB interp P r hext hagree hwf
      hsim hp hcmd hbun hcoins hsb hfb hbca hsent hrec_ne hin hRel
  exact ⟨t_clean', accepted', hsim', fun who ok hwho hlive _ hok =>
    (hstep who ok hwho hlive).2 hok⟩

end Symbolic.Swarm.Coinsplit.Lift.L08
