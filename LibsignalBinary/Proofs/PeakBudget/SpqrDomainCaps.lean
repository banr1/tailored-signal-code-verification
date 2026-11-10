/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PqValid
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState

@[expose] public section

set_option autoImplicit false

/-!
# `AllocCostModel`-Free SPQR V1 and Session Domain Caps

Protocol-level byte and point-count invariants for SPQR V1 live-heap peak bounds (re-exporting core
point-slice predicates and `sessionCapBytes` from `SpqrDomainCapsAux`):
1. Every SPQR state reachable via `ReachablePqxdhSession` satisfies `ValidStatePts`, `< 2 ^ 64`
   bytes, and `ValidEncoderPts` (`validEncoderPts_of_reachPq`), bounding each `.points` slice in
   `PolyEncoder` to `≤ 524,288` `GF16` elements (`≤ 1,048,576` serialized bytes).
2. Every active `States` decoded by `States.from_pb` satisfies `StatesDecPtsNeededBound`
   (`ptsNeeded ≤ 480 / 80 / 48 / 576`, `StatesDecPtsNeededBound.of_from_pb`).
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps

open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (GhostState KeyPair SessionState ShaCompress SignalMessage SpqrDirection
   initializeInitiatorSession initializeRecipientSession maxReceiverChains rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)
open CryptoVerification.E2E
  (LocalIdentity PEParams ReachablePqxdhSession RecordExtras
   acceptInput initiateInput keyPairOf modelPrims ofU8 pqxdhSessionParams responderRecordExtras)
open CryptoVerification.E2E.Record (receive_eq_afterRecv send_eq_afterSend)
open CryptoVerification.E2E.V1 (messageEncrypt_ok_props_gen tryDecryptFromRecord_ok_props_gen)
open CryptoVerification.SpqrV1Sync.Codec (decodeState_spqrDeps_encodeState_pb spqrDecodeState_encodeState)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Direction MlKem PqRatchetState Recv States SpqrApiResult V1Recv V1Send V1State Version
   initInner initialState libsignalSpqrParams liftSpqrPanic liftStatesResult messageKeyToSalt?
   pbToPqRatchetState pqRatchetStateToPb recv recvKeyToSalt? send spqrAuthApi spqrDeps spqrHkdfWith
   spqrPolyApi spqrV1 spqrV1_eq spqrV1Init spqrV1InitialStateFor spqrV1SessionUniformCoins
   toSpqrModel)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.SpqrV1.Top.StateSize
  (StatesPtsNeededBound decoderFromPbStateDecode_raw_le encodeState_len_lt_recv
   encodeState_len_lt_send encodeState_length_le_rawPqState except_bind_eq_ok
   initInner_spqrDeps_raw_le optRaw_none optRaw_some rawPqState rawVN sendAfterStates_raw_le)
open CryptoVerification.SignalSession.Cli.Slots.PqValid
  (initiateStateV1 paramsPV1 pqRatchetState_length_le_encodeRecordX reachPq_inv recvPrekeyStateV1)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (ValidPqPts statesPtsBounded_of_from_pb statesPtsBounded_of_recv statesPtsBounded_of_send
   validV1Pts_states_into_pb)
export LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (ValidEncoderPts ValidV1Pts msgCapBytes sessionCapBytes spqrStateTightCapBytes)

/-! ## 3. Reachable PQXDH SPQR State Preservation (`ValidStatePts`, `validEncoderPts_of_reachPq`) -/

/-- Serialized SPQR state that is either empty (`V0`) or the canonical encoding of a `ValidPqPts`
state. -/
def ValidStatePts (s : Bytes) : Prop :=
  s = [] ∨ ∃ st : PqRatchetState, s = encodeState st ∧ ValidPqPts st

private theorem validStatePts_exists_encodeState {s : Bytes} (h : ValidStatePts s) :
    ∃ st : PqRatchetState, s = encodeState st ∧ ValidPqPts st := by
  rcases h with rfl | h
  · exact ⟨default, rfl, trivial⟩
  · exact h

/-- Any `ValidStatePts s` shorter than `2 ^ 64` bytes satisfies `ValidEncoderPts s`. -/
theorem validEncoderPts_of_validStatePts {s : Bytes} (hlen : s.length < 2 ^ 64)
    (h : ValidStatePts s) : ValidEncoderPts s := by
  obtain ⟨st, rfl, hpq⟩ := validStatePts_exists_encodeState h
  unfold ValidEncoderPts
  rw [spqrDecodeState_encodeState st hlen]
  exact hpq

private theorem validV1Pts_initInner {F : ShaCompress} {K : MlKem}
    {v : Version} {dir : Direction} {authKey : Bytes} {inner? : Option V1State}
    (h : initInner (spqrDeps F K) v dir authKey = .ok inner?) :
    ∀ v1, inner? = some v1 → ValidV1Pts v1 := by
  unfold initInner at h
  cases v with
  | v0 =>
    dsimp only at h
    have hinj := Except.ok.inj h; subst hinj
    intro _ h0; nomatch h0
  | v1 =>
    dsimp only [Functor.map, Except.map] at h
    split at h <;> try contradiction
    rename_i v1pb hv1
    have hinj := Except.ok.inj h; subst hinj
    intro v1 hv1_eq; cases hv1_eq
    unfold spqrDeps at hv1; dsimp only at hv1
    cases dir with
    | a2b =>
      cases ha : States.init_a spqrPolyApi (spqrAuthApi F) authKey <;> rw [ha] at hv1
      · contradiction
      · have hinj2 := Except.ok.inj hv1; subst hinj2
        unfold States.init_a CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.new
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.new spqrAuthApi at ha
        dsimp only [Bind.bind, Except.bind] at ha
        have hst := Except.ok.inj ha; subst hst; trivial
    | b2a =>
      cases hb : States.init_b spqrPolyApi (spqrAuthApi F) authKey <;> rw [hb] at hv1
      · contradiction
      · have hinj2 := Except.ok.inj hv1; subst hinj2
        unfold States.init_b at hb
        rcases except_bind_eq_ok hb with ⟨_, _, hst⟩
        have hst_eq := Except.ok.inj hst; subst hst_eq; trivial

theorem validStatePts_spqrV1Init (F : ShaCompress) (K : MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    ValidStatePts (spqrV1Init F K dir k) ∧ (spqrV1Init F K dir k).length < 2 ^ 32 := by
  unfold spqrV1Init spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [initialState, libsignalSpqrParams] at hst
    rcases hi : initInner (spqrDeps F K) Version.v1
        (Direction.ofSpqrDirection dir) (keyToBytes32 k) with _ | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst; subst hst'
      have hin := initInner_spqrDeps_raw_le hi
      have hv_in := validV1Pts_initInner hi
      have hk : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
      have hpq : ValidPqPts (pbToPqRatchetState {
          inner := inner,
          versionNegotiation := some {
            direction := (Direction.ofSpqrDirection dir).toI32,
            minVersion := Version.v1.toI32,
            authKey := keyToBytes32 k,
            chainParams := some (CryptoVerification.LibsignalSpqrV1.libsignalChainParams false).intoPb },
          chain := none }) := by
        unfold ValidPqPts pbToPqRatchetState
        cases inner with
        | none => trivial
        | some v1 => exact hv_in v1 rfl
      refine ⟨Or.inr ⟨_, rfl, hpq⟩, ?_⟩
      have hle := encodeState_length_le_rawPqState (pbToPqRatchetState {
          inner := inner,
          versionNegotiation := some {
            direction := (Direction.ofSpqrDirection dir).toI32,
            minVersion := Version.v1.toI32,
            authKey := keyToBytes32 k,
            chainParams := some (CryptoVerification.LibsignalSpqrV1.libsignalChainParams false).intoPb },
          chain := none })
      have hraw : rawPqState (pbToPqRatchetState {
          inner := inner,
          versionNegotiation := some {
            direction := (Direction.ofSpqrDirection dir).toI32,
            minVersion := Version.v1.toI32,
            authKey := keyToBytes32 k,
            chainParams := some (CryptoVerification.LibsignalSpqrV1.libsignalChainParams false).intoPb },
          chain := none }) ≤ 456 := by
        simp only [rawPqState, pbToPqRatchetState, optRaw_some, optRaw_none, rawVN, hk]
        omega
      dsimp only [spqrDeps]
      omega
  · exact ⟨Or.inl rfl, by decide⟩

/-- Initial SPQR V1 state satisfies `ValidEncoderPts`. -/
theorem validEncoderPts_spqrV1Init (F : ShaCompress) (K : MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    ValidEncoderPts (spqrV1Init F K dir k) := by
  obtain ⟨hv, h32⟩ := validStatePts_spqrV1Init F K dir k
  exact validEncoderPts_of_validStatePts (Nat.lt_trans h32 (by decide)) hv

private theorem if_error_eq_ok_l {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {rest : Except ε α} {v : α}
    (h : (if c then Except.error e else rest) = .ok v) : rest = .ok v := by
  by_cases hc : c <;> simp [hc] at h; exact h

private theorem if_eq_ok_cases_l {ε α : Type} {c : Prop} [Decidable c]
    {t f : Except ε α} {v : α}
    (h : (if c then t else f) = .ok v) : t = .ok v ∨ f = .ok v := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

theorem validStatePts_spqrV1_send (F : ShaCompress) (K : MlKem)
    (s tape s' : Bytes) (salt : Salt) (msg : Bytes)
    (hval : ValidStatePts s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).send s tape = some (s', salt, msg)) :
    ValidStatePts s' := by
  obtain ⟨st, rfl, hst_pts⟩ := validStatePts_exists_encodeState hval
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hsend : (send (spqrDeps F K) (spqrHkdfWith F) (encodeState st) tape).1 with
  | error _ => rw [hsend] at h; contradiction
  | ok out =>
    rw [hsend] at h; dsimp only at h
    cases hsalt : messageKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only at h
      have hs'_eq := (Prod.mk.inj (Option.some.inj h)).1; subst hs'_eq
      have hdec := decodeState_spqrDeps_encodeState_pb F K st hlen
      unfold send at hsend; rw [hdec] at hsend; dsimp only at hsend
      cases hinner : (pqRatchetStateToPb st).inner with
      | none =>
        rw [hinner] at hsend; have hinj := Except.ok.inj hsend; subst hinj
        exact Or.inl rfl
      | some pb =>
        have hpb_pts : ValidV1Pts pb := by
          unfold ValidPqPts at hst_pts
          cases hin : st.inner with
          | none => simp [pqRatchetStateToPb, hin] at hinner
          | some i =>
            cases i with
            | v1 v =>
              simp only [pqRatchetStateToPb, hin, Option.map, Option.some.injEq] at hinner
              subst hinner; rw [hin] at hst_pts; exact hst_pts
        rw [hinner] at hsend; dsimp only at hsend
        cases hfrom : (spqrDeps F K).statesFromPb pb with
        | error _ => rw [hfrom] at hsend; contradiction
        | ok st0' =>
          rw [hfrom] at hsend; dsimp only at hsend
          unfold spqrDeps liftStatesResult at hfrom; dsimp only at hfrom
          cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
          | error e => rw [hs0] at hfrom; cases e <;> contradiction
          | ok st0 =>
            rw [hs0] at hfrom; have hst0 := Except.ok.inj hfrom; subst hst0
            have hst0_pts := statesPtsBounded_of_from_pb hpb_pts hs0
            cases hsend_st : ((spqrDeps F K).statesSend st0 tape).1 with
            | error _ => rw [hsend_st] at hsend; contradiction
            | ok val =>
              rcases val with ⟨mOut, kOut, st1⟩
              rw [hsend_st] at hsend; dsimp only at hsend
              unfold spqrDeps at hsend_st; dsimp only at hsend_st
              cases hsend0 : st0.send K tape with
              | error se => rw [hsend0] at hsend_st; cases se <;> contradiction
              | ok p =>
                rcases p with ⟨sOut, _⟩
                rw [hsend0] at hsend_st
                have hst1 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hsend_st)).2).2
                subst hst1
                have hsOut_pts := validV1Pts_states_into_pb
                  (statesPtsBounded_of_send hst0_pts hsend0)
                rcases sendAfterStates_raw_le hsend with ⟨chainPb, _, hout_eq⟩
                exact Or.inr ⟨_, hout_eq, hsOut_pts⟩

private theorem pure_bind_except_l {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Pure.pure x >>= f) = f x := rfl

private theorem if_pure_bind_eq_ok_l {ε α β : Type} {c : Prop} [Decidable c]
    {a : α} {K : α → Except ε β} {f : Except ε β} {v : β}
    (h : (if c then (Pure.pure a >>= K) else f) = .ok v) (P : α → Prop) (ha : P a)
    (hf : f = .ok v → ∃ a', P a' ∧ K a' = .ok v) : ∃ a', P a' ∧ K a' = .ok v := by
  rcases if_eq_ok_cases_l h with h1 | h1
  · rw [pure_bind_except_l] at h1; exact ⟨a, ha, h1⟩
  · exact hf h1

theorem validStatePts_spqrV1_recv (F : ShaCompress) (K : MlKem)
    (s msg s' : Bytes) (salt : Salt)
    (hval : ValidStatePts s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).recv s msg = .ok (s', salt)) :
    ValidStatePts s' := by
  obtain ⟨st, rfl, hst_pts⟩ := validStatePts_exists_encodeState hval
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) (encodeState st) msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only at h
    cases hsalt : recvKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only at h
      have hs'_eq := (Prod.mk.inj (Except.ok.inj h)).1; subst hs'_eq
      have hdec_eq := decodeState_spqrDeps_encodeState_pb F K st hlen
      unfold recv at hrecv; dsimp only at hrecv
      rcases except_bind_eq_ok hrecv with ⟨pmsg, _, h1⟩
      rcases except_bind_eq_ok h1 with ⟨prePb, hdec, h2⟩
      rw [SpqrApiResult.ofError_eq_ok, hdec_eq] at hdec
      have hpre := Except.ok.inj hdec; subst hpre
      replace h2 := if_error_eq_ok_l (if_error_eq_ok_l h2)
      rcases if_eq_ok_cases_l h2 with h2 | h2
      · have hinj := Except.ok.inj h2; subst hinj; exact Or.inl rfl
      · rcases if_eq_ok_cases_l h2 with h2 | h2
        · rcases except_bind_eq_ok h2 with ⟨chain0, _, h3⟩
          rcases except_bind_eq_ok h3 with ⟨⟨chain1, _⟩, _, h4⟩
          dsimp only at h4; have hinj := Except.ok.inj h4; subst hinj
          refine Or.inr ⟨_, rfl, ?_⟩
          unfold ValidPqPts pbToPqRatchetState pqRatchetStateToPb
          unfold ValidPqPts at hst_pts
          cases hin : st.inner with
          | none => trivial
          | some i => cases i; rw [hin] at hst_pts; exact hst_pts
        · have hpre_pts : ∀ pb, (pqRatchetStateToPb st).inner = some pb → ValidV1Pts pb := by
            intro pb hpb
            unfold ValidPqPts at hst_pts
            cases hin : st.inner with
            | none => simp [pqRatchetStateToPb, hin] at hpb
            | some i =>
              cases i with
              | v1 v =>
                simp only [pqRatchetStateToPb, hin, Option.map, Option.some.injEq] at hpb
                subst hpb; rw [hin] at hst_pts; exact hst_pts
          rcases if_pure_bind_eq_ok_l h2
            (fun statePb => ∀ pb, statePb.inner = some pb → ValidV1Pts pb)
            hpre_pts
            (by
              intro h2
              rcases if_eq_ok_cases_l h2 with h2 | h2
              · dsimp only [Bind.bind, Except.bind] at h2; contradiction
              · cases hvn : (pqRatchetStateToPb st).versionNegotiation with
                | none => rw [hvn] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                | some vn =>
                  rw [hvn] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                  cases hv : Version.fromU8? pmsg.version with
                  | none => rw [hv] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                  | some v =>
                    rw [hv] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                    cases hd : Direction.fromI32? vn.direction with
                    | none => rw [hd] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                    | some dir =>
                      rw [hd] at h2; dsimp only at h2; rw [pure_bind_except_l] at h2
                      rcases except_bind_eq_ok h2 with ⟨inner', hinit, hlt4⟩
                      rcases except_bind_eq_ok hlt4 with ⟨chain', _, hlt5⟩
                      rw [SpqrApiResult.ofPanic_eq_ok] at hinit
                      rw [pure_bind_except_l] at hlt5
                      exact ⟨{ inner := inner', versionNegotiation := none, chain := some chain'.intoPb },
                        validV1Pts_initInner hinit, hlt5⟩)
            with ⟨statePb, hstPb_pts, h3⟩
          cases hinner : statePb.inner with
          | none =>
            rw [hinner] at h3; have hinj := Except.ok.inj h3; subst hinj; exact Or.inl rfl
          | some pb =>
            rw [hinner] at h3; dsimp only at h3
            rcases except_bind_eq_ok h3 with ⟨sckaMsg, _, h4⟩
            rcases except_bind_eq_ok h4 with ⟨st0', hfrom, h5⟩
            rcases except_bind_eq_ok h5 with ⟨⟨key, st1⟩, hrecv_st, h6⟩
            unfold spqrDeps liftStatesResult at hfrom; dsimp only at hfrom
            cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
            | error se => rw [hs0] at hfrom; cases se <;> contradiction
            | ok st0 =>
              rw [hs0] at hfrom; have hst0 := Except.ok.inj hfrom; subst hst0
              have hst0_pts := statesPtsBounded_of_from_pb (hstPb_pts pb hinner) hs0
              unfold spqrDeps at hrecv_st; dsimp only at hrecv_st
              cases hr0 : st0.recv K sckaMsg with
              | error se => rw [hr0] at hrecv_st; cases se <;> contradiction
              | ok rOut =>
                rw [hr0] at hrecv_st
                have hst1 := (Prod.mk.inj (Except.ok.inj hrecv_st)).2; subst hst1
                have hrOut_pts := validV1Pts_states_into_pb
                  (statesPtsBounded_of_recv hst0_pts hr0)
                dsimp only at h6; split at h6 <;> [contradiction; skip]
                rcases except_bind_eq_ok h6 with ⟨chain0, _, h7⟩
                have htail : ∀ (chain1 : CryptoVerification.LibsignalSpqrV1.Chain),
                    (do
                      let (chain2, msgKey) ← SpqrApiResult.ofChainResult
                        (chain1.recvKey (spqrHkdfWith F) (pmsg.epoch - 1#64) pmsg.index)
                      Except.ok ({
                        state := (spqrDeps F K).encodeState {
                          inner := some ((spqrDeps F K).statesIntoPb rOut.state),
                          versionNegotiation := none, chain := some chain2.intoPb },
                        key := if msgKey.isEmpty then none else some msgKey } : Recv)) = .ok out →
                    ValidStatePts out.state := by
                  intro chain1 h8
                  rcases except_bind_eq_ok h8 with ⟨⟨chain2, msgKey⟩, _, h9⟩
                  have hinj := Except.ok.inj h9; subst hinj
                  exact Or.inr ⟨_, rfl, hrOut_pts⟩
                cases key with
                | none =>
                  dsimp only at h7; rw [pure_bind_except_l] at h7
                  exact htail chain0 h7
                | some es =>
                  dsimp only at h7
                  rcases except_bind_eq_ok h7 with ⟨chain1, _, h8⟩
                  exact htail chain1 h8

/-- Every reachable PQXDH session state satisfies both `ValidStatePts` and `< 2 ^ 64` bytes. -/
theorem validStatePts_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidStatePts g.session.pqRatchetState ∧ g.session.pqRatchetState.length < 2 ^ 64 := by
  induction h with
  | initiate X P me b t x g hi =>
    change initiateStateV1 X W W.Q.K P me b t = some (x, g) at hi
    unfold initiateStateV1 at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi
      unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C
            (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        obtain ⟨hv, h32⟩ := validStatePts_spqrV1Init W.C.F W.Q.K .a2b _
        exact ⟨hv, Nat.lt_trans h32 (by decide)⟩
  | recvPrekey X P me k m rc x g pt hr =>
    change recvPrekeyStateV1 X W W.Q.K P me k m rc = some (some (x, g, pt)) at hr
    unfold recvPrekeyStateV1 at hr
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at hr
    · rw [htf] at hr; dsimp only at hr
      split_ifs at hr with hids
      · simp at hr
      · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
          _ | dk
        · simp [hacc] at hr
        · rw [hacc] at hr; dsimp only at hr
          let st0 : SessionState Bytes :=
            initializeRecipientSession (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          have hseeds0 : SeedsLen32 st0 := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
              SeedsLen32]
          have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
          obtain ⟨hval0, h32_0⟩ := validStatePts_spqrV1Init W.C.F W.Q.K .b2a
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          change (match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with
            | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none) = some (some (x, g, pt)) at hr
          rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
          · rw [hdec] at hr; cases e <;> simp at hr
          · rw [hdec] at hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨-, -, -, -, key, hrecv⟩ :=
              tryDecryptFromRecord_ok_props_gen W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
                ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 st pt'
                hseeds0 hlen0 hdec
            exact ⟨validStatePts_spqrV1_recv W.C.F W.Q.K _ _ _ key hval0
                (Nat.lt_trans h32_0 (by decide)) hrecv,
              (encodeState_len_lt_recv W.C.F W.Q.K _ _ _ key h32_0 hrecv).2.2.2⟩
  | @send _ x_s g_s m r hr hlen ih =>
    have h32 : g_s.session.pqRatchetState.length < 2 ^ 32 := by
      have hle := pqRatchetState_length_le_encodeRecordX (fun _ => x_s) g_s
      omega
    rw [send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with ⟨_ | msg, s⟩
    · exact ih
    · obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
      obtain ⟨-, -, -, -, key, pm, hsend, -⟩ :=
        messageEncrypt_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg
          hseeds hlen' hm
      exact ⟨validStatePts_spqrV1_send W.C.F W.Q.K _ _ _ key pm ih.1 ih.2 hsend,
        (encodeState_len_lt_send W.C.F W.Q.K _ _ _ key pm h32 hsend).2.2.2⟩
  | @recv _ x_r g_r g'_r c rc res hr hlen hrec ih =>
    have h32 : g_r.session.pqRatchetState.length < 2 ^ 32 := by
      have hle := pqRatchetState_length_le_encodeRecordX (fun _ => x_r) g_r
      omega
    rcases res with ⟨_, _, pt⟩
    rw [receive_eq_afterRecv] at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
          msg .whisper rc g_r.session with ⟨_ | pt', s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec
        simp only [Option.some.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
        obtain ⟨-, -, -, -, key, hrecv⟩ :=
          tryDecryptFromRecord_ok_props_gen (pqxdhSessionParams W).C
            (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
            msg .whisper rc g_r.session s pt hseeds hlen' hd
        exact ⟨validStatePts_spqrV1_recv W.C.F W.Q.K _ _ _ key ih.1 ih.2 hrecv,
          (encodeState_len_lt_recv W.C.F W.Q.K _ _ _ key h32 hrecv).2.2.2⟩

/-- Every reachable PQXDH session state satisfies `ValidEncoderPts`. -/
theorem validEncoderPts_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidEncoderPts g.session.pqRatchetState := by
  obtain ⟨hv, hlen⟩ := validStatePts_of_reachPq h
  exact validEncoderPts_of_validStatePts hlen hv

/-! ## 4. SPQR V1 `PolyDecoder` `ptsNeeded` Caps (`StatesDecPtsNeededBound`) -/

/-- Upper bounds on `ptsNeeded` across every `PolyDecoder`-bearing constructor of `States`,
established by `States.from_pb`. -/
def StatesDecPtsNeededBound {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .headerSent s => s.receiving_ct1.ptsNeeded ≤ 480
  | .ekSentCt1Received s => s.receiving_ct2.ptsNeeded ≤ 80
  | .noHeaderReceived s => s.receiving_hdr.ptsNeeded ≤ 48
  | .headerReceived s => s.receiving_ek.ptsNeeded ≤ 576
  | .ct1Sampled s => s.receiving_ek.ptsNeeded ≤ 576
  | .ct1Acknowledged s => s.receiving_ek.ptsNeeded ≤ 576
  | _ => True

theorem StatesDecPtsNeededBound.toStatesPtsNeededBound {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} (h : StatesDecPtsNeededBound st) :
    StatesPtsNeededBound st := by
  cases st <;> simp_all [StatesDecPtsNeededBound, StatesPtsNeededBound]

private theorem ekSentCt1Received_from_pb_pts {F : ShaCompress}
    {pb : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkSentCt1Received}
    {s : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)}
    (hv : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    s.receiving_ct2.ptsNeeded ≤ 80 := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.from_pb at hv
  dsimp only [Bind.bind, Except.bind] at hv
  cases huc : pb.uc with
  | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
  | some u =>
    rw [huc] at hv
    cases hrec : pb.receivingCt2 with
    | none =>
      rw [hrec] at hv; dsimp only at hv
      rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
      simp [CryptoVerification.LibsignalSpqrV1.decoderFromPbStateDecode] at hv2
    | some d =>
      rw [hrec] at hv; dsimp only at hv
      split at hv
      · contradiction
      · rename_i hfls
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, hdec, hv3⟩
        have hinj := Except.ok.inj hv3; subst hinj
        rcases decoderFromPbStateDecode_raw_le hdec with ⟨_, _, hd', hpts⟩
        cases hd'
        have hval : d.ptsNeeded.toNat = 80 := bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hfls)
        rw [hpts, hval]

private theorem noHeaderReceived_from_pb_pts {F : ShaCompress}
    {pb : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived}
    {s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)}
    (hv : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    s.receiving_hdr.ptsNeeded ≤ 48 := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.from_pb at hv
  dsimp only [Bind.bind, Except.bind] at hv
  cases huc : pb.uc with
  | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
  | some u =>
    rw [huc] at hv
    cases hrec : pb.receivingHdr with
    | none =>
      rw [hrec] at hv; dsimp only at hv
      rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
      simp [CryptoVerification.LibsignalSpqrV1.decoderFromPbStateDecode] at hv2
    | some d =>
      rw [hrec] at hv; dsimp only at hv
      split at hv
      · contradiction
      · rename_i hfls
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, hdec, hv3⟩
        have hinj := Except.ok.inj hv3; subst hinj
        rcases decoderFromPbStateDecode_raw_le hdec with ⟨_, _, hd', hpts⟩
        cases hd'
        have hval : d.ptsNeeded = 48#32 := bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hfls)
        rw [hpts, hval]; decide

private theorem headerReceived_from_pb_pts {F : ShaCompress}
    {pb : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.HeaderReceived}
    {s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)}
    (hv : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    s.receiving_ek.ptsNeeded ≤ 576 := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.from_pb at hv
  dsimp only [Bind.bind, Except.bind] at hv
  cases huc : pb.uc with
  | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
  | some u =>
    rw [huc] at hv
    cases hrec : pb.receivingEk with
    | none =>
      rw [hrec] at hv; dsimp only at hv
      rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
      simp [CryptoVerification.LibsignalSpqrV1.decoderFromPbStateDecode] at hv2
    | some d =>
      rw [hrec] at hv; dsimp only at hv
      split at hv
      · contradiction
      · rename_i hfls
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, hdec, hv3⟩
        have hinj := Except.ok.inj hv3; subst hinj
        rcases decoderFromPbStateDecode_raw_le hdec with ⟨_, _, hd', hpts⟩
        cases hd'
        have hval : d.ptsNeeded.toNat = 576 := bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hfls)
        rw [hpts, hval]

private theorem ct1Sampled_from_pb_pts {F : ShaCompress}
    {pb : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Sampled}
    {s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    (hv : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    s.receiving_ek.ptsNeeded ≤ 576 := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.from_pb at hv
  dsimp only [Bind.bind, Except.bind] at hv
  cases huc : pb.uc with
  | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
  | some u =>
    rw [huc] at hv
    cases hrec : pb.receivingEk with
    | none =>
      rw [hrec] at hv; dsimp only at hv
      rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
      rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
      simp [CryptoVerification.LibsignalSpqrV1.decoderFromPbStateDecode] at hv3
    | some d =>
      rw [hrec] at hv; dsimp only at hv
      split at hv
      · contradiction
      · rename_i hfls
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
        rcases except_bind_eq_ok hv3 with ⟨_, hdec, hv4⟩
        have hinj := Except.ok.inj hv4; subst hinj
        rcases decoderFromPbStateDecode_raw_le hdec with ⟨_, _, hd', hpts⟩
        cases hd'
        have hval : d.ptsNeeded.toNat = 576 := bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hfls)
        rw [hpts, hval]

private theorem ct1Acknowledged_from_pb_pts {F : ShaCompress}
    {pb : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Acknowledged}
    {s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    (hv : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    s.receiving_ek.ptsNeeded ≤ 576 := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.from_pb at hv
  dsimp only [Bind.bind, Except.bind] at hv
  cases huc : pb.uc with
  | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
  | some u =>
    rw [huc] at hv
    cases hrec : pb.receivingEk with
    | none =>
      rw [hrec] at hv; dsimp only at hv
      rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
      simp [CryptoVerification.LibsignalSpqrV1.decoderFromPbStateDecode] at hv2
    | some d =>
      rw [hrec] at hv; dsimp only at hv
      split at hv
      · contradiction
      · rename_i hfls
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, hdec, hv3⟩
        have hinj := Except.ok.inj hv3; subst hinj
        rcases decoderFromPbStateDecode_raw_le hdec with ⟨_, _, hd', hpts⟩
        cases hd'
        have hval : d.ptsNeeded.toNat = 576 := bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hfls)
        rw [hpts, hval]

/-- `States.from_pb` establishes `StatesDecPtsNeededBound`. -/
theorem StatesDecPtsNeededBound.of_from_pb {F : ShaCompress}
    {pb : CryptoVerification.LibsignalSpqrV1.V1State}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    StatesDecPtsNeededBound st := by
  have hhs := (CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le h).2
  unfold States.from_pb at h
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; cases h
  | some inner =>
    rw [hinner] at h
    cases inner with
    | keysUnsampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      cases Except.ok.inj h; trivial
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      cases Except.ok.inj h; trivial
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      cases Except.ok.inj h; exact hhs
    | ct1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      cases Except.ok.inj h; trivial
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; cases Except.ok.inj h
      exact ekSentCt1Received_from_pb_pts hv
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; cases Except.ok.inj h
      exact noHeaderReceived_from_pb_pts hv
    | headerReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; cases Except.ok.inj h
      exact headerReceived_from_pb_pts hv
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; cases Except.ok.inj h
      exact ct1Sampled_from_pb_pts hv
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      cases Except.ok.inj h; trivial
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; cases Except.ok.inj h
      exact ct1Acknowledged_from_pb_pts hv
    | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      cases Except.ok.inj h; trivial

end LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
