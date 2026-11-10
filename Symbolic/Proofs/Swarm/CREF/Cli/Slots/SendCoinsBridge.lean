/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
public import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureA

/-!
# Send Coin-Prefix and Pending-Flag Bridges

Relates the 64-byte CLI randomness of a `send` call to the variable-length hardware RNG draw
(`0`, `32`, or `64` bytes via `trSendDrawSizeOf`), and characterizes `PureRecPending` and
`SingleSession` on `encodeRecordUnderExtras` under `PqxdhPartyInSpecDomain`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Proofs.libsignal.SR (AesW)
open Symbolic.Swarm.TRREF.SpqrSemOf
open Symbolic.Swarm.CREF.Cli

/-! ## `PureRecPending` and `SingleSession` on `encodeRecordUnderExtras` -/

theorem recPending_iff_pureRecPending {b : HwBytes} :
    Symbolic.Swarm.CREF.TR.PureRecPending b ↔ Symbolic.Swarm.CREF.CliPure.SndPure.PureRecPending b :=
  Iff.rfl

theorem singleSession_encodeRecordX_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    DY.Libsignal.Composed.Refinement.SingleSession (encodeRecordUnderExtras (fun _ => x) g) := by
  have hrc := recordCanonical_Q_of_wfPq hwf hsess
  exact ⟨Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.sessionToRecordRecPending (pqSession x g),
    hrc.1.trans
      (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q
        hrc).symm,
    rfl⟩

theorem recPending_encodeRecordX_iff {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    Symbolic.Swarm.CREF.TR.PureRecPending (encodeRecordUnderExtras (fun _ => x) g) ↔
      g.session.pendingPreKey = true := by
  have hrc_pq := recordCanonical_Q_of_wfPq hwf hsess
  constructor
  · rintro ⟨sess, hrc, his⟩
    cases hppk : g.session.pendingPreKey with
    | true => rfl
    | false =>
      exfalso
      have hb₁ : encodeRecordUnderExtras (fun _ => x) g =
          DY.Libsignal.Composed.Refinement.recordBytes
            (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.sessionToRecordRecPending sess) :=
        hrc.1.trans
          (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q
            hrc).symm
      have hb₂ : encodeRecordUnderExtras (fun _ => x) g =
          DY.Libsignal.Composed.Refinement.recordBytes
            (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.sessionToRecordRecPending (pqSession x g)) :=
        hrc_pq.1.trans
          (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q
            hrc_pq).symm
      have hinj := Symbolic.Swarm.CREF.TR.recordBytes_injective (hb₁.symm.trans hb₂)
      have hcur := congrArg (fun r => r.current.pendingPreKey) hinj
      obtain ⟨p, hp_some⟩ := Option.isSome_iff_exists.mp his
      simp [Symbolic.Swarm.CREF.TR.normPending, Symbolic.Swarm.CREF.TR.normPendingS,
        Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.sessionToRecordRecPending, hp_some] at hcur
      rw [hppk] at hcur
      exact Bool.noConfusion hcur.1
  · intro hppk
    refine ⟨pqSession x g, hrc_pq, ?_⟩
    simp [pqSession, hppk]

/-! ## SPQR `send` Draw-Size Analysis -/

section SpqrDraw

open CryptoVerification.LibsignalSpqrV1
open DY.Libsignal.Refinement (sha256CompressFunction)

/-- Draw size of `States.send`: `64` on `keysUnsampled`, `32` on `headerReceived`, and `0` otherwise. -/
def statesDrawSize {P : PolyApi} {Au : AuthApi} : States P Au → Nat
  | .keysUnsampled _ => 64
  | .headerReceived _ => 32
  | .keysSampled _ | .headerSent _ | .ct1Received _ | .ekSentCt1Received _
  | .noHeaderReceived _ | .ct1Sampled _ | .ekReceivedCt1Sampled _ | .ct1Acknowledged _
  | .ct2Sampled _ => 0

/-- State-only draw size of `spqr::send`. -/
def trSendDrawSize (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : List (BitVec 8)) : Nat :=
  match decodeState (spqrDepsWithMac F K mac) st with
  | .error _ => 0
  | .ok pb =>
    match pb.inner with
    | none => 0
    | some v1 =>
      match (spqrDepsWithMac F K mac).statesFromPb v1 with
      | .error _ => 0
      | .ok st0 => statesDrawSize st0

/-- State-only SPQR `send` draw size induced by `interp`. -/
abbrev trSendDrawSizeOf (i : ExternInterpretation) : List (BitVec 8) → Nat :=
  trSendDrawSize (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

private theorem generate_eq_match_sd (K : MlKem) (tape : List (BitVec 8)) :
    generate K tape =
      match (if h : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE
             then some ⟨tape.take KEY_GENERATION_SEED_SIZE, h⟩ else none) with
      | none => .error (.rngExhausted KEY_GENERATION_SEED_SIZE tape.length)
      | some seed =>
        let (hdr, ek, dk) := K.fromSeed seed
        .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList },
          tape.drop KEY_GENERATION_SEED_SIZE) := rfl

private theorem encaps1_eq_match_sd (K : MlKem) (hdr : Header) (tape : List (BitVec 8)) :
    encaps1 K hdr tape =
      match (if h1 : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE
             then some ⟨tape.take SHARED_SECRET_SIZE, h1⟩ else none) with
      | none => .error (.rngExhausted SHARED_SECRET_SIZE tape.length)
      | some rand =>
        match K.encaps1 hdr rand with
        | none => .error .encaps1Failed
        | some (ct1, es, ss) =>
          .ok ((ct1.toList, es.toList, ss.toList), tape.drop SHARED_SECRET_SIZE) := rfl

private def keysOf_sd (K : MlKem) (seed : List.Vector (BitVec 8) 64) : Keys :=
  let (hdr, ek, dk) := K.fromSeed seed
  { ek := ek.toList, dk := dk.toList, hdr := hdr.toList }

private def encaps1Out_sd (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    (rest : List (BitVec 8)) :
    Except StatesPanic ((Ciphertext1 × EncapsulationState × Secret) × List (BitVec 8)) :=
  match K.encaps1 hdr rand with
  | none => .error .encaps1Failed
  | some (ct1, es, ss) => .ok ((ct1.toList, es.toList, ss.toList), rest)

private theorem length_take_of_le_sd {n : Nat} {tape : List (BitVec 8)} (h : n ≤ tape.length) :
    (tape.take n).length = n := by rw [List.length_take]; omega

private theorem generate_of_le_sd (K : MlKem) {tape : List (BitVec 8)} (h : 64 ≤ tape.length) :
    generate K tape = .ok (keysOf_sd K ⟨tape.take 64, length_take_of_le_sd h⟩, tape.drop 64) := by
  rw [generate_eq_match_sd]
  have hlen : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE :=
    length_take_of_le_sd h
  rw [dite_eq_left hlen]; rfl

private theorem generate_take_sd (K : MlKem) {tape : List (BitVec 8)} (h : 64 ≤ tape.length) :
    generate K (tape.take 64) = .ok (keysOf_sd K ⟨tape.take 64, length_take_of_le_sd h⟩, []) := by
  have h' : 64 ≤ (tape.take 64).length := by rw [length_take_of_le_sd h]
  rw [generate_of_le_sd K h']; simp only [List.drop_take, Nat.sub_self, List.take_zero]
  have hv : (⟨(tape.take 64).take 64, length_take_of_le_sd h'⟩ : List.Vector (BitVec 8) 64) =
      ⟨tape.take 64, length_take_of_le_sd h⟩ := Subtype.ext (by simp)
  rw [hv]

private theorem encaps1_of_le_sd (K : MlKem) (hdr : Header) {tape : List (BitVec 8)}
    (h : 32 ≤ tape.length) :
    encaps1 K hdr tape =
      encaps1Out_sd K hdr ⟨tape.take 32, length_take_of_le_sd h⟩ (tape.drop 32) := by
  rw [encaps1_eq_match_sd]
  have hlen : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE := length_take_of_le_sd h
  rw [dite_eq_left hlen]; rfl

private theorem encaps1_take_sd (K : MlKem) (hdr : Header) {tape : List (BitVec 8)}
    (h : 32 ≤ tape.length) :
    encaps1 K hdr (tape.take 32) =
      encaps1Out_sd K hdr ⟨tape.take 32, length_take_of_le_sd h⟩ [] := by
  have h' : 32 ≤ (tape.take 32).length := by rw [length_take_of_le_sd h]
  rw [encaps1_of_le_sd K hdr h']; simp only [List.drop_take, Nat.sub_self, List.take_zero]
  have hv : (⟨(tape.take 32).take 32, length_take_of_le_sd h'⟩ : List.Vector (BitVec 8) 32) =
      ⟨tape.take 32, length_take_of_le_sd h⟩ := Subtype.ext (by simp)
  rw [hv]

private theorem ok_bind_sd {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x : Except ε α) >>= f = f x := rfl

private theorem liftM_spqr_ok_sd {α : Type} (v : α) :
    (liftM (Except.ok v : Except SpqrPanic α) : Except StatesPanic α) = .ok v := rfl

private def statesSendCore_sd {P : PolyApi} {Au : AuthApi} (K : MlKem) (s : States P Au)
    (pre : List (BitVec 8)) : StatesResult (V1Send P Au) := (s.send K pre).map Prod.fst

private theorem states_send_eq_sd {P : PolyApi} {Au : AuthApi} (K : MlKem) (s : States P Au)
    (tape : List (BitVec 8)) (h : statesDrawSize s ≤ tape.length) :
    s.send K tape =
      (statesSendCore_sd K s (tape.take (statesDrawSize s))).map
        (fun o => (o, tape.drop (statesDrawSize s))) := by
  unfold statesSendCore_sd; cases s
  case keysUnsampled st =>
    simp only [statesDrawSize] at h ⊢
    simp only [States.send, Chunked.SendEk.KeysUnsampled.send_hdr_chunk,
      Unchunked.SendEk.KeysUnsampled.send_header, generate_of_le_sd K h, generate_take_sd K h,
      ok_bind_sd]
    generalize keysOf_sd K ⟨tape.take 64, length_take_of_le_sd h⟩ = keys
    rcases hm : Au.mac_hdr st.uc.auth st.uc.epoch keys.hdr with _ | mac; · rfl
    simp only [liftM_spqr_ok_sd, ok_bind_sd]
    rcases he : expectEncodeBytes P "v1/chunked/send_ek.rs:63" (keys.hdr ++ mac) with _ | enc; · rfl
    simp only [ok_bind_sd]
    rcases hn : P.next_chunk enc with _ | ⟨enc', chunk⟩ <;> rfl
  case headerReceived st =>
    simp only [statesDrawSize] at h ⊢
    simp only [States.send, Chunked.SendCt.HeaderReceived.send_ct1_chunk,
      Unchunked.SendCt.HeaderReceived.send_ct1, encaps1_of_le_sd K _ h, encaps1_take_sd K _ h,
      encaps1Out_sd]
    generalize (⟨tape.take 32, length_take_of_le_sd h⟩ : List.Vector (BitVec 8) 32) = rand
    rcases hk : K.encaps1 st.uc.hdr rand with _ | ⟨ct1, es, ss⟩; · rfl
    simp only [ok_bind_sd]
    rcases hh : Au.hkdf_to_vec (List.replicate 32 0#8) ss.toList _ 32 with _ | secret; · rfl
    simp only [liftM_spqr_ok_sd, ok_bind_sd]
    rcases hu : Au.update st.uc.auth st.uc.epoch secret with _ | auth; · rfl
    simp only [liftM_spqr_ok_sd, ok_bind_sd]
    rcases he : expectEncodeBytes P "v1/chunked/send_ct.rs:131" ct1.toList with _ | enc; · rfl
    simp only [ok_bind_sd]
    rcases hn : P.next_chunk enc with _ | ⟨enc', chunk⟩ <;> rfl
  all_goals
    simp only [statesDrawSize, List.take_zero, List.drop_zero]
    first | rfl | (simp only [States.send, bind, Except.bind]; split <;> rfl)

private def preSend_sd (D : SpqrApiDeps) (state : SerializedState) :
    Except (SpqrApiResult Send) (PqRatchetStatePB D.V1StatePB × D.States) :=
  match decodeState D state with
  | .error e => .error (.error (.err e))
  | .ok statePb =>
    match statePb.inner with
    | none => .error (.ok { state := [], msg := [], key := none })
    | some pb =>
      match D.statesFromPb pb with
      | .error e => .error (.error e)
      | .ok st0 => .ok (statePb, st0)

private def sendPost_sd (D : SpqrApiDeps) (hkdf : HkdfFn) (statePb : PqRatchetStatePB D.V1StatePB)
    (q : SpqrApiResult (D.MessageV1 × Option EpochSecret × D.States) × List (BitVec 8)) :
    SpqrApiResult Send × List (BitVec 8) :=
  let (sendRes, tape') := q
  match sendRes with
  | .error e => (.error e, tape')
  | .ok (msg, key, st1) => (sendAfterStates D hkdf statePb msg key st1, tape')

private theorem sendPost_eq_sd (D : SpqrApiDeps) (hkdf : HkdfFn) (statePb : PqRatchetStatePB D.V1StatePB)
    (q : SpqrApiResult (D.MessageV1 × Option EpochSecret × D.States) × List (BitVec 8)) :
    sendPost_sd D hkdf statePb q =
      ((match q.1 with
        | .error e => .error e
        | .ok (msg, key, st1) => sendAfterStates D hkdf statePb msg key st1), q.2) := by
  rcases q with ⟨r, t⟩; rcases r with _ | ⟨_, _, _⟩ <;> rfl

private theorem send_eq_preSend_sd (D : SpqrApiDeps) (hkdf : HkdfFn) (state tape : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.send D hkdf state tape =
      match preSend_sd D state with
      | .error r => (r, tape)
      | .ok (statePb, st0) => sendPost_sd D hkdf statePb (D.statesSend st0 tape) := by
  unfold CryptoVerification.LibsignalSpqrV1.send preSend_sd sendPost_sd
  rcases decodeState D state with _ | statePb; · rfl
  dsimp only; rcases statePb.inner with _ | pb; · rfl
  dsimp only; rcases D.statesFromPb pb with _ | st0 <;> rfl

private theorem send_of_preSend_ok_sd (D : SpqrApiDeps) (hkdf : HkdfFn) {st : List (BitVec 8)}
    {statePb : PqRatchetStatePB D.V1StatePB} {st0 : D.States}
    (hp : preSend_sd D st = .ok (statePb, st0)) (tape : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.send D hkdf st tape =
      ((match (D.statesSend st0 tape).1 with
        | .error e => .error e
        | .ok (msg, key, st1) => sendAfterStates D hkdf statePb msg key st1),
       (D.statesSend st0 tape).2) := by
  have h1 := send_eq_preSend_sd D hkdf st tape
  rw [hp] at h1
  exact h1.trans (sendPost_eq_sd D hkdf statePb (D.statesSend st0 tape))

private theorem trSendDrawSize_eq_sd (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : List (BitVec 8)) :
    trSendDrawSize F K mac st =
      match preSend_sd (spqrDepsWithMac F K mac) st with
      | .error _ => 0
      | .ok (_, st0) => statesDrawSize st0 := by
  unfold trSendDrawSize preSend_sd
  rcases decodeState (spqrDepsWithMac F K mac) st with _ | statePb; · rfl
  dsimp only; rcases statePb.inner with _ | pb; · rfl
  dsimp only; rcases (spqrDepsWithMac F K mac).statesFromPb pb with _ | st0 <;> rfl

private def statesSendBody_sd (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)) (t : List (BitVec 8)) :
    SpqrApiResult (Message spqrPolyApi × Option EpochSecret ×
      States spqrPolyApi (spqrAuthApiWithMac F mac)) × List (BitVec 8) :=
  match st0.send K t with
  | .ok (sOut, tape') => (.ok (sOut.msg, sOut.key, sOut.state), tape')
  | .error (.err e) => (.error (.err e), t)
  | .error (.panic _) => (.error (.panic .v1), t)

private theorem spqrDepsWithMac_statesSend_sd (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)) (t : List (BitVec 8)) :
    (spqrDepsWithMac F K mac).statesSend st0 t = statesSendBody_sd F K mac st0 t := rfl

private theorem statesSend_fst_take_sd (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)) (tape : List (BitVec 8))
    (h : statesDrawSize st0 ≤ tape.length) :
    ((spqrDepsWithMac F K mac).statesSend st0 (tape.take (statesDrawSize st0))).1 =
      ((spqrDepsWithMac F K mac).statesSend st0 tape).1 := by
  have h' : statesDrawSize st0 ≤ (tape.take (statesDrawSize st0)).length := by
    rw [length_take_of_le_sd h]
  rw [spqrDepsWithMac_statesSend_sd, spqrDepsWithMac_statesSend_sd]
  unfold statesSendBody_sd
  rw [states_send_eq_sd K st0 (tape.take _) h', List.take_take, Nat.min_self,
      states_send_eq_sd K st0 tape h]
  rcases statesSendCore_sd K st0 (tape.take (statesDrawSize st0)) with e | _
  · cases e <;> rfl
  · rfl

theorem trSendDrawSizeOf_cases (i : ExternInterpretation) (st : List (BitVec 8)) :
    trSendDrawSizeOf i st = 0 ∨ trSendDrawSizeOf i st = 32 ∨ trSendDrawSizeOf i st = 64 := by
  unfold trSendDrawSizeOf; rw [trSendDrawSize_eq_sd]
  rcases preSend_sd _ st with _ | ⟨_, st0⟩
  · exact .inl rfl
  · cases st0 <;> simp [statesDrawSize]

theorem send_take_trSendDrawSize_spqrModelOf (i : ExternInterpretation)
    (st tape : List (BitVec 8)) (hlen : trSendDrawSizeOf i st ≤ tape.length) :
    (spqrModelOf i).send st (tape.take (trSendDrawSizeOf i st)) = (spqrModelOf i).send st tape ∧
      ((spqrModelOf i).sendPanics st (tape.take (trSendDrawSizeOf i st)) ↔
        (spqrModelOf i).sendPanics st tape) := by
  let F := sha256CompressFunction i
  let K := mlkemOf i
  let mac := hmacFnOf i
  have hfst :
      (CryptoVerification.LibsignalSpqrV1.send (spqrDepsWithMac F K mac) (spqrHkdfWith F)
        st (tape.take (trSendDrawSize F K mac st))).1 =
      (CryptoVerification.LibsignalSpqrV1.send (spqrDepsWithMac F K mac) (spqrHkdfWith F)
        st tape).1 := by
    change trSendDrawSize F K mac st ≤ tape.length at hlen
    rw [trSendDrawSize_eq_sd] at hlen ⊢
    rcases hp : preSend_sd (spqrDepsWithMac F K mac) st with r | ⟨statePb, st0⟩
    · rw [send_eq_preSend_sd, send_eq_preSend_sd, hp]
    · rw [hp] at hlen; dsimp only at hlen ⊢
      rw [send_of_preSend_ok_sd _ _ hp, send_of_preSend_ok_sd _ _ hp]
      dsimp only; rw [statesSend_fst_take_sd F K mac st0 tape hlen]
  refine ⟨?_, ?_⟩
  · change (toSpqrModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)).send st _ =
      (toSpqrModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)).send st tape
    unfold toSpqrModel; dsimp only; rw [hfst]
  · change (toSpqrModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)).sendPanics st _ ↔
      (toSpqrModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)).sendPanics st tape
    unfold toSpqrModel; dsimp only; unfold sendPanicsPureB; rw [hfst]

end SpqrDraw

/-! ## Drawn Coin Prefix (`sendCoinsOf`) -/

/-- Exact prefix (`0`, `32`, or `64` bytes) of `r_coins` consumed by SPQR `send` on `pq`. -/
def sendCoinsOf (interp : ExternInterpretation) (pq r_coins : HwBytes) : HwBytes :=
  r_coins.take (trSendDrawSizeOf interp pq)

/-- Hardware RNG event list corresponding to `coins` (`[]` when empty, `[.rng coins]` otherwise). -/
def sendMidOf (coins : HwBytes) : List MachineEvent :=
  if coins = [] then [] else [.rng coins]

theorem trSendDrawSizeOf_le_64 (interp : ExternInterpretation) (pq : HwBytes) :
    trSendDrawSizeOf interp pq ≤ 64 := by
  rcases trSendDrawSizeOf_cases interp pq with h | h | h <;> omega

theorem sendCoinsOf_prefix (interp : ExternInterpretation) (pq r_coins : HwBytes) :
    sendCoinsOf interp pq r_coins <+: r_coins :=
  List.take_prefix _ _

theorem sendMidOf_cases (coins : HwBytes) :
    (coins = [] ∧ sendMidOf coins = []) ∨
      (coins ≠ [] ∧ sendMidOf coins = [.rng coins]) := by
  unfold sendMidOf
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

theorem spqrModelOf_send_sendCoinsOf (interp : ExternInterpretation)
    (pq : HwBytes) {r_coins : HwBytes} (hr : r_coins.length = 64) :
    (spqrModelOf interp).send pq (sendCoinsOf interp pq r_coins) =
        (spqrModelOf interp).send pq r_coins ∧
      ((spqrModelOf interp).sendPanics pq (sendCoinsOf interp pq r_coins) ↔
        (spqrModelOf interp).sendPanics pq r_coins) :=
  send_take_trSendDrawSize_spqrModelOf interp pq r_coins
    (by rw [hr]; exact trSendDrawSizeOf_le_64 interp pq)

theorem outgoingTripleRatchet_encryptW_sendCoinsOf
    (interp : ExternInterpretation) (C : Crypto) (W_aes : AesW) (codec : SignalMessageProtoCodec)
    (m : HwBytes) (addrs : Option HwBytes) {r_coins : HwBytes} (hr : r_coins.length = 64)
    (otr : OutgoingTripleRatchet HwBytes) :
    Mut.exec (Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW C W_aes codec
        (pureSpqrOf interp) m addrs (sendCoinsOf interp otr.pqrState r_coins)) otr =
      Mut.exec (Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW C W_aes codec
        (pureSpqrOf interp) m addrs r_coins) otr := by
  obtain ⟨hsend, hpan⟩ := spqrModelOf_send_sendCoinsOf interp otr.pqrState hr
  have hpan_eq : (spqrModelOf interp).sendPanics otr.pqrState
      (sendCoinsOf interp otr.pqrState r_coins) =
      (spqrModelOf interp).sendPanics otr.pqrState r_coins :=
    Bool.eq_iff_iff.mpr hpan
  unfold Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW pureSpqrOf
  simp only [mut_exec_bind, mut_exec_get, hpan_eq, hsend]

theorem sessionState_messageEncryptW_sendCoinsOf
    (interp : ExternInterpretation) (C : Crypto) (W_aes : AesW) (codec : SignalMessageProtoCodec)
    (addrs : Option HwBytes) (m : HwBytes) {r_coins : HwBytes} (hr : r_coins.length = 64)
    (st : SessionState HwBytes) :
    Proofs.libsignal.SR.SessionState.messageEncryptW C W_aes codec (pureSpqrOf interp)
        addrs m (sendCoinsOf interp st.pqRatchetState r_coins) st =
      Proofs.libsignal.SR.SessionState.messageEncryptW C W_aes codec (pureSpqrOf interp)
        addrs m r_coins st := by
  unfold Proofs.libsignal.SR.SessionState.messageEncryptW
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨e | otr, taken⟩
  · rfl
  · have hpqr : otr.pqrState = st.pqRatchetState :=
      (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.mut_exec_fromSessionState_props st otr taken hfrom).1
    dsimp only
    rw [← hpqr, outgoingTripleRatchet_encryptW_sendCoinsOf interp C W_aes codec m
      (st.encryptAddresses addrs) hr otr]

end Symbolic.Swarm.CREF.Cli.Slots
