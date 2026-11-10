/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis
import DY.Trace.Basic
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Schedule `stepView` for `bobStart` and Whisper Half-Rounds

Computes `stepView` for Call 3 (`stepView_s3`) and generic DH-ratchet `messageDecrypt` steps
(`stepView_ratchetDecTr`), and packages the inductive trace, state, and `stepView` data across all
10 clean whisper half-rounds (`h < 10`) in `CleanHalfRoundWitness` (`cleanHalfRound_at`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent RecvChain kdfCk)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step VisEntry runTrace runSteps stepView
   bobVis decVis bobOpkPk pendingPreKey newIndices newRandoms
   received receivedPlaintext eventIdx isBobDone exposures pqExposureAt trExposureAt
   rngEntry randTerm)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (RndE NetE EvP EvT EvC rnd encMsg aliceTr aliceTrOpt recvKey ratchetState)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA t4 t5 t4_length bh1 kh1 o1 keys1)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedHooks0 evictedCompFitsPinned evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens ssClean cleanRecvTerm cleanMsgIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (runSteps_append)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs ratchetKeyTimestamps append_len le_append_of_le at?_mono
   at?_append_at setupTrace_eq_t4
   encTrGen encTrGen_le
   pt2Clean coins2Clean key2Clean stA2Clean m2Clean trClean2 trClean2_length
   trClean3 trClean3_length
   mhClean3 dhsB0Clean stB0'Clean cB0Clean seedB0Clean stB3Clean bobStartSpqrKey0
   trClean4 trClean4_length s0_next_ok s1_next_ok s2_next_ok s3_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend
  (encTrGen_stepView_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound
  (ratchetDecTr ratchetDecTr_length HalfRoundInv halfRound_step inv_at_4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
  (ssClean_succ)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
  (hrSender hrReceiver hrStHSend hrStHRecv hrTsSend hrIkSend hrIkRecv
   hr_swap_eqs hr_next_ts_mem ccs_get_send ccs_get_recv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVis
  (entry_proj_none pqExp_non trExp_non pendingPreKey_eq_none_of_receiver_mk)

theorem stepView_s3 (cls : Nat → Nat) (w : Bool) :
    stepView (.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)) (trClean3 cls) w =
      ⟨.recv, [o1.ek, o1.ct, m2Clean cls], .preKeyRecv, none⟩ ::
      [rngEntry (randTerm 45 32), ⟨.accept, [pt2Clean], .single, some 47⟩] := by
  obtain ⟨hn3, hok3⟩ := s3_next_ok cls
  have h53 : t5 ≤ trClean3 cls :=
    DY.Trace.le_trans _ _ _ (encTrGen_le ..) (encTrGen_le ..)
  have hek : (trClean3 cls).getMessageSentAt 25 = some o1.ek := by
    have hat : (trClean3 cls).at? 25 = some (NetE o1.ek) := by
      refine at?_mono h53 ?_
      dsimp only [t5, aliceTr, aliceTrOpt, o1,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
      rw [t4_length]
      exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
        (le_append_of_le (DY.Trace.append_le _ _) _) _) _) _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hct : (trClean3 cls).getMessageSentAt 26 = some o1.ct := by
    have hat : (trClean3 cls).at? 26 = some (NetE o1.ct) := by
      refine at?_mono h53 ?_
      dsimp only [t5, aliceTr, aliceTrOpt, o1,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
      rw [t4_length]
      exact at?_mono (le_append_of_le (le_append_of_le
        (le_append_of_le (DY.Trace.append_le _ _) _) _) _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hmsg : (trClean3 cls).getMessageSentAt 44 = some (m2Clean cls) := by
    have hat : (trClean3 cls).at? 44 = some (NetE (m2Clean cls)) := by
      dsimp only [trClean3, encTrGen, m2Clean]
      have hm : rnd (trClean2 cls).length 32 = pt2Clean := by rw [trClean2_length]; rfl
      have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
        rw [trClean2_length]; rfl
      rw [hm, hc]
      exact at?_append_at _ _ (by simp only [append_len, trClean2_length])
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hni : newIndices (trClean3 cls) (trClean4 cls) =
      [45, 46, 47, 48, 49, 50, 51, 52, 53, 54] := by
    unfold newIndices; rw [trClean3_length, trClean4_length]; decide
  let b0 := trClean3 cls
  let b1 := b0.append (RndE 32)
  let b2 := b1.append (NetE bobStartSpqrKey0)
  let b3 := b2.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1))
  let b4 := b3.append (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0Clean)))
  let b5 := b4.append (EvT (.HonestDH ((stB0'Clean cls).sessionInfo "bob") dhsB0Clean 0))
  let b6 := b5.append (EvC (.HandshakeSession ((stB0'Clean cls).sessionInfo "bob") 47))
  let b7 := b6.append (EvT (.SkippedKeyStored ((stB0'Clean cls).sessionInfo "bob") (dhPk dhsA)
    0 (kdfCk (cB0Clean cls).chainKey).2 2 54))
  let b8 := b7.append (EvT (.Received "bob" "alice" (dhPk dhsA) 1 pt2Clean))
  let b9 := b8.append (EvT (.MessageKey ((stB0'Clean cls).sessionInfo "bob") .receiver
    (seedB0Clean cls) (key2Clean cls) 1 2 54))
  have hb9 : b9 ≤ trClean4 cls := by dsimp only [trClean4]; exact DY.Trace.append_le _ _
  have hb8 : b8 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb9
  have hb7 : b7 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb8
  have hb6 : b6 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb7
  have hb5 : b5 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb6
  have hb4 : b4 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb5
  have hb3 : b3 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb4
  have hb2 : b2 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb3
  have hb1 : b1 ≤ trClean4 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb2
  have hnr : newRandoms (trClean3 cls) (trClean4 cls) = [(randTerm 45 32, 32)] := by
    unfold newRandoms; rw [hni]
    have r45 : ((trClean4 cls).at? 45 : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono hb1 (at?_append_at b0 _ (trClean3_length cls))
    have r46 := entry_proj_none (E2 := DY.Random.ExecEntryT) 46 hb2 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r47 := entry_proj_none (E2 := DY.Random.ExecEntryT) 47 hb3 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r48 := entry_proj_none (E2 := DY.Random.ExecEntryT) 48 hb4 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r49 := entry_proj_none (E2 := DY.Random.ExecEntryT) 49 hb5 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r50 := entry_proj_none (E2 := DY.Random.ExecEntryT) 50 hb6 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r51 := entry_proj_none (E2 := DY.Random.ExecEntryT) 51 hb7 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r52 := entry_proj_none (E2 := DY.Random.ExecEntryT) 52 hb8 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r53 := entry_proj_none (E2 := DY.Random.ExecEntryT) 53 hb9 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have r54 : ((trClean4 cls).at? 54 : Option DY.Random.ExecEntryT) = none := by
      refine entry_proj_none (tr₀ := b9) (e := Symbolic.Proofs.Tests.Shared.Composed.Runs.StT "bob" (stB3Clean cls))
        54 ?_ (by simp +zetaDelta only [append_len, trClean3_length]) rfl
      dsimp only [trClean4]; exact DY.Trace.le_refl _
    change List.filterMap (fun i => ((trClean4 cls).at? i : Option DY.Random.ExecEntryT).map _) _ = _
    simp [r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, RndE]
  have hrpt : receivedPlaintext (trClean3 cls) (trClean4 cls) = some pt2Clean := by
    unfold receivedPlaintext; rw [hni]
    have t45 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 45 hb1 (trClean3_length cls).symm rfl
    have t46 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 46 hb2 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have t47 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 47 hb3 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have t48 : ((trClean4 cls).at? 48 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0Clean))) :=
      at?_mono hb4 (at?_append_at b3 _ (by simp +zetaDelta only [append_len, trClean3_length]))
    have t49 : ((trClean4 cls).at? 49 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.HonestDH ((stB0'Clean cls).sessionInfo "bob") dhsB0Clean 0)) :=
      at?_mono hb5 (at?_append_at b4 _ (by simp +zetaDelta only [append_len, trClean3_length]))
    have t50 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 50 hb6 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have t51 : ((trClean4 cls).at? 51 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.SkippedKeyStored ((stB0'Clean cls).sessionInfo "bob") (dhPk dhsA)
          0 (kdfCk (cB0Clean cls).chainKey).2 2 54)) :=
      at?_mono hb7 (at?_append_at b6 _ (by simp +zetaDelta only [append_len, trClean3_length]))
    have t52 : ((trClean4 cls).at? 52 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.Received "bob" "alice" (dhPk dhsA) 1 pt2Clean)) :=
      at?_mono hb8 (at?_append_at b7 _ (by simp +zetaDelta only [append_len, trClean3_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t45, t46, t47, t48, t49, t50, t51, t52, EvT]
  have hev : eventIdx isBobDone (trClean3 cls) (trClean4 cls) = some 47 := by
    unfold eventIdx; rw [hni]
    have p45 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 45 hb1 (trClean3_length cls).symm rfl
    have p46 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 46 hb2 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have p47 : ((trClean4 cls).at? 47 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
        some (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
          (kemPk pqskB) none o1.ek o1.ct keys1)) :=
      at?_mono hb3 (at?_append_at b2 _ (by simp +zetaDelta only [append_len, trClean3_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, p45, p46, p47, EvP, isBobDone]
  have hexp : exposures (trClean3 cls) (trClean4 cls) = [] := by
    unfold exposures; rw [hni]
    have hp45 := pqExp_non 45 hb1 (trClean3_length cls).symm rfl
    have hp46 := pqExp_non 46 hb2 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp47 : pqExposureAt (trClean4 cls) 47 = none := by
      unfold pqExposureAt
      have p47 : ((trClean4 cls).at? 47 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
            (kemPk pqskB) none o1.ek o1.ct keys1)) :=
        at?_mono hb3 (at?_append_at b2 _ (by simp +zetaDelta only [append_len, trClean3_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, p47, EvP]
    have hp48 := pqExp_non 48 hb4 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp49 := pqExp_non 49 hb5 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp50 := pqExp_non 50 hb6 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp51 := pqExp_non 51 hb7 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp52 := pqExp_non 52 hb8 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp53 := pqExp_non 53 hb9 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have hp54 : pqExposureAt (trClean4 cls) 54 = none := by
      refine pqExp_non (tr₀ := b9) (e := Symbolic.Proofs.Tests.Shared.Composed.Runs.StT "bob" (stB3Clean cls))
        54 ?_ (by simp +zetaDelta only [append_len, trClean3_length]) rfl
      dsimp only [trClean4]; exact DY.Trace.le_refl _
    have ht45 := trExp_non 45 hb1 (trClean3_length cls).symm rfl
    have ht46 := trExp_non 46 hb2 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have ht47 := trExp_non 47 hb3 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have ht48 : trExposureAt (trClean4 cls) 48 = none := by
      unfold trExposureAt
      have t48 : ((trClean4 cls).at? 48 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0Clean))) :=
        at?_mono hb4 (at?_append_at b3 _ (by simp +zetaDelta only [append_len, trClean3_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t48, EvT]
    have ht49 : trExposureAt (trClean4 cls) 49 = none := by
      unfold trExposureAt
      have t49 : ((trClean4 cls).at? 49 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.HonestDH ((stB0'Clean cls).sessionInfo "bob") dhsB0Clean 0)) :=
        at?_mono hb5 (at?_append_at b4 _ (by simp +zetaDelta only [append_len, trClean3_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t49, EvT]
    have ht50 := trExp_non 50 hb6 (by simp +zetaDelta only [append_len, trClean3_length]) rfl
    have ht51 : trExposureAt (trClean4 cls) 51 = none := by
      unfold trExposureAt
      have t51 : ((trClean4 cls).at? 51 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.SkippedKeyStored ((stB0'Clean cls).sessionInfo "bob") (dhPk dhsA)
            0 (kdfCk (cB0Clean cls).chainKey).2 2 54)) :=
        at?_mono hb7 (at?_append_at b6 _ (by simp +zetaDelta only [append_len, trClean3_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t51, EvT]
    have ht52 : trExposureAt (trClean4 cls) 52 = none := by
      unfold trExposureAt
      have t52 : ((trClean4 cls).at? 52 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.Received "bob" "alice" (dhPk dhsA) 1 pt2Clean)) :=
        at?_mono hb8 (at?_append_at b7 _ (by simp +zetaDelta only [append_len, trClean3_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t52, EvT]
    have ht53 : trExposureAt (trClean4 cls) 53 = none := by
      unfold trExposureAt
      have t53 : ((trClean4 cls).at? 53 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.MessageKey ((stB0'Clean cls).sessionInfo "bob") .receiver
            (seedB0Clean cls) (key2Clean cls) 1 2 54)) :=
        at?_mono hb9 (at?_append_at b8 _ (by simp +zetaDelta only [append_len, trClean3_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t53, EvT]
    have ht54 : trExposureAt (trClean4 cls) 54 = none := by
      refine trExp_non (tr₀ := b9) (e := Symbolic.Proofs.Tests.Shared.Composed.Runs.StT "bob" (stB3Clean cls))
        54 ?_ (by simp +zetaDelta only [append_len, trClean3_length]) rfl
      dsimp only [trClean4]; exact DY.Trace.le_refl _
    change List.filterMap (pqExposureAt (trClean4 cls)) _ ++
      List.filterMap (trExposureAt (trClean4 cls)) _ = []
    simp [hp45, hp46, hp47, hp48, hp49, hp50, hp51, hp52, hp53, hp54,
      ht45, ht46, ht47, ht48, ht49, ht50, ht51, ht52, ht53, ht54]
  unfold stepView bobVis
  simp only [hok3, ↓reduceIte, hn3, hexp, List.append_nil, hnr, hrpt, hev]
  dsimp only [bobOpkPk, kh1, Option.bind, Option.toList, List.append_nil, mhClean3,
    received, List.filterMap]
  simp [hek, hct, hmsg]

theorem stepView_ratchetDecTr {tr1 : ExecTrace} {me : Participant} {stH msgH pqH : Nat}
    {st' : TRState} {c : RecvChain} {pk seed pq pt key mSent : Bytes} {stOut : TRState}
    (hok : (Step.messageDecrypt me stH msgH pqH 1).ok tr1 = true)
    (hnext : (Step.messageDecrypt me stH msgH pqH 1).next tr1 =
      ratchetDecTr tr1 me stH st' c pk seed pq pt key stOut)
    (hmsg : tr1.getMessageSentAt msgH = some mSent) :
    stepView (.messageDecrypt me stH msgH pqH 1) tr1 false =
      ⟨.recv, [mSent], .whisper, none⟩ ::
      [rngEntry (randTerm tr1.length 32), ⟨.accept, [pt], .single, none⟩] := by
  let tr2 := ratchetDecTr tr1 me stH st' c pk seed pq pt key stOut
  have hni : newIndices tr1 tr2 =
      [tr1.length, tr1.length + 1, tr1.length + 2, tr1.length + 3,
       tr1.length + 4, tr1.length + 5, tr1.length + 6] := by
    unfold newIndices; rw [ratchetDecTr_length, Nat.add_sub_cancel_left]
    simp [List.range', Nat.add_assoc]
  let d0 := tr1
  let d1 := d0.append (RndE 32)
  let d2 := d1.append (NetE key)
  let d3 := d2.append (EvT (.DHRatchet me st'.peer pk (dhPk st'.dhs)))
  let d4 := d3.append (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2)))
  let d5 := d4.append (EvT (.Received me st'.peer pk 0 pt))
  let d6 := d5.append (EvT (.MessageKey (st'.sessionInfo me) .receiver
    seed pq 0 c.rIdx stH))
  have hd6 : d6 ≤ tr2 := by dsimp only [tr2, ratchetDecTr]; exact DY.Trace.append_le _ _
  have hd5 : d5 ≤ tr2 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd6
  have hd4 : d4 ≤ tr2 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd5
  have hd3 : d3 ≤ tr2 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd4
  have hd2 : d2 ≤ tr2 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd3
  have hd1 : d1 ≤ tr2 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd2
  have hnr : newRandoms tr1 tr2 = [(randTerm tr1.length 32, 32)] := by
    unfold newRandoms; rw [hni]
    have r0 : (tr2.at? tr1.length : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono hd1 (at?_append_at d0 _ rfl)
    have r1 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr1.length + 1) hd2 (by simp +zetaDelta only [append_len]) rfl
    have r2 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr1.length + 2) hd3 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have r3 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr1.length + 3) hd4 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have r4 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr1.length + 4) hd5 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have r5 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr1.length + 5) hd6 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have r6 : (tr2.at? (tr1.length + 6) : Option DY.Random.ExecEntryT) = none := by
      refine entry_proj_none (tr₀ := d6) (e := Symbolic.Proofs.Tests.Shared.Composed.Runs.StT me stOut)
        (tr1.length + 6) ?_ (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
      dsimp only [tr2, ratchetDecTr]; exact DY.Trace.le_refl _
    change List.filterMap (fun i => (tr2.at? i : Option DY.Random.ExecEntryT).map _) _ = _
    simp [r0, r1, r2, r3, r4, r5, r6, RndE]
  have hrpt : receivedPlaintext tr1 tr2 = some pt := by
    unfold receivedPlaintext; rw [hni]
    have t0 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) tr1.length hd1 rfl rfl
    have t1' := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) (tr1.length + 1) hd2 (by simp +zetaDelta only [append_len]) rfl
    have t2' : (tr2.at? (tr1.length + 2) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.DHRatchet me st'.peer pk (dhPk st'.dhs))) :=
      at?_mono hd3 (at?_append_at d2 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
    have t3' : (tr2.at? (tr1.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2))) :=
      at?_mono hd4 (at?_append_at d3 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
    have t4' : (tr2.at? (tr1.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.Received me st'.peer pk 0 pt)) :=
      at?_mono hd5 (at?_append_at d4 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t0, t1', t2', t3', t4', EvT]
  have hexp : exposures tr1 tr2 = [] := by
    unfold exposures; rw [hni]
    have hp0 := pqExp_non tr1.length hd1 rfl rfl
    have hp1 := pqExp_non (tr1.length + 1) hd2 (by simp +zetaDelta only [append_len]) rfl
    have hp2 := pqExp_non (tr1.length + 2) hd3 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have hp3 := pqExp_non (tr1.length + 3) hd4 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have hp4 := pqExp_non (tr1.length + 4) hd5 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have hp5 := pqExp_non (tr1.length + 5) hd6 (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
    have hp6 : pqExposureAt tr2 (tr1.length + 6) = none := by
      refine pqExp_non (tr₀ := d6) (e := Symbolic.Proofs.Tests.Shared.Composed.Runs.StT me stOut)
        (tr1.length + 6) ?_ (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
      dsimp only [tr2, ratchetDecTr]; exact DY.Trace.le_refl _
    have ht0 := trExp_non tr1.length hd1 rfl rfl
    have ht1 := trExp_non (tr1.length + 1) hd2 (by simp +zetaDelta only [append_len]) rfl
    have ht2 : trExposureAt tr2 (tr1.length + 2) = none := by
      unfold trExposureAt
      have t2' : (tr2.at? (tr1.length + 2) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.DHRatchet me st'.peer pk (dhPk st'.dhs))) :=
        at?_mono hd3 (at?_append_at d2 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t2', EvT]
    have ht3 : trExposureAt tr2 (tr1.length + 3) = none := by
      unfold trExposureAt
      have t3' : (tr2.at? (tr1.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2))) :=
        at?_mono hd4 (at?_append_at d3 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t3', EvT]
    have ht4 : trExposureAt tr2 (tr1.length + 4) = none := by
      unfold trExposureAt
      have t4' : (tr2.at? (tr1.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.Received me st'.peer pk 0 pt)) :=
        at?_mono hd5 (at?_append_at d4 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t4', EvT]
    have ht5 : trExposureAt tr2 (tr1.length + 5) = none := by
      unfold trExposureAt
      have t5' : (tr2.at? (tr1.length + 5) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.MessageKey (st'.sessionInfo me) .receiver
            seed pq 0 c.rIdx stH)) :=
        at?_mono hd6 (at?_append_at d5 _ (by simp +zetaDelta only [append_len, Nat.add_assoc]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t5', EvT]
    have ht6 : trExposureAt tr2 (tr1.length + 6) = none := by
      refine trExp_non (tr₀ := d6) (e := Symbolic.Proofs.Tests.Shared.Composed.Runs.StT me stOut)
        (tr1.length + 6) ?_ (by simp +zetaDelta only [append_len, Nat.add_assoc]) rfl
      dsimp only [tr2, ratchetDecTr]; exact DY.Trace.le_refl _
    change List.filterMap (pqExposureAt tr2) _ ++ List.filterMap (trExposureAt tr2) _ = []
    simp [hp0, hp1, hp2, hp3, hp4, hp5, hp6, ht0, ht1, ht2, ht3, ht4, ht5, ht6]
  unfold stepView
  rw [hok]
  simp only [↓reduceIte, hnext]
  change decVis tr1 tr2 stH msgH false ++ exposures tr1 tr2 = _
  unfold decVis
  simp [hmsg, hnr, hrpt, hexp]

/-- Clean-schedule trace, state, and `stepView` data for whisper half-round `h` (`h < 10`). -/
structure CleanHalfRoundWitness (r : ProtocolSetup) (cls : Nat → Nat) (h : Nat) where
  tsRecv : Nat
  stSend : TRState
  stRecv : TRState
  len4 : (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))).length = 55 + 14 * h
  inv : HalfRoundInv (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h)))
    (hrSender h) (hrReceiver h) (hrStHSend h) (hrStHRecv h)
    (hrTsSend h) tsRecv (hrIkSend h) (hrIkRecv h) stSend stRecv
  ppk_none : pendingPreKey (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) (hrStHSend h) = none
  ok_send : (Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2)).ok
    (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) = true
  next_send : (Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2)).next
    (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) =
    runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))
  len5 : (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))).length = 55 + 14 * h + 7
  ok_recv : (Step.messageDecrypt (hrReceiver h) (hrStHRecv h) (55 + 14 * h + 6)
    (55 + 14 * h + 2) 1).ok (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) = true
  next_recv : (Step.messageDecrypt (hrReceiver h) (hrStHRecv h) (55 + 14 * h + 6)
    (55 + 14 * h + 2) 1).next (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) =
    runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1)))
  term_eq : cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h) =
    encMsg stSend (rnd (55 + 14 * h + 1) (cls (2 + h)))
      (DY.Spqr.spqrSend stSend.spqr (rnd (55 + 14 * h + 1) (cls (2 + h)))).2.1
      (rnd (55 + 14 * h) 32)
  msg_sent : (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))).getMessageSentAt
    (55 + 14 * h + 6) = some (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h))
  view_send : stepView
    (.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2))
    (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) false =
    ⟨.pt, [randTerm (55 + 14 * h) 32], .single, none⟩ ::
    ((if cls (2 + h) != 0 then [rngEntry (randTerm (55 + 14 * h + 1) (cls (2 + h)))] else []) ++
     [⟨.send, [cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)], .whisper, none⟩])
  view_recv : stepView
    (.messageDecrypt (hrReceiver h) (hrStHRecv h) (55 + 14 * h + 6) (55 + 14 * h + 2) 1)
    (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) false =
    ⟨.recv, [cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)], .whisper, none⟩ ::
    [rngEntry (randTerm (55 + 14 * h + 7) 32),
     ⟨.accept, [rnd (55 + 14 * h) 32], .single, none⟩]

private theorem cleanHalfRound_inv {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls) :
    ∀ h ≤ 10, ∃ (tsRecv : Nat) (stSend stRecv : TRState),
      (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))).length = 55 + 14 * h ∧
      HalfRoundInv (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h)))
        (hrSender h) (hrReceiver h) (hrStHSend h) (hrStHRecv h)
        (hrTsSend h) tsRecv (hrIkSend h) (hrIkRecv h) stSend stRecv ∧
      ∃ j < hrStHSend h, ∃ seed pq n rIdx pIdx,
        (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))).at? j =
          some (EvT (.MessageKey (stSend.sessionInfo (hrSender h)) .receiver
            seed pq n rIdx pIdx))
  | 0, _ => by
    have htake4 : ssClean cls cleanSpqrIdxs 4 =
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)] := rfl
    have hrun4 : runTrace r (ssClean cls cleanSpqrIdxs 4) = trClean4 cls := by
      unfold runTrace
      rw [setupTrace_eq_t4 hfit, htake4]
      dsimp only [runSteps]
      rw [(s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1, (s3_next_ok cls).1]
    refine ⟨24, stB3Clean cls, stA2Clean cls, ?_, ?_, 53, by decide,
      seedB0Clean cls, key2Clean cls, 1, 2, 54, ?_⟩
    · rw [hrun4, trClean4_length]
    · rw [hrun4]; exact inv_at_4 cls
    · rw [hrun4]
      dsimp only [trClean4]
      have hsinfo : (stB3Clean cls).sessionInfo (hrSender 0) = (stB0'Clean cls).sessionInfo "bob" := rfl
      rw [hsinfo]
      exact at?_mono (DY.Trace.append_le _ _)
        (at?_append_at _ _ (by simp only [append_len, trClean3_length]))
  | h + 1, hh1 => by
    have hh : h < 10 := by omega
    obtain ⟨tsRecv, stSend, stRecv, hlen4, hinv, _⟩ :=
      cleanHalfRound_inv hfit hv h (by omega)
    have htsNew : (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))).length + 7 ∈
        ratchetKeyTimestamps := by
      rw [hlen4]; exact hr_next_ts_mem hh
    obtain ⟨tr1, tr2, stSendNext, stRecvOut,
      _, _, _, hnext1, _, _, _, hnext2, _, _, _, hlen1, hlen2,
      _, htr2_eq, _, hstR_eq, hinvNext⟩ :=
      halfRound_step (cl := cls (2 + h)) hinv (hv (2 + h) (by omega)) htsNew
    rw [hlen4] at hnext1 hnext2 hlen1 hlen2 htr2_eq hstR_eq hinvNext
    have hss5 : ssClean cls cleanSpqrIdxs (5 + 2 * h) =
        ssClean cls cleanSpqrIdxs (4 + 2 * h) ++
          [Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2)] := by
      rw [show 5 + 2 * h = (4 + 2 * h) + 1 by omega]
      exact ssClean_succ (ccs_get_send cls hh)
    have hrun5 : runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h)) = tr1 := by
      unfold runTrace at hnext1 ⊢
      rw [hss5, runSteps_append]
      dsimp only [runSteps]
      exact hnext1
    have hss6 : ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1)) =
        ssClean cls cleanSpqrIdxs (5 + 2 * h) ++
          [Step.messageDecrypt (hrReceiver h) (hrStHRecv h)
            (55 + 14 * h + 6) (55 + 14 * h + 2) 1] := by
      rw [show 4 + 2 * (h + 1) = (5 + 2 * h) + 1 by omega]
      exact ssClean_succ (ccs_get_recv cls hh)
    have hrun6 : runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1))) = tr2 := by
      unfold runTrace
      rw [hss6, runSteps_append]
      change Step.next _ (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) = tr2
      rw [hrun5]
      exact hnext2
    obtain ⟨hSwapS, hSwapR, _, _, _, hSwapIkS, hSwapIkR⟩ :=
      hr_swap_eqs hh
    have hSwapStS : 55 + 14 * h + 13 = hrStHSend (h + 1) := by unfold hrStHSend; omega
    have hSwapStR : 55 + 14 * h + 5 = hrStHRecv (h + 1) := by
      unfold hrStHRecv; simp only [Nat.succ_ne_zero, ↓reduceIte]; omega
    have hSwapTs : 55 + 14 * h + 7 = hrTsSend (h + 1) := by
      unfold hrTsSend; simp only [Nat.succ_ne_zero, ↓reduceIte]; omega
    rw [← hrun6, hSwapS, hSwapR, hSwapStS, hSwapStR, hSwapTs, hSwapIkS, hSwapIkR] at hinvNext
    refine ⟨hrTsSend h, stRecvOut, stSendNext, ?_, hinvNext,
      55 + 14 * h + 12, ?_, ?_⟩
    · rw [hrun6, hlen2]; omega
    · rw [← hSwapStS]; omega
    · let coins := rnd (55 + 14 * h + 1) (cls (2 + h))
      let pqKey := (DY.Spqr.spqrSend stSend.spqr coins).2.1
      let pqMsg := (DY.Spqr.spqrSend stSend.spqr coins).2.2
      let rs := ratchetState stRecv (dhPk stSend.dhs) (rnd (55 + 14 * h + 7) 32)
      have hsinfo : stRecvOut.sessionInfo (hrSender (h + 1)) =
          rs.1.sessionInfo (hrReceiver h) := by
        rw [← hSwapS, hstR_eq]; rfl
      refine ⟨(kdfCk rs.2.chainKey).2, pqKey, 0, rs.2.rIdx,
        hrStHRecv h, ?_⟩
      rw [hrun6, hsinfo]
      have htr2_clean : tr2 = ratchetDecTr tr1 (hrReceiver h) (hrStHRecv h) rs.1 rs.2
          (dhPk stSend.dhs) (kdfCk rs.2.chainKey).2 pqKey (rnd (55 + 14 * h) 32)
          (recvKey stRecv.spqr pqMsg) stRecvOut := htr2_eq
      rw [htr2_clean]
      dsimp only [ratchetDecTr]
      exact at?_mono (DY.Trace.append_le _ _)
        (at?_append_at _ _ (by simp [append_len, hlen1]))

theorem cleanHalfRound_at {r : ProtocolSetup} {cls : Nat → Nat} {h : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hv : ValidCoinLens cls)
    (hh : h < 10) :
    Nonempty (CleanHalfRoundWitness r cls h) := by
  obtain ⟨tsRecv, stSend, stRecv, hlen4, hinv, j, hj, seed, pq, n, rIdx, pIdx, hat_mk⟩ :=
    cleanHalfRound_inv hfit hv h (by omega)
  have hppk : pendingPreKey (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) (hrStHSend h) = none :=
    pendingPreKey_eq_none_of_receiver_mk hinv.at_send hj hat_mk
  have htsNew : (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))).length + 7 ∈
      ratchetKeyTimestamps := by
    rw [hlen4]; exact hr_next_ts_mem hh
  obtain ⟨tr1, tr2, stSendNext, stRecvOut,
    _, _, hok1, hnext1, _, _, hok2, hnext2, hmsg1, _, _, hlen1, _,
    htr1_eq, htr2_eq, _, _, _⟩ :=
    halfRound_step (cl := cls (2 + h)) hinv (hv (2 + h) (by omega)) htsNew
  rw [hlen4] at hok1 hnext1 hok2 hnext2 hmsg1 hlen1 htr1_eq htr2_eq
  have hss5 : ssClean cls cleanSpqrIdxs (5 + 2 * h) =
      ssClean cls cleanSpqrIdxs (4 + 2 * h) ++
        [Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2)] := by
    rw [show 5 + 2 * h = (4 + 2 * h) + 1 by omega]
    exact ssClean_succ (ccs_get_send cls hh)
  have hrun5 : runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h)) = tr1 := by
    unfold runTrace at hnext1 ⊢
    rw [hss5, runSteps_append]
    dsimp only [runSteps]
    exact hnext1
  have hss6 : ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1)) =
      ssClean cls cleanSpqrIdxs (5 + 2 * h) ++
        [Step.messageDecrypt (hrReceiver h) (hrStHRecv h)
          (55 + 14 * h + 6) (55 + 14 * h + 2) 1] := by
    rw [show 4 + 2 * (h + 1) = (5 + 2 * h) + 1 by omega]
    exact ssClean_succ (ccs_get_recv cls hh)
  have hrun6 : runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1))) = tr2 := by
    unfold runTrace
    rw [hss6, runSteps_append]
    change Step.next _ (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) = tr2
    rw [hrun5]
    exact hnext2
  have hmidx : cleanMsgIdx (5 + 2 * h) = 55 + 14 * h + 6 := by
    unfold cleanMsgIdx
    simp only [show 5 + 2 * h ≠ 3 by omega, show 5 + 2 * h ≠ 24 by omega, ↓reduceIte]
    omega
  have hterm : cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h) =
      encMsg stSend (rnd (55 + 14 * h + 1) (cls (2 + h)))
        (DY.Spqr.spqrSend stSend.spqr (rnd (55 + 14 * h + 1) (cls (2 + h)))).2.1
        (rnd (55 + 14 * h) 32) := by
    unfold cleanRecvTerm
    rw [hrun5, hmidx, hmsg1]
    rfl
  have hmsg_sent : (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))).getMessageSentAt
      (55 + 14 * h + 6) = some (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)) := by
    rw [hrun5, hmsg1, hterm]
  have hview_send : stepView
      (.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2))
      (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) false =
      ⟨.pt, [randTerm (55 + 14 * h) 32], .single, none⟩ ::
      ((if cls (2 + h) != 0 then [rngEntry (randTerm (55 + 14 * h + 1) (cls (2 + h)))] else []) ++
       [⟨.send, [cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)], .whisper, none⟩]) := by
    have htr1_gen : (Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h))
        (55 + 14 * h + 2)).next (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) =
        encTrGen (runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))) (hrSender h) (hrStHSend h)
          (cls (2 + h)) stSend
          (DY.Spqr.spqrSend stSend.spqr
            (rnd ((runTrace r (ssClean cls cleanSpqrIdxs (4 + 2 * h))).length + 1)
              (cls (2 + h)))).2.1 := by
      rw [hnext1, htr1_eq, hlen4]
    have hv0 := encTrGen_stepView_ok (wrapped := false) hok1 htr1_gen
    rw [hlen4, hppk, ← hterm] at hv0
    exact hv0
  have hview_recv : stepView
      (.messageDecrypt (hrReceiver h) (hrStHRecv h) (55 + 14 * h + 6) (55 + 14 * h + 2) 1)
      (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h))) false =
      ⟨.recv, [cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)], .whisper, none⟩ ::
      [rngEntry (randTerm (55 + 14 * h + 7) 32),
       ⟨.accept, [rnd (55 + 14 * h) 32], .single, none⟩] := by
    rw [hrun5] at hmsg_sent ⊢
    have hv0 := stepView_ratchetDecTr hok2 (hnext2.trans htr2_eq) hmsg_sent
    rw [hlen1] at hv0
    exact hv0
  exact ⟨{
    tsRecv := tsRecv
    stSend := stSend
    stRecv := stRecv
    len4 := hlen4
    inv := hinv
    ppk_none := hppk
    ok_send := hok1
    next_send := hnext1.trans hrun5.symm
    len5 := hrun5.symm ▸ hlen1
    ok_recv := hrun5.symm ▸ hok2
    next_recv := by rw [hrun5, hnext2, hrun6]
    term_eq := hterm
    msg_sent := hmsg_sent
    view_send := hview_send
    view_recv := hview_recv
  }⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB
