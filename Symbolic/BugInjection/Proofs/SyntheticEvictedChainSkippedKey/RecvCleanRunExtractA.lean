/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRep
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Representation Membership and Randomness Draw Matching

Proves representation membership (`preKeyRepresentationsOn` and `recvRepresentationsOn`) for the
clean schedule's prekey, whisper, and replayed messages (`cleanPreKeyRep_mem`,
`cleanRecvTerm_mem_whisper`, `cleanRecvTerm_mem_24`), together with `DrawsMatch` lemmas for
handshake, encryption, and decryption coin draws under `gClean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtractA

open scoped DY.Libsignal.Composed
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step PreKeyFields OpkNamed
   gamma slice ecKey pubBytes secretBytes preKeyWire parsePreKeyWire
   setupTrace runTrace runSteps rngEntry kyberCoinEntries randTerm
   BytesMatchEntry DrawsMatch recvRepresentationsOn preKeyRepresentationsOn
   getMessageSentAt_attackerKnows)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (NetE rnd aliceTr aliceTrOpt)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (t4_length t5 t5_length bh1 o1)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (runSteps_le runSteps_append)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (cleanCallSteps cleanCallSteps_length ssClean cleanPreKeyRep cleanRecvTerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev ev3_preKey_fields tryFrom_of_parsePreKeyWire)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (ev1_to_ev24 ev2_to_ev3 whisper_wire_eq ev0_coins_facts ev3_full_fields)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs append_len le_append_of_le at?_mono at?_append_at setupTrace_eq_t4
   encTrGen encTrGen_le pt1Clean coins1Clean m1Clean pt2Clean coins2Clean m2Clean
   trClean2 trClean2_length trClean3 s0_next_ok s1_next_ok s2_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (gClean gClean_sigma_22 gClean_sigma_23 gClean_sigma_24 gamma_dhPk_ratchetTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRep
  (encMsg_mem_recvRepresentationsOn encMsg_faithfulInner)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
  (cleanPreKeyRep_eq cleanRecvTerm_24_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC
  (ev3_input_len_lt ev24_input_len_lt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
  (evictedPubOfIdx_len hr_mem_whisper CleanPrefixData)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunVisB
  (cleanHalfRound_at)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

theorem gamma_randTerm_pos {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts n : Nat} (hn : n ≠ 0) :
    gamma evictedI0 S g (randTerm ts n) = g.σ ts n := by
  unfold randTerm
  rw [gamma_rand]
  simp only [hn, ↓reduceIte]

private theorem ikA_pub_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    pubBytes evictedI0 (secretBytes r 0) = evictedPubOfIdx ⟨0, by decide⟩ := by
  rw [hfit.1.1.2.2.2.2.2.2.1]
  decide +kernel

private theorem dhsA_rk_len (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (cls : Nat → Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    (gamma evictedI0 S (gClean r cls) (dhPk (rnd 24 32))).length = 32 := by
  rw [gamma_dhPk_ratchetTs (S := S) (cls := cls) hfit (by decide)]
  exact evictedPubOfIdx_len _

private theorem trClean3_sent_eqs {r : ProtocolSetup} (cls : Nat → Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    (runTrace r (ssClean cls cleanSpqrIdxs 3)).getMessageSentAt 25 = some o1.ek ∧
    (runTrace r (ssClean cls cleanSpqrIdxs 3)).getMessageSentAt 26 = some o1.ct ∧
    (runTrace r (ssClean cls cleanSpqrIdxs 3)).getMessageSentAt 44 = some (m2Clean cls) := by
  have htake3 : ssClean cls cleanSpqrIdxs 3 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33,
       Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
  have hrun3 : runTrace r (ssClean cls cleanSpqrIdxs 3) = trClean3 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, htake3]; dsimp only [runSteps]
    rw [(s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1]
  rw [hrun3]
  have h53 : t5 ≤ trClean3 cls :=
    DY.Trace.le_trans _ _ _ (encTrGen_le ..) (encTrGen_le ..)
  have hat25 : (trClean3 cls).at? 25 = some (NetE o1.ek) := by
    refine at?_mono h53 ?_
    dsimp only [t5, aliceTr, aliceTrOpt, o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
    rw [t4_length]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (DY.Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hat26 : (trClean3 cls).at? 26 = some (NetE o1.ct) := by
    refine at?_mono h53 ?_
    dsimp only [t5, aliceTr, aliceTrOpt, o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
    rw [t4_length]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (DY.Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hat44 : (trClean3 cls).at? 44 = some (NetE (m2Clean cls)) := by
    dsimp only [trClean3, encTrGen, m2Clean]
    have hm : rnd (trClean2 cls).length 32 = pt2Clean := by rw [trClean2_length]; rfl
    have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
      rw [trClean2_length]; rfl
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, trClean2_length])
  refine ⟨?_, ?_, ?_⟩
  · rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat25]
  · rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat26]
  · rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat44]

theorem cleanPreKeyRep_mem {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls) :
    cleanPreKeyRep r cls cleanSpqrIdxs ∈
      preKeyRepresentationsOn evictedI0 r S (gClean r cls)
        (runTrace r (ssClean cls cleanSpqrIdxs 3)) (ev 3).input ∧
    OpkNamed r (ev 3).input false := by
  rw [cleanPreKeyRep_eq hfit]
  obtain ⟨hs25, hs26, hs44⟩ := trClean3_sent_eqs cls hfit
  obtain ⟨_, p₃, hp₃, _, _, _⟩ := ev3_preKey_fields
  have hfull := ev3_full_fields hp₃
  have hev3_in : (ev 3).input = preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes evictedI0 (secretBytes r 0)))
      (gamma evictedI0 S (gClean r cls) o1.ek)
      (gamma evictedI0 S (gClean r cls) o1.ct)
      (gamma evictedI0 S (gClean r cls) (m2Clean cls)) := by
    have hcomb := ev2_to_ev3.symm.trans d.ev2_out
    injection hcomb with hpair
    exact (Prod.mk.inj hpair).2
  obtain ⟨_, hp₃_ct, hp₃_bk, hp₃_msg⟩ :=
    parsePreKeyWire_preKeyWire_inv hev3_in ev3_input_len_lt hp₃
  have hopk : OpkNamed r (ev 3).input false := ⟨p₃, hp₃, hfull.2.2.1⟩
  have hbk_take : p₃.baseKey.take 33 = ecKey (gamma evictedI0 S (gClean r cls) o1.ek) := by
    have hlen33 : p₃.baseKey.length = 33 := by rw [hfull.2.2.2.2.2.1]; decide
    rw [List.take_of_length_le (Nat.le_of_eq hlen33), hp₃_bk]
  have hik_take : p₃.identityKey.take 33 =
      ecKey (pubBytes evictedI0 (secretBytes r 0)) := by
    rw [hfull.2.2.2.2.2.2.1, ikA_pub_eq hfit]
    have hlen33 : (ecKey (evictedPubOfIdx ⟨0, by decide⟩)).length = 33 := by decide
    exact List.take_of_length_le (Nat.le_of_eq hlen33)
  have hspkId : p₃.signedPreKeyId = r.spkId := by
    rw [hfull.2.1, hfit.1.1.2.2.2.2.1]; rfl
  have hkpkId : p₃.kyberPreKeyId = some r.kpkId := by
    rw [hfull.2.2.2.1, hfit.1.1.2.2.2.2.2.1]; rfl
  have hfaith : DY.Libsignal.Composed.Refinement.FaithfulInner
      evictedI0 S (gClean r cls) (m2Clean cls) p₃ :=
    encMsg_faithfulInner hp₃_msg.symm (dhsA_rk_len r S cls hfit)
      (tryFrom_of_parsePreKeyWire hp₃)
  have hver : p₃.version = 4 := by
    have hp' := hp₃
    rw [hev3_in] at hp'
    simp only [parsePreKeyWire, preKeyWire, ↓reduceIte,
      DY.Libsignal.Composed.Refinement.parsePreKey] at hp'
    split at hp'
    · cases hp'
    · split at hp'
      · cases hp'
      · split at hp'
        · split at hp'
          · split at hp'
            · injection hp' with hp'; subst hp'; dsimp only; decide
            · cases hp'
          · cases hp'
        · cases hp'
  refine ⟨⟨getMessageSentAt_attackerKnows hs25,
    getMessageSentAt_attackerKnows hs26,
    getMessageSentAt_attackerKnows hs44,
    ⟨p₃, hp₃, hbk_take, hp₃_ct, hp₃_msg, hver, hspkId, hkpkId, hik_take, false, hopk⟩,
    p₃, hp₃, hfaith⟩, hopk⟩

theorem cleanRecvTerm_mem_whisper {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k h : Nat} {cls : Nat → Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hh : h < 10) (hlt : 4 + 2 * h < k) :
    cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h) ∈
      recvRepresentationsOn evictedI0 S (gClean r cls)
        (runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h)))
        ((ev (5 + 2 * h)).input.drop 1) := by
  have w := Classical.choice (cleanHalfRound_at hfit d.validCls hh)
  have hw_eq := whisper_wire_eq (hr_mem_whisper hh) (by omega)
  rw [show 5 + 2 * h - 1 = 4 + 2 * h by omega] at hw_eq
  have hcomb := hw_eq.1.symm.trans (d.whisper_out h hh hlt)
  injection hcomb with hpair
  have hin : (ev (5 + 2 * h)).input =
      wireWhisperTag :: gamma evictedI0 S (gClean r cls)
        (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)) :=
    (Prod.mk.inj hpair).2
  have hdrop : (ev (5 + 2 * h)).input.drop 1 =
      gamma evictedI0 S (gClean r cls) (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)) := by
    rw [hin]; rfl
  have hak := getMessageSentAt_attackerKnows w.msg_sent
  rw [w.term_eq] at hak hdrop ⊢
  have hrk_len : (gamma evictedI0 S (gClean r cls) (dhPk w.stSend.dhs)).length = 32 := by
    rw [w.inv.dhs_eq.1, gamma_dhPk_ratchetTs (S := S) (cls := cls) hfit w.inv.ts_mem]
    exact evictedPubOfIdx_len _
  exact encMsg_mem_recvRepresentationsOn hak hdrop.symm hrk_len

theorem cleanRecvTerm_mem_24 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {k : Nat} {cls : Nat → Nat} {p : PreKeyFields}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (d : CleanPrefixData r S g ss k cls)
    (hp : parsePreKeyWire (ev 24).input = some p) :
    cleanRecvTerm r cls cleanSpqrIdxs 24 ∈
      recvRepresentationsOn evictedI0 S (gClean r cls)
        (runTrace r (ssClean cls cleanSpqrIdxs 24)) p.message := by
  have hsent : (runTrace r (ssClean cls cleanSpqrIdxs 24)).getMessageSentAt 37 =
      some (m1Clean cls) := by
    have htake2 : (cleanCallSteps cls cleanSpqrIdxs).take 2 =
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33] := rfl
    have h2_le_24 : trClean2 cls ≤ runTrace r (ssClean cls cleanSpqrIdxs 24) := by
      unfold runTrace ssClean
      rw [setupTrace_eq_t4 hfit, List.take_of_length_le (by rw [cleanCallSteps_length])]
      have hsplit := (List.take_append_drop 2 (cleanCallSteps cls cleanSpqrIdxs)).symm
      rw [hsplit, runSteps_append, htake2]
      dsimp only [runSteps]
      rw [(s0_next_ok).1, (s1_next_ok cls).1]
      exact runSteps_le _ _
    have hm1 : (trClean2 cls).at? 37 = some (NetE (m1Clean cls)) := by
      dsimp only [trClean2, encTrGen, m1Clean]
      have hm : rnd t5.length 32 = pt1Clean := by rw [t5_length]; rfl
      have hc : rnd (t5.length + 1) (cls 0) = coins1Clean cls := by rw [t5_length]; rfl
      rw [hm, hc]
      exact at?_append_at _ _ (by simp only [append_len, t5_length])
    have hat : (runTrace r (ssClean cls cleanSpqrIdxs 24)).at? 37 = some (NetE (m1Clean cls)) :=
      at?_mono h2_le_24 hm1
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat]
  have hev24_in : (ev 24).input = preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes evictedI0 (secretBytes r 0)))
      (gamma evictedI0 S (gClean r cls) o1.ek)
      (gamma evictedI0 S (gClean r cls) o1.ct)
      (gamma evictedI0 S (gClean r cls) (m1Clean cls)) := by
    have hcomb := ev1_to_ev24.symm.trans d.ev1_out
    injection hcomb with hpair
    exact (Prod.mk.inj hpair).2
  obtain ⟨_, _, _, hp_msg⟩ :=
    parsePreKeyWire_preKeyWire_inv hev24_in ev24_input_len_lt hp
  rw [cleanRecvTerm_24_eq hfit]
  exact encMsg_mem_recvRepresentationsOn (getMessageSentAt_attackerKnows hsent)
    hp_msg.symm (dhsA_rk_len r S cls hfit)

private theorem forall2_append {α β : Type} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h1 : List.Forall₂ R xs₁ ys₁) (h2 : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h1 with
  | nil => exact h2
  | cons hr _ ih => exact .cons hr ih

private theorem kyber_pieces_flatten :
    ∀ n ≤ 32, ∀ (b : HwBytes), b.length = 192 →
      ((List.range n).map fun j => slice b (32 + 4 * j) 4).flatten = slice b 32 (4 * n)
  | 0, _, b, _ => by simp [slice]
  | n + 1, hn, b, hlen => by
    rw [List.range_succ, List.map_append, List.flatten_append,
      kyber_pieces_flatten n (by omega) b hlen]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, slice]
    rw [show 4 * (n + 1) = 4 * n + 4 by omega, List.take_add, List.drop_drop,
      show 32 + 4 * n = 32 + 4 * n from rfl]

private theorem kyber_pieces_forall2 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) :
    ∀ n ≤ 32,
      List.Forall₂
        (fun p v => BytesMatchEntry evictedI0 r S (gClean r cls) .rng p v)
        ((List.range n).map fun j => slice (ev 0).coins (32 + 4 * j) 4)
        ((List.range n).map fun j => ⟨.rng, [randTerm 23 32], .kyberCoin j, none⟩)
  | 0, _ => .nil
  | n + 1, hn => by
    obtain ⟨hlen192, _, _, hent_len, _, hent_at⟩ := ev0_coins_facts
    rw [List.range_succ, List.map_append, List.map_append]
    refine forall2_append (kyber_pieces_forall2 r S cls n (by omega)) ?_
    refine List.Forall₂.cons ?_ .nil
    refine ⟨rfl, ?_, randTerm 23 32, rfl, ?_, ?_⟩
    · simp only [slice, List.length_take, List.length_drop, hlen192]; omega
    · rw [gamma_randTerm_pos (by decide), gClean_sigma_23]; exact hent_len
    · rw [gamma_randTerm_pos (by decide), gClean_sigma_23, hent_at n (by omega)]
      dsimp only [slice]
      cases (ev 0).coins.drop (32 + 4 * n) <;> rfl

theorem drawsMatch_ev0 (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (cls : Nat → Nat) :
    DrawsMatch evictedI0 r S (gClean r cls)
      (rngEntry (randTerm 22 32) ::
        (kyberCoinEntries (randTerm 23 32) ++
          [{ rngEntry (randTerm 24 32) with anchor := some 27 }]))
      (ev 0).coins := by
  have hlen192 := ev0_coins_facts.1
  let kpcs := (List.range 32).map fun j => slice (ev 0).coins (32 + 4 * j) 4
  refine ⟨slice (ev 0).coins 0 32 :: (kpcs ++ [slice (ev 0).coins 160 32]), ?_, ?_, ?_⟩
  · intro p hp
    dsimp only [kpcs] at hp
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | ⟨j, hj, rfl⟩ | rfl
    · intro heq; have := congrArg List.length heq
      simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega
    · intro heq; have := congrArg List.length heq
      simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega
    · intro heq; have := congrArg List.length heq
      simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega
  · simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.append_nil]
    rw [kyber_pieces_flatten 32 (Nat.le_refl 32) (ev 0).coins hlen192]
    have hcat : slice (ev 0).coins 0 32 ++ (slice (ev 0).coins 32 128 ++ slice (ev 0).coins 160 32) =
        (ev 0).coins := by
      simp only [slice, List.drop_zero]
      rw [← List.append_assoc]
      have h1 : (ev 0).coins.take 32 ++ ((ev 0).coins.drop 32).take 128 =
          (ev 0).coins.take 160 := by
        simpa using (List.take_add (i := 32) (j := 128) (l := (ev 0).coins)).symm
      rw [h1]
      have h2 : (ev 0).coins.take 160 ++ ((ev 0).coins.drop 160).take 32 =
          (ev 0).coins.take 192 := by
        simpa using (List.take_add (i := 160) (j := 32) (l := (ev 0).coins)).symm
      rw [h2, List.take_of_length_le (Nat.le_of_eq hlen192)]
    rw [hcat]
  · refine List.Forall₂.cons ?_ (forall2_append (kyber_pieces_forall2 r S cls 32 (Nat.le_refl 32))
      (List.Forall₂.cons ?_ .nil))
    · refine ⟨rfl, ?_⟩
      simp only [rngEntry, List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
        gClean_sigma_22]
    · refine ⟨rfl, ?_⟩
      simp only [rngEntry, List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
        gClean_sigma_24]

theorem drawsMatch_single32 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts : Nat} {coins : HwBytes}
    (hlen : 32 ≤ coins.length)
    (hsig : (gClean r cls).σ ts 32 = coins.take 32) :
    DrawsMatch evictedI0 r S (gClean r cls) [rngEntry (randTerm ts 32)] coins := by
  refine ⟨[coins.take 32], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    intro heq
    have := congrArg List.length heq
    simp only [List.length_take, List.length_nil] at this
    omega
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact List.take_prefix 32 coins
  · simp only [rngEntry, List.map_cons, List.map_nil,
      gamma_randTerm_pos (by decide : 32 ≠ 0), hsig]

theorem drawsMatch_enc (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts cl : Nat} {coins : HwBytes}
    (hcl : cl = 0 ∨ cl = 32 ∨ cl = 64)
    (hlen : 64 ≤ coins.length)
    (hsig : (gClean r cls).σ ts cl = coins.take cl) :
    DrawsMatch evictedI0 r S (gClean r cls)
      (if cl != 0 then [rngEntry (randTerm ts cl)] else []) coins := by
  rcases hcl with rfl | rfl | rfl
  · exact ⟨[], by simp, List.nil_prefix, .nil⟩
  · refine ⟨[coins.take 32], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; intro heq
      have := congrArg List.length heq
      simp only [List.length_take, List.length_nil] at this; omega
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      exact List.take_prefix 32 coins
    · simp only [rngEntry, List.map_cons, List.map_nil,
        gamma_randTerm_pos (by decide : 32 ≠ 0), hsig]
  · refine ⟨[coins.take 64], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; intro heq
      have := congrArg List.length heq
      simp only [List.length_take, List.length_nil] at this; omega
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      exact List.take_prefix 64 coins
    · simp only [rngEntry, List.map_cons, List.map_nil,
        gamma_randTerm_pos (by decide : 64 ≠ 0), hsig]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunExtractA
