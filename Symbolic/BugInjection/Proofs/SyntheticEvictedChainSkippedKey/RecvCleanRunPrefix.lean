/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvB
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvD
import DY.Trace.Basic

/-!
# Clean-Run Prefix Extraction

From any prefix explanation `Explains evictedI0 r S g ss vis (trace0.take k)` at `k ∈ recvCallIndices`,
`extract_clean_prefix` extracts a valid SPQR coin-length schedule `cls` and packages
`CleanPrefixData`: setup compatibility of `gClean r cls`, agreement of prekey and whisper `.send`
wire outputs with the canonical clean terms, absence of Bob state at `k = 3`, and presence of
Alice's ephemeral base key in `bobDoneBaseKeys (runTrace r ss)` for `3 < k`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet (TRState RecvChain kdfCk setRecvChain)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry Step
   GhostAndSemMatchSetup GhostWF Explains runTrace setupTrace runSteps
   gamma clamp pubBytes preKeyWire ecKey secretBytes bobDoneBaseKeys runWrapped)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd ratchetState encMsg encSt)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB t4 o1 stA0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens recvCallIndices whisperOrReplayIndices cleanCallSteps ssClean
   cleanMsgIdx cleanRecvTerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev WhisperInputSpec ev7_whisper ev11_whisper ev15_whisper ev19_whisper ev23_whisper
   ev7_coins_idx ev11_coins_idx ev15_coins_idx ev19_coins_idx ev23_coins_idx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (step_le_next runSteps_le runSteps_append bobDoneBaseKeys_mono)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (lt_25_of_mem_recvCallIndices whisper_wire_eq sendCallOf
   send_runWrapped_prekey send_runWrapped_whisper nextBundleIds_non_init
   ev5_whisper ev9_whisper ev13_whisper ev17_whisper ev21_whisper
   ev5_coins_idx ev9_coins_idx ev13_coins_idx ev17_coins_idx ev21_coins_idx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs ratchetKeyTimestamps setupTrace_eq_t4
   pt1Clean coins1Clean key1Clean stA1Clean m1Clean
   pt2Clean coins2Clean key2Clean stA2Clean m2Clean
   stB3Clean trClean4 trClean4_length s0_next_ok s1_next_ok s2_next_ok s3_next_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (gClean gClean_sigma_31 gClean_sigma_32 gClean_sigma_38 gClean_sigma_39
   gClean_sigma_whisper_pt gClean_sigma_whisper_coins gClean_sigma_whisper_dhs
   gClean_addr_m1 gClean_addr_m2 gClean_addr_whisper
   ghostAndSemMatchSetup_gClean gamma_dhPk_ratchetTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
  (PeeledCall PeeledValid trace0_take_eq_evsRange peel_evsRange
   stepCoinLen clsOfCalls validCoinLens_clsOfCalls PkiUnchanged)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
  (NoPartyState NoNewPartyState noPartyState_of_noNew noNewPartyState_runSteps_network
   ActivePartySt noNewPartyState_preserves_active)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvB
  (alice_call0_agree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend
  (party_send_agree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC
  (bob_call3_agree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvD
  (party_whisper_recv_agree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound
  (HalfRoundInv halfRound_step inv_at_4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
  (ssClean_succ)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

theorem peeledValid_trace_le {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ {j : Nat} {initIds : Option DY.Libsignal.Composed.Refinement.BundlePreKeyIds}
      {tr : ExecTrace} {cs : List PeeledCall} {ss : List Step},
      PeeledValid r S g visAll j initIds tr cs ss →
      tr ≤ runSteps ss tr
  | _, _, tr, _, tail, .nil _ => runSteps_le tail tr
  | _, _, tr, c :: _, _, .cons _ _ _ _ _ hpv => by
    rw [runSteps_append]
    dsimp only [runSteps]
    exact DY.Trace.le_trans _ _ _
      (DY.Trace.le_trans _ _ _ (runSteps_le c.pre tr) (step_le_next c.s _))
      (peeledValid_trace_le hpv)

def hrSender (h : Nat) : Participant := if h % 2 = 0 then "bob" else "alice"
def hrReceiver (h : Nat) : Participant := if h % 2 = 0 then "alice" else "bob"
def hrSendInit (h : Nat) : Bool := decide (h % 2 = 1)
def hrRecvInit (h : Nat) : Bool := decide (h % 2 = 0)
def hrStHSend (h : Nat) : Nat := 54 + 14 * h
def hrStHRecv (h : Nat) : Nat := if h = 0 then 43 else 46 + 14 * h
def hrTsSend (h : Nat) : Nat := if h = 0 then 45 else 48 + 14 * h

def hrIkSend (h : Nat) : Bytes :=
  if h % 2 = 0 then DY.Libsignal.PQXDH.serializedIk (dhPk ikB)
  else DY.Libsignal.PQXDH.serializedIk (dhPk ikA)

def hrIkRecv (h : Nat) : Bytes :=
  if h % 2 = 0 then DY.Libsignal.PQXDH.serializedIk (dhPk ikA)
  else DY.Libsignal.PQXDH.serializedIk (dhPk ikB)

def hrSendSk (h : Nat) : Fin 16 := ⟨(5 + h) % 16, Nat.mod_lt _ (by decide)⟩
def hrRecvSk (h : Nat) : Fin 16 := ⟨(4 + h) % 16, Nat.mod_lt _ (by decide)⟩

def hrSendIdxs : Nat → List (Fin 16)
  | 0 => [⟨4, by decide⟩]
  | 1 => [⟨2, by decide⟩, ⟨5, by decide⟩]
  | 2 => [⟨4, by decide⟩, ⟨6, by decide⟩]
  | 3 => [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩]
  | 4 => [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩]
  | 5 => [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩]
  | 6 => [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩]
  | 7 => [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩]
  | 8 => [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩]
  | 9 => [⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩]
  | _ => [⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩]

def hrRecvIdxs : Nat → List (Fin 16)
  | 0 => [⟨2, by decide⟩]
  | h + 1 => hrSendIdxs h

theorem evictedPubOfIdx_len (idx : Fin 16) : (evictedPubOfIdx idx).length = 32 := by
  revert idx; decide

theorem hr_ne_party {h : Nat} (hh : h < 10) : hrReceiver h ≠ hrSender h := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; decide
  | n + 10 => intro h; omega

theorem hr_send_party_cmd {h : Nat} (hh : h < 10) :
    (ev (4 + 2 * h)).party = hrSender h ∧ ∃ peer, (ev (4 + 2 * h)).cmd = .send peer := by
  unfold ev; revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; exact ⟨rfl, _, rfl⟩
  | n + 10 => intro h; omega

theorem hr_recv_party_cmd {h : Nat} (hh : h < 10) :
    (ev (5 + 2 * h)).party = hrReceiver h ∧ ∃ peer, (ev (5 + 2 * h)).cmd = .recv peer := by
  unfold ev; revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; exact ⟨rfl, _, rfl⟩
  | n + 10 => intro h; omega

theorem hr_whisper_spec {h : Nat} (hh : h < 10) :
    WhisperInputSpec (ev (5 + 2 * h)) (hrSendSk h) := by
  revert hh; match h with
  | 0 => intro _; exact ev5_whisper
  | 1 => intro _; exact ev7_whisper
  | 2 => intro _; exact ev9_whisper
  | 3 => intro _; exact ev11_whisper
  | 4 => intro _; exact ev13_whisper
  | 5 => intro _; exact ev15_whisper
  | 6 => intro _; exact ev17_whisper
  | 7 => intro _; exact ev19_whisper
  | 8 => intro _; exact ev21_whisper
  | 9 => intro _; exact ev23_whisper
  | n + 10 => intro h; omega

theorem hr_recv_coins_idx {h : Nat} (hh : h < 10) :
    evictedSecretIdx (clamp (((ev (5 + 2 * h)).coins).take 32)) = some (hrSendSk (h + 1)) := by
  revert hh; match h with
  | 0 => intro _; exact ev5_coins_idx
  | 1 => intro _; exact ev7_coins_idx
  | 2 => intro _; exact ev9_coins_idx
  | 3 => intro _; exact ev11_coins_idx
  | 4 => intro _; exact ev13_coins_idx
  | 5 => intro _; exact ev15_coins_idx
  | 6 => intro _; exact ev17_coins_idx
  | 7 => intro _; exact ev19_coins_idx
  | 8 => intro _; exact ev21_coins_idx
  | 9 => intro _; exact ev23_coins_idx
  | n + 10 => intro h; omega

private theorem hr_pk_not_mem {h : Nat} (hh : h < 10) : hrSendSk h ∉ hrRecvIdxs h := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; decide
  | n + 10 => intro h; omega

private theorem hr_idxs_step {h : Nat} (hh : h < 10) :
    ((hrRecvIdxs h ++ [hrSendSk h]).drop (((hrRecvIdxs h).length + 1) - 5)) =
      hrSendIdxs (h + 1) := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; rfl
  | n + 10 => intro h; omega

theorem hr_swap_eqs {h : Nat} (hh : h < 10) :
    hrReceiver h = hrSender (h + 1) ∧
    hrSender h = hrReceiver (h + 1) ∧
    hrRecvInit h = hrSendInit (h + 1) ∧
    hrSendInit h = hrRecvInit (h + 1) ∧
    hrSendSk h = hrRecvSk (h + 1) ∧
    hrIkRecv h = hrIkSend (h + 1) ∧
    hrIkSend h = hrIkRecv (h + 1) := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
    intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | n + 10 => intro h; omega

theorem hr_next_ts_mem {h : Nat} (hh : h < 10) :
    55 + 14 * h + 7 ∈ ratchetKeyTimestamps := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; decide
  | n + 10 => intro h; omega

theorem hr_mem_whisper {h : Nat} (hh : h < 10) :
    5 + 2 * h ∈ whisperOrReplayIndices := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; decide
  | n + 10 => intro h; omega

theorem ccs_get_send (cls : Nat → Nat) {h : Nat} (hh : h < 10) :
    (cleanCallSteps cls cleanSpqrIdxs)[4 + 2 * h]? =
      some (Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2)) := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; rfl
  | n + 10 => intro h; omega

theorem ccs_get_recv (cls : Nat → Nat) {h : Nat} (hh : h < 10) :
    (cleanCallSteps cls cleanSpqrIdxs)[5 + 2 * h]? =
      some (Step.messageDecrypt (hrReceiver h) (hrStHRecv h)
        (55 + 14 * h + 6) (55 + 14 * h + 2) 1) := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; rfl
  | n + 10 => intro h; omega

theorem sendCallOf_whisper {h : Nat} (hh : h < 10) :
    sendCallOf (2 + h) = 4 + 2 * h := by
  revert hh; match h with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => intro _; rfl
  | n + 10 => intro h; omega

private theorem whisper_rounds_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {visAll : List VisEntry} {csOrig : List PeeledCall}
    {cls : Nat → Nat} {ek0 ct0 : Bytes}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hgwf : GhostWF g visAll)
    (hvCls : ValidCoinLens cls)
    (hcl_at : ∀ sIdx c, csOrig[sendCallOf sIdx]? = some c → cls sIdx = stepCoinLen c.s)
    (hek0 : gamma evictedI0 S g ek0 = gamma evictedI0 S (gClean r cls) o1.ek)
    (hct0 : gamma evictedI0 S g ct0 = gamma evictedI0 S (gClean r cls) o1.ct) :
    ∀ (fuel h : Nat) {tr trCleanH : ExecTrace} {csRem : List PeeledCall} {ssRem : List Step}
      {tsRecv : Nat} {stSend stRecv : TRState},
      10 - h ≤ fuel →
      (∀ i, csRem[i]? = csOrig[(4 + 2 * h) + i]?) →
      PeeledValid r S g visAll (4 + 2 * h) (some (none, 7#32, 9#32)) tr csRem ssRem →
      4 + 2 * h + csRem.length ≤ 25 →
      PkiUnchanged tr →
      ActivePartySt (hrSender h) (hrSendInit h) S g (gClean r cls)
        (hrSendIdxs h) (hrSendSk h) stSend tr →
      ActivePartySt (hrReceiver h) (hrRecvInit h) S g (gClean r cls)
        (hrRecvIdxs h) (hrRecvSk h) stRecv tr →
      trCleanH = runSteps (ssClean cls cleanSpqrIdxs (4 + 2 * h)) t4 →
      trCleanH.length = 55 + 14 * h →
      HalfRoundInv trCleanH (hrSender h) (hrReceiver h) (hrStHSend h) (hrStHRecv h)
        (hrTsSend h) tsRecv (hrIkSend h) (hrIkRecv h) stSend stRecv →
      ∀ (h' : Nat), h' < 10 → h ≤ h' → 4 + 2 * h' < 4 + 2 * h + csRem.length →
        (ev (4 + 2 * h')).exit =
          some (0, wireWhisperTag ::
            gamma evictedI0 S (gClean r cls) (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h'))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h _ _ _ _ _ _ _ hfuel _ _ _ _ _ _ _ _ _ h' hh' hle _
    omega
  | succ fuel ih =>
    intro h tr trCleanH csRem ssRem tsRecv stSend stRecv hfuel hsh hpv hbound hpki
      hActSend hActRecv htrClean hlenClean hinv h' hh' hle hlt_k
    have hh : h < 10 := by omega
    cases csRem with
    | nil => simp at hlt_k; omega
    | cons cSend csAfterSend =>
      cases hpv with
      | cons hnetS hpreS hlokS hrmS hsubS hpvAfterSend =>
        have htsNew : trCleanH.length + 7 ∈ ratchetKeyTimestamps := by
          rw [hlenClean]; exact hr_next_ts_mem hh
        obtain ⟨tr1, tr2, stSendNext, stRecvOut,
          _, _, _, hnext1, _, _, _, hnext2, hmsg1, _, _, hlen1, hlen2,
          _, _, hstS_eq, hstR_eq, hinvNext⟩ :=
          halfRound_step (cl := cls (2 + h)) hinv (hvCls (2 + h) (by omega)) htsNew
        rw [hlenClean] at hnext1 hnext2 hmsg1 hlen1 hlen2 hstS_eq hstR_eq hinvNext
        have hss5 : ssClean cls cleanSpqrIdxs (5 + 2 * h) =
            ssClean cls cleanSpqrIdxs (4 + 2 * h) ++
              [Step.messageEncrypt (hrSender h) (hrStHSend h) (cls (2 + h)) (55 + 14 * h + 2)] := by
          rw [show 5 + 2 * h = (4 + 2 * h) + 1 by omega]
          exact ssClean_succ (ccs_get_send cls hh)
        have hrun5 : runTrace r (ssClean cls cleanSpqrIdxs (5 + 2 * h)) = tr1 := by
          unfold runTrace
          rw [setupTrace_eq_t4 hfit, hss5, runSteps_append, ← htrClean]
          dsimp only [runSteps]
          exact hnext1
        have hmidx : cleanMsgIdx (5 + 2 * h) = 55 + 14 * h + 6 := by
          unfold cleanMsgIdx
          simp only [show 5 + 2 * h ≠ 3 by omega, show 5 + 2 * h ≠ 24 by omega, ↓reduceIte]
          omega
        have hterm5 : cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h) =
            encMsg stSend (rnd (55 + 14 * h + 1) (cls (2 + h)))
              (DY.Spqr.spqrSend stSend.spqr (rnd (55 + 14 * h + 1) (cls (2 + h)))).2.1
              (rnd (55 + 14 * h) 32) := by
          unfold cleanRecvTerm
          rw [hrun5, hmidx, hmsg1]
          rfl
        have hsc : sendCallOf (2 + h) = 4 + 2 * h := sendCallOf_whisper hh
        have hgetS : csOrig[sendCallOf (2 + h)]? = some cSend := by
          rw [hsc, ← Nat.add_zero (4 + 2 * h), ← hsh 0]; rfl
        have hwrap_false : runWrapped (ev (sendCallOf (2 + h))) = false :=
          send_runWrapped_whisper (by omega) (by omega)
        have hts_ne24 : hrTsSend h ≠ 24 := by unfold hrTsSend; split <;> omega
        have hpt_cl : (gClean r cls).σ (55 + 14 * h) 32 = (ev (sendCallOf (2 + h))).input := by
          rw [hsc]; exact gClean_sigma_whisper_pt r cls hh
        have hcoins_cl : ∀ n, (gClean r cls).σ (55 + 14 * h + 1) n =
            (ev (sendCallOf (2 + h))).coins.take n := by
          intro n; rw [hsc]; exact gClean_sigma_whisper_coins r cls hh
        have hparty_sc : (ev (sendCallOf (2 + h))).party = hrSender h ∧
            ∃ peer, (ev (sendCallOf (2 + h))).cmd = .send peer := by
          rw [hsc]; exact hr_send_party_cmd hh
        have hrmS' : DY.Libsignal.Composed.Refinement.RunMatches evictedI0 r S g
            (runSteps cSend.pre tr) cSend.s (ev (sendCallOf (2 + h))) cSend.v
            (some (none, 7#32, 9#32)) := by
          rw [hsc]; exact hrmS
        obtain ⟨hpki1, _, hActSend1, hnoNewRecv1, hexitS⟩ :=
          party_send_agree cls (otherParty := hrReceiver h)
            (sIdx := 2 + h) (tsPt := 55 + 14 * h) (tsCoins := 55 + 14 * h + 1)
            (hr_ne_party hh) hgwf hpki
            (fun hw => by rw [hwrap_false] at hw; cases hw)
            hek0 hct0 hActSend hparty_sc (hcl_at (2 + h) cSend hgetS)
            hpt_cl hcoins_cl
            (Or.inr ⟨hwrap_false, gClean_addr_whisper r cls hinv.dhs_eq.1 hts_ne24⟩)
            hnetS hpreS hlokS hrmS' hsubS
        simp only [hwrap_false, Bool.false_eq_true, ↓reduceIte] at hexitS
        rw [hsc, ← hterm5] at hexitS
        by_cases heq_h : h' = h
        · subst heq_h; exact hexitS
        · have hlt_h : h + 1 ≤ h' := by omega
          cases csAfterSend with
          | nil => simp at hlt_k; omega
          | cons cRecv csNext =>
            rw [nextBundleIds_non_init (by omega) (by omega),
                show (4 + 2 * h) + 1 = 5 + 2 * h by omega] at hpvAfterSend
            cases hpvAfterSend with
            | cons hnetR hpreR hlokR hrmR hsubR hpvNext =>
              rw [nextBundleIds_non_init (by omega) (by omega),
                  show (5 + 2 * h) + 1 = 4 + 2 * (h + 1) by omega] at hpvNext
              have hActRecv1 := noNewPartyState_preserves_active hnoNewRecv1 hActRecv
              have hw_eq := (whisper_wire_eq (hr_mem_whisper hh) (by omega)).1
              rw [show 5 + 2 * h - 1 = 4 + 2 * h by omega] at hw_eq
              have hin5 : (ev (5 + 2 * h)).input =
                  wireWhisperTag :: gamma evictedI0 S (gClean r cls)
                    (encMsg stSend (rnd (55 + 14 * h + 1) (cls (2 + h)))
                      (DY.Spqr.spqrSend stSend.spqr (rnd (55 + 14 * h + 1) (cls (2 + h)))).2.1
                      (rnd (55 + 14 * h) 32)) := by
                have hpair := Option.some.inj (hw_eq.symm.trans hexitS)
                exact (congrArg Prod.snd hpair).trans (by rw [hterm5])
              have hrk_len : (gamma evictedI0 S (gClean r cls) (dhPk stSend.dhs)).length = 32 := by
                rw [hinv.dhs_eq.1, gamma_dhPk_ratchetTs hfit hinv.ts_mem]
                exact evictedPubOfIdx_len _
              obtain ⟨hpki2, hActRecv2, hnoNewSend2⟩ :=
                party_whisper_recv_agree cls (otherParty := hrSender h)
                  (tsDhsNew := 55 + 14 * h + 7)
                  (Ne.symm (hr_ne_party hh)) hgwf hpki1 hActRecv1
                  (hr_recv_party_cmd hh) (hr_whisper_spec hh) (hr_recv_coins_idx hh)
                  (hr_pk_not_mem hh) hin5 hrk_len hinv.spqr_recv
                  (gClean_sigma_whisper_dhs r cls hh)
                  hnetR hpreR hrmR hsubR
              have hActSend2 := noNewPartyState_preserves_active hnoNewSend2 hActSend1
              rw [← hstS_eq] at hActSend2
              rw [hr_idxs_step hh, ← hstR_eq] at hActRecv2
              obtain ⟨hsw1, hsw2, hsw3, hsw4, hsw5, hsw6, hsw7⟩ := hr_swap_eqs hh
              rw [hsw1, hsw3] at hActRecv2
              have hRecvIdxs_next : hrSendIdxs h = hrRecvIdxs (h + 1) := rfl
              rw [hsw2, hsw4, hRecvIdxs_next, hsw5] at hActSend2
              have hss_next : ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1)) =
                  ssClean cls cleanSpqrIdxs (5 + 2 * h) ++
                    [Step.messageDecrypt (hrReceiver h) (hrStHRecv h)
                      (55 + 14 * h + 6) (55 + 14 * h + 2) 1] := by
                rw [show 4 + 2 * (h + 1) = (5 + 2 * h) + 1 by omega]
                exact ssClean_succ (ccs_get_recv cls hh)
              have htrCleanNext : tr2 = runSteps (ssClean cls cleanSpqrIdxs (4 + 2 * (h + 1))) t4 := by
                have hrun5_t4 : runSteps (ssClean cls cleanSpqrIdxs (5 + 2 * h)) t4 = tr1 := by
                  rw [hss5, runSteps_append, ← htrClean]; exact hnext1
                rw [hss_next, runSteps_append, hrun5_t4]; exact hnext2.symm
              have hlenCleanNext : tr2.length = 55 + 14 * (h + 1) := by omega
              have hstH1 : 55 + 14 * h + 13 = hrStHSend (h + 1) := by unfold hrStHSend; omega
              have hstH2 : 55 + 14 * h + 5 = hrStHRecv (h + 1) := by
                unfold hrStHRecv; simp only [Nat.succ_ne_zero, ↓reduceIte]; omega
              have htsH : 55 + 14 * h + 7 = hrTsSend (h + 1) := by
                unfold hrTsSend; simp only [Nat.succ_ne_zero, ↓reduceIte]; omega
              rw [hsw1, hsw2, hstH1, hstH2, htsH, hsw6, hsw7] at hinvNext
              have hshNext : ∀ i, csNext[i]? = csOrig[(4 + 2 * (h + 1)) + i]? := by
                intro i
                have h2 := hsh (i + 2)
                simp only [List.getElem?_cons_succ] at h2
                rw [h2, show (4 + 2 * h) + (i + 2) = (4 + 2 * (h + 1)) + i by omega]
              exact ih (h + 1) (by omega)
                hshNext hpvNext (by simp at hbound ⊢; omega) hpki2
                hActRecv2 hActSend2 htrCleanNext hlenCleanNext hinvNext
                h' hh' hlt_h (by simp at hlt_k ⊢; omega)

private theorem ge_3_of_mem_recvCallIndices {k : Nat} (hk : k ∈ recvCallIndices) : 3 ≤ k := by
  revert hk k; decide

/-- Canonical wire-output and Bob-session invariants extracted from an arbitrary prefix explanation
of `trace0.take k`. -/
structure CleanPrefixData (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ss : List Step) (k : Nat) (cls : Nat → Nat) : Prop where
  validCls : ValidCoinLens cls
  compatClean : GhostAndSemMatchSetup evictedI0 r S (gClean r cls)
  ev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
    (ecKey (pubBytes evictedI0 (secretBytes r 0)))
    (gamma evictedI0 S (gClean r cls) o1.ek)
    (gamma evictedI0 S (gClean r cls) o1.ct)
    (gamma evictedI0 S (gClean r cls) (m1Clean cls)))
  ev2_out : (ev 2).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
    (ecKey (pubBytes evictedI0 (secretBytes r 0)))
    (gamma evictedI0 S (gClean r cls) o1.ek)
    (gamma evictedI0 S (gClean r cls) o1.ct)
    (gamma evictedI0 S (gClean r cls) (m2Clean cls)))
  whisper_out : ∀ h < 10, 4 + 2 * h < k →
    (ev (4 + 2 * h)).exit =
      some (0, wireWhisperTag ::
        gamma evictedI0 S (gClean r cls) (cleanRecvTerm r cls cleanSpqrIdxs (5 + 2 * h)))
  noBob3 : k = 3 → NoPartyState "bob" (runTrace r ss)
  bob_done : 3 < k →
    ∃ ek ∈ bobDoneBaseKeys (runTrace r ss),
      ecKey (gamma evictedI0 S g ek) = ecKey (evictedPubOfIdx ⟨3, by decide⟩)

theorem extract_clean_prefix {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {k : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hk : k ∈ recvCallIndices)
    (hex : Explains evictedI0 r S g ss vis (trace0.take k)) :
    ∃ cls : Nat → Nat, CleanPrefixData r S g ss k cls := by
  have hk3 : 3 ≤ k := ge_3_of_mem_recvCallIndices hk
  have hk25 : k < 25 := lt_25_of_mem_recvCallIndices hk
  obtain ⟨hCompat, hgwf, hmwf, hm⟩ := hex
  rw [trace0_take_eq_evsRange (Nat.le_of_lt hk25)] at hm
  unfold DY.Libsignal.Composed.Refinement.MatchesEvents at hm
  rw [← Nat.zero_add k] at hm
  obtain ⟨csOrig, hcs_len, hpv0⟩ :=
    peel_evsRange k 0 (by omega) hmwf.2.2.1 hm (fun _ hw => hw)
  let cls := clsOfCalls csOrig
  have hvCls : ValidCoinLens cls := validCoinLens_clsOfCalls hpv0
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  have hcl_at : ∀ sIdx c, csOrig[sendCallOf sIdx]? = some c → cls sIdx = stepCoinLen c.s := by
    intro sIdx c hget; unfold cls clsOfCalls; rw [hget]
  have hsh0 : ∀ i, csOrig[i]? = csOrig[0 + i]? := by simp
  rcases hcs_eq : csOrig with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, cs3⟩⟩⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len; omega
  · rw [hcs_eq] at hcs_len; simp at hcs_len; omega
  · rw [hcs_eq] at hcs_len; simp at hcs_len; omega
  · rw [hcs_eq] at hpv0
    have hget0 : csOrig[0]? = some c0 := by rw [hcs_eq]; rfl
    have hget1 : csOrig[sendCallOf 0]? = some c1 := by rw [hcs_eq]; rfl
    have hget2 : csOrig[sendCallOf 1]? = some c2 := by rw [hcs_eq]; rfl
    cases hpv0 with
    | cons hnet0 hpre0 hlok0 hrm0 hsub0 hpv1 =>
      obtain ⟨ek0, ct0, hek0, hct0, hpki1, honly1, hActA1, hnoB1, hids0⟩ :=
        alice_call0_agree cls hfit hCompat hgwf hnet0 hrm0 hsub0
      rw [hids0] at hpv1
      cases hpv1 with
      | cons hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
        obtain ⟨hpki2, honly2, hActA2, hnoNewB2, hexit1⟩ :=
          party_send_agree cls (otherParty := "bob") (sIdx := 0) (tsPt := 31) (tsCoins := 32)
            (by decide) hgwf hpki1 (fun _ => honly1) hek0 hct0 hActA1
            (by unfold ev; exact ⟨rfl, _, rfl⟩) (hcl_at 0 c1 hget1)
            (gClean_sigma_31 r cls 32) (gClean_sigma_32 r cls)
            (Or.inl ⟨send_runWrapped_prekey.1, gClean_addr_m1 r cls⟩)
            hnet1 hpre1 hlok1 hrm1 hsub1
        have hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
            (ecKey (pubBytes evictedI0 (secretBytes r 0)))
            (gamma evictedI0 S (gClean r cls) o1.ek)
            (gamma evictedI0 S (gClean r cls) o1.ct)
            (gamma evictedI0 S (gClean r cls) (m1Clean cls))) := by
          have hw1 : runWrapped (ev (sendCallOf 0)) = true := send_runWrapped_prekey.1
          simp only [hw1, ↓reduceIte] at hexit1
          exact hexit1
        have hnoB2 : NoPartyState "bob" _ := noPartyState_of_noNew hnoNewB2 hnoB1
        rw [nextBundleIds_non_init (by decide) (by decide)] at hpv2
        cases hpv2 with
        | cons hnet2 hpre2 hlok2 hrm2 hsub2 hpv3 =>
          obtain ⟨hpki3, _, hActA3, hnoNewB3, hexit2⟩ :=
            party_send_agree cls (otherParty := "bob") (sIdx := 1) (tsPt := 38) (tsCoins := 39)
              (by decide) hgwf hpki2 (fun _ => honly2 send_runWrapped_prekey.1) hek0 hct0 hActA2
              (by unfold ev; exact ⟨rfl, _, rfl⟩) (hcl_at 1 c2 hget2)
              (gClean_sigma_38 r cls 32) (gClean_sigma_39 r cls)
              (Or.inl ⟨send_runWrapped_prekey.2, gClean_addr_m2 r cls⟩)
              hnet2 hpre2 hlok2 hrm2 hsub2
          have hev2_out : (ev 2).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
              (ecKey (pubBytes evictedI0 (secretBytes r 0)))
              (gamma evictedI0 S (gClean r cls) o1.ek)
              (gamma evictedI0 S (gClean r cls) o1.ct)
              (gamma evictedI0 S (gClean r cls) (m2Clean cls))) := by
            have hw2 : runWrapped (ev (sendCallOf 1)) = true := send_runWrapped_prekey.2
            simp only [hw2, ↓reduceIte] at hexit2
            exact hexit2
          have hnoB3 : NoPartyState "bob" _ := noPartyState_of_noNew hnoNewB3 hnoB2
          rw [nextBundleIds_non_init (by decide) (by decide)] at hpv3
          cases cs3 with
          | nil =>
            cases hpv3 with
            | nil hnet_tail =>
              have hk_eq3 : k = 3 := by rw [hcs_eq] at hcs_len; simpa using hcs_len.symm
              exact ⟨cls,
                { validCls := hvCls
                  compatClean := hCompatClean
                  ev1_out := hev1_out
                  ev2_out := hev2_out
                  whisper_out := fun h _ hlt => by omega
                  noBob3 := fun _ => by
                    unfold runTrace
                    simp only [runSteps_append, runSteps]
                    exact noPartyState_of_noNew (noNewPartyState_runSteps_network _ _ hnet_tail) hnoB3
                  bob_done := fun hlt => by omega }⟩
          | cons c3 cs4 =>
            cases hpv3 with
            | @cons _ _ _ _ _ rest4 hnet3 hpre3 hlok3 hrm3 hsub3 hpv4 =>
              obtain ⟨hpki4, hActB4, hnoNewA4, ek3, hek3_mem, hek3_ec⟩ :=
                bob_call3_agree cls hfit hCompat hgwf hpki3 hnoB3 hev2_out
                  hnet3 hrm3 hsub3
              have hActA4 := noNewPartyState_preserves_active hnoNewA4 hActA3
              rw [nextBundleIds_non_init (by decide) (by decide)] at hpv4
              have hbob_done : 3 < k →
                  ∃ ek ∈ bobDoneBaseKeys (runTrace r (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: (c3.pre ++ c3.s :: rest4))))),
                    ecKey (gamma evictedI0 S g ek) = ecKey (evictedPubOfIdx ⟨3, by decide⟩) :=
                fun _ => ⟨ek3, bobDoneBaseKeys_mono
                  (by unfold runTrace; simp only [runSteps_append, runSteps]; exact peeledValid_trace_le hpv4)
                  hek3_mem, hek3_ec⟩
              have hsh4 : ∀ i, cs4[i]? = csOrig[(4 + 2 * 0) + i]? := by
                intro i
                rw [hcs_eq]
                simp only [Nat.mul_zero, Nat.add_zero, Nat.add_comm 4 i, List.getElem?_cons_succ]
              have htrClean0 : trClean4 cls = runSteps (ssClean cls cleanSpqrIdxs (4 + 2 * 0)) t4 := by
                have htake4 : ssClean cls cleanSpqrIdxs 4 =
                    [Step.aliceStart "alice" "bob" 4 6 Symbolic.Proofs.Tests.Shared.Composed.HonestSession.bh1,
                     Step.messageEncrypt "alice" 30 (cls 0) 33,
                     Step.messageEncrypt "alice" 36 (cls 1) 40,
                     Step.bobStart "bob" "alice" Symbolic.Proofs.Tests.Shared.Composed.HonestSession.kh1
                       1 Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase.mhClean3
                       40 (cleanSpqrIdxs 3)] := rfl
                simp only [Nat.mul_zero, Nat.add_zero, htake4, runSteps,
                  (s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1, (s3_next_ok cls).1]
              have hk_len4 : 4 + 2 * 0 + cs4.length = k := by
                rw [hcs_eq] at hcs_len
                simp only [List.length_cons] at hcs_len
                omega
              have hwh_out := whisper_rounds_agree hfit hgwf hvCls hcl_at hek0 hct0 10 0 (by omega)
                hsh4 hpv4 (by omega) hpki4 hActB4 hActA4
                htrClean0 (trClean4_length cls) (inv_at_4 cls)
              exact ⟨cls,
                { validCls := hvCls
                  compatClean := hCompatClean
                  ev1_out := hev1_out
                  ev2_out := hev2_out
                  whisper_out := fun h hh hlt =>
                    hwh_out h hh (Nat.zero_le h) (by omega)
                  noBob3 := fun heq => by omega
                  bob_done := hbob_done }⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunPrefix
