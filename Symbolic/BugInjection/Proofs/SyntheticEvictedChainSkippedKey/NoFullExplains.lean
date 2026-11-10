/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTag
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfePrefix
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec

/-!
# Full-Trace Explanation Refutation

Proves `not_explains_full`: `EvictedChainSkippedKeyCli.trace` (25 CLI calls) admits no full model
explanation under `evictedCompFitsPinned`. After Call 3 (`bobStart`) and five ping-pong DH ratchets
(Calls `4..23`), `pk_A0` is absent from Bob's 5-element `recv` list (`maxReceiverChains = 5`). Call
24 then fails in every candidate step: `.bobStart` violates `PathFaithfulAt`,
`.messageDecryptSkipped` fails its `findRecvChain` guard, and `.messageDecrypt` derives a
`compTag4`-tagged MAC from off-table `(15, 4)` DH agreement.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NoFullExplains

open scoped DY.Libsignal.Composed
open DY (Traceful)
open DY.Libsignal.TripleRatchet
  (TRState createChain kdfCk consumeMessageKey receiveSignalMsg
   messageDecrypt messageDecryptSkipped)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma sessionBaseKeys decVis stepView ReadsFaithfully Explains)
open Symbolic.Swarm.COMPOSED.CompTrace (run_bind_fst)
open Symbolic.Swarm.CREF (rpkT_getMessageSentAt_of_at? rpkT_receiveSignalMsg_some)
open Symbolic.Swarm.CREF.TR.RecvDec (getLocalState_snd trDhRatchetState)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTag
  (TT tt_createChain_15_4 tt_kdfCk_snd tt_trMsgKeys_macKey computeMac_take4_of_tt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev_bob_recv tryFrom_of_parsePreKeyWire ev24_preKey_fields)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (bobActiveInv_pin_state preCond_messageDecrypt preCond_messageDecryptSkipped
   step_ok_decrypt step_ok_decryptSkipped)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
  (findRecvChain_none_of_not_mem not_decryptSkipped_of_find_none decrypt_ratchet_inv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfePrefix
  (prefix_to_call24)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

theorem not_explains_full
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    ¬ Explains evictedI0 r S g ss vis
        Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace := by
  intro hex
  obtain ⟨tr₂₄, s₂₄, v₂₄, initIds₂₄, hinv, hpre, hrm⟩ := prefix_to_call24 hfit hex
  obtain ⟨hbob, peer, hcmd⟩ := ev_bob_recv 24 (by decide)
  obtain ⟨hwrap, p₂₄, hp₂₄, hp_bk, hp_rk, hp_cnt, hp_mac⟩ := ev24_preKey_fields
  have htry := tryFrom_of_parsePreKeyWire hp₂₄
  have hnotMem4 : (⟨4, by decide⟩ : Fin 16) ∉
      ([⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩] :
        List (Fin 16)) := by decide
  obtain ⟨_, hparty, hfits, _, hok, _, hvis_eq,
    inp, drs, outs, hv_split, _, _, _, hrf, hpf⟩ := hrm
  rw [hbob] at hparty
  rw [hcmd] at hfits
  cases s₂₄ with
  | bobStart b a kh regA mh pqIdx spqr =>
    have hnknown := hpf p₂₄ hp₂₄
    obtain ⟨ek, hek, hek_eq⟩ := hinv.2.2
    exact hnknown ⟨ek, hek, hek_eq.trans hp_bk.symm⟩
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have hcur := preCond_messageDecryptSkipped hpre
    have hok_copy := hok
    rw [step_ok_decryptSkipped] at hok_copy
    unfold messageDecryptSkipped at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₂₄).1 with _ | st
    · try rw [hst] at hok_copy
      cases hok_copy
    · try rw [hst] at hok_copy
      rw [getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₂₄).1 with _ | msg
      · try rw [hmsg_run] at hok_copy
        cases hok_copy
      · obtain ⟨_, hrecv_map, _⟩ := bobActiveInv_pin_state hinv hst hcur
        obtain ⟨t, hat, hparse, _⟩ := rpkT_receiveSignalMsg_some hmsg_run
        have hinp : inp = ⟨.recv, [t], .preKeyInner (sessionBaseKeys tr₂₄ stateIdx), none⟩ := by
          have hv0 := hv_split.symm.trans hvis_eq
          unfold stepView decVis at hv0
          simp only [hok, ↓reduceIte, hwrap, rpkT_getMessageSentAt_of_at? hat,
            Option.map_some, Option.toList_some, List.cons_append] at hv0
          injection hv0
        rw [hinp] at hrf
        dsimp only [ReadsFaithfully] at hrf
        have ht_rep := hrf p₂₄ hp₂₄
        have hrk4 : gamma evictedI0 S g msg.ratchetKey = evictedPubOfIdx ⟨4, by decide⟩ :=
          ((ht_rep.2.2.2 msg hparse).2.2.2 p₂₄.inner htry).2.1.trans hp_rk
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk4 hnotMem4
        rw [not_decryptSkipped_of_find_none hst hmsg_run hfind] at hok
        cases hok
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have hcur := preCond_messageDecrypt hpre
    have hok_copy := hok
    rw [step_ok_decrypt] at hok_copy
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₂₄).1 with _ | st
    · try rw [hst] at hok_copy
      cases hok_copy
    · try rw [hst] at hok_copy
      rw [getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₂₄).1 with _ | msg
      · try rw [hmsg_run] at hok_copy
        cases hok_copy
      · obtain ⟨_, hrecv_map, hdhs⟩ := bobActiveInv_pin_state hinv hst hcur
        obtain ⟨t₀, hat₀, hparse₀, _⟩ := rpkT_receiveSignalMsg_some hmsg_run
        have hinp : inp = ⟨.recv, [t₀], .preKeyInner (sessionBaseKeys tr₂₄ stateIdx), none⟩ := by
          have hv0 := hv_split.symm.trans hvis_eq
          unfold stepView decVis at hv0
          simp only [hok, ↓reduceIte, hwrap, rpkT_getMessageSentAt_of_at? hat₀,
            Option.map_some, Option.toList_some, List.cons_append] at hv0
          injection hv0
        rw [hinp] at hrf
        dsimp only [ReadsFaithfully] at hrf
        have ht_rep := hrf p₂₄ hp₂₄
        have hmsg_fields := ht_rep.2.2.2 msg hparse₀
        have hinner_fields := hmsg_fields.2.2.2 p₂₄.inner htry
        have hrk4 : gamma evictedI0 S g msg.ratchetKey = evictedPubOfIdx ⟨4, by decide⟩ :=
          hinner_fields.2.1.trans hp_rk
        have hcnt0 : msg.counter.toNat = 0 :=
          hinner_fields.2.2.2.1.trans hp_cnt
        have hmac_untagged : (gamma evictedI0 S g msg.mac).take 4 ≠ compTag4 := by
          rw [hmsg_fields.2.1]; exact hp_mac
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk4 hnotMem4
        obtain ⟨w, hw_msg⟩ := decrypt_ratchet_inv hok hst hmsg_run hfind
        rw [← hw_msg] at hrk4 hcnt0 hmac_untagged
        have hseed_eq : w.seed = (kdfCk (createChain st.rk w.msg.ratchetKey st.dhs).2).2 := by
          have hc := w.hcons
          unfold consumeMessageKey trDhRatchetState at hc
          dsimp only at hc
          split at hc
          · cases hc
          · split at hc
            · cases hc
            · split at hc
              · cases hc
              · rw [hcnt0] at hc
                injection hc with hpair
                exact (congrArg Prod.fst hpair).symm
        have htt_ck := tt_createChain_15_4 S g st.rk w.msg.ratchetKey st.dhs hrk4 hdhs
        have htt_seed : TT S g w.seed := hseed_eq ▸ tt_kdfCk_snd htt_ck
        have htt_mk := tt_trMsgKeys_macKey w.pqSalt htt_seed
        have htag : (gamma evictedI0 S g w.msg.mac).take 4 = compTag4 := by
          rw [w.hmac_eq]; exact computeMac_take4_of_tt _ _ _ htt_mk
        exact hmac_untagged htag
  | _ => cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NoFullExplains
