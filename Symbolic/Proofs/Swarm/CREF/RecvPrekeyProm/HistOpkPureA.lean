/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.QuietTransferPure
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BinPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNonePure
public import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.OooRpkPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Tie.BlockReadPure
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Post-Move Record State, Receiver-Chain Inclusion, and Record Encoding on Session Promotion

Establishes post-move `PureTRRecordStateInv` and `RoleSnapshots` helpers, receiver-chain
`senderRatchetKey` inclusion across `SessionState.tryDecryptWithStateW`, and canonical `recordBytes`
identities (`recordBytes_of_promAcceptOut` and `prom_sm_recordBytes`) for session promotion.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding kdfRk createChain x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Seeds
open CryptoVerification.E2E.Record
open Proofs.libsignal.RngG.R3
open Proofs.libsignal.SR
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure (slots_RecordCanonical_Q)
open Symbolic.Swarm.CREF.TR (normPending)
open Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
open Symbolic.Swarm.CREF.CliPure.RpkCli

abbrev ho_PromStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev ho_PromTREntry := DY.ProtocolEvent.ExecEntryT TREvent

/-! ## Post-move `PureTRRecordStateInv` and `RoleSnapshots` -/

theorem quiet_trRecordStateInv_symm {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {Z : TR.PureTRSlots} {g : Ghost} {ms ms' : List Move} {records : Participant → Option HwBytes}
    (h : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r ms) (runTraceMoves r ms'))
    (hrsi : TR.PureTRRecordStateInv interpretation r S Z g ms' records) :
    TR.PureTRRecordStateInv interpretation r S Z g ms records := by
  intro q b hqb
  obtain ⟨hq_mem, rec, st, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩ := hrsi q b hqb
  refine ⟨hq_mem, rec, st, stateIdx, hb, ?_, ?_, hrel, ?_, hcanon, hks, hnd⟩
  · rwa [← Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_getLocalState h]
  · rwa [← Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_isCurrentSnapshot h]
  · intro c hc k hk
    obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk c hc k hk
    refine ⟨pk, rIdx, srcIdx, skIdx, seed, (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt h _ _).mp hlog, ?_, ?_, hgam, hsrk, hfind⟩
    · unfold TripleRatchet.skippedKeyUsedB at hsu ⊢; rwa [← Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_someEventOnTraceB h]
    · unfold TripleRatchet.receiverKeyUsedB at hru ⊢; rwa [← Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_someEventOnTraceB h]

theorem prom_inv_of_cRecRel_post
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {state : HwBytes}
    (hwf : ProtocolSetupWF r)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₀ ++ pre))) post)
    (hrec' : PureCRecRel interpretation r S g (ms₀ ++ (pre ++ m :: post)) r.bob state) :
    TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre ++ [m])
      (fun q => if q = r.bob then some state else none) := by
  have hinv_post : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g
      (ms₀ ++ (pre ++ m :: post))
      (fun q => if q = r.bob then some state else none) := by
    rcases hrec' with htr | ⟨hab, _⟩
    · exact htr
    · exact False.elim (hwf.1 hab.symm)
  exact quiet_trRecordStateInv_symm (prom_quietPost hpost) hinv_post

theorem prom_role_pair_of_roleSnapshots
    {r : ProtocolSetup} {ms₀ pre : List Move} {m : Move}
    (hwf : ProtocolSetupWF r)
    (hrole₀ : RoleSnapshots r (runTraceMoves r ms₀))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hm : DecryptBy r.bob m) :
    ∀ (st₁ st₂ : TRState) (i j : Nat),
      ((runTraceMoves r (ms₀ ++ pre ++ [m])).at? i : Option ho_PromStEntry) = some ⟨⟨r.bob, st₁⟩⟩ →
      ((runTraceMoves r (ms₀ ++ pre ++ [m])).at? j : Option ho_PromStEntry) = some ⟨⟨r.bob, st₂⟩⟩ →
      st₁.initiator = st₂.initiator := by
  intro st₁ st₂ i j h₁ h₂
  have hrole_pre : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole₀
  have hrole_m : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
    rw [TR.runTrace_snoc]
    exact roleSnapshots_of_bobStartBy_or_decryptBy hwf.1 (Or.inr hm) hrole_pre
  rw [hrole_m r.bob st₁ i h₁, hrole_m r.bob st₂ j h₂]

/-! ## Receiver-chain inclusion and `recordBytes` across `tryDecryptWithStateW` -/

@[local simp] theorem ho_exec_pure_hw {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

@[local simp] theorem ho_exec_get_hw {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] theorem ho_exec_set_hw {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] theorem ho_exec_liftE_hw {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

@[local simp] theorem ho_exec_bind_hw {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

private theorem mem_set_cases_hw {α : Type} {l : List α} {i : Nat} {x y : α}
    (h : y ∈ l.set i x) : y = x ∨ y ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.set, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a h)
    | succ i =>
      simp only [List.set, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with rfl | h'
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem a h')

private theorem mem_of_getElem?_hw {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : x ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      exact List.mem_cons_of_mem a (ih h)

private theorem prom_takeSkippedKey_srk_mem (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  unfold RatchetState.takeSkippedKey at hrc'
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp only [h1, ho_exec_bind_hw, ho_exec_get_hw, ho_exec_pure_hw] at hrc'
    exact ⟨rc', hrc', rfl⟩
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp only [h1, h2, ho_exec_bind_hw, ho_exec_get_hw] at hrc'
      exact ⟨rc', hrc', rfl⟩
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp only [h1, h2, h3, ho_exec_bind_hw, ho_exec_get_hw, ho_exec_pure_hw] at hrc'
        exact ⟨rc', hrc', rfl⟩
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp only [h1, h2, h3, h4, ho_exec_bind_hw, ho_exec_get_hw] at hrc'
          exact ⟨rc', hrc', rfl⟩
        · simp only [h1, h2, h3, h4, ho_exec_bind_hw, ho_exec_get_hw, ho_exec_set_hw, ho_exec_pure_hw] at hrc'
          rcases mem_set_cases_hw hrc' with rfl | hmem
          · exact ⟨c, mem_of_getElem?_hw h2, rfl⟩
          · exact ⟨rc', hmem, rfl⟩

private theorem prom_storeSkippedKey_srk_mem (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  unfold RatchetState.storeSkippedKey at hrc'
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp only [h1, ho_exec_bind_hw, ho_exec_get_hw] at hrc'
    exact ⟨rc', hrc', rfl⟩
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp only [h1, h2, ho_exec_bind_hw, ho_exec_get_hw] at hrc'
      exact ⟨rc', hrc', rfl⟩
    · simp only [h1, h2, ho_exec_bind_hw, ho_exec_get_hw, ho_exec_set_hw] at hrc'
      rcases mem_set_cases_hw hrc' with rfl | hmem
      · exact ⟨c, mem_of_getElem?_hw h2, rfl⟩
      · exact ⟨rc', hmem, rfl⟩

private theorem prom_setReceiverChainKey_srk_mem (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  unfold RatchetState.setReceiverChainKey at hrc'
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp only [h1, ho_exec_bind_hw, ho_exec_get_hw] at hrc'
    exact ⟨rc', hrc', rfl⟩
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp only [h1, h2, ho_exec_bind_hw, ho_exec_get_hw] at hrc'
      exact ⟨rc', hrc', rfl⟩
    · simp only [h1, h2, ho_exec_bind_hw, ho_exec_get_hw, ho_exec_set_hw] at hrc'
      rcases mem_set_cases_hw hrc' with rfl | hmem
      · exact ⟨c, mem_of_getElem?_hw h2, rfl⟩
      · exact ⟨rc', hmem, rfl⟩

private theorem prom_advanceChain_srk_mem (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : Nat) (ck : ChainKey) (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  induction fuel generalizing ck r with
  | zero => exact ⟨rc', hrc', rfl⟩
  | succ fuel ih =>
    unfold RatchetState.advanceChain at hrc'
    split at hrc'
    · rw [ho_exec_bind_hw] at hrc'
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at hrc'
        have h1 : rc' ∈ (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r).2.receiverChains := by
          rw [hs]; exact hrc'
        exact prom_storeSkippedKey_srk_mem their (ck.messageKeys F) r h1
      · rw [hs] at hrc'
        simp only [ho_exec_bind_hw, ho_exec_liftE_hw] at hrc'
        have h_r1 : ∀ rc1 ∈ r1.receiverChains,
            ∃ rc₀ ∈ r.receiverChains, rc1.senderRatchetKey = rc₀.senderRatchetKey := by
          intro rc1 hrc1
          have h1 : rc1 ∈ (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r).2.receiverChains := by
            rw [hs]; exact hrc1
          exact prom_storeSkippedKey_srk_mem their (ck.messageKeys F) r h1
        rcases hn : ck.nextChainKey F with _ | ck'
        · rw [hn] at hrc'
          exact h_r1 rc' hrc'
        · rw [hn] at hrc'
          obtain ⟨rc1, hrc1, heq1⟩ := ih ck' r1 hrc'
          obtain ⟨rc₀, hrc₀, heq0⟩ := h_r1 rc1 hrc1
          exact ⟨rc₀, hrc₀, heq1.trans heq0⟩
    · exact ⟨rc', hrc', rfl⟩

private theorem prom_dhRatchetStep_srk_mem {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hDh : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1))
    {rc' : ReceiverChain} (hrc' : rc' ∈ r1.receiverChains) :
    (∃ rc₀ ∈ r0.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
      rc'.senderRatchetKey = their := by
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, _hsc, _hrc1, _hrc2, hr1⟩ :=
    Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
  rw [hr1] at hrc'
  dsimp only [RatchetState.evictReceiverChains] at hrc'
  have hmem := List.mem_of_mem_drop hrc'
  rcases List.mem_append.mp hmem with hold | hnew
  · exact Or.inl ⟨rc', hold, rfl⟩
  · simp only [List.mem_singleton] at hnew
    subst hnew
    exact Or.inr rfl

/-- Across a successful `SessionState.tryDecryptWithStateW`, either every receiver chain in `st'`
shares its `senderRatchetKey` with one in `st.receiverChains`, or `RatchetState.dhRatchetStep`
succeeded on `msg.senderRatchetKey` and every new `senderRatchetKey` equals `msg.senderRatchetKey`. -/
theorem tryDecryptWithStateW_receiverChains_cases {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {pt : List (BitVec 8)}
    (hok : Mut.exec (SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins) st =
      (.ok pt, st')) :
    (∀ rc' ∈ st'.receiverChains,
      ∃ rc₀ ∈ st.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
    (∃ (ck : ChainKey) (r1 : RatchetState),
      Mut.exec (RatchetState.dhRatchetStep C msg.senderRatchetKey coins) (ratchetStateOf st) =
        (.ok ck, r1) ∧
      ∀ rc' ∈ st'.receiverChains,
        (∃ rc₀ ∈ st.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
          rc'.senderRatchetKey = msg.senderRatchetKey) := by
  obtain ⟨remIk, tr_out, _, hTr, hSt2⟩ := tryDecryptWithStateW_ok_inv hok
  obtain ⟨ck0, r1_0, r2, mkGen, newPqrState, pqrKey, hEnsure, hConsume, _, hMac, _, hTrOut⟩ :=
    tripleRatchet_decryptW_ok_inv hTr
  have hBr := decryptOkBranch_of_ensure_consume hEnsure hConsume hMac
  have hrc_st' : st'.receiverChains = r2.receiverChains := by rw [hSt2, hTrOut]
  have hrc_r0 : (ratchetStateOf st).receiverChains = st.receiverChains := rfl
  rcases hBr with
    ⟨ck, _, _, hTake, _⟩ |
    ⟨ck, ck_adv, ck_next, r_adv, _, _, _, hAdv, _, hSet, _, _⟩ |
    ⟨ck, ck_adv, ck_next, r1, r_adv, _, hDh, _, _, hAdv, _, hSet, _, _⟩
  · left
    intro rc' hrc'
    rw [hrc_st'] at hrc'
    have hmem : rc' ∈ (Mut.exec (RatchetState.takeSkippedKey msg.senderRatchetKey msg.counter)
        (ratchetStateOf st)).2.receiverChains := by
      erw [hTake]; exact hrc'
    simpa [hrc_r0] using
      prom_takeSkippedKey_srk_mem msg.senderRatchetKey msg.counter (ratchetStateOf st) hmem
  · left
    intro rc' hrc'
    rw [hrc_st'] at hrc'
    have hmemSet : rc' ∈ (Mut.exec (RatchetState.setReceiverChainKey msg.senderRatchetKey ck_next)
        r_adv).2.receiverChains := by
      rw [hSet]; exact hrc'
    obtain ⟨rc₁, hrc₁, heq₁⟩ :=
      prom_setReceiverChainKey_srk_mem msg.senderRatchetKey ck_next r_adv hmemSet
    have hmemAdv : rc₁ ∈ (Mut.exec (RatchetState.advanceChain C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck) (ratchetStateOf st)).2.receiverChains := by
      erw [hAdv]; exact hrc₁
    obtain ⟨rc₀, hrc₀, heq₀⟩ :=
      prom_advanceChain_srk_mem C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck (ratchetStateOf st) hmemAdv
    exact ⟨rc₀, by simpa [hrc_r0] using hrc₀, heq₁.trans heq₀⟩
  · right
    refine ⟨ck, r1, hDh, fun rc' hrc' => ?_⟩
    rw [hrc_st'] at hrc'
    have hmemSet : rc' ∈ (Mut.exec (RatchetState.setReceiverChainKey msg.senderRatchetKey ck_next)
        r_adv).2.receiverChains := by
      rw [hSet]; exact hrc'
    obtain ⟨rc₂, hrc₂, heq₂⟩ :=
      prom_setReceiverChainKey_srk_mem msg.senderRatchetKey ck_next r_adv hmemSet
    have hmemAdv : rc₂ ∈ (Mut.exec (RatchetState.advanceChain C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck) r1).2.receiverChains := by
      rw [hAdv]; exact hrc₂
    obtain ⟨rc₁, hrc₁, heq₁⟩ :=
      prom_advanceChain_srk_mem C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck r1 hmemAdv
    rcases prom_dhRatchetStep_srk_mem hDh hrc₁ with ⟨rc₀, hrc₀, heq₀⟩ | hnew
    · exact Or.inl ⟨rc₀, by simpa [hrc_r0] using hrc₀, (heq₂.trans heq₁).trans heq₀⟩
    · exact Or.inr ((heq₂.trans heq₁).trans hnew)

private theorem seedsLen32_of_tryDecryptWithStateW {PQC : Type}
    {C : Crypto} {W : AesW} {spqr : Spqr (List (BitVec 8)) PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState (List (BitVec 8))} {pt : List (BitVec 8)}
    (hok : Mut.exec (SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins) st =
      (.ok pt, st'))
    (hSeeds : SeedsLen32 st) :
    SeedsLen32 st' := by
  obtain ⟨remIk, tr_out, _, hTr, hSt'⟩ := tryDecryptWithStateW_ok_inv hok
  obtain ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, hens, hcmk, _, _, _, hTrOut⟩ :=
    tripleRatchet_decryptW_ok_inv hTr
  rw [hSt', hTrOut]
  have h1 : RatchetSeedsLen32 r1 := by
    have h := ensureReceiverChain_preserves C msg.senderRatchetKey coins
      ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, LibsignalSession.maxForwardJumps⟩
      hSeeds
    simpa [hens] using h
  have h2 : RatchetSeedsLen32 r2 := by
    have h := consumeMessageKey_preserves C.F msg.senderRatchetKey ck
      msg.counter msgType r1 h1
    simpa [hcmk] using h
  exact h2

private theorem flatten_map_lenField_length_ge_prom {α : Type} (tag : Nat) (f : α → List (BitVec 8))
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem encReceiverChain_length_le_encSession_prom (s : Session (List (BitVec 8)))
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := flatten_map_lenField_length_ge_prom 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega

private theorem encSession_length_le_encodeRecord_prom (s : Session (List (BitVec 8))) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  dsimp only [Option.map_some]
  simp only [List.length_append]
  omega

theorem recordBytes_of_promAcceptOut
    {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {rec b : HwBytes} {mid : List MachineEvent} {sm : StateAndMessage}
    {pf : PreKeyFields} {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt) :
    recordBytes (sessionToRecordRecPending sess') = sm.state := by
  obtain ⟨_, _, ⟨_, _, hchains_sc, halice_lt, _, _, _⟩⟩ := hOut.hcan_in
  have hSeeds0 : SeedsLen32 sess.state := fun rc hrc mk hmk => (hchains_sc rc hrc).2 mk hmk
  have hSeeds' : SeedsLen32 sess'.state := seedsLen32_of_tryDecryptWithStateW hOut.hexec hSeeds0
  obtain ⟨sess₁, hrc₁, -, -, -, h62, -⟩ := hOut.hwrc
  have hpq_eq : sess₁.state.pqRatchetState = sess'.state.pqRatchetState :=
    EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁.1 hOut.hstate h62
  obtain ⟨_, _, ⟨_, _, _, _, _, hpq₁_lt, _⟩⟩ := hrc₁
  have hpq_lt : sess'.state.pqRatchetState.length < 2 ^ 64 := by
    rw [← hpq_eq]; omega
  have halice_lt' : sess'.aliceBaseKey.length < 2 ^ 64 := by
    rw [hOut.halice]; omega
  have hseeds' : ∀ rc ∈ sess'.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk
    have h32 := hSeeds' rc hrc mk hmk
    omega
  have hsess_len : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 64 := by
    have hle := encSession_length_le_encodeRecord_prom sess'
    rw [← hOut.hstate] at hle
    omega
  rw [hOut.hstate]
  refine recordBytes_sessionToRecordRecPending_eq_encodeRecord sess'
    halice_lt' hpq_lt hseeds' (fun rc hrc => ?_) hsess_len
  exact Nat.lt_of_le_of_lt (encReceiverChain_length_le_encSession_prom sess' rc hrc) hsess_len

theorem prom_sm_recordBytes
    {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {rec b : HwBytes} {mid : List MachineEvent} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hout : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt) :
    sm.state = recordBytes (sessionToRecordRecPending sess') ∧ sm.state ≠ [] := by
  have hbytes := (recordBytes_of_promAcceptOut hout).symm
  exact ⟨hbytes, hbytes ▸ prom_recordBytes_ne_nil _⟩

theorem ho_prom_normPending_of_canonical_Q
    {Q : List (BitVec 8) → Prop} {rec : HwBytes} {rr₀ : RecordRec} {sess : Session (List (BitVec 8))}
    (hrec : rec = recordBytes rr₀)
    (hcan : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Q rec sess) :
    normPending rr₀ = normPending (sessionToRecordRecPending sess) := by
  apply TR.recordBytes_injective
  rw [← hrec, (recordBytes_sessionToRecordRecPending_of_canonical_Q hcan).2]

end Symbolic.Swarm.CREF.CliPure
