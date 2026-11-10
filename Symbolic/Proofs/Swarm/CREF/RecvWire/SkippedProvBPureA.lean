/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkPeel
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrDHS
public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepGood
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkBobGuard
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkRootTwin
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSep
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkTwin
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineLink
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SupplyVck -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.ProvBAux -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvWire.SkippedNotJunkFixPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.G1.SkippedPkLineage -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Skipped-Key `ProvB` Trace Invariants

Provenance, `SpineRkK`, and `spb_ProvRIdx2Inv` trace-preservation lemmas for `SkippedKeyStored`
events on reachable composed traces.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir RecvChain findRecvChain setRecvChain
  recvChainFor consumeMessageKey chainKeyAt kdfCk litByte)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open Symbolic.Swarm.CREF.TR hiding StEntry
open Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry logSkippedKeysTr decTailTr run_bind_fst run_bind_snd at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add logSkippedKeysTr_length at?_eq_none_of_le
open Symbolic.Swarm.CREF.TR.G1

theorem good_of_skippedKeyStored {T : ExecTrace} (hT : ReachableTrace T)
    {ses : SessionInfo} {pk seed : DY.Bytes} {n : UInt32} {rIdx srcIdx skIdx : Nat}
    (hlog : T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n seed rIdx srcIdx) skIdx) :
    TR.G1.Spine.Good T seed := by
  obtain ⟨pk', R, j, rfl, hR⟩ :=
    TR.G1.Spine.recvLinkSkipped_of_reachable hT hlog
  exact .inl ⟨pk', R, j, true, hR, rfl⟩

theorem exists_kdfCk_of_skippedKeyStored {T : ExecTrace} (hT : ReachableTrace T)
    {ses : SessionInfo} {pk seed : DY.Bytes} {n : UInt32} {rIdx srcIdx skIdx : Nat}
    (hlog : T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n seed rIdx srcIdx) skIdx) :
    ∃ ck, seed = (DY.Libsignal.TripleRatchet.kdfCk ck).2 := by
  obtain ⟨_pk', R, j, rfl, _hR⟩ :=
    TR.G1.Spine.recvLinkSkipped_of_reachable hT hlog
  exact ⟨DY.Libsignal.TripleRatchet.chainKeyAt R j, rfl⟩

theorem pk_attackerKnows_of_skippedKeyStored {T : ExecTrace} (hT : ReachableTrace T)
    {ses : SessionInfo} {pk seed : DY.Bytes} {n : UInt32} {rIdx srcIdx skIdx : Nat}
    (hlog : T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n seed rIdx srcIdx) skIdx) :
    pk.AttackerKnows T :=
  (provEvTR_reachable hT ses pk n seed rIdx srcIdx skIdx hlog).1

/-- `SeedSepAK` for `Good T` holds on any reachable trace `T` satisfying `AliceKemLen32`. -/
theorem seedSepAK_good_of_reachable
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g T)
    (t₁ t₂ : DY.Bytes) :
    TR.G1.Spine.SeedSepAK interpretation S g T (TR.G1.Spine.Good T) t₁ t₂ := by
  have hRkTwin : TR.G1.Spine.RkTwinStmt interpretation S g T :=
    TR.G1.Spine.rkTwin interpretation S g hT
      (TR.G1.Spine.aliceBobTwin_of_reachable interpretation S g hT hKem32)
  exact TR.G1.Spine.seedSepAK_good interpretation S g hT
    (TR.G1.Spine.recvLinkStored_of_reachable hT) hRkTwin
    (TR.G1.Spine.rkTwinStored interpretation S g hT)
    (TR.G1.Spine.rootTwin interpretation S g hT hKem32 hRkTwin) t₁ t₂

theorem spineRkK_chainKeyAt {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop} {c : Bool} :
    ∀ (n : Nat) {ck : DY.Bytes},
      TR.G1.Spine.SpineRkK K B c ck →
      TR.G1.Spine.SpineRkK K B c (chainKeyAt ck n)
  | 0, _, h => h
  | n + 1, _, h => spineRkK_chainKeyAt n (.ckStep1 h)

theorem spineRkK_of_kdfCk_fst {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}
    {c : Bool} {ck : DY.Bytes}
    (h : TR.G1.Spine.SpineRkK K B c (kdfCk ck).1) :
    TR.G1.Spine.SpineRkK K B c ck := by
  generalize hv : (kdfCk ck).1 = v at h
  change KdfExtract.kdfExtract ck (litByte 0x02) = v at hv
  cases h with
  | hsRk _ =>
    obtain ⟨_, h2⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hv.symm
    exact False.elim (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _ h2.symm)
  | hsCk _ =>
    obtain ⟨_, h2⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hv.symm
    exact False.elim (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _ h2.symm)
  | rkStep1 _ _ =>
    obtain ⟨_, h2⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hv.symm
    exact False.elim (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _ h2.symm)
  | rkStep2 _ _ =>
    obtain ⟨_, h2⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hv.symm
    exact False.elim (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _ h2.symm)
  | ckStep1 hck =>
    obtain ⟨h1, _⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hv.symm
    exact h1 ▸ hck
  | ckStep2 _ =>
    obtain ⟨_, h2⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hv.symm
    have h2' := Symbolic.DYBridge.DY.BytesView.pack_inj.mp h2
    simp at h2'

theorem spineRkK_of_chainKeyAt {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}
    {c : Bool} :
    ∀ (n : Nat) {ck : DY.Bytes},
      TR.G1.Spine.SpineRkK K B c (chainKeyAt ck n) →
      TR.G1.Spine.SpineRkK K B c ck
  | 0, _, h => h
  | n + 1, _, h => spineRkK_of_kdfCk_fst (spineRkK_of_chainKeyAt n h)

open Symbolic.Swarm.COMPOSED.CompTermAlgebra Symbolic.Swarm.COMPOSED.CompKeyInversion in
theorem spb_compSessionAt_resp_ikm_dh_eq {tr : ExecTrace} {s : SessionInfo}
    {d₁ d₂ : Nat} {ikm₁ ikm₂ dh₁ dh₂ : DY.Bytes}
    (hs₁ : Symbolic.Swarm.COMPOSED.CompRatchet.CompSessionAt tr s d₁ ikm₁ dh₁)
    (hs₂ : Symbolic.Swarm.COMPOSED.CompRatchet.CompSessionAt tr s d₂ ikm₂ dh₂)
    (hinit : s.initiator = false) :
    ikm₁ = ikm₂ ∧ dh₁ = dh₂ := by
  obtain ⟨_, _, hrole₁⟩ := hs₁
  obtain ⟨_, _, hrole₂⟩ := hs₂
  simp only [hinit, Bool.false_eq_true, ↓reduceIte] at hrole₁ hrole₂
  obtain ⟨_, _, _, ikB₁, _, spkSk₁, _, _, ek₁, _, dh4₁, e₁, _, _, hne₁, _, _, _, hikm₁, pk₁, hsid₁, hdh₁⟩ := hrole₁
  obtain ⟨_, _, _, ikB₂, _, spkSk₂, _, _, ek₂, _, dh4₂, e₂, _, _, _, _, _, _, hikm₂, pk₂, hsid₂, hdh₂⟩ := hrole₂
  obtain ⟨hpk_eq, hrk_eq⟩ := concat_inj (hsid₁.symm.trans hsid₂)
  have hikm_eq : ikm₁ = ikm₂ := pqxdhKdf_rk_inj hrk_eq
  refine ⟨hikm_eq, ?_⟩
  obtain ⟨_, hdh2_eq, hdh3_eq, _⟩ :=
    pqxdhIkm_inj_parts (hikm₁.symm.trans (hikm_eq.trans hikm₂))
  have hspk_eq : spkSk₁ = spkSk₂ := Classical.byContradiction fun hne_spk => by
    obtain ⟨hek₁, hek₂⟩ := dh_eq_of_sk_ne hne_spk hdh3_eq
    rw [hek₁, hek₂] at hdh2_eq
    rcases dh_eq_dh_dhPk_cases hdh2_eq with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hne_spk (dhPk_inj h1).symm
    · exact hne₁ h2
  rw [hdh₁, hdh₂, hpk_eq, hspk_eq]

def spb_RecvKeysUnique (l : List RecvChain) : Prop :=
  ∀ c₁ ∈ l, ∀ c₂ ∈ l, c₁.ratchetKey = c₂.ratchetKey → c₁ = c₂

theorem spb_recvKeysUnique_drop {l : List RecvChain} (k : Nat) (h : spb_RecvKeysUnique l) :
    spb_RecvKeysUnique (l.drop k) :=
  fun c₁ h₁ c₂ h₂ => h c₁ (List.mem_of_mem_drop h₁) c₂ (List.mem_of_mem_drop h₂)

private theorem recvKeysUnique_setRecvChain {l : List RecvChain} (c' : RecvChain) (h : spb_RecvKeysUnique l) :
    spb_RecvKeysUnique (setRecvChain l c') := by
  intro c₁ h₁ c₂ h₂ hrk
  unfold setRecvChain at h₁ h₂
  obtain ⟨d₁, hd₁_mem, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨d₂, hd₂_mem, rfl⟩ := List.mem_map.mp h₂
  have hrk_pres : ∀ d : RecvChain,
      (if d.ratchetKey == c'.ratchetKey then c' else d).ratchetKey = d.ratchetKey := by
    intro d
    cases hbeq : (d.ratchetKey == c'.ratchetKey)
    · rfl
    · exact (beq_iff_eq.mp hbeq).symm
  have hd_eq : d₁ = d₂ := h d₁ hd₁_mem d₂ hd₂_mem (by rw [← hrk_pres d₁, ← hrk_pres d₂, hrk])
  rw [hd_eq]

theorem spb_recvKeysUnique_append_singleton {l : List RecvChain} {c1 : RecvChain}
    (h : spb_RecvKeysUnique l) (hfind : findRecvChain l c1.ratchetKey = none) :
    spb_RecvKeysUnique (l ++ [c1]) := by
  have hnot_mem : ∀ d ∈ l, d.ratchetKey ≠ c1.ratchetKey := by
    intro d hd heq
    have hnone : l.find? (fun x => x.ratchetKey == c1.ratchetKey) = none := hfind
    exact absurd (beq_iff_eq.mpr heq) (List.find?_eq_none.mp hnone d hd)
  intro d₁ h₁ d₂ h₂ hrk
  rcases List.mem_append.mp h₁ with h₁ | h₁ <;> rcases List.mem_append.mp h₂ with h₂ | h₂
  · exact h d₁ h₁ d₂ h₂ hrk
  · rw [List.mem_singleton.mp h₂] at hrk; exact absurd hrk (hnot_mem d₁ h₁)
  · rw [List.mem_singleton.mp h₁] at hrk; exact absurd hrk.symm (hnot_mem d₂ h₂)
  · rw [List.mem_singleton.mp h₁, List.mem_singleton.mp h₂]

theorem spb_recvKeysUnique_singleton (c : RecvChain) : spb_RecvKeysUnique [c] :=
  fun _ h₁ _ h₂ _ => by rw [List.mem_singleton.mp h₁, List.mem_singleton.mp h₂]

section ProvRIdx2Proof
open Symbolic.Swarm.COMPOSED.CompTrace hiding run_bind_fst run_bind_snd NetE
open Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS (InertOnNonTR)
open DY.Libsignal.TripleRatchet (logSkippedKeys logMessageKeyAndStore)
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry)

set_option quotPrecheck false in
local notation "SkippedEventRIdx2At" => fun (tr : ExecTrace) (pk : DY.Bytes) (n : UInt32) (rIdx src : Nat) =>
  (∃ (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain) (fresh : Bool) (seed' : DY.Bytes) (c₀' : RecvChain),
    TR.G1.TRStateStoredAt p₀ st₀ src tr ∧
    recvChainFor st₀.toDRState pk = some (c₀, fresh) ∧
    consumeMessageKey c₀ n = some (seed', c₀')) ∨ rIdx = 2

private theorem skippedEventRIdx2At_mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {pk : DY.Bytes} {n : UInt32} {rIdx src : Nat} (h : SkippedEventRIdx2At tr pk n rIdx src) :
    SkippedEventRIdx2At tr' pk n rIdx src :=
  h.elim (fun ⟨p₀, st₀, c₀, fresh, seed', c₀', hst₀, hrc, hcons⟩ =>
    .inl ⟨p₀, st₀, c₀, fresh, seed', c₀', trStateStoredAt_mono hle hst₀, hrc, hcons⟩) Or.inr

def spb_ProvRIdx2Inv (tr : ExecTrace) : Prop :=
  (∀ p st i, TR.G1.TRStateStoredAt p st i tr → spb_RecvKeysUnique st.recv) ∧
  (∀ s pk n seed rIdx src skIdx,
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) skIdx →
    SkippedEventRIdx2At tr pk n rIdx src)

theorem spb_provRIdx2Inv_nil : spb_ProvRIdx2Inv Trace.nil :=
  ⟨fun _ _ _ h => by
     simp only [TR.G1.TRStateStoredAt, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt,
       ↓reduceDIte, reduceCtorEq] at h,
   fun _ _ _ _ _ _ _ h => by
     simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
       Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h⟩

theorem spb_provRIdx2Inv_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {x : E}
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option StEntry) = none)
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option TREntry) = none)
    (h : spb_ProvRIdx2Inv tr) : spb_ProvRIdx2Inv (tr.append x) :=
  ⟨fun p st i hst => h.1 p st i (trStateStoredAt_append_other hnone_st hst),
   fun s pk n seed rIdx src skIdx hl =>
     skippedEventRIdx2At_mono (Trace.append_le tr x) (h.2 s pk n seed rIdx src skIdx (eventLoggedAt_append_other hnone_tr hl))⟩

theorem spb_provRIdx2Inv_append_tr {tr : ExecTrace} {ev : TREvent}
    (hev : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src)
    (h : spb_ProvRIdx2Inv tr) : spb_ProvRIdx2Inv (tr.append (TREvE ev)) :=
  ⟨fun p st i hst => h.1 p st i (trStateStoredAt_append_other rfl hst),
   fun s pk n seed rIdx src skIdx hl =>
     skippedEventRIdx2At_mono (Trace.append_le tr _)
       ((eventLoggedAt_append_same hl).elim
         (fun ⟨_, hl0⟩ => h.2 s pk n seed rIdx src skIdx hl0)
         (fun ⟨_, heq⟩ => absurd heq (hev s pk n seed rIdx src)))⟩

private theorem provRIdx2Inv_append_st {tr : ExecTrace} {me : Participant} {st₀ : TRState}
    (huniq : spb_RecvKeysUnique st₀.recv) (h : spb_ProvRIdx2Inv tr) :
    spb_ProvRIdx2Inv (tr.append (TRStE me st₀)) :=
  ⟨fun p st i hst =>
     (trStateStoredAt_append_same hst).elim
       (fun ⟨_, hst0⟩ => h.1 p st i hst0)
       (fun ⟨_, _, heq⟩ => heq ▸ huniq),
   fun s pk n seed rIdx src skIdx hl =>
     skippedEventRIdx2At_mono (Trace.append_le tr _)
       (h.2 s pk n seed rIdx src skIdx (eventLoggedAt_append_other rfl hl))⟩

theorem spb_provRIdx2Inv_inertOnNonTR : InertOnNonTR spb_ProvRIdx2Inv where
  append_net _ _ h := spb_provRIdx2Inv_append_other rfl rfl h
  append_rnd _ _ h := spb_provRIdx2Inv_append_other rfl rfl h
  append_pqxEv _ _ h := spb_provRIdx2Inv_append_other rfl rfl h
  append_cEv _ _ h := spb_provRIdx2Inv_append_other rfl rfl h
  append_pqxSt _ _ _ h := spb_provRIdx2Inv_append_other rfl rfl h

private theorem trStateStoredAt_logSkippedKeysTr
    {s : SessionInfo} {pk : DY.Bytes} {rIdx src : Nat} {ck : DY.Bytes} {n : UInt32} {k : Nat}
    {tr : ExecTrace} {p : Participant} {st : TRState} {i : Nat}
    (h : TR.G1.TRStateStoredAt p st i (logSkippedKeysTr s pk rIdx src ck n k tr)) :
    TR.G1.TRStateStoredAt p st i tr := by
  induction k generalizing ck n tr with
  | zero => exact h
  | succ k ih =>
    exact trStateStoredAt_append_other rfl (ih h)

private theorem consumeMessageKey_skipped_rIdx2 {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) {j : Nat}
    (hj : j < counter.toNat - c.index.toNat) :
    ∃ c₀', consumeMessageKey c (c.index + UInt32.ofNat j) =
      some ((kdfCk (chainKeyAt c.chainKey j)).2, c₀') := by
  unfold consumeMessageKey at h
  split at h; · cases h
  rename_i hlt; split at h; · cases h
  rename_i hjump; split at h; · cases h
  rename_i hne
  have hlt' : c.index.toNat ≤ counter.toNat := by rw [UInt32.lt_iff_toNat_lt] at hlt; omega
  have hcn : counter.toNat < 2 ^ 32 := counter.toNat_lt
  have hcne : counter.toNat ≠ 4294967295 := fun heq => hne (UInt32.toNat_inj.mp (by rw [heq]; rfl))
  have hjNat : (UInt32.ofNat j).toNat = j := UInt32.toNat_ofNat_of_lt' (by change j < 4294967296; omega)
  have hsum : (c.index + UInt32.ofNat j).toNat = c.index.toNat + j := by
    rw [UInt32.toNat_add, hjNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold consumeMessageKey
  have h1 : ¬ (c.index + UInt32.ofNat j < c.index) := by rw [UInt32.lt_iff_toNat_lt, hsum]; omega
  have h2 : ¬ ((c.index + UInt32.ofNat j).toNat - c.index.toNat > DY.Libsignal.TripleRatchet.maxForwardJumps) := by
    rw [hsum]; have := Nat.le_of_not_gt hjump; omega
  have h3 : ¬ (c.index + UInt32.ofNat j = DY.Libsignal.TripleRatchet.u32Max) := by
    intro heq; have := congrArg UInt32.toNat heq; rw [hsum] at this; change c.index.toNat + j = 4294967295 at this; omega
  have hidx : (c.index + UInt32.ofNat j).toNat - c.index.toNat = j := by rw [hsum]; omega
  have h2' : ¬ (j > DY.Libsignal.TripleRatchet.maxForwardJumps) := hidx ▸ h2
  simp only [h1, h3, ↓reduceIte, hidx, h2']; exact ⟨_, rfl⟩

private theorem logSkippedKeys_run_step_rIdx2 (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).2.val =
        logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero =>
    simp [logSkippedKeys, logSkippedKeysTr, DY.Traceful.run_pure]
  | succ k ih =>
    unfold logSkippedKeys logSkippedKeysTr
    have hlog : (DY.ProtocolEvent.logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)).run tr =
        (some (), ⟨tr.append (TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)), Trace.append_le tr _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hlog]
    exact ih (kdfCk ck).1 (n + 1) _

theorem spb_decTailTr_run_rIdx2 (me : Participant) (stH : Nat) (st1 : TRState) (c c' : RecvChain)
    (pk seed pqSalt m spqr' : DY.Bytes) (n : UInt32) (tr : ExecTrace) :
    ((do
      let _ ← logSkippedKeys (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat)
      let _ ← DY.ProtocolEvent.logEvent (TREvent.Received me st1.peer pk n m)
      logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt n
        c.rIdx stH { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } : Traceful Nat).run tr).2.val =
      decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n := by
  obtain ⟨hsk1, hsk2⟩ := logSkippedKeys_run_step_rIdx2 (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hsk1, hsk2]
  dsimp only [logMessageKeyAndStore, DY.Libsignal.TripleRatchet.traceLength]
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    DY.Traceful.run_bind, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk, DY.Traceful.run_pure]
  rfl

private theorem decTailTr_le_rIdx2 (tr : ExecTrace) (me : Participant) (stH : Nat) (st1 : TRState)
    (c c' : RecvChain) (pk seed pqSalt m spqr' : DY.Bytes) (n : UInt32) :
    tr ≤ decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n := by
  rw [← spb_decTailTr_run_rIdx2]
  exact ((do
    let _ ← logSkippedKeys (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat)
    let _ ← DY.ProtocolEvent.logEvent (TREvent.Received me st1.peer pk n m)
    logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt n
      c.rIdx stH { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } : Traceful Nat).run tr).2.property

private theorem provRIdx2Inv_decTailTr_gen {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st1 : TRState} {c c' : RecvChain} {pk seed pqSalt m spqr' : DY.Bytes} {n : UInt32}
    (hInv : spb_ProvRIdx2Inv tr) (huniq1 : spb_RecvKeysUnique st1.recv)
    (hsk : ∀ j, j < n.toNat - c.index.toNat →
      SkippedEventRIdx2At (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) pk (c.index + UInt32.ofNat j) c.rIdx stH) :
    spb_ProvRIdx2Inv (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) := by
  have hle := decTailTr_le_rIdx2 tr me stH st1 c c' pk seed pqSalt m spqr' n
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr
  let tr_rcv := tr_sk.append (TREvE (TREvent.Received me st1.peer pk n m))
  let tr_mk := tr_rcv.append (TREvE (TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stH))
  let st₁_post : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
  refine ⟨fun p st i hst => ?_, fun s' pk' n' seed' r' src' i hlog => ?_⟩
  · have hst' : TR.G1.TRStateStoredAt p st i (tr_mk.append (TRStE me st₁_post)) := hst
    rcases trStateStoredAt_append_same hst' with ⟨_, hst_mk⟩ | ⟨_, _, rfl⟩
    · exact hInv.1 p st i (trStateStoredAt_logSkippedKeysTr (trStateStoredAt_append_other rfl (trStateStoredAt_append_other rfl hst_mk)))
    · exact recvKeysUnique_setRecvChain c' huniq1
  · have hlog' : (tr_mk.append (TRStE me st₁_post)).EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' r' src') i := hlog
    rcases eventLoggedAt_append_same (eventLoggedAt_append_other rfl hlog') with ⟨_, hlog_rcv⟩ | ⟨_, heq⟩
    · rcases eventLoggedAt_append_same hlog_rcv with ⟨_, hlog_sk⟩ | ⟨_, heq⟩
      · by_cases hi : i < tr.length
        · have hlog0 : tr.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' r' src') i := by
            rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_sk ⊢
            rwa [← at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]
          exact skippedEventRIdx2At_mono hle (hInv.2 s' pk' n' seed' r' src' i hlog0)
        · have hi_lt : i < tr_sk.length := by
            by_contra hge; have hnone : (tr_sk.at? i : Option TREntry) = none := at?_eq_none_of_le tr_sk (Nat.le_of_not_lt hge)
            rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_sk
            rw [hnone] at hlog_sk; cases hlog_sk
          have hlen_sk : tr_sk.length = tr.length + (n.toNat - c.index.toNat) := logSkippedKeysTr_length _ _ _ _ _ _ _ _
          have hj : i - tr.length < n.toNat - c.index.toNat := by omega
          have hi_eq : i = tr.length + (i - tr.length) := by omega
          have hat := at?_trEntry_logSkippedKeysTr_add (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr hj
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_sk
          rw [hi_eq, hat] at hlog_sk; cases hlog_sk
          exact hsk (i - tr.length) hj
      · nomatch heq
    · nomatch heq

theorem spb_provRIdx2Inv_decTailTr {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st₀ st1 : TRState} {c c' : RecvChain} {fresh : Bool} {pk seed pqSalt m spqr' : DY.Bytes} {n : UInt32}
    (hInv : spb_ProvRIdx2Inv tr) (hst₀ : TR.G1.TRStateStoredAt me st₀ stH tr)
    (huniq1 : spb_RecvKeysUnique st1.recv)
    (hrc : recvChainFor st₀.toDRState pk = some (c, fresh))
    (hcons : consumeMessageKey c n = some (seed, c')) :
    spb_ProvRIdx2Inv (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) :=
  provRIdx2Inv_decTailTr_gen hInv huniq1 fun _ hj =>
    let ⟨c₀', hc0⟩ := consumeMessageKey_skipped_rIdx2 hcons hj
    .inl ⟨me, st₀, c, fresh, _, c₀', trStateStoredAt_mono (decTailTr_le_rIdx2 _ _ _ _ _ _ _ _ _ _ _ _) hst₀, hrc, hc0⟩

theorem spb_provRIdx2Inv_decTailTr_bob {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st1 : TRState} {c c' : RecvChain} {pk seed pqSalt m spqr' : DY.Bytes} {n : UInt32}
    (hInv : spb_ProvRIdx2Inv tr) (huniq1 : spb_RecvKeysUnique st1.recv) (hrIdx2 : c.rIdx = 2) :
    spb_ProvRIdx2Inv (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) :=
  provRIdx2Inv_decTailTr_gen hInv huniq1 fun _ _ => .inr hrIdx2

theorem spb_provRIdx2Inv_logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (mk pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    {l : List RecvChain} (hrecv : st.recv = l) (huniq : spb_RecvKeysUnique l) :
    Preserves spb_ProvRIdx2Inv (logMessageKeyAndStore me s dir mk pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  refine Preserves.bind (fun _ h => ?_) fun _ _ h => ?_
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_tr (by intro _ _ _ _ _ _; nofun) h
  · simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact provRIdx2Inv_append_st (hrecv ▸ huniq) h

theorem spb_provRIdx2Inv_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves spb_ProvRIdx2Inv (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  have hsend : ∀ m : DY.Bytes, Preserves spb_ProvRIdx2Inv (DY.Network.sendMessage m) := by
    intro _ _ h
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  refine spb_provRIdx2Inv_inertOnNonTR.bind_aliceHandshake a b idStateIdx regIdxB bh tr₀ hInv₀ fun _ => ?_
  refine (?_ : Preserves spb_ProvRIdx2Inv _) _ (spb_provRIdx2Inv_append_other rfl rfl (spb_provRIdx2Inv_append_other rfl rfl hInv₀))
  refine Preserves.bind (fun _ h => ?_) fun _ =>
    Preserves.bind (hsend _) fun _ =>
    Preserves.bind (hsend _) fun _ => Preserves.bind Preserves.traceLength fun _ =>
    Preserves.bind (fun _ h => ?_) fun _ =>
    Preserves.bind (fun _ h => ?_) fun _ =>
    Preserves.bind (fun _ h => ?_) fun _ _ h => ?_
  · simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_tr (by intro _ _ _ _ _ _; nofun) h
  · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  · simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact provRIdx2Inv_append_st (spb_recvKeysUnique_singleton _) h

theorem spb_run_sendMessage_bind_snd_rIdx2 {α : Type} (msg : DY.Bytes) (f : Nat → Traceful α) (tr : ExecTrace) :
    ((Network.sendMessage msg >>= f).run tr).2.val = ((f tr.length).run (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.NetE msg))).2.val := by
  have hnet : (Network.sendMessage msg).run tr =
      (some tr.length, ⟨tr.append (Symbolic.Swarm.COMPOSED.CompTrace.NetE msg), Trace.append_le tr _⟩) := by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
    erw [DY.Traceful.run_mk]
  rw [DY.Traceful.run_bind, hnet]

theorem spb_receiveMessage_trace_rIdx2 (idx : Nat) (tr : ExecTrace) :
    ((Network.receiveMessage idx).run tr).2.val = tr :=
  Preserves.receiveMessage (Inv := fun t => t = tr) idx tr rfl

theorem spb_receiveSignalMsg_trace_rIdx2 (msgH : Nat) (tr : ExecTrace) :
    ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgH).run tr).2.val = tr :=
  Preserves.receiveSignalMsg (Inv := fun t => t = tr) msgH tr rfl

end ProvRIdx2Proof

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
