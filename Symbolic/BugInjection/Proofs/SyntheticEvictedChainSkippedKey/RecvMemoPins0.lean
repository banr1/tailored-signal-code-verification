/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
public import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
public import Symbolic.Proofs.Tests.Shared.Composed.Runs

/-!
# Wire, MAC, and Ghost Pinning Primitives

Byte-level injectivity and `DrawsMatch`, `trWireBytes`, and `computeMac` pinning lemmas for
recovering `g.σ`, `pqKey`, and `pqMsg` bytes along clean prefix steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins0

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY.Libsignal (HwBytes)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeKey encodeVarint encodeBytesField encodeUint32Field)
open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet
  (TRState messageVersion kdfCk trMsgKeys trHonestWireMsg computeMac parseTrSignalMsg)
open DY.Libsignal.Refinement (WireFields paddedVarint encodeField encodeWith)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto versionByte)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry
   randTerm litOf ecKey kyberKey rngEntry kyberCoinEntries preKeyWire
   GhostWF BytesMatchEntry DrawsMatch SendMatches
   trWireBytes trWireBytes_canonical concretizeRandom concretizeSym concretizeTrWire gamma gamma')
open DY.TrWire (canonicalVariation)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encMsg encSig parse_encMsg)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_lit ms_pack_sym ms_pack_trWire)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedAesPerm evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
  (gamma_concatE gamma_trunc8E gamma_hmacE gamma_hmacE_length gamma_spqrSendKey_length
   gamma_trMsgKeys_congr_prk computeMac_pins_salt_and_seed)

theorem append_inj_right_len {α : Type} {l₁ r₁ l₂ r₂ : List α}
    (h : l₁ ++ r₁ = l₂ ++ r₂) (hr : r₁.length = r₂.length) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have hlen : (l₁ ++ r₁).length = (l₂ ++ r₂).length := congrArg List.length h
  rw [List.length_append, List.length_append, hr] at hlen
  have hl : l₁.length = l₂.length := Nat.add_right_cancel hlen
  exact List.append_inj h hl

private theorem encodeVarint_len_check :
    ((List.range 2048).all fun n =>
      (encodeVarint (BitVec.ofNat 64 n)).length == (if n < 128 then 1 else 2)) = true := by
  decide +kernel

theorem encodeVarint_len_lt2048 {n : Nat} (hn : n < 2048) :
    (encodeVarint (BitVec.ofNat 64 n)).length = (if n < 128 then 1 else 2) := by
  have hall := List.all_eq_true.mp encodeVarint_len_check n (List.mem_range.mpr hn)
  exact beq_iff_eq.mp hall

private theorem paddedVarint_len_check :
    ((List.range 2048).all fun n =>
      (paddedVarint n 0).length == (if n < 128 then 1 else 2)) = true := by
  decide +kernel

theorem paddedVarint_len_lt2048 {n : Nat} (hn : n < 2048) :
    (paddedVarint n 0).length = (if n < 128 then 1 else 2) := by
  have hall := List.all_eq_true.mp paddedVarint_len_check n (List.mem_range.mpr hn)
  exact beq_iff_eq.mp hall

theorem encodeBytesField_some_inj {tag : Nat} {v v₀ : HwBytes}
    (hv : v.length < 2048) (hv₀ : v₀.length < 2048)
    (heq : encodeBytesField tag (some v) = encodeBytesField tag (some v₀)) :
    v = v₀ := by
  unfold encodeBytesField at heq
  dsimp only at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have hkv := List.append_cancel_left heq
  have hlen := congrArg List.length hkv
  rw [List.length_append, List.length_append,
      encodeVarint_len_lt2048 hv, encodeVarint_len_lt2048 hv₀] at hlen
  have hveq : v.length = v₀.length := by
    by_cases h1 : v.length < 128 <;> by_cases h2 : v₀.length < 128 <;>
      simp only [h1, h2, ↓reduceIte] at hlen <;> omega
  rw [hveq] at hkv
  exact List.append_cancel_left hkv

theorem preKeyWire_msg_inj
    {pkId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32}
    {ik ek ct msg msg₀ : HwBytes}
    (hlen₀ : (preKeyWire pkId spkId kpkId regId ik ek ct msg₀).length < 2048)
    (heq : preKeyWire pkId spkId kpkId regId ik ek ct msg =
           preKeyWire pkId spkId kpkId regId ik ek ct msg₀) :
    msg = msg₀ := by
  have htot : (preKeyWire pkId spkId kpkId regId ik ek ct msg).length < 2048 := heq ▸ hlen₀
  unfold preKeyWire PreKeyProto.encode at heq htot hlen₀
  dsimp only at heq htot hlen₀
  have hm_lt : msg.length < 2048 := by
    simp only [List.length_cons, List.length_append, encodeBytesField] at htot
    omega
  have hm₀_lt : msg₀.length < 2048 := by
    simp only [List.length_cons, List.length_append, encodeBytesField] at hlen₀
    omega
  injection heq with _ hbody
  injection hbody with _ hproto
  let pre := encodeUint32Field 1 pkId ++ encodeBytesField 2 (some (ecKey ek)) ++
    encodeBytesField 3 (some ik)
  let suf := encodeUint32Field 5 (some regId) ++ encodeUint32Field 6 (some spkId) ++
    encodeUint32Field 7 (some kpkId) ++ encodeBytesField 8 (some (kyberKey ct))
  have hgrp : ∀ m : HwBytes,
      encodeUint32Field 1 pkId ++ encodeBytesField 2 (some (ecKey ek)) ++
      encodeBytesField 3 (some ik) ++ encodeBytesField 4 (some m) ++
      encodeUint32Field 5 (some regId) ++ encodeUint32Field 6 (some spkId) ++
      encodeUint32Field 7 (some kpkId) ++ encodeBytesField 8 (some (kyberKey ct)) =
      pre ++ (encodeBytesField 4 (some m) ++ suf) := by
    intro m; simp only [pre, suf, List.append_assoc]
  have hp1 := hgrp msg
  have hp2 := hgrp msg₀
  have hf4 : encodeBytesField 4 (some msg) ++ suf = encodeBytesField 4 (some msg₀) ++ suf :=
    List.append_cancel_left ((hp1.symm.trans hproto).trans hp2)
  exact encodeBytesField_some_inj hm_lt hm₀_lt (append_inj_right_len hf4 rfl).1

theorem trWireBytes_canonical_pq_inj {addr pq pq₀ : HwBytes} {f : WireFields}
    (hlen₀ : (trWireBytes addr canonicalVariation f pq₀).length < 2048)
    (heq : trWireBytes addr canonicalVariation f pq =
           trWireBytes addr canonicalVariation f pq₀) :
    pq = pq₀ := by
  have htot : (trWireBytes addr canonicalVariation f pq).length < 2048 := heq ▸ hlen₀
  rw [trWireBytes_canonical] at heq htot hlen₀
  rw [trWireBytes_canonical] at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have hmid_suf := List.append_cancel_left heq
  have hmid := (append_inj_right_len hmid_suf rfl).1
  have hpv42 : (paddedVarint 42 0).length = 1 := paddedVarint_len_lt2048 (by decide)
  by_cases hpq : pq = [] <;> by_cases hpq₀ : pq₀ = []
  · rw [hpq, hpq₀]
  · simp only [hpq, hpq₀, ↓reduceIte, encodeField] at hmid
    have h0 := congrArg List.length hmid
    simp only [List.length_nil, List.length_append, hpv42] at h0
    omega
  · simp only [hpq, hpq₀, ↓reduceIte, encodeField] at hmid
    have h0 := congrArg List.length hmid
    simp only [List.length_nil, List.length_append, hpv42] at h0
    omega
  · have hp_lt : pq.length < 2048 := by
      simp only [hpq, ↓reduceIte, List.length_append, encodeField] at htot
      omega
    have hp₀_lt : pq₀.length < 2048 := by
      simp only [hpq₀, ↓reduceIte, List.length_append, encodeField] at hlen₀
      omega
    simp only [hpq, hpq₀, ↓reduceIte, encodeField, List.append_assoc] at hmid
    have hvp := List.append_cancel_left hmid
    have hlen := congrArg List.length hvp
    rw [List.length_append, List.length_append,
        paddedVarint_len_lt2048 hp_lt, paddedVarint_len_lt2048 hp₀_lt] at hlen
    have hl_eq : pq.length = pq₀.length := by
      by_cases h1 : pq.length < 128 <;> by_cases h2 : pq₀.length < 128 <;>
        simp only [h1, h2, ↓reduceIte] at hlen <;> omega
    rw [hl_eq] at hvp
    exact List.append_cancel_left hvp

theorem gamma_randTerm_ne_zero (S : OpaqueSymbolSemantics) (g : Ghost) {ts sz : Nat}
    (hsz : sz ≠ 0) :
    gamma evictedI0 S g (randTerm ts sz) = g.σ ts sz := by
  have hg := ms_pack_random evictedI0 S g ⟨ts, sz⟩
  unfold gamma randTerm
  rw [hg]; dsimp only [DY.Libsignal.Composed.Refinement.gRandom, concretizeRandom]
  simp only [hsz, ↓reduceIte]; rfl

theorem prefix_eq_take {α : Type} {p coins : List α} {sz : Nat}
    (hpre : p <+: coins) (hlen : p.length = sz) :
    p = coins.take sz := by
  obtain ⟨rest, rfl⟩ := hpre
  subst hlen
  exact (List.take_left' rfl).symm

theorem gamma_litOf (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes) :
    gamma evictedI0 S g (litOf b) = b := by
  have hv_aux : ∀ l : HwBytes, (l.map UInt8.ofBitVec).map UInt8.toBitVec = l := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => exact congrArg (x :: ·) ih
  let ba := ByteArray.mk (b.map UInt8.ofBitVec).toArray
  have hg := ms_pack_lit evictedI0 S g { lit := ba }
  change gamma' evictedI0 S g (litOf b) = _ at hg
  unfold gamma
  rw [hg]; dsimp only [DY.Libsignal.Composed.Refinement.gLit0,
    DY.Libsignal.Composed.Refinement.concretizeLit, DY.Libsignal.Composed.Refinement.node]
  exact hv_aux b

private theorem forall₂_cons_right {α β : Type} {R : α → β → Prop}
    {xs : List α} {y : β} {ys : List β}
    (h : List.Forall₂ R xs (y :: ys)) :
    ∃ x xs', xs = x :: xs' ∧ R x y ∧ List.Forall₂ R xs' ys := by
  cases h with
  | cons hr hrest => exact ⟨_, _, rfl, hr, hrest⟩

private theorem forall₂_nil_right {α β : Type} {R : α → β → Prop} {xs : List α}
    (h : List.Forall₂ R xs []) : xs = [] := by
  cases h; rfl

private theorem forall₂_map_right {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β},
      List.Forall₂ R xs (ys.map f) → List.Forall₂ (fun x y => R x (f y)) xs ys
  | _, [], h => by rw [forall₂_nil_right h]; exact .nil
  | _, _ :: _, .cons hr hrest => .cons hr (forall₂_map_right hrest)

theorem drawsMatch_singleton_single {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {v : VisEntry} {coins : HwBytes} {ts sz : Nat}
    (hsz : sz ≠ 0) (hgwf : GhostWF g vis) (hmem : v ∈ vis)
    (hk : v.kind = .rng) (hl : v.layout = .single) (ht : v.terms = [randTerm ts sz])
    (hdrs : DrawsMatch evictedI0 r S g [v] coins) :
    g.σ ts sz = coins.take sz := by
  obtain ⟨pieces, _, hflat, hfa⟩ := hdrs
  obtain ⟨p₀, ps', rfl, hbme, hnil⟩ := forall₂_cons_right hfa
  rw [forall₂_nil_right hnil] at hflat
  have hp₀ : p₀ = g.σ ts sz := by
    unfold BytesMatchEntry at hbme
    rw [hl, ht] at hbme
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hbme
    rw [← hbme.2, gamma_randTerm_ne_zero S g hsz]
  have hlen : (g.σ ts sz).length = sz :=
    hgwf.1 v hmem hk ts sz hsz (by rw [ht]; exact List.mem_singleton.mpr rfl)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hflat
  rw [hp₀] at hflat
  exact prefix_eq_take hflat hlen

private theorem forall₂_append_right {α β : Type} {R : α → β → Prop} :
    ∀ (ys : List β) {zs : List β} {xs : List α},
      List.Forall₂ R xs (ys ++ zs) →
      ∃ xs₁ xs₂, xs = xs₁ ++ xs₂ ∧ List.Forall₂ R xs₁ ys ∧ List.Forall₂ R xs₂ zs
  | [], _, xs, h => ⟨[], xs, rfl, .nil, h⟩
  | _ :: ys, _, _ :: xs, .cons hr hrest => by
    obtain ⟨xs₁, xs₂, rfl, h1, h2⟩ := forall₂_append_right ys hrest
    exact ⟨_ :: xs₁, xs₂, rfl, .cons hr h1, h2⟩

private theorem kyberCoins_forall₂_aux {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {t : Bytes} :
    ∀ (idxs : List Nat) (ps : List HwBytes),
      List.Forall₂ (fun p j =>
        BytesMatchEntry evictedI0 r S g .rng p ⟨.rng, [t], .kyberCoin j, none⟩) ps idxs →
      ps.flatten.length = 4 * idxs.length ∧
      (idxs ≠ [] → (gamma evictedI0 S g t).length = 32) ∧
      ∀ k (hk : k < idxs.length),
        (gamma evictedI0 S g t)[idxs[k]'hk]? = ps.flatten[4 * k]?
  | [], [], .nil => ⟨rfl, fun h => absurd rfl h, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | j :: js, p :: ps, .cons hbme hrest => by
    obtain ⟨hflen, hlen_rest, hget_rest⟩ := kyberCoins_forall₂_aux js ps hrest
    unfold BytesMatchEntry at hbme
    obtain ⟨_, hp4, t', ht', htlen, hhead⟩ := hbme
    simp only [List.cons.injEq, and_true] at ht'
    subst ht'
    refine ⟨?_, fun _ => htlen, ?_⟩
    · simp only [List.flatten_cons, List.length_append, hp4, hflen, List.length_cons]
      omega
    · intro k hk
      cases k with
      | zero =>
        simp only [Nat.mul_zero, List.getElem_cons_zero, List.flatten_cons]
        rw [List.getElem?_append_left (by rw [hp4]; omega)]
        cases p with
        | nil => simp at hp4
        | cons b0 bs =>
          simp only [List.head?_cons, List.getElem?_cons_zero] at hhead ⊢
          exact hhead.symm
      | succ k' =>
        have hk' : k' < js.length := by simp only [List.length_cons] at hk; omega
        simp only [List.getElem_cons_succ, List.flatten_cons]
        rw [show 4 * (k' + 1) = p.length + 4 * k' by omega,
            List.getElem?_append_right (by omega),
            Nat.add_sub_cancel_left]
        exact hget_rest k' hk'

/-- `DrawsMatch` on the 34 RNG entries of `aliceStart` pins `g.σ` at timestamps `22`, `23` (strided Kyber coins), and `24`. -/
theorem drawsMatch_aliceStart {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {v24 : VisEntry} {coins : HwBytes}
    (hgwf : GhostWF g vis)
    (hsub : ∀ w ∈ rngEntry (randTerm 22 32) :: kyberCoinEntries (randTerm 23 32) ++ [v24], w ∈ vis)
    (hk24 : v24.kind = .rng) (hl24 : v24.layout = .single) (ht24 : v24.terms = [randTerm 24 32])
    (hdrs : DrawsMatch evictedI0 r S g
      (rngEntry (randTerm 22 32) :: kyberCoinEntries (randTerm 23 32) ++ [v24]) coins) :
    g.σ 22 32 = coins.take 32 ∧
    (g.σ 23 32).length = 32 ∧
    (∀ j : Nat, (h : j < 32) → (g.σ 23 32)[j]? = coins[32 + 4 * j]?) ∧
    g.σ 24 32 = (coins.drop 160).take 32 := by
  obtain ⟨pieces, _, hflat, hfa⟩ := hdrs
  simp only [List.cons_append] at hfa
  obtain ⟨p22, ps_rest, rfl, hb22, hfa_rest⟩ := forall₂_cons_right hfa
  obtain ⟨ps_kyb, ps_tail, rfl, hfa_kyb, hfa_24⟩ :=
    forall₂_append_right (kyberCoinEntries (randTerm 23 32)) hfa_rest
  obtain ⟨p24, ps_nil, rfl, hb24, hnil⟩ := forall₂_cons_right hfa_24
  rw [forall₂_nil_right hnil] at hflat
  have hp22 : p22 = g.σ 22 32 := by
    unfold BytesMatchEntry rngEntry at hb22
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hb22
    rw [← hb22.2, gamma_randTerm_ne_zero S g (by decide)]
  have hlen22 : (g.σ 22 32).length = 32 :=
    hgwf.1 (rngEntry (randTerm 22 32)) (hsub _ List.mem_cons_self) rfl 22 32 (by decide)
      (List.mem_singleton.mpr rfl)
  have hp24 : p24 = g.σ 24 32 := by
    unfold BytesMatchEntry at hb24
    rw [hl24, ht24] at hb24
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hb24
    rw [← hb24.2, gamma_randTerm_ne_zero S g (by decide)]
  have hlen24 : (g.σ 24 32).length = 32 :=
    hgwf.1 v24 (hsub _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))))
      hk24 24 32 (by decide) (by rw [ht24]; exact List.mem_singleton.mpr rfl)
  unfold kyberCoinEntries at hfa_kyb
  have hfa_kyb' := forall₂_map_right hfa_kyb
  obtain ⟨hflen_kyb, hlen23_g, hget_kyb⟩ := kyberCoins_forall₂_aux (List.range 32) ps_kyb hfa_kyb'
  simp only [List.length_range] at hflen_kyb hget_kyb
  have hg23 : gamma evictedI0 S g (randTerm 23 32) = g.σ 23 32 :=
    gamma_randTerm_ne_zero S g (by decide)
  have hlen23 : (g.σ 23 32).length = 32 := hg23 ▸ hlen23_g (by decide)
  obtain ⟨rest_c, hcoins_eq⟩ := hflat
  simp only [List.flatten_cons, List.flatten_append, List.flatten_nil,
    List.append_nil, List.append_assoc] at hcoins_eq
  rw [hp22, hp24] at hcoins_eq
  refine ⟨?_, hlen23, ?_, ?_⟩
  · rw [← hcoins_eq]
    exact (List.take_left' hlen22).symm
  · intro j hj
    have hgk := hget_kyb j hj
    simp only [List.getElem_range, hg23] at hgk
    rw [hgk, ← hcoins_eq,
        show 32 + 4 * j = (g.σ 22 32).length + 4 * j by omega,
        List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left,
        List.getElem?_append_left (by omega)]
  · rw [← hcoins_eq,
        show (160 : Nat) = (g.σ 22 32 ++ ps_kyb.flatten).length by
          rw [List.length_append, hlen22, hflen_kyb],
        ← List.append_assoc, List.drop_left,
        List.take_left' hlen24]

theorem gamma_spqrSend_key_length (S : OpaqueSymbolSemantics) (g : Ghost) (spqr c : Bytes) :
    (gamma evictedI0 S g (DY.Spqr.spqrSend spqr c).2.1).length = 32 := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · unfold gamma gamma' DY.Spqr.spqrChainKey
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.gSpqrChainKey S)
      (DY.Libsignal.Composed.Refinement.gAll evictedI0 S g)]
    exact ShaMacLaws.spqrKeyBytes_length _
  · exact gamma_spqrSendKey_length S g spqr c

/-- Recovers the `gamma` bytes of both the SPQR message key (via `computeMac` salt pinning on an
untagged MAC) and the SPQR wire payload (via `trWireBytes` injectivity) from `encMsg`. -/
theorem encMsg_pins_pqKey_and_pqMsg
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {coins : Bytes} {ptTs : Nat}
    {salt₀ seed₀ rk₀ myIk₀ peerIk₀ pt₀ addr₀ pqm₀ ckey₀ iv₀ ct₀ wire₀ mac₀ : HwBytes}
    (hpq_eq : let pq := (DY.Spqr.spqrSend st.spqr coins).2.1; pq = pq)
    (hmsg : gamma evictedI0 S g
        (encMsg st coins (DY.Spqr.spqrSend st.spqr coins).2.1 (randTerm ptTs 32)) =
      wire₀ ++ mac₀)
    (hmac_len : mac₀.length = 8)
    (hsalt_len : salt₀.length = 32)
    (huntag : mac₀.take 4 ≠ compTag4)
    (hseed : gamma evictedI0 S g (kdfCk st.cks).2 = seed₀)
    (hrk : gamma evictedI0 S g (dhPk st.dhs) = rk₀)
    (_hmyIk : gamma evictedI0 S g st.myIk = myIk₀)
    (_hpeerIk : gamma evictedI0 S g st.peerIk = peerIk₀)
    (hpt : g.σ ptTs 32 = pt₀)
    (haddr : g.addr
      (trHonestWireMsg (dhPk st.dhs) st.ns st.pn
        (DY.SymEnc.symEnc
          (trMsgKeys (DY.Spqr.spqrSend st.spqr coins).2.1 (kdfCk st.cks).2).cipherKey
          (trMsgKeys (DY.Spqr.spqrSend st.spqr coins).2.1 (kdfCk st.cks).2).iv
          (randTerm ptTs 32))
        (DY.Spqr.spqrSend st.spqr coins).2.2) = addr₀)
    (hmac₀_eq : mac₀ =
      gamma evictedI0 S g
        (computeMac (trMsgKeys (litOf salt₀) (litOf seed₀)).macKey
          (litOf myIk₀) (litOf peerIk₀) (litOf wire₀)))
    (hckey₀ : gamma evictedI0 S g (trMsgKeys (litOf salt₀) (litOf seed₀)).cipherKey = ckey₀)
    (hiv₀ : gamma evictedI0 S g (trMsgKeys (litOf salt₀) (litOf seed₀)).iv = iv₀)
    (hct₀ : evictedAesPerm ckey₀ (iv₀.take 16) pt₀ = ct₀)
    (hwire₀ : trWireBytes addr₀ canonicalVariation
      { version := messageVersion.toNat, ratchetKey := rk₀, counter := st.ns.toNat,
        previousCounter := st.pn.toNat, ciphertext := ct₀ } pqm₀ = wire₀)
    (hwire₀_lt : wire₀.length < 2048) :
    gamma evictedI0 S g (DY.Spqr.spqrSend st.spqr coins).2.1 = salt₀ ∧
    gamma evictedI0 S g (DY.Spqr.spqrSend st.spqr coins).2.2 = pqm₀ := by
  let _ := hpq_eq
  set pq := (DY.Spqr.spqrSend st.spqr coins).2.1
  set pqm := (DY.Spqr.spqrSend st.spqr coins).2.2
  set keys := trMsgKeys pq (kdfCk st.cks).2
  set wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) pqm
  unfold encMsg at hmsg
  rw [gamma_concatE] at hmsg
  have hgmac_len : (gamma evictedI0 S g (computeMac keys.macKey st.myIk st.peerIk wire)).length = 8 := by
    unfold computeMac
    rw [gamma_trunc8E, List.length_take, gamma_hmacE_length]; rfl
  obtain ⟨hwire_eq, hmac_eq⟩ := append_inj_right_len hmsg (hgmac_len.trans hmac_len.symm)
  have hlit_len : (gamma evictedI0 S g (litOf salt₀)).length = 32 := by
    rw [gamma_litOf]; exact hsalt_len
  have hpq_len : (gamma evictedI0 S g pq).length = 32 :=
    gamma_spqrSend_key_length S g st.spqr coins
  have hpins := computeMac_pins_salt_and_seed hpq_len hlit_len
    (hmac_eq.symm ▸ huntag) (hmac_eq.trans hmac₀_eq)
  have hpq_pin : gamma evictedI0 S g pq = salt₀ :=
    hpins.1.trans (gamma_litOf S g salt₀)
  have hprk_eq : gamma evictedI0 S g (DY.Libsignal.TripleRatchet.hmac pq (kdfCk st.cks).2) =
      gamma evictedI0 S g (DY.Libsignal.TripleRatchet.hmac (litOf salt₀) (litOf seed₀)) := by
    rw [gamma_hmacE, gamma_hmacE, hpq_pin, hseed, gamma_litOf, gamma_litOf]
  obtain ⟨hck_eq, _, hiv_eq⟩ := gamma_trMsgKeys_congr_prk hprk_eq
  have hct_eq : gamma evictedI0 S g (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) = ct₀ := by
    have hg := ms_pack_sym evictedI0 S g ⟨keys.cipherKey, keys.iv, randTerm ptTs 32⟩
    change gamma' evictedI0 S g (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) = _ at hg
    unfold gamma
    rw [hg]; dsimp only [DY.Libsignal.Composed.Refinement.gSym0, concretizeSym,
      DY.Libsignal.Composed.Refinement.node]
    change evictedAesPerm (gamma evictedI0 S g keys.cipherKey)
      ((gamma evictedI0 S g keys.iv).take 16)
      (gamma evictedI0 S g (randTerm ptTs 32)) = ct₀
    rw [hck_eq, hckey₀, hiv_eq, hiv₀, gamma_randTerm_ne_zero S g (by decide), hpt, hct₀]
  have hgw : gamma evictedI0 S g wire =
      trWireBytes addr₀ canonicalVariation
        { version := messageVersion.toNat, ratchetKey := rk₀, counter := st.ns.toNat,
          previousCounter := st.pn.toNat, ciphertext := ct₀ }
        (gamma evictedI0 S g pqm) := by
    have hg := ms_pack_trWire evictedI0 S g
      ⟨messageVersion, dhPk st.dhs, st.ns, st.pn,
       DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32), pqm, canonicalVariation⟩
    change gamma' evictedI0 S g wire = _ at hg
    have haddr' : g.addr (DY.BytesView.pack (SubF := DY.TrWire.TrWireMsg.SubF)
      ⟨messageVersion, dhPk st.dhs, st.ns, st.pn,
       DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32), pqm, canonicalVariation⟩) = addr₀ := haddr
    unfold gamma
    rw [hg]; dsimp only [DY.Libsignal.Composed.Refinement.gTrWire0, concretizeTrWire,
      DY.Libsignal.Composed.Refinement.node]
    rw [haddr']
    change trWireBytes addr₀ canonicalVariation
      { version := messageVersion.toNat,
        ratchetKey := gamma evictedI0 S g (dhPk st.dhs),
        counter := st.ns.toNat,
        previousCounter := st.pn.toNat,
        ciphertext := gamma evictedI0 S g (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) }
      (gamma evictedI0 S g pqm) = _
    rw [hrk, hct_eq]; rfl
  have hpqm_pin : gamma evictedI0 S g pqm = pqm₀ :=
    trWireBytes_canonical_pq_inj (hwire₀.symm ▸ hwire₀_lt) (hgw.symm.trans (hwire_eq.trans hwire₀.symm))
  exact ⟨hpq_pin, hpqm_pin⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins0
