/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure -- proof-setup: allow-public-import

/-!
# `Tier2GsRel` Transition Proofs and `Hop2TblRel` Helpers

Proves `Tier2GsRel` preservation for initialization, `record`, `delete`, and `accept`, and defines
the `Hop2TblRel` association-list table invariant.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs

open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record GameState)
open CryptoGames.LibsignalSession (PublicKey GhostState)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (spkMaxWireLen spkWireChunks
  wireKeyVal_eq_some_of_le spkWireKeyVal ptKeyVal ptKeyVal_injective)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (headOf ChainLinks
  dllPushPrev dllPushNext chainLinks_push dllUnlinkHead dllUnlinkPrev dllUnlinkNext
  chainLinks_unlink Tier2Gs updParty updParty_self updParty_ne updParty_eq_update updTbl1
  updPosTbl updPosTbl_self updPosTbl_ne posBound posBound_ne_next posBound_mono_epoch bucketIds
  Tier2GsRel)

/-! ## Initialization -/

theorem tier2GsRel_init_pair {ℓ : ℕ} (stA stB : GhostState Bytes) (b : Bool) :
    Tier2GsRel ℓ
      ({ st := fun | .A => stA | .B => stB, b := b } :
        GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (Tier2Gs.init stA stB b) where
  h_st := rfl
  h_b := rfl
  h_win := rfl
  h_epoch := rfl
  h_idx := rfl
  h_tL := rfl
  h_maxAcc := rfl
  h_pos_trans := by simp
  h_pos_chall := by simp
  h_pos_comp := by simp
  h_trans_nodup := by simp
  h_chall_nodup := by simp
  h_nextId_pos := Nat.le_refl 1
  h_node0 := rfl
  h_posNode_zero_iff := by simp [Tier2Gs.init]
  h_trans_nodes := by simp
  h_head := by intro P key; simp [Tier2Gs.init, bucketIds, headOf]
  h_chain := by intro P key; simp [bucketIds, ChainLinks]
  h_challTbl := by simp [Tier2Gs.init]
  h_challCount := by simp [Tier2Gs.init]
  h_compTbl := by simp [Tier2Gs.init]
  h_uncompCount := by simp [Tier2Gs.init]

/-! ## Transition preservation -/

theorem tier2GsRel_record_preserves {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (Δ : ℕ) (P : Party)
    (st' : GhostState Bytes) (r : Record (Plain ℓ) Bytes) (isChall : Bool)
    (hpos : r.pos = ⟨P, gs.epoch P, gs.idx P + 1⟩)
    (hlen : r.ct.length ≤ spkMaxWireLen ℓ) :
    Tier2GsRel ℓ (gs.record Δ P st' r isChall) (d.record Δ P st' r isChall) := by
  obtain ⟨k0, hwk⟩ : ∃ k0, spkWireKeyVal ℓ r.ct = some k0 :=
    ⟨_, wireKeyVal_eq_some_of_le (n := spkWireChunks ℓ) hlen⟩
  have hr_sender : r.pos.sender = P := by rw [hpos]
  have hr_epoch : r.pos.epoch = gs.epoch P := by rw [hpos]
  have hr_idx : r.pos.idx = gs.idx P + 1 := by rw [hpos]
  have hr_not_trans : ∀ r' ∈ gs.trans, r'.pos ≠ r.pos :=
    fun r' hr' => hpos ▸ posBound_ne_next gs.epoch gs.idx P (hrel.h_pos_trans r' hr')
  have hr_not_chall : r.pos ∉ gs.chall :=
    fun hm => posBound_ne_next gs.epoch gs.idx P (hrel.h_pos_chall r.pos hm) hpos
  have hr_not_comp : r.pos ∉ gs.comp :=
    fun hm => posBound_ne_next gs.epoch gs.idx P (hrel.h_pos_comp r.pos hm) hpos
  have hpos_upd : ∀ q : Pos, posBound gs.epoch gs.idx q →
      posBound gs.epoch (Function.update gs.idx P r.pos.idx) q := by
    intro q hq
    by_cases hqs : q.sender = P
    · rcases hq with hlt | ⟨he, hi⟩
      · exact Or.inl hlt
      · right; refine ⟨he, ?_⟩
        rw [hqs, Function.update_self, hr_idx]
        have := hqs ▸ hi; omega
    · rcases hq with hlt | ⟨he, hi⟩
      · exact Or.inl hlt
      · right; rw [Function.update_of_ne hqs]; exact ⟨he, hi⟩
  have hr_posBound : posBound gs.epoch (Function.update gs.idx P r.pos.idx) r.pos := by
    right; rw [hr_sender, hr_epoch, Function.update_self]; exact ⟨rfl, Nat.le_refl _⟩
  have hsafe := hrel.safeCh_eq Δ P
  set gs' := gs.record Δ P st' r isChall
  set d' := d.record Δ P st' r isChall
  have hd' : d' =
      { d with
        st := updParty d.st P st'
        idx := updParty d.idx P r.pos.idx
        nextId := d.nextId + 1
        headTbl := updTbl1 d.headTbl P k0 d.nextId
        nodeRec := fun j => if j = d.nextId then some r else d.nodeRec j
        nodeKey := fun j => if j = d.nextId then k0 else d.nodeKey j
        nodePrev := dllPushPrev (d.headTbl P k0) d.nextId d.nodePrev
        nodeNext := dllPushNext (d.headTbl P k0) d.nextId d.nodeNext
        posNode := updPosTbl d.posNode r.pos d.nextId
        challTbl := if isChall then updPosTbl d.challTbl r.pos true else d.challTbl
        challCount := if isChall then updParty d.challCount P (d.challCount P + 1) else d.challCount
        compTbl := if gs.safeCh Δ P then d.compTbl else updPosTbl d.compTbl r.pos true
        uncompCount := if gs.safeCh Δ P then updParty d.uncompCount P (d.uncompCount P + 1) else d.uncompCount } := by
    simp [d', Tier2Gs.record, hwk, hsafe]
  have hbucket_tail : ∀ Q k,
      (gs.trans.filter (fun r' => (r'.pos.sender == Q) &&
        decide (spkWireKeyVal ℓ r'.ct = some k))).map
          (fun r' => d'.posNode r'.pos.sender r'.pos.epoch r'.pos.idx) =
      bucketIds gs d Q k := by
    intro Q k
    refine List.map_congr_left fun r' hr' => ?_
    have hm := (List.mem_filter.mp hr').1
    rw [hd']; dsimp only
    exact updPosTbl_ne d.posNode r.pos r'.pos d.nextId (hr_not_trans r' hm)
  have hbucket_eq : ∀ Q k,
      bucketIds gs' d' Q k =
        if Q = P ∧ k = k0 then d.nextId :: bucketIds gs d P k0
        else bucketIds gs d Q k := by
    intro Q k
    change ((r :: gs.trans).filter (fun r' => (r'.pos.sender == Q) &&
      decide (spkWireKeyVal ℓ r'.ct = some k))).map
        (fun r' => d'.posNode r'.pos.sender r'.pos.epoch r'.pos.idx) = _
    by_cases hqk : Q = P ∧ k = k0
    · rcases hqk with ⟨rfl, rfl⟩
      have hcond : ((r.pos.sender == Q) && decide (spkWireKeyVal ℓ r.ct = some k)) = true := by
        rw [hr_sender, beq_self_eq_true, Bool.true_and, decide_eq_true hwk]
      simp only [List.filter_cons, hcond, ↓reduceIte, List.map_cons, hbucket_tail Q k, and_self]
      rw [hd']; dsimp only; rw [updPosTbl_self]
    · have hcond : ((r.pos.sender == Q) && decide (spkWireKeyVal ℓ r.ct = some k)) = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        rcases Bool.and_eq_true_iff.mp htrue with ⟨hq_b, hk_b⟩
        have hq : Q = P := (beq_iff_eq.mp hq_b).symm.trans hr_sender
        have hk : k = k0 := Option.some.inj ((of_decide_eq_true hk_b).symm.trans hwk)
        exact hqk ⟨hq, hk⟩
      simp only [List.filter_cons, hcond, Bool.false_eq_true, ↓reduceIte, hbucket_tail Q k, hqk]
  refine {
    h_st := by rw [hd']; dsimp only [gs', GameState.record]; rw [hrel.h_st, updParty_eq_update]
    h_b := by rw [hd']; dsimp only [gs', GameState.record]; exact hrel.h_b
    h_win := by rw [hd']; dsimp only [gs', GameState.record]; exact hrel.h_win
    h_epoch := by rw [hd']; dsimp only [gs', GameState.record]; exact hrel.h_epoch
    h_idx := by rw [hd']; dsimp only [gs', GameState.record]; rw [hrel.h_idx, updParty_eq_update]
    h_tL := by rw [hd']; dsimp only [gs', GameState.record]; exact hrel.h_tL
    h_maxAcc := by rw [hd']; dsimp only [gs', GameState.record]; exact hrel.h_maxAcc
    h_pos_trans := fun r' hr' => by
      rcases List.mem_cons.mp hr' with rfl | hm
      · exact hr_posBound
      · exact hpos_upd r'.pos (hrel.h_pos_trans r' hm)
    h_pos_chall := fun p hp => by
      dsimp only [gs', GameState.record] at hp
      split_ifs at hp with hc
      · rcases List.mem_cons.mp hp with rfl | hm
        · exact hr_posBound
        · exact hpos_upd p (hrel.h_pos_chall p hm)
      · exact hpos_upd p (hrel.h_pos_chall p hp)
    h_pos_comp := fun p hp => by
      dsimp only [gs', GameState.record] at hp
      split_ifs at hp with hs0
      · exact hpos_upd p (hrel.h_pos_comp p hp)
      · rcases List.mem_cons.mp hp with rfl | hm
        · exact hr_posBound
        · exact hpos_upd p (hrel.h_pos_comp p hm)
    h_trans_nodup := by
      change (r.pos :: gs.trans.map Record.pos).Nodup
      refine List.nodup_cons.mpr ⟨?_, hrel.h_trans_nodup⟩
      intro hm
      rcases List.mem_map.mp hm with ⟨r', hr', heq⟩
      exact hr_not_trans r' hr' heq
    h_chall_nodup := by
      dsimp only [gs', GameState.record]
      split_ifs
      · exact List.nodup_cons.mpr ⟨hr_not_chall, hrel.h_chall_nodup⟩
      · exact hrel.h_chall_nodup
    h_nextId_pos := by rw [hd']; dsimp only; have := hrel.h_nextId_pos; omega
    h_node0 := by
      rw [hd']; dsimp only
      have hne : (0 : ℕ) ≠ d.nextId := by have := hrel.h_nextId_pos; omega
      simp [hne, hrel.h_node0]
    h_posNode_zero_iff := fun p => by
      rw [hd']; dsimp only
      by_cases hp : p = r.pos
      · subst hp
        rw [updPosTbl_self]
        have hne : d.nextId ≠ 0 := by have := hrel.h_nextId_pos; omega
        constructor
        · intro h0; exact absurd h0 hne
        · intro hall; exact absurd rfl (hall r List.mem_cons_self)
      · rw [updPosTbl_ne d.posNode r.pos p d.nextId hp, hrel.h_posNode_zero_iff p]
        constructor
        · intro hall r' hr'
          rcases List.mem_cons.mp hr' with rfl | hm
          · exact Ne.symm hp
          · exact hall r' hm
        · intro hall r' hm
          exact hall r' (List.mem_cons_of_mem r hm)
    h_trans_nodes := fun r' hr' => by
      rw [hd']; dsimp only
      rcases List.mem_cons.mp hr' with rfl | hm
      · rw [updPosTbl_self]
        exact ⟨hrel.h_nextId_pos, Nat.lt_succ_self _, by simp, by simp [hwk]⟩
      · rw [updPosTbl_ne d.posNode r.pos r'.pos d.nextId (hr_not_trans r' hm)]
        obtain ⟨h1, hlt, hrec, hkey⟩ := hrel.h_trans_nodes r' hm
        have hne_id : d.posNode r'.pos.sender r'.pos.epoch r'.pos.idx ≠ d.nextId :=
          Nat.ne_of_lt hlt
        exact ⟨h1, Nat.lt_succ_of_lt hlt, by simp [hne_id, hrec], by simp [hne_id, hkey]⟩
    h_head := fun Q k => by
      rw [hbucket_eq Q k, hd']; dsimp only [updTbl1]
      by_cases hq : Q = P
      · subst hq
        rw [updParty_self]
        by_cases hk : k = k0
        · subst hk; simp [headOf]
        · simp [hk, hrel.h_head]
      · rw [updParty_ne _ _ hq]; simp [hq, hrel.h_head]
    h_chain := fun Q k => by
      rw [hbucket_eq Q k, hd']; dsimp only
      by_cases hqk : Q = P ∧ k = k0
      · rcases hqk with ⟨rfl, rfl⟩
        simp only [and_self, ↓reduceIte]
        rw [hrel.h_head Q k]
        exact chainLinks_push (hrel.h_chain Q k) (hrel.bucketIds_nodup Q k)
          (hrel.bucketIds_pos Q k) (fun hm => Nat.lt_irrefl _ (hrel.bucketIds_lt_nextId Q k _ hm))
      · simp only [hqk, ↓reduceIte]
        refine (hrel.h_chain Q k).congr fun x hx => ?_
        have hx_lt := hrel.bucketIds_lt_nextId Q k x hx
        have hx_ne_new : x ≠ d.nextId := Nat.ne_of_lt hx_lt
        by_cases hhd0 : d.headTbl P k0 = 0
        · simp [dllPushPrev, dllPushNext, hhd0, hx_ne_new]
        · have hhd_mem : d.headTbl P k0 ∈ bucketIds gs d P k0 := by
            have hh := hrel.h_head P k0
            rw [hh] at hhd0 ⊢
            cases hnil : bucketIds gs d P k0 with
            | nil => rw [hnil] at hhd0; exact absurd rfl hhd0
            | cons z zs => exact List.mem_cons_self
          have hx_ne_hd : x ≠ d.headTbl P k0 := by
            intro heq
            rw [heq] at hx
            obtain ⟨r₁, _, hrec₁, hs₁, hk₁⟩ := hrel.bucketIds_party_key hx
            obtain ⟨r₂, _, hrec₂, hs₂, hk₂⟩ := hrel.bucketIds_party_key hhd_mem
            have hr12 : r₁ = r₂ := Option.some.inj (hrec₁.symm.trans hrec₂)
            subst hr12
            exact hqk ⟨hs₁.symm.trans hs₂, hk₁.symm.trans hk₂⟩
          simp [dllPushPrev, dllPushNext, hhd0, hx_ne_new, hx_ne_hd]
    h_challTbl := fun p => by
      rw [hd']; dsimp only [gs', GameState.record]
      cases isChall
      · simp [hrel.h_challTbl p]
      · simp only [↓reduceIte, List.contains_cons]
        by_cases hp : p = r.pos
        · subst hp; simp
        · rw [updPosTbl_ne _ _ _ _ hp, hrel.h_challTbl p]
          have hbeq : (p == r.pos) = false := beq_eq_false_iff_ne.mpr hp
          simp [hbeq]
    h_challCount := fun Q => by
      rw [hd']; dsimp only [gs', GameState.record]
      cases isChall
      · simp [hrel.h_challCount Q]
      · simp only [↓reduceIte, List.countP_cons, hr_sender]
        by_cases hq : Q = P
        · subst hq; simp [hrel.h_challCount]
        · rw [updParty_ne _ _ hq, hrel.h_challCount Q]
          have hbeq : (P == Q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
          simp [hbeq]
    h_compTbl := fun p => by
      rw [hd']; dsimp only [gs', GameState.record]
      cases hsc : gs.safeCh Δ P
      · simp only [Bool.false_eq_true, ↓reduceIte, List.contains_cons]
        by_cases hp : p = r.pos
        · subst hp; simp
        · rw [updPosTbl_ne _ _ _ _ hp, hrel.h_compTbl p]
          have hbeq : (p == r.pos) = false := beq_eq_false_iff_ne.mpr hp
          simp [hbeq]
      · simp [hrel.h_compTbl p]
    h_uncompCount := fun Q => by
      rw [hd']; dsimp only [gs', GameState.record]
      cases hsc : gs.safeCh Δ P
      · simp only [Bool.false_eq_true, ↓reduceIte, List.countP_cons]
        have hhead_f : ((r.pos.sender == Q) && !(r.pos :: gs.comp).contains r.pos) = false := by
          rw [List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.not_true, Bool.and_false]
        have htail : gs.trans.countP (fun r' => (r'.pos.sender == Q) &&
            !(r.pos :: gs.comp).contains r'.pos) =
            gs.trans.countP (fun r' => (r'.pos.sender == Q) && !gs.comp.contains r'.pos) := by
          refine List.countP_congr fun r' hr' => ?_
          have hbeq : (r'.pos == r.pos) = false := beq_eq_false_iff_ne.mpr (hr_not_trans r' hr')
          rw [List.contains_cons, hbeq, Bool.false_or]
        rw [hhead_f, htail, hrel.h_uncompCount Q]
        simp
      · simp only [↓reduceIte, List.countP_cons, hr_sender]
        have hr_cont : gs.comp.contains r.pos = false := by
          rw [Bool.eq_false_iff]; intro hc
          exact hr_not_comp (List.contains_iff_mem.mp hc)
        rw [hr_cont, Bool.not_false, Bool.and_true]
        by_cases hq : Q = P
        · subst hq
          rw [updParty_self, beq_self_eq_true, hrel.h_uncompCount]
          simp
        · rw [updParty_ne _ _ hq, hrel.h_uncompCount Q]
          have hbeq : (P == Q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
          simp [hbeq] }

private theorem countP_filter_ne_of_nodup {α : Type} [DecidableEq α] {L : List α}
    (hnd : L.Nodup) (x0 : α) (f : α → Bool) :
    (L.filter (fun x => x != x0)).countP f =
      if x0 ∈ L ∧ f x0 = true then L.countP f - 1 else L.countP f := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨hy_not, hnd_ys⟩ := List.nodup_cons.mp hnd
    by_cases hy : y = x0
    · subst hy
      have hfilt : (y :: ys).filter (fun x => x != y) = ys := by
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact List.filter_eq_self.mpr fun z hz =>
          bne_iff_ne.mpr (fun h => hy_not (h ▸ hz))
      rw [hfilt, List.countP_cons]
      cases f y <;> simp
    · have hne_b : (y != x0) = true := bne_iff_ne.mpr hy
      simp only [List.filter_cons, hne_b, ↓reduceIte, List.countP_cons, ih hnd_ys]
      have hmem_iff : x0 ∈ y :: ys ↔ x0 ∈ ys :=
        ⟨fun hm => (List.mem_cons.mp hm).resolve_left (Ne.symm hy), List.mem_cons_of_mem y⟩
      simp only [hmem_iff]
      by_cases hcond : x0 ∈ ys ∧ f x0 = true
      · have hpos : 0 < ys.countP f := List.countP_pos_iff.mpr ⟨x0, hcond.1, hcond.2⟩
        simp only [hcond, and_self, ↓reduceIte]
        cases f y <;> omega
      · simp [hcond]

private theorem countP_filter_pos_ne {ℓ : ℕ} :
    ∀ {trs : List (Record (Plain ℓ) Bytes)},
      (trs.map Record.pos).Nodup →
      ∀ (p0 : Pos) (f : Record (Plain ℓ) Bytes → Bool),
        (trs.filter (fun r => r.pos != p0)).countP f =
          match trs.find? (fun r => r.pos == p0) with
          | none => trs.countP f
          | some r0 => if f r0 = true then trs.countP f - 1 else trs.countP f
  | [], _, _, _ => rfl
  | r :: rs, hnd, p0, f => by
    obtain ⟨hr_not, hnd_rs⟩ := List.nodup_cons.mp hnd
    by_cases hrp : r.pos = p0
    · subst hrp
      have hfilt : (r :: rs).filter (fun r' => r'.pos != r.pos) = rs := by
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        refine List.filter_eq_self.mpr fun r' hr' => bne_iff_ne.mpr ?_
        intro heq; exact hr_not (List.mem_map.mpr ⟨r', hr', heq⟩)
      simp only [hfilt, List.find?_cons, beq_self_eq_true, List.countP_cons]
      cases f r <;> simp
    · have hbeq : (r.pos == p0) = false := beq_eq_false_iff_ne.mpr hrp
      have hbne : (r.pos != p0) = true := bne_iff_ne.mpr hrp
      simp only [List.filter_cons, hbne, ↓reduceIte, List.find?_cons, hbeq, List.countP_cons,
        countP_filter_pos_ne hnd_rs p0 f]
      cases hfind : rs.find? (fun r' => r'.pos == p0) with
      | none => rfl
      | some r0 =>
        have hr0_mem : r0 ∈ rs := List.mem_of_find?_eq_some hfind
        by_cases hfr0 : f r0 = true
        · have hpos : 0 < rs.countP f := List.countP_pos_iff.mpr ⟨r0, hr0_mem, hfr0⟩
          simp only [hfr0, ↓reduceIte]
          cases f r <;> omega
        · simp [hfr0]

theorem tier2GsRel_delete_preserves {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (p0 : Pos) :
    Tier2GsRel ℓ (gs.delete p0) (d.delete p0) := by
  have hchall_tbl : ∀ p : Pos,
      updPosTbl d.challTbl p0 false p.sender p.epoch p.idx =
        (gs.chall.filter (fun q => q != p0)).contains p := by
    intro p
    by_cases hp : p = p0
    · subst hp; simp [List.mem_filter]
    · rw [updPosTbl_ne _ _ _ _ hp, hrel.h_challTbl p]
      simp [List.mem_filter, bne_iff_ne, hp]
  have hcomp_tbl : ∀ p : Pos,
      updPosTbl d.compTbl p0 false p.sender p.epoch p.idx =
        (gs.comp.filter (fun q => q != p0)).contains p := by
    intro p
    by_cases hp : p = p0
    · subst hp; simp [List.mem_filter]
    · rw [updPosTbl_ne _ _ _ _ hp, hrel.h_compTbl p]
      simp [List.mem_filter, bne_iff_ne, hp]
  have hchall_cnt : ∀ Q : Party,
      (if d.challTbl p0.sender p0.epoch p0.idx then
        updParty d.challCount p0.sender (d.challCount p0.sender - 1)
       else d.challCount) Q =
        (gs.chall.filter (fun q => q != p0)).countP (fun q => q.sender == Q) := by
    intro Q
    rw [hrel.h_challTbl p0, countP_filter_ne_of_nodup hrel.h_chall_nodup p0]
    cases hmem : gs.chall.contains p0
    · have hnot : p0 ∉ gs.chall := fun hm => by
        rw [List.contains_iff_mem.mpr hm] at hmem; cases hmem
      simp [hnot, hrel.h_challCount Q]
    · have hin : p0 ∈ gs.chall := List.contains_iff_mem.mp hmem
      simp only [↓reduceIte, hin, true_and]
      by_cases hq : Q = p0.sender
      · subst hq; simp [hrel.h_challCount]
      · rw [updParty_ne _ _ hq, hrel.h_challCount Q]
        have hbeq : (p0.sender == Q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
        simp [hbeq]
  by_cases hid0 : d.posNode p0.sender p0.epoch p0.idx = 0
  · have hall_ne : ∀ r ∈ gs.trans, r.pos ≠ p0 := (hrel.h_posNode_zero_iff p0).mp hid0
    have htrans_eq : gs.trans.filter (fun r => r.pos != p0) = gs.trans :=
      List.filter_eq_self.mpr fun r hr => bne_iff_ne.mpr (hall_ne r hr)
    have hd_eq : d.delete p0 =
        { d with
          challTbl := updPosTbl d.challTbl p0 false
          challCount := if d.challTbl p0.sender p0.epoch p0.idx then
              updParty d.challCount p0.sender (d.challCount p0.sender - 1) else d.challCount
          compTbl := updPosTbl d.compTbl p0 false } := by
      simp [Tier2Gs.delete, hid0]
    rw [hd_eq]
    refine {
      h_st := hrel.h_st
      h_b := hrel.h_b
      h_win := hrel.h_win
      h_epoch := hrel.h_epoch
      h_idx := hrel.h_idx
      h_tL := hrel.h_tL
      h_maxAcc := hrel.h_maxAcc
      h_pos_trans := fun r hr => hrel.h_pos_trans r (List.mem_of_mem_filter hr)
      h_pos_chall := fun p hp => hrel.h_pos_chall p (List.mem_of_mem_filter hp)
      h_pos_comp := fun p hp => hrel.h_pos_comp p (List.mem_of_mem_filter hp)
      h_trans_nodup := by dsimp only [GameState.delete]; rw [htrans_eq]; exact hrel.h_trans_nodup
      h_chall_nodup := hrel.h_chall_nodup.filter _
      h_nextId_pos := hrel.h_nextId_pos
      h_node0 := hrel.h_node0
      h_posNode_zero_iff := fun p => by
        dsimp only [GameState.delete]; rw [htrans_eq]; exact hrel.h_posNode_zero_iff p
      h_trans_nodes := fun r hr => by
        dsimp only [GameState.delete] at hr; rw [htrans_eq] at hr; exact hrel.h_trans_nodes r hr
      h_head := fun Q k => by
        dsimp only; unfold bucketIds; dsimp only [GameState.delete]; rw [htrans_eq]
        exact hrel.h_head Q k
      h_chain := fun Q k => by
        dsimp only; unfold bucketIds; dsimp only [GameState.delete]; rw [htrans_eq]
        exact hrel.h_chain Q k
      h_challTbl := hchall_tbl
      h_challCount := hchall_cnt
      h_compTbl := hcomp_tbl
      h_uncompCount := fun Q => by
        dsimp only [GameState.delete]
        rw [htrans_eq, hrel.h_uncompCount Q]
        refine List.countP_congr fun r hr => ?_
        have hne := hall_ne r hr
        have hc : (gs.comp.filter (fun q => q != p0)).contains r.pos = gs.comp.contains r.pos := by
          simp [List.mem_filter, bne_iff_ne, hne]
        rw [hc] }
  · set idDel := d.posNode p0.sender p0.epoch p0.idx
    have hex_r0 : ∃ r0 ∈ gs.trans, r0.pos = p0 := by
      by_contra hno
      exact hid0 ((hrel.h_posNode_zero_iff p0).mpr (fun r hr heq => hno ⟨r, hr, heq⟩))
    rcases hex_r0 with ⟨r0, hr0_mem, hr0_pos⟩
    obtain ⟨hid_pos, _, hr0_rec, hr0_wk⟩ := hrel.h_trans_nodes r0 hr0_mem
    have hidDel_eq : d.posNode r0.pos.sender r0.pos.epoch r0.pos.idx = idDel := by
      rw [hr0_pos]
    rw [hidDel_eq] at hid_pos hr0_rec hr0_wk
    set k0 := d.nodeKey idDel
    have hd_eq : d.delete p0 =
        { d with
          headTbl := updTbl1 d.headTbl p0.sender k0
            (dllUnlinkHead (d.headTbl p0.sender k0) (d.nodePrev idDel) (d.nodeNext idDel))
          nodePrev := dllUnlinkPrev (d.nodePrev idDel) (d.nodeNext idDel) d.nodePrev
          nodeNext := dllUnlinkNext (d.nodePrev idDel) (d.nodeNext idDel) d.nodeNext
          posNode := updPosTbl d.posNode p0 0
          challTbl := updPosTbl d.challTbl p0 false
          challCount := if d.challTbl p0.sender p0.epoch p0.idx then
              updParty d.challCount p0.sender (d.challCount p0.sender - 1) else d.challCount
          compTbl := updPosTbl d.compTbl p0 false
          uncompCount := if d.compTbl p0.sender p0.epoch p0.idx then d.uncompCount
              else updParty d.uncompCount p0.sender (d.uncompCount p0.sender - 1) } := by
      simp [Tier2Gs.delete, idDel, hid0, k0]
    have hid_iff_pos : ∀ r ∈ gs.trans,
        d.posNode r.pos.sender r.pos.epoch r.pos.idx = idDel ↔ r.pos = p0 := by
      intro r hr
      constructor
      · intro hid
        have hrec := (hrel.h_trans_nodes r hr).2.2.1
        rw [hid] at hrec
        have hrr : r = r0 := Option.some.inj (hrec.symm.trans hr0_rec)
        exact hrr ▸ hr0_pos
      · intro hp; rw [hp]
    have hid_mem_b0 : idDel ∈ bucketIds gs d p0.sender k0 := by
      refine List.mem_map.mpr ⟨r0, List.mem_filter.mpr ⟨hr0_mem, ?_⟩, hidDel_eq⟩
      rw [hr0_pos, beq_self_eq_true, Bool.true_and, decide_eq_true hr0_wk]
    have hbucket_del : ∀ Q k,
        bucketIds (gs.delete p0) (d.delete p0) Q k =
          (bucketIds gs d Q k).filter (fun x => decide (x ≠ idDel)) := by
      intro Q k
      unfold bucketIds
      dsimp only [GameState.delete]
      rw [List.filter_comm]
      set L := gs.trans.filter (fun r => (r.pos.sender == Q) &&
        decide (spkWireKeyVal ℓ r.ct = some k))
      have hL_sub : ∀ r ∈ L, r ∈ gs.trans := fun r hr => (List.mem_filter.mp hr).1
      rw [List.filter_map]
      have hflt_eq : L.filter (fun r => r.pos != p0) =
          L.filter (fun r => decide (d.posNode r.pos.sender r.pos.epoch r.pos.idx ≠ idDel)) := by
        refine List.filter_congr fun r hr => ?_
        have hiff := hid_iff_pos r (hL_sub r hr)
        by_cases hp : r.pos = p0
        · simp [hp, idDel]
        · have hid_ne : d.posNode r.pos.sender r.pos.epoch r.pos.idx ≠ idDel :=
            fun h => hp (hiff.mp h)
          simp [hp, hid_ne]
      rw [hflt_eq]
      refine List.map_congr_left fun r hr => ?_
      have hr_ne : r.pos ≠ p0 := fun hp => by
        have := (List.mem_filter.mp hr).2
        rw [(hid_iff_pos r (hL_sub r (List.mem_filter.mp hr).1)).mpr hp] at this
        simp at this
      rw [hd_eq]; dsimp only
      exact updPosTbl_ne d.posNode p0 r.pos 0 hr_ne
    obtain ⟨hunl_hd, hunl_cl⟩ := chainLinks_unlink (hrel.h_chain p0.sender k0)
      (hrel.bucketIds_nodup p0.sender k0) (hrel.bucketIds_pos p0.sender k0) hid_mem_b0
    have hnd_map_filt : ((gs.trans.filter (fun r => r.pos != p0)).map Record.pos).Nodup := by
      change ((gs.trans.filter ((fun x => x != p0) ∘ Record.pos)).map Record.pos).Nodup
      rw [← List.filter_map]
      exact hrel.h_trans_nodup.filter _
    refine {
      h_st := by rw [hd_eq]; exact hrel.h_st
      h_b := by rw [hd_eq]; exact hrel.h_b
      h_win := by rw [hd_eq]; exact hrel.h_win
      h_epoch := by rw [hd_eq]; exact hrel.h_epoch
      h_idx := by rw [hd_eq]; exact hrel.h_idx
      h_tL := by rw [hd_eq]; exact hrel.h_tL
      h_maxAcc := by rw [hd_eq]; exact hrel.h_maxAcc
      h_pos_trans := fun r hr => hrel.h_pos_trans r (List.mem_of_mem_filter hr)
      h_pos_chall := fun p hp => hrel.h_pos_chall p (List.mem_of_mem_filter hp)
      h_pos_comp := fun p hp => hrel.h_pos_comp p (List.mem_of_mem_filter hp)
      h_trans_nodup := hnd_map_filt
      h_chall_nodup := hrel.h_chall_nodup.filter _
      h_nextId_pos := by rw [hd_eq]; exact hrel.h_nextId_pos
      h_node0 := by rw [hd_eq]; exact hrel.h_node0
      h_posNode_zero_iff := fun p => by
        rw [hd_eq]; dsimp only [GameState.delete]
        by_cases hp : p = p0
        · subst hp
          rw [updPosTbl_self]
          exact ⟨fun _ r hr => bne_iff_ne.mp (List.mem_filter.mp hr).2, fun _ => rfl⟩
        · rw [updPosTbl_ne _ _ _ _ hp, hrel.h_posNode_zero_iff p]
          constructor
          · intro hall r hr; exact hall r (List.mem_filter.mp hr).1
          · intro hall r hr
            by_cases hrp : r.pos = p0
            · exact hrp ▸ Ne.symm hp
            · exact hall r (List.mem_filter.mpr ⟨hr, bne_iff_ne.mpr hrp⟩)
      h_trans_nodes := fun r hr => by
        rw [hd_eq]; dsimp only [GameState.delete] at hr ⊢
        rcases List.mem_filter.mp hr with ⟨hm, hne_b⟩
        rw [updPosTbl_ne _ _ _ _ (bne_iff_ne.mp hne_b)]
        exact hrel.h_trans_nodes r hm
      h_head := fun Q k => by
        rw [hbucket_del Q k, hd_eq]; dsimp only [updTbl1]
        by_cases hqk : Q = p0.sender ∧ k = k0
        · rcases hqk with ⟨rfl, rfl⟩
          rw [updParty_self]
          simp only [↓reduceIte]
          rw [hrel.h_head p0.sender k0]
          exact hunl_hd
        · have hid_not : idDel ∉ bucketIds gs d Q k := by
            intro hm
            obtain ⟨r₁, _, hrec₁, hs₁, hk₁⟩ := hrel.bucketIds_party_key hm
            have hr10 : r₁ = r0 := Option.some.inj (hrec₁.symm.trans hr0_rec)
            subst hr10
            exact hqk ⟨hs₁.symm.trans (congrArg Pos.sender hr0_pos), hk₁.symm⟩
          have hflt_id : (bucketIds gs d Q k).filter (fun x => decide (x ≠ idDel)) =
              bucketIds gs d Q k :=
            List.filter_eq_self.mpr fun x hx => decide_eq_true (fun h => hid_not (h ▸ hx))
          rw [hflt_id]
          by_cases hq : Q = p0.sender
          · subst hq
            have hk : k ≠ k0 := fun h => hqk ⟨rfl, h⟩
            rw [updParty_self]; simp [hk, hrel.h_head]
          · rw [updParty_ne _ _ hq, hrel.h_head]
      h_chain := fun Q k => by
        rw [hbucket_del Q k, hd_eq]; dsimp only
        by_cases hqk : Q = p0.sender ∧ k = k0
        · rcases hqk with ⟨rfl, rfl⟩; exact hunl_cl
        · have hid_not : idDel ∉ bucketIds gs d Q k := by
            intro hm
            obtain ⟨r₁, _, hrec₁, hs₁, hk₁⟩ := hrel.bucketIds_party_key hm
            have hr10 : r₁ = r0 := Option.some.inj (hrec₁.symm.trans hr0_rec)
            subst hr10
            exact hqk ⟨hs₁.symm.trans (congrArg Pos.sender hr0_pos), hk₁.symm⟩
          have hflt_id : (bucketIds gs d Q k).filter (fun x => decide (x ≠ idDel)) =
              bucketIds gs d Q k :=
            List.filter_eq_self.mpr fun x hx => decide_eq_true (fun h => hid_not (h ▸ hx))
          rw [hflt_id]
          obtain ⟨hp_mem, hn_mem⟩ := (hrel.h_chain p0.sender k0).mem_prev_next hid_mem_b0
          refine (hrel.h_chain Q k).congr fun x hx => ?_
          have hx0 : x ≠ 0 := Nat.ne_of_gt (hrel.bucketIds_pos Q k x hx)
          have hdisj : ∀ y ∈ bucketIds gs d p0.sender k0, x ≠ y := by
            intro y hy heq
            rw [← heq] at hy
            obtain ⟨r₁, _, hrec₁, hs₁, hk₁⟩ := hrel.bucketIds_party_key hx
            obtain ⟨r₂, _, hrec₂, hs₂, hk₂⟩ := hrel.bucketIds_party_key hy
            have hr12 : r₁ = r₂ := Option.some.inj (hrec₁.symm.trans hrec₂)
            subst hr12
            exact hqk ⟨hs₁.symm.trans hs₂, hk₁.symm.trans hk₂⟩
          have hx_ne_p : x ≠ d.nodePrev idDel := by
            rcases hp_mem with hp0 | hpin
            · exact hp0 ▸ hx0
            · exact hdisj _ hpin
          have hx_ne_n : x ≠ d.nodeNext idDel := by
            rcases hn_mem with hn0 | hnin
            · exact hn0 ▸ hx0
            · exact hdisj _ hnin
          constructor
          · by_cases hn0 : d.nodeNext idDel = 0 <;> simp [dllUnlinkPrev, hn0, hx_ne_n]
          · by_cases hp0 : d.nodePrev idDel = 0 <;> simp [dllUnlinkNext, hp0, hx_ne_p]
      h_challTbl := fun p => by rw [hd_eq]; exact hchall_tbl p
      h_challCount := fun Q => by rw [hd_eq]; exact hchall_cnt Q
      h_compTbl := fun p => by rw [hd_eq]; exact hcomp_tbl p
      h_uncompCount := fun Q => by
        rw [hd_eq]; dsimp only [GameState.delete]
        have hcomp_congr :
            (gs.trans.filter (fun r => r.pos != p0)).countP
              (fun r => (r.pos.sender == Q) && !(gs.comp.filter (fun q => q != p0)).contains r.pos) =
            (gs.trans.filter (fun r => r.pos != p0)).countP
              (fun r => (r.pos.sender == Q) && !gs.comp.contains r.pos) := by
          refine List.countP_congr fun r hr => ?_
          have hne : r.pos ≠ p0 := bne_iff_ne.mp (List.mem_filter.mp hr).2
          have hc : (gs.comp.filter (fun q => q != p0)).contains r.pos = gs.comp.contains r.pos := by
            simp [List.mem_filter, bne_iff_ne, hne]
          rw [hc]
        rw [hcomp_congr, countP_filter_pos_ne hrel.h_trans_nodup p0]
        have hfind_some : gs.trans.find? (fun r => r.pos == p0) = some r0 := by
          cases hfd : gs.trans.find? (fun r => r.pos == p0) with
          | none =>
            exfalso
            have := List.find?_eq_none.mp hfd r0 hr0_mem
            rw [hr0_pos, beq_self_eq_true] at this
            exact this rfl
          | some r1 =>
            have hr1_mem := List.mem_of_find?_eq_some hfd
            have hr1_pos : r1.pos = p0 :=
              beq_iff_eq.mp (List.find?_some (p := fun (r : Record (Plain ℓ) Bytes) => r.pos == p0) hfd)
            have hid1 := (hid_iff_pos r1 hr1_mem).mpr hr1_pos
            have hrec1 := (hrel.h_trans_nodes r1 hr1_mem).2.2.1
            rw [hid1] at hrec1
            exact congrArg some (Option.some.inj (hrec1.symm.trans hr0_rec))
        rw [hfind_some]; dsimp only
        rw [hr0_pos, hrel.h_compTbl p0]
        cases hc0 : gs.comp.contains p0
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true]
          by_cases hq : Q = p0.sender
          · subst hq; simp [hrel.h_uncompCount]
          · rw [updParty_ne _ _ hq, hrel.h_uncompCount Q]
            have hbeq : (p0.sender == Q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
            simp [hbeq]
        · simp [hrel.h_uncompCount Q] }

theorem tier2GsRel_accept_preserves {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (P : Party)
    (st' : GhostState Bytes) (p0 : Pos) :
    Tier2GsRel ℓ (gs.accept P st' p0) (d.accept P st' p0) := by
  have hdel := tier2GsRel_delete_preserves hrel p0
  have hma : (d.delete p0).maxAcc = (gs.delete p0).maxAcc := hdel.h_maxAcc
  have hep_le : ∀ Q : Party,
      (gs.delete p0).epoch Q ≤
        Function.update (gs.delete p0).epoch P (max ((gs.delete p0).epoch P) p0.epoch) Q := by
    intro Q
    by_cases hq : Q = P
    · subst hq; rw [Function.update_self]; exact Nat.le_max_left _ _
    · rw [Function.update_of_ne hq]
  refine { hdel with
    h_st := by dsimp only [Tier2Gs.accept, GameState.accept]; rw [hdel.h_st, updParty_eq_update]
    h_epoch := by
      dsimp only [Tier2Gs.accept, GameState.accept]; rw [hdel.h_epoch, updParty_eq_update]
    h_maxAcc := by
      dsimp only [Tier2Gs.accept, GameState.accept]
      funext Q t
      by_cases hq : Q = P
      · subst hq
        simp only [updTbl1, updParty_self]
        by_cases ht : t = p0.epoch
        · subst ht; simp [hma]
        · simp [ht, hma]
      · simp [updTbl1, hq, hma]
    h_pos_trans := fun r hr => posBound_mono_epoch hep_le (fun _ _ => rfl) (hdel.h_pos_trans r hr)
    h_pos_chall := fun p hp => posBound_mono_epoch hep_le (fun _ _ => rfl) (hdel.h_pos_chall p hp)
    h_pos_comp := fun p hp => posBound_mono_epoch hep_le (fun _ _ => rfl) (hdel.h_pos_comp p hp) }

/-! ## `Hop2TblRel` invariant -/

@[expose] def hop2TblGet {Pt : Type} (encT : Pt → PublicKey)
    (tbl : ℕ → ℕ → Option (BitVec 256)) (t : ℕ) (Q : Pt) : Option (BitVec 256) :=
  tbl t (ptKeyVal encT Q)

@[expose] def hop2TblSet {Pt : Type} (encT : Pt → PublicKey)
    (tbl : ℕ → ℕ → Option (BitVec 256)) (t0 : ℕ) (Q0 : Pt) (v : BitVec 256) :
    ℕ → ℕ → Option (BitVec 256) :=
  fun t k => if t = t0 then (if k = ptKeyVal encT Q0 then some v else tbl t k) else tbl t k

/-- Simulation relation between an association list `L` and its 2D table counterpart `tbl`. -/
@[expose] def Hop2TblRel {Pt : Type} [DecidableEq Pt] (encT : Pt → PublicKey)
    (L : List ((ℕ × Pt) × BitVec 256)) (tbl : ℕ → ℕ → Option (BitVec 256)) : Prop :=
  ∀ (t : ℕ) (Q : Pt), hop2TblGet encT tbl t Q = L.lookup (t, Q)

theorem hop2TblRel_nil {Pt : Type} [DecidableEq Pt] (encT : Pt → PublicKey) :
    Hop2TblRel encT [] (fun _ _ => none) :=
  fun _ _ => rfl

theorem hop2TblRel_cons {Pt : Type} [DecidableEq Pt] {encT : Pt → PublicKey}
    (hinj : Function.Injective encT)
    {L : List ((ℕ × Pt) × BitVec 256)} {tbl : ℕ → ℕ → Option (BitVec 256)}
    (hrel : Hop2TblRel encT L tbl) (t0 : ℕ) (Q0 : Pt) (v : BitVec 256) :
    Hop2TblRel encT (((t0, Q0), v) :: L) (hop2TblSet encT tbl t0 Q0 v) := by
  intro t Q
  unfold hop2TblGet hop2TblSet
  rw [List.lookup_cons]
  by_cases ht : t = t0
  · subst ht
    simp only [↓reduceIte]
    by_cases hq : Q = Q0
    · subst hq; simp
    · have hkne : ptKeyVal encT Q ≠ ptKeyVal encT Q0 :=
        fun hk => hq (ptKeyVal_injective hinj hk)
      have hbeq : ((t, Q) == (t, Q0)) = false :=
        beq_eq_false_iff_ne.mpr (fun h => hq (Prod.mk.inj h).2)
      simp only [hkne, ↓reduceIte, hbeq]
      exact hrel t Q
  · simp only [ht, ↓reduceIte]
    have hbeq : ((t, Q) == (t0, Q0)) = false :=
      beq_eq_false_iff_ne.mpr (fun h => ht (Prod.mk.inj h).1)
    simp only [hbeq]
    exact hrel t Q

theorem hop2TblRel_cons_of_dec {Pt : Type} [DecidableEq Pt]
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt}
    (hdec : ∀ T, decT (encT T) = some T)
    {L : List ((ℕ × Pt) × BitVec 256)} {tbl : ℕ → ℕ → Option (BitVec 256)}
    (hrel : Hop2TblRel encT L tbl) (t0 : ℕ) (Q0 : Pt) (v : BitVec 256) :
    Hop2TblRel encT (((t0, Q0), v) :: L) (hop2TblSet encT tbl t0 Q0 v) := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a
    rw [h, hdec b] at ha
    exact (Option.some.inj ha).symm
  exact hop2TblRel_cons hinj hrel t0 Q0 v

end Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
