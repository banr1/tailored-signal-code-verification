/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SmReachInv -- proof-setup: allow-public-import

/-!
# Pure Table Bookkeeping and Invariants for Tier-2 SPK Reductions

Defines the pure table-backed game state `Tier2Gs` and the simulation relation `Tier2GsRel`
mirroring `SM.GameState` via doubly-linked ciphertext buckets and per-position flag tables.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure

open CryptoGames (Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record GameState initState healedBy maxOpt)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp_contains dedupComp_afterCorr_eq)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (spkWireKeyVal
  spkWireKeyVal_injective)

/-! ## Doubly-linked bucket chains -/

@[expose] def headOf : List ℕ → ℕ
  | [] => 0
  | x :: _ => x

/-- Inductive doubly-linked list invariant along `ids` starting from predecessor `predId`. -/
@[expose] def ChainLinks (prev next : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | predId, x :: xs => prev x = predId ∧ next x = headOf xs ∧ ChainLinks prev next x xs

theorem ChainLinks.congr {prev₁ prev₂ next₁ next₂ : ℕ → ℕ} :
    ∀ {predId : ℕ} {ids : List ℕ},
      ChainLinks prev₁ next₁ predId ids →
      (∀ x ∈ ids, prev₂ x = prev₁ x ∧ next₂ x = next₁ x) →
      ChainLinks prev₂ next₂ predId ids
  | _, [], _, _ => trivial
  | predId, x :: xs, ⟨hp, hn, htl⟩, hfg => by
    obtain ⟨hpx, hnx⟩ := hfg x List.mem_cons_self
    exact ⟨hpx.trans hp, hnx.trans hn,
      htl.congr (fun y hy => hfg y (List.mem_cons_of_mem x hy))⟩

theorem ChainLinks.mem_prev_next {prev next : ℕ → ℕ} :
    ∀ {predId : ℕ} {ids : List ℕ} {id0 : ℕ},
      ChainLinks prev next predId ids →
      id0 ∈ ids →
      (prev id0 = predId ∨ prev id0 ∈ ids) ∧ (next id0 = 0 ∨ next id0 ∈ ids)
  | _, [], _, _, hmem => nomatch hmem
  | predId, x :: xs, id0, ⟨hp, hn, htl⟩, hmem => by
    rcases List.mem_cons.mp hmem with rfl | hxs
    · refine ⟨Or.inl hp, ?_⟩
      cases xs with
      | nil => exact Or.inl hn
      | cons y ys =>
        right
        rw [hn]
        exact List.mem_cons_of_mem id0 List.mem_cons_self
    · obtain ⟨hp', hn'⟩ := htl.mem_prev_next hxs
      refine ⟨?_, ?_⟩
      · rcases hp' with hp' | hp'
        · exact Or.inr (hp' ▸ List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem x hp')
      · rcases hn' with hn' | hn'
        · exact Or.inl hn'
        · exact Or.inr (List.mem_cons_of_mem x hn')

@[expose] def dllPushPrev (head idNew : ℕ) (prev : ℕ → ℕ) : ℕ → ℕ :=
  let prev1 := fun j => if j = idNew then 0 else prev j
  if head = 0 then prev1 else fun j => if j = head then idNew else prev1 j

@[expose] def dllPushNext (head idNew : ℕ) (next : ℕ → ℕ) : ℕ → ℕ :=
  fun j => if j = idNew then head else next j

theorem chainLinks_push {prev next : ℕ → ℕ} {ids : List ℕ} {idNew : ℕ}
    (hchain : ChainLinks prev next 0 ids)
    (hnd : ids.Nodup)
    (hpos : ∀ x ∈ ids, 0 < x)
    (hfresh : idNew ∉ ids) :
    ChainLinks (dllPushPrev (headOf ids) idNew prev)
      (dllPushNext (headOf ids) idNew next) 0 (idNew :: ids) := by
  cases ids with
  | nil =>
    simp [ChainLinks, headOf, dllPushPrev, dllPushNext]
  | cons y ys =>
    obtain ⟨hy_not_ys, _⟩ := List.nodup_cons.mp hnd
    have hy0 : y ≠ 0 := Nat.ne_of_gt (hpos y List.mem_cons_self)
    have hne_new_y : idNew ≠ y := fun h => hfresh (h ▸ List.mem_cons_self)
    obtain ⟨_, hny, htl⟩ := hchain
    refine ⟨?_, ?_, ?_⟩
    · simp [dllPushPrev, headOf, hy0, hne_new_y]
    · simp [dllPushNext, headOf]
    · refine ⟨?_, ?_, ?_⟩
      · simp [dllPushPrev, headOf, hy0]
      · simp [dllPushNext, headOf, Ne.symm hne_new_y, hny]
      · refine htl.congr fun z hz => ?_
        have hz_ne_new : z ≠ idNew := fun h => hfresh (h ▸ List.mem_cons_of_mem y hz)
        have hz_ne_y : z ≠ y := fun h => hy_not_ys (h ▸ hz)
        simp [dllPushPrev, dllPushNext, headOf, hy0, hz_ne_new, hz_ne_y]

@[expose] def dllUnlinkHead (head p n : ℕ) : ℕ :=
  if p = 0 then n else head

@[expose] def dllUnlinkPrev (p n : ℕ) (prev : ℕ → ℕ) : ℕ → ℕ :=
  if n = 0 then prev else fun j => if j = n then p else prev j

@[expose] def dllUnlinkNext (p n : ℕ) (next : ℕ → ℕ) : ℕ → ℕ :=
  if p = 0 then next else fun j => if j = p then n else next j

theorem chainLinks_unlink_aux {prev next : ℕ → ℕ} :
    ∀ {predId idDel : ℕ} {ids : List ℕ},
      ChainLinks prev next predId ids →
      ids.Nodup →
      (∀ x ∈ ids, 0 < x) →
      predId ∉ ids →
      idDel ∈ ids →
      (if prev idDel = predId then next idDel else headOf ids) =
        headOf (ids.filter (fun x => decide (x ≠ idDel))) ∧
      ChainLinks (dllUnlinkPrev (prev idDel) (next idDel) prev)
        (dllUnlinkNext (prev idDel) (next idDel) next)
        predId (ids.filter (fun x => decide (x ≠ idDel)))
  | predId, idDel, [], _, _, _, _, hmem => nomatch hmem
  | predId, idDel, x :: xs, ⟨hpx, hnx, htl⟩, hnd, hpos, hpred_not, hmem => by
    obtain ⟨hx_not_xs, hnd_xs⟩ := List.nodup_cons.mp hnd
    have hpos_xs : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem x hy)
    by_cases hxeq : x = idDel
    · subst hxeq
      have hfilt : (x :: xs).filter (fun y => decide (y ≠ x)) = xs := by
        rw [List.filter_cons_of_neg (by simp)]
        exact List.filter_eq_self.mpr fun y hy =>
          decide_eq_true (fun h => hx_not_xs (h ▸ hy))
      rw [hfilt, hpx, hnx]
      refine ⟨by simp, ?_⟩
      cases xs with
      | nil => trivial
      | cons y ys =>
        obtain ⟨hy_not_ys, _⟩ := List.nodup_cons.mp hnd_xs
        obtain ⟨_, hny, htl_ys⟩ := htl
        have hy0 : y ≠ 0 := Nat.ne_of_gt (hpos_xs y List.mem_cons_self)
        have hpx_ne_y : predId ≠ y := fun h => hpred_not (h ▸ List.mem_cons_of_mem x List.mem_cons_self)
        refine ⟨?_, ?_, ?_⟩
        · simp [dllUnlinkPrev, headOf, hy0]
        · by_cases hp0 : predId = 0
          · simp [dllUnlinkNext, hp0, hny]
          · simp [dllUnlinkNext, hp0, Ne.symm hpx_ne_y, hny]
        · refine htl_ys.congr fun z hz => ?_
          have hz_ne_y : z ≠ y := fun h => hy_not_ys (h ▸ hz)
          have hz_ne_pred : z ≠ predId :=
            fun h => hpred_not (h ▸ List.mem_cons_of_mem x (List.mem_cons_of_mem y hz))
          refine ⟨?_, ?_⟩
          · simp [dllUnlinkPrev, headOf, hy0, hz_ne_y]
          · by_cases hp0 : predId = 0 <;> simp [dllUnlinkNext, hp0, hz_ne_pred]
    · have hmem_xs : idDel ∈ xs := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd rfl hxeq
        · exact h
      have hx0 : x ≠ 0 := Nat.ne_of_gt (hpos x List.mem_cons_self)
      obtain ⟨hp_mem, hn_mem⟩ := htl.mem_prev_next hmem_xs
      have hp_ne_pred : prev idDel ≠ predId := by
        rcases hp_mem with hp_eq | hp_in
        · intro h; exact hpred_not (h ▸ hp_eq ▸ List.mem_cons_self)
        · intro h; exact hpred_not (h ▸ List.mem_cons_of_mem x hp_in)
      have hn_ne_x : next idDel ≠ x := by
        rcases hn_mem with hn0 | hn_in
        · exact hn0 ▸ hx0.symm
        · exact fun h => hx_not_xs (h ▸ hn_in)
      obtain ⟨hhd_xs, hcl_xs⟩ :=
        chainLinks_unlink_aux htl hnd_xs hpos_xs hx_not_xs hmem_xs
      have hfilt : (x :: xs).filter (fun y => decide (y ≠ idDel)) =
          x :: xs.filter (fun y => decide (y ≠ idDel)) :=
        List.filter_cons_of_pos (decide_eq_true hxeq)
      rw [hfilt]
      simp only [hp_ne_pred, ↓reduceIte]
      refine ⟨rfl, ?_, ?_, hcl_xs⟩
      · by_cases hn0 : next idDel = 0 <;> simp [dllUnlinkPrev, hn0, Ne.symm hn_ne_x, hpx]
      · by_cases hpx_id : prev idDel = x
        · rw [← hhd_xs]
          simp [dllUnlinkNext, hpx_id, hx0]
        · rw [← hhd_xs]
          by_cases hp0 : prev idDel = 0 <;>
            simp [dllUnlinkNext, hp0, hpx_id, Ne.symm hpx_id, Ne.symm hx0, hnx]

theorem chainLinks_unlink {prev next : ℕ → ℕ} {idDel : ℕ} {ids : List ℕ}
    (hchain : ChainLinks prev next 0 ids)
    (hnd : ids.Nodup)
    (hpos : ∀ x ∈ ids, 0 < x)
    (hmem : idDel ∈ ids) :
    dllUnlinkHead (headOf ids) (prev idDel) (next idDel) =
      headOf (ids.filter (fun x => decide (x ≠ idDel))) ∧
    ChainLinks (dllUnlinkPrev (prev idDel) (next idDel) prev)
      (dllUnlinkNext (prev idDel) (next idDel) next)
      0 (ids.filter (fun x => decide (x ≠ idDel))) :=
  chainLinks_unlink_aux hchain hnd hpos (fun h => Nat.lt_irrefl 0 (hpos 0 h)) hmem


/-! ## Pure `Tier2Gs` state -/

/-- Pure table-backed mirror of `SM.GameState (GhostState Bytes) (Plain ℓ) Bytes`. -/
structure Tier2Gs (ℓ : ℕ) where
  st : Party → GhostState Bytes
  b : Bool
  win : Bool
  epoch : Party → ℕ
  idx : Party → ℕ
  tL : Option ℕ
  maxAcc : Party → ℕ → ℕ
  nextId : ℕ
  headTbl : Party → ℕ → ℕ
  nodeRec : ℕ → Option (Record (Plain ℓ) Bytes)
  nodeKey : ℕ → ℕ
  nodePrev : ℕ → ℕ
  nodeNext : ℕ → ℕ
  posNode : Party → ℕ → ℕ → ℕ
  challTbl : Party → ℕ → ℕ → Bool
  challCount : Party → ℕ
  compTbl : Party → ℕ → ℕ → Bool
  uncompCount : Party → ℕ

@[expose] def updParty {α : Type} (f : Party → α) (P : Party) (v : α) : Party → α
  | .A => match P with | .A => v | .B => f .A
  | .B => match P with | .A => f .B | .B => v

@[simp] theorem updParty_self {α : Type} (f : Party → α) (P : Party) (v : α) :
    updParty f P v P = v := by cases P <;> rfl

@[simp] theorem updParty_ne {α : Type} (f : Party → α) {P Q : Party} (v : α) (hne : Q ≠ P) :
    updParty f P v Q = f Q := by cases P <;> cases Q <;> first | exact absurd rfl hne | rfl

theorem updParty_eq_update {α : Type} (f : Party → α) (P : Party) (v : α) :
    updParty f P v = Function.update f P v := by
  funext Q; cases P <;> cases Q <;> rfl

@[expose] def updTbl1 {α : Type} (f : Party → ℕ → α) (P : Party) (i : ℕ) (v : α) : Party → ℕ → α :=
  updParty f P (fun j => if j = i then v else f P j)

@[expose] def updPosTbl {α : Type} (f : Party → ℕ → ℕ → α) (p : Pos) (v : α) : Party → ℕ → ℕ → α :=
  updParty f p.sender (fun ep =>
    if ep = p.epoch then (fun idx => if idx = p.idx then v else f p.sender ep idx)
    else f p.sender ep)

@[simp] theorem updPosTbl_self {α : Type} (f : Party → ℕ → ℕ → α) (p : Pos) (v : α) :
    updPosTbl f p v p.sender p.epoch p.idx = v := by
  simp [updPosTbl]

theorem updPosTbl_ne {α : Type} (f : Party → ℕ → ℕ → α) (p q : Pos) (v : α) (hne : q ≠ p) :
    updPosTbl f p v q.sender q.epoch q.idx = f q.sender q.epoch q.idx := by
  rcases p with ⟨ps, pe, pi⟩
  rcases q with ⟨qs, qe, qi⟩
  by_cases hs : qs = ps
  · subst hs
    simp only [updPosTbl, updParty_self]
    by_cases he : qe = pe
    · subst he
      have hi : qi ≠ pi := fun h => hne (by subst h; rfl)
      simp [hi]
    · simp [he]
  · simp [updPosTbl, hs]

namespace Tier2Gs

@[expose] def init {ℓ : ℕ} (stA stB : GhostState Bytes) (b : Bool) : Tier2Gs ℓ where
  st := fun | .A => stA | .B => stB
  b := b
  win := false
  epoch := fun _ => 0
  idx := fun _ => 0
  tL := none
  maxAcc := fun _ _ => 0
  nextId := 1
  headTbl := fun _ _ => 0
  nodeRec := fun _ => none
  nodeKey := fun _ => 0
  nodePrev := fun _ => 0
  nodeNext := fun _ => 0
  posNode := fun _ _ _ => 0
  challTbl := fun _ _ _ => false
  challCount := fun _ => 0
  compTbl := fun _ _ _ => false
  uncompCount := fun _ => 0

@[expose] def setWin {ℓ : ℕ} (d : Tier2Gs ℓ) (w : Bool) : Tier2Gs ℓ :=
  { d with win := w }

@[expose] def safeCh {ℓ : ℕ} (d : Tier2Gs ℓ) (Δ : ℕ) (P : Party) : Bool :=
  healedBy d.tL Δ (d.epoch P)

@[expose] def safeInj {ℓ : ℕ} (d : Tier2Gs ℓ) (Δ : ℕ) : Bool :=
  healedBy d.tL Δ (min (d.epoch .A) (d.epoch .B))

@[expose] def leak {ℓ : ℕ} (d : Tier2Gs ℓ) (l : ℕ) : Tier2Gs ℓ :=
  { d with tL := some (maxOpt d.tL l) }

@[expose] def epMgmt {ℓ : ℕ} (d : Tier2Gs ℓ) (Δ qep : ℕ) (P : Party) (bad : Bool) : Option (Tier2Gs ℓ) :=
  let epNext := d.epoch P + 1
  if P.sendsIn epNext then
    if qep < epNext then none
    else
      let d1 := if bad && !(d.safeCh Δ P) then d.leak epNext else d
      some { d1 with
        epoch := updParty d1.epoch P (d1.epoch P + 1)
        idx := updParty d1.idx P 0 }
  else
    if qep < d.epoch P then none else some d

@[expose] def challContains {ℓ : ℕ} (d : Tier2Gs ℓ) (p : Pos) : Bool :=
  d.challTbl p.sender p.epoch p.idx

@[expose] def compContains {ℓ : ℕ} (d : Tier2Gs ℓ) (p : Pos) : Bool :=
  d.compTbl p.sender p.epoch p.idx

@[expose] def trivial {ℓ : ℕ} (d : Tier2Gs ℓ) (Δ : ℕ) (p : Pos) : Bool :=
  d.compContains p ||
    ((d.posNode p.sender p.epoch p.idx == 0) && !(healedBy d.tL Δ p.epoch))

@[expose] def corrAllowed {ℓ : ℕ} (d : Tier2Gs ℓ) (P : Party) : Bool :=
  (d.challCount P.other == 0) && (d.uncompCount P.other == 0)

@[expose] def afterCorrAllowed {ℓ : ℕ} (d : Tier2Gs ℓ) (_P : Party) : Tier2Gs ℓ :=
  d.leak (max (d.epoch .A) (d.epoch .B))

@[expose] def inTransit {ℓ : ℕ} (d : Tier2Gs ℓ) (Q : Party) (c : Bytes) : Option (Record (Plain ℓ) Bytes) :=
  match spkWireKeyVal ℓ c with
  | none => none
  | some k => d.nodeRec (d.headTbl Q k)

@[expose] def record {ℓ : ℕ} (d : Tier2Gs ℓ) (Δ : ℕ) (P : Party) (st' : GhostState Bytes)
    (r : Record (Plain ℓ) Bytes) (isChall : Bool) : Tier2Gs ℓ :=
  match spkWireKeyVal ℓ r.ct with
  | none => d
  | some k =>
    let safe := d.safeCh Δ P
    let idNew := d.nextId
    let oldHead := d.headTbl P k
    { d with
      st := updParty d.st P st'
      idx := updParty d.idx P r.pos.idx
      nextId := idNew + 1
      headTbl := updTbl1 d.headTbl P k idNew
      nodeRec := fun j => if j = idNew then some r else d.nodeRec j
      nodeKey := fun j => if j = idNew then k else d.nodeKey j
      nodePrev := dllPushPrev oldHead idNew d.nodePrev
      nodeNext := dllPushNext oldHead idNew d.nodeNext
      posNode := updPosTbl d.posNode r.pos idNew
      challTbl := if isChall then updPosTbl d.challTbl r.pos true else d.challTbl
      challCount := if isChall then updParty d.challCount P (d.challCount P + 1) else d.challCount
      compTbl := if safe then d.compTbl else updPosTbl d.compTbl r.pos true
      uncompCount := if safe then updParty d.uncompCount P (d.uncompCount P + 1) else d.uncompCount }

@[expose] def delete {ℓ : ℕ} (d : Tier2Gs ℓ) (p0 : Pos) : Tier2Gs ℓ :=
  let idDel := d.posNode p0.sender p0.epoch p0.idx
  let wasChall := d.challTbl p0.sender p0.epoch p0.idx
  let wasComp := d.compTbl p0.sender p0.epoch p0.idx
  let challTbl' := updPosTbl d.challTbl p0 false
  let challCount' :=
    if wasChall then updParty d.challCount p0.sender (d.challCount p0.sender - 1) else d.challCount
  let compTbl' := updPosTbl d.compTbl p0 false
  if idDel = 0 then
    { d with challTbl := challTbl', challCount := challCount', compTbl := compTbl' }
  else
    let k := d.nodeKey idDel
    let p := d.nodePrev idDel
    let n := d.nodeNext idDel
    { d with
      headTbl := updTbl1 d.headTbl p0.sender k
        (dllUnlinkHead (d.headTbl p0.sender k) p n)
      nodePrev := dllUnlinkPrev p n d.nodePrev
      nodeNext := dllUnlinkNext p n d.nodeNext
      posNode := updPosTbl d.posNode p0 0
      challTbl := challTbl'
      challCount := challCount'
      compTbl := compTbl'
      uncompCount :=
        if wasComp then d.uncompCount
        else updParty d.uncompCount p0.sender (d.uncompCount p0.sender - 1) }

@[expose] def accept {ℓ : ℕ} (d : Tier2Gs ℓ) (P : Party) (st' : GhostState Bytes) (p0 : Pos) : Tier2Gs ℓ :=
  let d1 := d.delete p0
  { d1 with
    st := updParty d1.st P st'
    epoch := updParty d1.epoch P (max (d1.epoch P) p0.epoch)
    maxAcc := updTbl1 d1.maxAcc P p0.epoch (max (d1.maxAcc P p0.epoch) p0.idx) }

end Tier2Gs

/-! ## `Tier2GsRel` simulation relation -/

@[expose] def posBound (ep idx : Party → ℕ) (p : Pos) : Prop :=
  p.epoch < ep p.sender ∨ (p.epoch = ep p.sender ∧ p.idx ≤ idx p.sender)

theorem posBound_ne_next (ep idx : Party → ℕ) (P : Party) {p : Pos}
    (hb : posBound ep idx p) : p ≠ ⟨P, ep P, idx P + 1⟩ := by
  rintro rfl
  dsimp only [posBound] at hb
  rcases hb with hlt | ⟨_, hle⟩ <;> omega

theorem posBound_mono_epoch {ep₁ ep₂ idx : Party → ℕ}
    (hle : ∀ P, ep₁ P ≤ ep₂ P)
    (heq_idx : ∀ P, ep₁ P = ep₂ P → idx P = idx P)
    {p : Pos} (hb : posBound ep₁ idx p) : posBound ep₂ idx p := by
  have _ := heq_idx
  have hp := hle p.sender
  rcases hb with hlt | ⟨he, hi⟩
  · exact Or.inl (Nat.lt_of_lt_of_le hlt hp)
  · by_cases hstrict : ep₁ p.sender < ep₂ p.sender
    · exact Or.inl (he ▸ hstrict)
    · have he2 : ep₂ p.sender = ep₁ p.sender := by omega
      exact Or.inr ⟨he.trans he2.symm, hi⟩

theorem posBound_epMgmt_adv (ep idx : Party → ℕ) (P : Party) {p : Pos}
    (hb : posBound ep idx p) :
    posBound (updParty ep P (ep P + 1)) (updParty idx P 0) p := by
  by_cases hs : p.sender = P
  · rcases hb with hlt | ⟨he, _⟩
    · left; rw [hs, updParty_self]; exact Nat.lt_succ_of_lt (hs ▸ hlt)
    · left; rw [hs, updParty_self]; have := hs ▸ he; omega
  · rcases hb with hlt | ⟨he, hi⟩
    · left; rwa [updParty_ne _ _ hs]
    · right; rw [updParty_ne _ _ hs, updParty_ne _ _ hs]; exact ⟨he, hi⟩

@[expose] def bucketIds {ℓ : ℕ} (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (d : Tier2Gs ℓ) (P : Party) (k : ℕ) : List ℕ :=
  (gs.trans.filter (fun r => (r.pos.sender == P) &&
    decide (spkWireKeyVal ℓ r.ct = some k))).map
      (fun r => d.posNode r.pos.sender r.pos.epoch r.pos.idx)

/-- Simulation relation between shallow `SM.GameState` and `Tier2Gs`. -/
structure Tier2GsRel (ℓ : ℕ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (d : Tier2Gs ℓ) : Prop where
  h_st : d.st = gs.st
  h_b : d.b = gs.b
  h_win : d.win = gs.win
  h_epoch : d.epoch = gs.epoch
  h_idx : d.idx = gs.idx
  h_tL : d.tL = gs.tL
  h_maxAcc : d.maxAcc = gs.maxAcc
  h_pos_trans : ∀ r ∈ gs.trans, posBound gs.epoch gs.idx r.pos
  h_pos_chall : ∀ p ∈ gs.chall, posBound gs.epoch gs.idx p
  h_pos_comp : ∀ p ∈ gs.comp, posBound gs.epoch gs.idx p
  h_trans_nodup : (gs.trans.map Record.pos).Nodup
  h_chall_nodup : gs.chall.Nodup
  h_nextId_pos : 1 ≤ d.nextId
  h_node0 : d.nodeRec 0 = none
  h_posNode_zero_iff : ∀ p : Pos, d.posNode p.sender p.epoch p.idx = 0 ↔ ∀ r ∈ gs.trans, r.pos ≠ p
  h_trans_nodes : ∀ r ∈ gs.trans,
    let id := d.posNode r.pos.sender r.pos.epoch r.pos.idx
    1 ≤ id ∧ id < d.nextId ∧ d.nodeRec id = some r ∧ spkWireKeyVal ℓ r.ct = some (d.nodeKey id)
  h_head : ∀ P k, d.headTbl P k = headOf (bucketIds gs d P k)
  h_chain : ∀ P k, ChainLinks d.nodePrev d.nodeNext 0 (bucketIds gs d P k)
  h_challTbl : ∀ p : Pos, d.challTbl p.sender p.epoch p.idx = gs.chall.contains p
  h_challCount : ∀ P : Party, d.challCount P = gs.chall.countP (fun p => p.sender == P)
  h_compTbl : ∀ p : Pos, d.compTbl p.sender p.epoch p.idx = gs.comp.contains p
  h_uncompCount : ∀ P : Party,
    d.uncompCount P = gs.trans.countP (fun r => (r.pos.sender == P) && !gs.comp.contains r.pos)

namespace Tier2GsRel

theorem bucketIds_nodup {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (P : Party) (k : ℕ) :
    (bucketIds gs d P k).Nodup := by
  have hnd_trans : gs.trans.Nodup := List.Nodup.of_map Record.pos hrel.h_trans_nodup
  have hnd_filt : (gs.trans.filter (fun r => (r.pos.sender == P) &&
      decide (spkWireKeyVal ℓ r.ct = some k))).Nodup := hnd_trans.filter _
  refine hnd_filt.map_on ?_
  intro r₁ hr₁ r₂ hr₂ hid
  have hm₁ := (List.mem_filter.mp hr₁).1
  have hm₂ := (List.mem_filter.mp hr₂).1
  have hn₁ := (hrel.h_trans_nodes r₁ hm₁).2.2.1
  have hn₂ := (hrel.h_trans_nodes r₂ hm₂).2.2.1
  rw [hid] at hn₁
  exact Option.some.inj (hn₁.symm.trans hn₂)

theorem bucketIds_pos {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (P : Party) (k : ℕ) :
    ∀ x ∈ bucketIds gs d P k, 0 < x := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
  have hm := (List.mem_filter.mp hr).1
  have h1 := (hrel.h_trans_nodes r hm).1
  omega

theorem bucketIds_lt_nextId {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (P : Party) (k : ℕ) :
    ∀ x ∈ bucketIds gs d P k, x < d.nextId := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
  exact (hrel.h_trans_nodes r (List.mem_filter.mp hr).1).2.1

theorem bucketIds_party_key {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) {P : Party} {k x : ℕ}
    (hx : x ∈ bucketIds gs d P k) :
    ∃ r ∈ gs.trans, d.nodeRec x = some r ∧ r.pos.sender = P ∧ d.nodeKey x = k := by
  rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
  rcases List.mem_filter.mp hr with ⟨hm, hpk⟩
  rcases Bool.and_eq_true_iff.mp hpk with ⟨hp, hk⟩
  have hps : r.pos.sender = P := by
    cases hs : r.pos.sender <;> cases P <;> rw [hs] at hp <;> first | rfl | cases hp
  have hks : spkWireKeyVal ℓ r.ct = some k := of_decide_eq_true hk
  obtain ⟨_, _, hrec, hkey⟩ := hrel.h_trans_nodes r hm
  rw [hks] at hkey
  exact ⟨r, hm, hrec, hps, Option.some.inj hkey.symm⟩

theorem init {ℓ : ℕ} {Key : Type}
    (sm : SMScheme Key (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (k : Key) (b : Bool) :
    Tier2GsRel ℓ (initState sm k b) (Tier2Gs.init (sm.initA k) (sm.initB k) b) where
  h_st := by funext P; cases P <;> rfl
  h_b := rfl
  h_win := rfl
  h_epoch := rfl
  h_idx := rfl
  h_tL := rfl
  h_maxAcc := rfl
  h_pos_trans := by simp [initState]
  h_pos_chall := by simp [initState]
  h_pos_comp := by simp [initState]
  h_trans_nodup := by simp [initState]
  h_chall_nodup := by simp [initState]
  h_nextId_pos := Nat.le_refl 1
  h_node0 := rfl
  h_posNode_zero_iff := by simp [Tier2Gs.init, initState]
  h_trans_nodes := by simp [initState]
  h_head := by intro P key; simp [Tier2Gs.init, bucketIds, initState, headOf]
  h_chain := by intro P key; simp [bucketIds, initState, ChainLinks]
  h_challTbl := by simp [Tier2Gs.init, initState]
  h_challCount := by simp [Tier2Gs.init, initState]
  h_compTbl := by simp [Tier2Gs.init, initState]
  h_uncompCount := by simp [Tier2Gs.init, initState]

theorem setWin {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (w : Bool) :
    Tier2GsRel ℓ { gs with win := w } (d.setWin w) :=
  { hrel with h_win := rfl }

theorem safeCh_eq {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (Δ : ℕ) (P : Party) :
    d.safeCh Δ P = gs.safeCh Δ P := by
  simp [Tier2Gs.safeCh, GameState.safeCh, hrel.h_tL, hrel.h_epoch]

theorem safeInj_eq {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (Δ : ℕ) :
    d.safeInj Δ = gs.safeInj Δ := by
  simp [Tier2Gs.safeInj, GameState.safeInj, hrel.h_tL, hrel.h_epoch]

theorem challContains_eq {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (p : Pos) :
    d.challContains p = gs.chall.contains p :=
  hrel.h_challTbl p

theorem compContains_eq {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (p : Pos) :
    d.compContains p = gs.comp.contains p :=
  hrel.h_compTbl p

theorem trivial_eq {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (Δ : ℕ) (p : Pos) :
    d.trivial Δ p = gs.trivial Δ p := by
  unfold Tier2Gs.trivial GameState.trivial
  rw [hrel.compContains_eq, hrel.h_tL]
  congr 2
  have hz := hrel.h_posNode_zero_iff p
  cases hbeq : (d.posNode p.sender p.epoch p.idx == 0)
  · have hne0 : d.posNode p.sender p.epoch p.idx ≠ 0 := by
      intro h; rw [h] at hbeq; cases hbeq
    have hex : ∃ r ∈ gs.trans, r.pos = p := by
      by_contra hno
      exact hne0 (hz.mpr (fun r hr heq => hno ⟨r, hr, heq⟩))
    rcases hex with ⟨r, hr, rfl⟩
    have hany : (gs.trans.any fun r' => r'.pos == r.pos) = true :=
      List.any_eq_true.mpr ⟨r, hr, beq_self_eq_true _⟩
    simp [hany]
  · have heq0 : d.posNode p.sender p.epoch p.idx = 0 := of_decide_eq_true hbeq
    have hall := hz.mp heq0
    have hany : (gs.trans.any fun r' => r'.pos == p) = false := by
      rw [Bool.eq_false_iff]
      intro hany
      rcases List.any_eq_true.mp hany with ⟨r, hr, hreq⟩
      exact hall r hr (beq_iff_eq.mp hreq)
    simp [hany]

private theorem countP_beq_zero_eq_not_any {α : Type} (L : List α) (f : α → Bool) :
    (L.countP f == 0) = !(L.any f) := by
  cases hany : L.any f
  · have h0 : L.countP f = 0 := by
      rw [List.countP_eq_zero]
      intro x hx hfx
      have : L.any f = true := List.any_eq_true.mpr ⟨x, hx, hfx⟩
      rw [hany] at this; cases this
    rw [h0]; rfl
  · rcases List.any_eq_true.mp hany with ⟨x, hx, hfx⟩
    have hpos : 0 < L.countP f := List.countP_pos_iff.mpr ⟨x, hx, hfx⟩
    have hne : (L.countP f == 0) = false := by
      rw [beq_eq_false_iff_ne]; omega
    rw [hne]; rfl

theorem corrAllowed_eq {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (P : Party) :
    d.corrAllowed P = gs.corrAllowed P := by
  unfold Tier2Gs.corrAllowed GameState.corrAllowed
  rw [hrel.h_challCount, hrel.h_uncompCount, countP_beq_zero_eq_not_any, countP_beq_zero_eq_not_any]

theorem inTransit_eq {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (Q : Party) (c : Bytes) :
    d.inTransit Q c = gs.inTransit Q c := by
  unfold Tier2Gs.inTransit GameState.inTransit
  cases hck : spkWireKeyVal ℓ c with
  | none =>
    symm
    rw [List.find?_eq_none]
    intro r hr
    rw [Bool.and_eq_true_iff]
    rintro ⟨_, hct⟩
    have hreq : r.ct = c := of_decide_eq_true hct
    obtain ⟨_, _, _, hrk⟩ := hrel.h_trans_nodes r hr
    rw [hreq, hck] at hrk
    cases hrk
  | some k =>
    have hpred : ∀ r ∈ gs.trans,
        ((r.pos.sender == Q) && decide (r.ct = c)) =
          ((r.pos.sender == Q) && decide (spkWireKeyVal ℓ r.ct = some k)) := by
      intro r hr
      congr 1
      by_cases heq : r.ct = c
      · subst heq; simp [hck]
      · have hne_k : spkWireKeyVal ℓ r.ct ≠ some k :=
          fun hk => heq (spkWireKeyVal_injective hℓ hk hck)
        simp [heq, hne_k]
    have hfind : (gs.trans.find? fun r => (r.pos.sender == Q) && decide (r.ct = c)) =
        (gs.trans.filter fun r =>
          (r.pos.sender == Q) && decide (spkWireKeyVal ℓ r.ct = some k)).head? := by
      have hcongr : (gs.trans.find? fun r => (r.pos.sender == Q) && decide (r.ct = c)) =
          (gs.trans.find? fun r =>
            (r.pos.sender == Q) && decide (spkWireKeyVal ℓ r.ct = some k)) :=
        List.find?_congr hpred
      rw [hcongr, List.head?_filter]
    dsimp only
    rw [hfind, hrel.h_head Q k]
    unfold bucketIds
    cases hfilt : gs.trans.filter (fun r =>
        (r.pos.sender == Q) && decide (spkWireKeyVal ℓ r.ct = some k)) with
    | nil => simp [headOf, hrel.h_node0]
    | cons r0 rs =>
      have hr0_mem : r0 ∈ gs.trans :=
        (List.mem_filter.mp (hfilt ▸ List.mem_cons_self)).1
      simp only [List.map_cons, headOf, List.head?_cons]
      exact (hrel.h_trans_nodes r0 hr0_mem).2.2.1

theorem leak_preserves {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (l : ℕ) :
    Tier2GsRel ℓ (gs.leak l) (d.leak l) :=
  { hrel with h_tL := by simp [Tier2Gs.leak, GameState.leak, hrel.h_tL] }

theorem epMgmt_preserves {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (Δ qep : ℕ) (P : Party) (bad : Bool) :
    ((gs.epMgmt Δ qep P bad).isNone = (d.epMgmt Δ qep P bad).isNone) ∧
    ∀ gs' d', gs.epMgmt Δ qep P bad = some gs' → d.epMgmt Δ qep P bad = some d' →
      Tier2GsRel ℓ gs' d' := by
  unfold GameState.epMgmt Tier2Gs.epMgmt
  have hsafe := hrel.safeCh_eq Δ P
  rw [hrel.h_epoch, hsafe]
  by_cases hs : P.sendsIn (gs.epoch P + 1)
  · simp only [hs, ↓reduceIte]
    by_cases hq : qep < gs.epoch P + 1
    · simp [hq]
    · simp only [hq, ↓reduceIte, Option.isNone_some, Option.some.injEq, true_and]
      rintro _ _ rfl rfl
      have hrel1 : Tier2GsRel ℓ
          (if (bad && !gs.safeCh Δ P) = true then gs.leak (gs.epoch P + 1) else gs)
          (if (bad && !gs.safeCh Δ P) = true then d.leak (gs.epoch P + 1) else d) := by
        split_ifs
        · exact hrel.leak_preserves (gs.epoch P + 1)
        · exact hrel
      set gs1 := if (bad && !gs.safeCh Δ P) = true then gs.leak (gs.epoch P + 1) else gs
      set d1 := if (bad && !gs.safeCh Δ P) = true then d.leak (gs.epoch P + 1) else d
      refine { hrel1 with
        h_epoch := by dsimp only; rw [hrel1.h_epoch, updParty_eq_update]
        h_idx := by dsimp only; rw [hrel1.h_idx, updParty_eq_update]
        h_pos_trans := fun r hr => by
          dsimp only
          rw [← updParty_eq_update, ← updParty_eq_update]
          exact posBound_epMgmt_adv gs1.epoch gs1.idx P (hrel1.h_pos_trans r hr)
        h_pos_chall := fun p hp => by
          dsimp only
          rw [← updParty_eq_update, ← updParty_eq_update]
          exact posBound_epMgmt_adv gs1.epoch gs1.idx P (hrel1.h_pos_chall p hp)
        h_pos_comp := fun p hp => by
          dsimp only
          rw [← updParty_eq_update, ← updParty_eq_update]
          exact posBound_epMgmt_adv gs1.epoch gs1.idx P (hrel1.h_pos_comp p hp) }
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hq : qep < gs.epoch P
    · simp [hq]
    · simp only [hq, ↓reduceIte, Option.isNone_some, Option.some.injEq, true_and]
      rintro _ _ rfl rfl
      exact hrel

theorem afterCorrAllowed_preserves {ℓ : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {d : Tier2Gs ℓ} (hrel : Tier2GsRel ℓ gs d) (P : Party)
    (hallow : gs.corrAllowed P = true) :
    Tier2GsRel ℓ (gs.afterCorr P) (d.afterCorrAllowed P) := by
  have hdedup := dedupComp_afterCorr_eq gs P hallow
  have hcont : ∀ p : Pos, (gs.afterCorr P).comp.contains p = gs.comp.contains p := fun p => by
    rw [← dedupComp_contains, hdedup, dedupComp_contains]
  have hleak := hrel.leak_preserves (max (gs.epoch .A) (gs.epoch .B))
  have hd_eq : d.afterCorrAllowed P = d.leak (max (gs.epoch .A) (gs.epoch .B)) := by
    simp [Tier2Gs.afterCorrAllowed, hrel.h_epoch]
  rw [hd_eq]
  refine { hleak with
    h_pos_comp := fun p hp => by
      simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map,
        List.mem_filter] at hp
      rcases hp with ⟨r, ⟨hr, _⟩, rfl⟩ | hp
      · exact hrel.h_pos_trans r hr
      · exact hrel.h_pos_comp p hp
    h_compTbl := fun p => (hrel.h_compTbl p).trans (hcont p).symm
    h_uncompCount := fun Q => by
      dsimp only [Tier2Gs.leak, GameState.afterCorr, GameState.leak]
      rw [hrel.h_uncompCount Q]
      refine List.countP_congr fun r _ => ?_
      have hc := hcont r.pos
      dsimp only [GameState.afterCorr, GameState.leak] at hc
      rw [hc] }

end Tier2GsRel

end Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure
