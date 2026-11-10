/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import ProofLib.Hoare.SubroutineHook

/-!
# Per-Block Ghost Ownership Token

Ghost live-block map (`MallocngLiveMap`, `MallocngLiveAuth`), per-block ownership tokens
(`MallocngBlockTokenK`, `MallocngBlockToken`, `MallocngTightBlock`), and startup `auxv`
agreement tickets (`MallocngAuxvTicket`) for `mallocng`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-- Computable injection `(a, b) ↦ (2 ^ a) * (2 * b + 1)` splitting a single `GhostName` (`Nat`)
    into an independent live-block ghost name and an `auxv`-snapshot ghost name. -/
def natPair (a b : Nat) : Nat :=
  (2 ^ a) * (2 * b + 1)

def natUnpair (n : Nat) : Nat × Nat :=
  if _ : n = 0 then (0, 0)
  else if n % 2 = 0 then
    let p := natUnpair (n / 2)
    (p.1 + 1, p.2)
  else
    (0, n / 2)
termination_by n
decreasing_by omega

theorem natUnpair_natPair (a b : Nat) :
    natUnpair (natPair a b) = (a, b) := by
  induction a with
  | zero =>
    unfold natPair
    rw [Nat.pow_zero, Nat.one_mul, natUnpair]
    have hDiv : (2 * b + 1) / 2 = b := by omega
    simp [hDiv]
  | succ a ih =>
    have hEq : natPair (a + 1) b = 2 * natPair a b := by
      unfold natPair
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have hPos : 0 < natPair a b := Nat.mul_pos (Nat.two_pow_pos a) (by omega)
    rw [hEq, natUnpair]
    have hNe : 2 * natPair a b ≠ 0 := by omega
    have hEven : (2 * natPair a b) % 2 = 0 := by omega
    have hDiv : (2 * natPair a b) / 2 = natPair a b := by omega
    simp [hNe, hEven, hDiv, ih]

theorem natUnpair_snd_le (n : Nat) : (natUnpair n).2 ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natUnpair]
    split
    · omega
    · split
      · dsimp only
        exact Nat.le_trans (ih (n / 2) (by omega)) (Nat.div_le_self n 2)
      · dsimp only
        exact Nat.div_le_self n 2

abbrev liveGhost (γ : GhostName) : GhostName := (natUnpair γ).1
abbrev auxvGhost (γ : GhostName) : GhostName := (natUnpair γ).2

/-- Ghost live-block map: `req p = some n` iff `p` is a live block of request size `n`; `ov p` is
    the recorded alignment-overhead bound of `p` (meaningful only while `req p ≠ none`). -/
structure MallocngLiveMap where
  req : BitVec 64 → Option Nat
  ov  : BitVec 64 → Nat

instance : CoeFun MallocngLiveMap (fun _ => BitVec 64 → Option Nat) := ⟨MallocngLiveMap.req⟩

namespace MallocngLiveMap

def empty : MallocngLiveMap := ⟨fun _ => none, fun _ => 0⟩

def ofReq (L : BitVec 64 → Option Nat) : MallocngLiveMap := ⟨L, fun _ => 0⟩

def insert (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat) : MallocngLiveMap :=
  ⟨fun q => if q = p then some n else L.req q, fun q => if q = p then k else L.ov q⟩

def erase (L : MallocngLiveMap) (p : BitVec 64) : MallocngLiveMap :=
  ⟨fun q => if q = p then none else L.req q, L.ov⟩

def enc (L : MallocngLiveMap) : BitVec 64 → Option Nat :=
  fun q => (L.req q).map (natPair (L.ov q))

@[simp] theorem empty_req (q : BitVec 64) : empty.req q = none := rfl
@[simp] theorem ofReq_req (L : BitVec 64 → Option Nat) : (ofReq L).req = L := rfl
@[simp] theorem ofReq_ov (L : BitVec 64 → Option Nat) (q : BitVec 64) : (ofReq L).ov q = 0 := rfl
@[simp] theorem insert_req (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat) (q : BitVec 64) :
    (L.insert p n k).req q = if q = p then some n else L.req q := rfl
@[simp] theorem insert_ov (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat) (q : BitVec 64) :
    (L.insert p n k).ov q = if q = p then k else L.ov q := rfl
@[simp] theorem erase_req (L : MallocngLiveMap) (p : BitVec 64) (q : BitVec 64) :
    (L.erase p).req q = if q = p then none else L.req q := rfl
@[simp] theorem erase_ov (L : MallocngLiveMap) (p : BitVec 64) : (L.erase p).ov = L.ov := rfl

end MallocngLiveMap

/-- Authoritative live-allocation ghost map component of `γ`. -/
def MallocngLiveAuth (γ : GhostName) (L : MallocngLiveMap) : SepProp :=
  ghostMapAuth (liveGhost γ) L.enc

@[simp]
theorem noRO_mallocngLiveAuth (γ : GhostName) (L : MallocngLiveMap) :
    SepProp.NoRO (MallocngLiveAuth γ L) :=
  SepProp.NoRO.ghostMapAuth (liveGhost γ) L.enc

/-- Pure alignment and bounds invariant carried by every live `mallocng` block token `Block γ p n`. -/
abbrev MallocngBlockWf (p : BitVec 64) (n : Nat) : Prop :=
  p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize

/-- Overhead-indexed block token: `MallocngBlockWf p n` plus the fragment `p ↦ natPair k n`, so the
    authoritative map records `ov p = k`. -/
def MallocngBlockTokenK (γ : GhostName) (p : BitVec 64) (n k : Nat) : SepProp :=
  ⌜MallocngBlockWf p n⌝ ∗ ghostMapElem (liveGhost γ) p (natPair k n)

/-- Concrete per-block ghost ownership token `Block γ p n` (overhead hidden). -/
def MallocngBlockToken (γ : GhostName) (p : BitVec 64) (n : Nat) : SepProp :=
  ∃∗ k : Nat, MallocngBlockTokenK γ p n k

/-- Alignment-indexed block token: overhead bounded by `a - 16`. -/
def MallocngTightBlock (γ : GhostName) (p : BitVec 64) (n a : Nat) : SepProp :=
  ∃∗ k : Nat, ⌜k ≤ a - 16⌝ ∗ MallocngBlockTokenK γ p n k

@[simp]
theorem noRO_mallocngBlockTokenK (γ : GhostName) (p : BitVec 64) (n k : Nat) :
    SepProp.NoRO (MallocngBlockTokenK γ p n k) :=
  SepProp.NoRO.sepConj (SepProp.NoRO.pure _) (SepProp.NoRO.ghostMapElem (liveGhost γ) p _)

@[simp]
theorem noRO_mallocngBlockToken (γ : GhostName) (p : BitVec 64) (n : Nat) :
    SepProp.NoRO (MallocngBlockToken γ p n) :=
  SepProp.NoRO.sepExists fun k => noRO_mallocngBlockTokenK γ p n k

@[simp]
theorem noRO_mallocngTightBlock (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    SepProp.NoRO (MallocngTightBlock γ p n a) :=
  SepProp.NoRO.sepExists fun k =>
    SepProp.NoRO.sepConj (SepProp.NoRO.pure _) (noRO_mallocngBlockTokenK γ p n k)

theorem mallocngBlockTokenK_to_token (γ : GhostName) (p : BitVec 64) (n k : Nat) :
    MallocngBlockTokenK γ p n k ⊢ MallocngBlockToken γ p n :=
  Entails.sepExists_intro (P := fun k => MallocngBlockTokenK γ p n k) k

theorem mallocngTightBlock_to_token (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    MallocngTightBlock γ p n a ⊢ MallocngBlockToken γ p n :=
  Entails.sepExists_elim fun k =>
    Entails.pure_left fun _ => mallocngBlockTokenK_to_token γ p n k

theorem mallocngBlockTokenK_to_tight (γ : GhostName) (p : BitVec 64) (n k a : Nat)
    (hk : k ≤ a - 16) :
    MallocngBlockTokenK γ p n k ⊢ MallocngTightBlock γ p n a :=
  Entails.sepExists_right (Q := fun k => ⌜k ≤ a - 16⌝ ∗ MallocngBlockTokenK γ p n k) k
    (Entails.pure_right hk (Entails.refl _))

theorem mallocngBlockToken_elim {γ : GhostName} {p : BitVec 64} {n : Nat} {R Q : SepProp}
    (h : ∀ k, MallocngBlockTokenK γ p n k ∗ R ⊢ Q) :
    MallocngBlockToken γ p n ∗ R ⊢ Q := by
  unfold MallocngBlockToken
  rw [sepExists_sepConj_left]
  exact Entails.sepExists_elim h

theorem mallocngBlock_noRO (γ : GhostName) (p : BitVec 64) (n : Nat)
    (h : Heap) (a : BitVec 64) (v : BitVec 8)
    (hHolds : SepProp.Holds (MallocngBlockToken γ p n) h) :
    h a ≠ some (.ro v) :=
  noRO_mallocngBlockToken γ p n h a v hHolds

theorem mallocngBlock_wf (γ : GhostName) (p : BitVec 64) (n : Nat) :
    MallocngBlockToken γ p n ⊢ ⌜MallocngBlockWf p n⌝ ∗ MallocngBlockToken γ p n := by
  unfold MallocngBlockToken
  refine Entails.sepExists_elim fun k => ?_
  unfold MallocngBlockTokenK
  refine Entails.pure_left fun hwf => Entails.pure_right hwf ?_
  exact Entails.sepExists_right (Q := fun k => ⌜MallocngBlockWf p n⌝ ∗
    ghostMapElem (liveGhost γ) p (natPair k n)) k (Entails.pure_right hwf (Entails.refl _))

theorem mallocngBlock_noWrap (γ : GhostName) (p : BitVec 64) (n : Nat) :
    MallocngBlockToken γ p n ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ MallocngBlockToken γ p n := by
  refine Entails.trans (mallocngBlock_wf γ p n) (Entails.pure_left fun hwf => ?_)
  have hnw : p.toNat + n ≤ 2 ^ 64 := Nat.le_trans hwf.2.2.1 (by decide)
  exact Entails.pure_right hnw (Entails.refl _)

theorem mallocngBlock_nonnull (γ : GhostName) (p : BitVec 64) (n : Nat) :
    MallocngBlockToken γ p n ⊢
      ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗
        MallocngBlockToken γ p n :=
  mallocngBlock_wf γ p n

theorem mallocngBlock_exclusive (γ : GhostName)
    (p₁ : BitVec 64) (n₁ : Nat) (p₂ : BitVec 64) (n₂ : Nat) :
    MallocngBlockToken γ p₁ n₁ ∗ MallocngBlockToken γ p₂ n₂ ⊢
      ⌜p₁ ≠ p₂⌝ ∗ MallocngBlockToken γ p₁ n₁ ∗ MallocngBlockToken γ p₂ n₂ := by
  by_cases hne : p₁ = p₂
  · subst hne
    refine mallocngBlockToken_elim fun k₁ => ?_
    rw [sepConj_comm]
    refine mallocngBlockToken_elim fun k₂ => ?_
    unfold MallocngBlockTokenK
    have hDrop :
        (⌜MallocngBlockWf p₁ n₂⌝ ∗ ghostMapElem (liveGhost γ) p₁ (natPair k₂ n₂)) ∗
        (⌜MallocngBlockWf p₁ n₁⌝ ∗ ghostMapElem (liveGhost γ) p₁ (natPair k₁ n₁)) ⊢
        ghostMapElem (liveGhost γ) p₁ (natPair k₂ n₂) ∗
          ghostMapElem (liveGhost γ) p₁ (natPair k₁ n₁) :=
      sepConj_mono (Entails.pure_left fun _ => Entails.refl _)
        (Entails.pure_left fun _ => Entails.refl _)
    refine Entails.trans hDrop (Entails.trans (ghostMapElem_exclusive (liveGhost γ) p₁ _ _) ?_)
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left False.elim
  · exact Entails.pure_right hne (Entails.refl _)

theorem mallocngBlockK_lookup (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat) :
    MallocngLiveAuth γ L ∗ MallocngBlockTokenK γ p n k ⊢
      ⌜MallocngBlockWf p n ∧ L p = some n ∧ L.ov p = k⌝ ∗
        MallocngLiveAuth γ L ∗ MallocngBlockTokenK γ p n k := by
  unfold MallocngLiveAuth MallocngBlockTokenK
  rw [← sepConj_assoc, sepConj_comm (ghostMapAuth (liveGhost γ) L.enc), sepConj_assoc]
  refine Entails.pure_left fun hwf => ?_
  refine Entails.trans (ghostMap_lookup (liveGhost γ) L.enc p (natPair k n)) ?_
  refine Entails.pure_left fun hLp => ?_
  have hEq : L.req p = some n ∧ L.ov p = k := by
    unfold MallocngLiveMap.enc at hLp
    cases hR : L.req p with
    | none => rw [hR] at hLp; simp at hLp
    | some m =>
      rw [hR] at hLp
      have h1 : natPair (L.ov p) m = natPair k n := Option.some.inj hLp
      have h2 := congrArg natUnpair h1
      rw [natUnpair_natPair, natUnpair_natPair] at h2
      obtain ⟨hk, hm⟩ := Prod.mk.inj h2
      exact ⟨by rw [hm], hk⟩
  rw [pure_sepConj_of_true ⟨hwf, hEq.1, hEq.2⟩, pure_sepConj_of_true hwf]
  exact Entails.refl _

theorem mallocngBlock_lookup (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n : Nat) :
    MallocngLiveAuth γ L ∗ MallocngBlockToken γ p n ⊢
      ⌜MallocngBlockWf p n ∧ L p = some n⌝ ∗
        MallocngLiveAuth γ L ∗ MallocngBlockToken γ p n := by
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine mallocngBlockToken_elim fun k => ?_
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine Entails.trans (mallocngBlockK_lookup γ L p n k) (Entails.pure_left fun h => ?_)
  exact Entails.pure_right ⟨h.1, h.2.1⟩
    (sepConj_mono (Entails.refl _) (mallocngBlockTokenK_to_token γ p n k))

theorem mallocngBlockK_alloc_bupd (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat)
    (hwf : MallocngBlockWf p n)
    (hnone : L p = none) :
    MallocngLiveAuth γ L ⊢
      |==> (MallocngLiveAuth γ (L.insert p n k) ∗ MallocngBlockTokenK γ p n k) := by
  unfold MallocngLiveAuth
  have hnone' : L.enc p = none := by
    unfold MallocngLiveMap.enc; rw [show L.req p = none from hnone]; rfl
  refine Entails.trans (ghostMap_alloc (liveGhost γ) L.enc p (natPair k n) hnone') (bupd_mono ?_)
  have hEnc : (fun q => if q = p then some (natPair k n) else L.enc q) = (L.insert p n k).enc := by
    funext q
    unfold MallocngLiveMap.enc MallocngLiveMap.insert
    by_cases hq : q = p <;> simp [hq]
  rw [hEnc]
  unfold MallocngBlockTokenK
  rw [pure_sepConj_of_true hwf]
  exact Entails.refl _

theorem mallocngBlock_alloc_bupd (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat)
    (hwf : MallocngBlockWf p n)
    (hnone : L p = none) :
    MallocngLiveAuth γ L ⊢
      |==> (MallocngLiveAuth γ (L.insert p n k) ∗ MallocngBlockToken γ p n) :=
  Entails.trans (mallocngBlockK_alloc_bupd γ L p n k hwf hnone)
    (bupd_mono (sepConj_mono (Entails.refl _) (mallocngBlockTokenK_to_token γ p n k)))

theorem mallocngBlockK_delete_bupd (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n k : Nat) :
    MallocngLiveAuth γ L ∗ MallocngBlockTokenK γ p n k ⊢
      |==> MallocngLiveAuth γ (L.erase p) := by
  unfold MallocngLiveAuth MallocngBlockTokenK
  rw [← sepConj_assoc, sepConj_comm (ghostMapAuth (liveGhost γ) L.enc), sepConj_assoc]
  refine Entails.pure_left fun _ => ?_
  have hEnc : (fun q => if q = p then none else L.enc q) = (L.erase p).enc := by
    funext q
    unfold MallocngLiveMap.enc MallocngLiveMap.erase
    by_cases hq : q = p <;> simp [hq]
  rw [← hEnc]
  exact ghostMap_delete (liveGhost γ) L.enc p (natPair k n)

theorem mallocngBlock_delete_bupd (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n : Nat) :
    MallocngLiveAuth γ L ∗ MallocngBlockToken γ p n ⊢
      |==> MallocngLiveAuth γ (L.erase p) := by
  rw [sepConj_comm (MallocngLiveAuth γ L) (MallocngBlockToken γ p n)]
  refine mallocngBlockToken_elim fun k => ?_
  rw [sepConj_comm (MallocngBlockTokenK γ p n k)]
  exact mallocngBlockK_delete_bupd γ L p n k

theorem mallocngBlockK_replace_bupd (γ : GhostName) (L : MallocngLiveMap)
    (p1 : BitVec 64) (n1 k : Nat) (p2 : BitVec 64) (n2 : Nat)
    (hwf2 : MallocngBlockWf p2 n2) (hFresh : p2 = p1 ∨ L p2 = none) :
    MallocngLiveAuth γ L ∗ MallocngBlockTokenK γ p1 n1 k ⊢
      |==> (MallocngLiveAuth γ ((L.erase p1).insert p2 n2 k) ∗ MallocngBlockTokenK γ p2 n2 k) := by
  have hNone : (L.erase p1) p2 = none := by
    show (L.erase p1).req p2 = none
    rw [MallocngLiveMap.erase_req]
    by_cases hE : p2 = p1
    · simp [hE]
    · rcases hFresh with h | hN
      · exact False.elim (hE h)
      · simp only [hE, ↓reduceIte]; exact hN
  refine Entails.trans (mallocngBlockK_delete_bupd γ L p1 n1 k) ?_
  refine Entails.trans (bupd_mono (mallocngBlockK_alloc_bupd γ (L.erase p1) p2 n2 k hwf2 hNone)) ?_
  exact bupd_trans _

theorem mallocngBlock_replaceOv_bupd (γ : GhostName) (L : MallocngLiveMap)
    (p1 : BitVec 64) (n1 : Nat) (p2 : BitVec 64) (n2 : Nat)
    (hwf2 : MallocngBlockWf p2 n2) (hFresh : p2 = p1 ∨ L p2 = none) :
    MallocngLiveAuth γ L ∗ MallocngBlockToken γ p1 n1 ⊢
      |==> (MallocngLiveAuth γ ((L.erase p1).insert p2 n2 (L.ov p1)) ∗
        MallocngBlockToken γ p2 n2) := by
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine mallocngBlockToken_elim fun k => ?_
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine Entails.trans (mallocngBlockK_lookup γ L p1 n1 k) (Entails.pure_left fun h => ?_)
  rw [h.2.2]
  exact Entails.trans (mallocngBlockK_replace_bupd γ L p1 n1 k p2 n2 hwf2 hFresh)
    (bupd_mono (sepConj_mono (Entails.refl _) (mallocngBlockTokenK_to_token γ p2 n2 k)))

theorem mallocngTightBlock_elim {γ : GhostName} {p : BitVec 64} {n a : Nat} {R Q : SepProp}
    (h : ∀ k, k ≤ a - 16 → MallocngBlockTokenK γ p n k ∗ R ⊢ Q) :
    MallocngTightBlock γ p n a ∗ R ⊢ Q := by
  unfold MallocngTightBlock
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun k => ?_
  show (⌜k ≤ a - 16⌝ ∗ MallocngBlockTokenK γ p n k) ∗ R ⊢ Q
  rw [sepConj_assoc]
  exact Entails.pure_left fun hk => h k hk

theorem mallocngTightBlock_lookup (γ : GhostName) (L : MallocngLiveMap) (p : BitVec 64) (n a : Nat) :
    MallocngLiveAuth γ L ∗ MallocngTightBlock γ p n a ⊢
      ⌜MallocngBlockWf p n ∧ L p = some n ∧ L.ov p ≤ a - 16⌝ ∗
        MallocngLiveAuth γ L ∗ MallocngTightBlock γ p n a := by
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine mallocngTightBlock_elim fun k hk => ?_
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine Entails.trans (mallocngBlockK_lookup γ L p n k) (Entails.pure_left fun h => ?_)
  exact Entails.pure_right ⟨h.1, h.2.1, h.2.2 ▸ hk⟩
    (sepConj_mono (Entails.refl _) (mallocngBlockTokenK_to_tight γ p n k a hk))

theorem mallocngTightBlock_replaceOv_bupd (γ : GhostName) (L : MallocngLiveMap)
    (p1 : BitVec 64) (n1 : Nat) (p2 : BitVec 64) (n2 a : Nat)
    (hwf2 : MallocngBlockWf p2 n2) (hFresh : p2 = p1 ∨ L p2 = none) :
    MallocngLiveAuth γ L ∗ MallocngTightBlock γ p1 n1 a ⊢
      |==> (MallocngLiveAuth γ ((L.erase p1).insert p2 n2 (L.ov p1)) ∗
        MallocngTightBlock γ p2 n2 a) := by
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine mallocngTightBlock_elim fun k hk => ?_
  refine Entails.trans (by rw [sepConj_comm]; exact Entails.refl _) ?_
  refine Entails.trans (mallocngBlockK_lookup γ L p1 n1 k) (Entails.pure_left fun h => ?_)
  rw [h.2.2]
  exact Entails.trans (mallocngBlockK_replace_bupd γ L p1 n1 k p2 n2 hwf2 hFresh)
    (bupd_mono (sepConj_mono (Entails.refl _) (mallocngBlockTokenK_to_tight γ p2 n2 k a hk)))

theorem mallocngTightBlock_noWrap (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    MallocngTightBlock γ p n a ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ MallocngTightBlock γ p n a := by
  have h : MallocngTightBlock γ p n a ∗ emp ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ MallocngTightBlock γ p n a :=
    mallocngTightBlock_elim fun k hk => by
      rw [sepConj_emp]
      have hwfE : MallocngBlockTokenK γ p n k ⊢
          ⌜MallocngBlockWf p n⌝ ∗ MallocngBlockTokenK γ p n k := by
        unfold MallocngBlockTokenK
        exact Entails.pure_left fun hwf => Entails.pure_right hwf (Entails.pure_right hwf (Entails.refl _))
      refine Entails.trans hwfE (Entails.pure_left fun hwf => ?_)
      exact Entails.pure_right (Nat.le_trans hwf.2.2.1 (by decide))
        (mallocngBlockTokenK_to_tight γ p n k a hk)
  rw [sepConj_emp] at h; exact h

set_option linter.unusedVariables false in
/-- `MallocngInitBlock mallocngIface γ` with the alignment-indexed token `MallocngTightBlock γ p sz a`
    (ghost overhead `≤ a - 16`) in place of `mallocngIface.Block γ p sz`; same `pureWf`. -/
@[reducible] def MallocngTightInitBlock (γ : GhostName) (a : Nat) :
    Arm64.CType.SemType (Nat × List (BitVec 8)) where
  tyName := "void * (mallocng block with initialized prefix, overhead ≤ a - 16)"
  interp := fun p (sz, bs) =>
    MallocngTightBlock γ p sz a ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length)
  pureWf := fun p (sz, bs) =>
    p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + sz < 2 ^ 64 ∧ bs.length ≤ sz

/-! ## Tracked Startup `auxv` Snapshot & Ghost Agreement Ticket -/

/-- Concrete startup `auxv` snapshot `(preEntries, randPtr, sufEntries, nullVal, sec)` preserved
    across `mallocngIface.MallocngCore` for post-allocator `getauxval` teardown. -/
abbrev MallocngAuxvSnap : Type :=
  List (BitVec 64 × BitVec 64) × BitVec 64 × List (BitVec 64 × BitVec 64) × BitVec 64 × BitVec 64

def encodePairList : List (BitVec 64 × BitVec 64) → Nat
  | [] => 0
  | (t, v) :: rest => natPair (natPair t.toNat v.toNat) (encodePairList rest) + 1

def decodePairList (n : Nat) : List (BitVec 64 × BitVec 64) :=
  if _ : n = 0 then []
  else
    let p := natUnpair (n - 1)
    let tv := natUnpair p.1
    (BitVec.ofNat 64 tv.1, BitVec.ofNat 64 tv.2) :: decodePairList p.2
termination_by n
decreasing_by
  have hLe := natUnpair_snd_le (n - 1)
  omega

theorem decodePairList_encodePairList (xs : List (BitVec 64 × BitVec 64)) :
    decodePairList (encodePairList xs) = xs := by
  induction xs with
  | nil =>
    simp [encodePairList, decodePairList]
  | cons hd rest ih =>
    rcases hd with ⟨t, v⟩
    unfold encodePairList
    rw [decodePairList]
    simp [natUnpair_natPair, ih]

def encodeAuxvSnap (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) : Nat :=
  let (pre, randPtr, suf, nullVal, sec) := snap
  natPair auxvPtr.toNat
    (natPair (encodePairList pre)
      (natPair randPtr.toNat
        (natPair (encodePairList suf)
          (natPair nullVal.toNat sec.toNat))))

def decodeAuxvSnap (n : Nat) : BitVec 64 × MallocngAuxvSnap :=
  let p0 := natUnpair n
  let p1 := natUnpair p0.2
  let p2 := natUnpair p1.2
  let p3 := natUnpair p2.2
  let p4 := natUnpair p3.2
  (BitVec.ofNat 64 p0.1,
    (decodePairList p1.1, BitVec.ofNat 64 p2.1, decodePairList p3.1,
     BitVec.ofNat 64 p4.1, BitVec.ofNat 64 p4.2))

theorem decodeAuxvSnap_encodeAuxvSnap (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) :
    decodeAuxvSnap (encodeAuxvSnap auxvPtr snap) = (auxvPtr, snap) := by
  rcases snap with ⟨pre, randPtr, suf, nullVal, sec⟩
  simp [encodeAuxvSnap, decodeAuxvSnap, natUnpair_natPair, decodePairList_encodePairList]

/-- Ghost agreement ticket witnessing that `mallocngIface.MallocngCore γ` was initialized from the
    concrete startup `auxv` table `(auxvPtr, snap)` instead of existentialized `MallocngAuxvAt`. -/
def MallocngAuxvTicket (γ : GhostName) (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) : SepProp :=
  ghostMapElem (auxvGhost γ) 0#64 (encodeAuxvSnap auxvPtr snap)

@[simp]
theorem noRO_mallocngAuxvTicket (γ : GhostName) (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) :
    SepProp.NoRO (MallocngAuxvTicket γ auxvPtr snap) :=
  SepProp.NoRO.ghostMapElem (auxvGhost γ) 0#64 (encodeAuxvSnap auxvPtr snap)

end VerifiedLibraries.Mallocng.Proofs
