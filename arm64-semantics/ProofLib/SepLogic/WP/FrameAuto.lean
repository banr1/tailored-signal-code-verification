/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP.Structural
public import ProofLib.SepLogic.WP.TacticCore
public import ProofLib.SepLogic.FrameInfer
public import ProofLib.SepLogic.ByteRegion
public import ProofLib.SepLogic.Stack
import Arm64.Trusted.Spec.SepLogic

/-!
# Frame-Inferring `SepWP` Rules

Structural `SepWP` rules (`SepWP.frame_post_entails`, `SepWP.frame_auto`,
`SepWP.call_subroutine_frame_auto`) whose residual frame `F` and callee ghost arguments are
inferred automatically by `sep_frame`, together with framed precondition view-shifts on memory
regions, cells, and byte slices.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Frame rule for `SepWP` with an entailment-shaped postcondition: running `P₀` to a final
    context entailing `P'` also runs `P₀ ∗ F` to a final context entailing `P' ∗ F`. -/
theorem SepWP.frame_post_entails {prog : Program} {target_pc : BitVec 64} {s : State}
    {P₀ P' F : SepProp} {Q : State → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P₀ (fun sf Pf => (Pf ⊢ P') ∧ Q sf) oom) :
    SepWP prog target_pc s (P₀ ∗ F) (fun sf Pf => (Pf ⊢ P' ∗ F) ∧ Q sf) oom := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono (h (F ∗ R) hm) ?_ (fun _ _ ho => Satisfies.drop_mid ho)
  intro sf _ _ ⟨Pf, hmf, hent, hQ⟩
  exact ⟨Pf ∗ F, by rw [sepConj_assoc]; exact hmf, sepConj_mono_left hent, hQ⟩

/-- Frame-inferring `SepWP.frame_post_entails`: the goal precondition `P` only has to contain the
    atoms of the step's precondition `P₀` (in any order and association, up to address
    normalization, region carving and ghost unification); `sep_frame` proves `P = P₀ ∗ F` and so
    computes the frame `F`.

    Typical use: `refine SepWP.seq (SepWP.frame_auto (step_lemma ...)) ?_`. -/
theorem SepWP.frame_auto {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P₀ P' F : SepProp} {Q : State → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P₀ (fun sf Pf => (Pf ⊢ P') ∧ Q sf) oom)
    (hsplit : P = P₀ ∗ F := by sep_frame) :
    SepWP prog target_pc s P (fun sf Pf => (Pf ⊢ P' ∗ F) ∧ Q sf) oom := by
  subst hsplit
  exact SepWP.frame_post_entails h

/-- `SepWP.call_subroutine_frame` with the caller frame `F` inferred: the premise `hpre` is
    discharged last by `sep_frame`, which cancels the callee precondition `spec.pre x s` (unfolded
    from a concrete `Spec`) against the current context `P`, assigns `F` to the unmatched atoms
    and, when `x` is not given, the callee ghost argument by unification. Pure atoms of the
    precondition are closed from local hypotheses.

    Typical use:
    ```
    refine SepWP.call_subroutine_frame_auto hcallee hpc hrun halign hlr ?_ ?_ ?_
    ```
    leaving the panic, exit and continuation goals; the continuation's context is
    `spec.post x s sf ∗ F` with `F` already instantiated. -/
theorem SepWP.call_subroutine_frame_auto {α : Type} {prog : Program} {entry target_pc : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ret_pc : BitVec 64}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post oom)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)) := by sep_frame)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom :=
  SepWP.call_subroutine_frame hcall hpc hrun hsp_align hlr hpre h_no_panic h_no_exit hnext h_oom

/-! ## Region, Cell, and Byte-Slice View-Shift Combinators -/

/-- Precondition weakening on the left framed component (`A ⊢ B` lifts `B ∗ F` to `A ∗ F`,
    shaped for `sep_frame_apply`). -/
theorem SepWP.weaken_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {A B F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hAB : A ⊢ B) (h : SepWP prog target_pc s (B ∗ F) post oom) :
    SepWP prog target_pc s (A ∗ F) post oom :=
  SepWP.weaken_pre (sepConj_mono_left hAB) h

abbrev SepWP.weakenFrame := @SepWP.weaken_left

/-- Fold a byte cell `a ↦₈ v` back into `memRegion a 1` in a `SepWP` precondition. -/
theorem SepWP.byte_merge {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) (v : BitVec 8)
    (h : SepWP prog target_pc s (memRegion a 1 ∗ F) post oom)
    (hf : P = (a ↦₈ v) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf]
  refine SepWP.weaken_pre ?_ h
  rw [memRegion_one]
  exact sepConj_mono_left (Entails.sepExists_right v (Entails.refl _))

/-- Carve `[b + k, b + k + m)` out of `memRegion b N` in a `SepWP` precondition. -/
theorem SepWP.region_split3 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (b : BitVec 64) (N k m : Nat) (hk : k + m ≤ N) (hN : N ≤ 2 ^ 64)
    (h : SepWP prog target_pc s ((memRegion (b + BitVec.ofNat 64 k) m ∗
      (memRegion b k ∗ memRegion (b + BitVec.ofNat 64 (k + m)) (N - k - m))) ∗ F) post oom)
    (hf : P = memRegion b N ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rwa [hf, memRegion_split3 b N k m hk hN]

/-- Rejoin the three pieces produced by `SepWP.region_split3` back into `memRegion b N`. -/
theorem SepWP.region_merge3 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (b : BitVec 64) (N k m : Nat) (hk : k + m ≤ N) (hN : N ≤ 2 ^ 64)
    (h : SepWP prog target_pc s (memRegion b N ∗ F) post oom)
    (hf : P = (memRegion (b + BitVec.ofNat 64 k) m ∗
      (memRegion b k ∗ memRegion (b + BitVec.ofNat 64 (k + m)) (N - k - m))) ∗ F := by
      sep_focus) :
    SepWP prog target_pc s P post oom := by
  rwa [hf, ← memRegion_split3 b N k m hk hN]

/-- Split `memRegion p N` at byte `k` (`N = k + m`) in a `SepWP` precondition. -/
theorem SepWP.region_split {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) (N k m : Nat) {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hN : N = k + m := by decide) (hb : N ≤ 2 ^ 64 := by decide)
    (hP : P = memRegion p N ∗ F := by sep_focus)
    (h : SepWP prog tpc s (memRegion p k ∗ memRegion (p + BitVec.ofNat 64 k) m ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  subst hN; rw [hP, memRegion_split p k m hb, sepConj_assoc]; exact h

/-- Merge `memRegion p k ∗ memRegion (p + k) m` back into `memRegion p N` (`N = k + m`). -/
theorem SepWP.region_merge {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) (N k m : Nat) {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hN : N = k + m := by decide) (hb : N ≤ 2 ^ 64 := by decide)
    (hP : P = (memRegion p k ∗ memRegion (p + BitVec.ofNat 64 k) m) ∗ F := by sep_focus)
    (h : SepWP prog tpc s (memRegion p N ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  subst hN; rw [hP, ← memRegion_split p k m hb]; exact h

/-- Peel the first 64-bit cell off `memRegion p n` (`n = 8 + m`). -/
theorem SepWP.region_head {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) (n m : Nat) {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (hP : P = memRegion p n ∗ F := by sep_focus)
    (h : ∀ v : BitVec 64, SepWP prog tpc s ((p ↦₆₄ v) ∗ memRegion (p + 8#64) m ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  subst hnm
  rw [hP, memRegion_split p 8 m hb, memRegion_eight, sepConj_assoc, sepExists_sepConj_left]
  exact SepWP.exists_elim fun v => by simpa only [sepConj_assoc] using h v

/-- Fold a 64-bit head cell back into `memRegion p n` (`n = 8 + m`). -/
theorem SepWP.head_region {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) (n m : Nat) {v : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (hP : P = ((p ↦₆₄ v) ∗ memRegion (p + 8#64) m) ∗ F := by sep_focus)
    (h : SepWP prog tpc s (memRegion p n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  subst hnm
  rw [hP]
  refine SepWP.weaken_pre (sepConj_mono_left ?_) h
  rw [memRegion_split p 8 m hb]
  exact sepConj_mono_left (pointsTo64_entails_memRegion p v)

/-- Open an 8-byte region as one 64-bit cell. -/
theorem SepWP.region_last {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hP : P = memRegion p 8 ∗ F := by sep_focus)
    (h : ∀ v : BitVec 64, SepWP prog tpc s ((p ↦₆₄ v) ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  rw [hP, memRegion_eight, sepExists_sepConj_left]; exact SepWP.exists_elim h

/-- Fold one 64-bit cell back into an 8-byte region. -/
theorem SepWP.last_region {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) {v : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hP : P = (p ↦₆₄ v) ∗ F := by sep_focus)
    (h : SepWP prog tpc s (memRegion p 8 ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  rw [hP]; exact SepWP.weaken_pre (sepConj_mono_left (pointsTo64_entails_memRegion p v)) h

/-- `open_cells p n k`: peel `k` 64-bit cells off `memRegion p n` (at `p`, `p + 8#64`, ...). -/
syntax "open_cells " term:max num num : tactic
macro_rules
  | `(tactic| open_cells $p $n $k) => do
    let (n, k) := (n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then `(tactic| (apply SepWP.region_last $p; intro _)) else
    let n' := Lean.Syntax.mkNumLit (toString (n - 8))
    let k' := Lean.Syntax.mkNumLit (toString (k - 1))
    `(tactic| (apply SepWP.region_head $p $(Lean.quote n) $n'; intro _; open_cells ($p + 8#64) $n' $k'))

/-- `close_cells p n k`: inverse of `open_cells p n k`. -/
syntax "close_cells " term:max num num : tactic
macro_rules
  | `(tactic| close_cells $p $n $k) => do
    let (n, k) := (n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then `(tactic| apply SepWP.last_region $p) else
    let n' := Lean.Syntax.mkNumLit (toString (n - 8))
    let k' := Lean.Syntax.mkNumLit (toString (k - 1))
    `(tactic| (close_cells ($p + 8#64) $n' $k'; apply SepWP.head_region $p $(Lean.quote n) $n'))

/-- Two 64-bit cells are the 16-byte slice `unpack64 w0 ++ unpack64 w1`. -/
theorem SepWP.words_bytes16 {prog : Program} {tpc : BitVec 64} {s : State}
    (p : BitVec 64) {w0 w1 : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hP : P = ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1)) ∗ F := by sep_focus)
    (h : SepWP prog tpc s ((p ↦ₛ (unpack64 w0 ++ unpack64 w1)) ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  rwa [hP, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, ← unpack64_length w0,
    ← pointsToBytes_append]

/-- Inverse of `SepWP.words_bytes16`. -/
theorem SepWP.bytes16_words {prog : Program} {tpc : BitVec 64} {s : State}
    (p w0 w1 : BitVec 64) {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hP : P = (p ↦ₛ (unpack64 w0 ++ unpack64 w1)) ∗ F := by sep_focus)
    (h : SepWP prog tpc s ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  rwa [hP, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes, sepConj_assoc]

/-- Open `k` 8-byte stack cells at `a`, carved (by `sep_frame`) out of whatever stack regions
    cover them; follow with `cells_unfold` and `SepWP.exists_elim` to name the old contents. -/
theorem SepWP.open_cells {prog : Program} {tpc : BitVec 64} {s : State}
    (a : BitVec 64) (k : Nat) {P F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp} (hk : 8 * k ≤ 2 ^ 64 := by decide)
    (hP : P ⊢ memRegion a (8 * k) ∗ F := by sep_frame)
    (h : SepWP prog tpc s (cells a k ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  rw [← memRegion_cells a k hk] at h
  exact SepWP.weaken_pre hP h

/-- Reshape the precondition to `Q ∗ F` (frame `F` and any region carving/merging found by
    `sep_frame`), e.g. to hand a tail-called callee its expected stack frame. -/
theorem SepWP.reframe {prog : Program} {tpc : BitVec 64} {s : State}
    (Q : SepProp) {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ Q ∗ F := by sep_frame)
    (h : SepWP prog tpc s (Q ∗ F) post oom) :
    SepWP prog tpc s P post oom :=
  SepWP.weaken_pre hP h

/-- Forget the contents of the stack words `a ↦₆₄* ws` (values found by `sep_frame`), so that the
    resulting `memRegion` can be merged back into the caller-visible stack region. -/
theorem SepWP.forget_words {prog : Program} {tpc : BitVec 64} {s : State}
    (a : BitVec 64) (ws : List (BitVec 64)) (n : Nat) {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hn : 8 * ws.length = n := by simp) (hk : n ≤ 2 ^ 64 := by decide)
    (hP : P ⊢ (a ↦₆₄* ws) ∗ F := by
      simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp]; sep_frame)
    (h : SepWP prog tpc s (memRegion a n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  subst hn
  exact SepWP.weaken_pre (Entails.trans hP
    (sepConj_mono_left (pointsToWords64_entails_memRegion ws a hk))) h

/-- View the region `memRegion a n` of the precondition as an arbitrary byte slice. -/
theorem SepWP.memRegion_bytes {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64 := by decide)
    (hf : P = memRegion a n ∗ F := by sep_focus)
    (h : ∀ bs : List (BitVec 8), bs.length = n → SepWP prog target_pc s ((a ↦ₛ bs) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, memRegion_eq_exists_bytes a n hn, sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  exact SepWP.pure_elim (h bs)

/-- Forget the contents of a byte slice of known length in the precondition. -/
theorem SepWP.bytes_memRegion {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) (n : Nat) {bs : List (BitVec 8)}
    (h : SepWP prog target_pc s (memRegion a n ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus)
    (hn : bs.length = n := by byte_region_len) :
    SepWP prog target_pc s P post oom := by
  rw [hf]
  refine SepWP.weaken_pre (sepConj_mono_left ?_) h
  rw [← hn]; exact pointsToBytes_entails_memRegion a bs

/-- Replace the contents of a byte slice in the precondition by an equal list. -/
theorem SepWP.bytes_congr {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {bs : List (BitVec 8)} (bs' : List (BitVec 8))
    (h : SepWP prog target_pc s ((a ↦ₛ bs') ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus)
    (heq : bs = bs') :
    SepWP prog target_pc s P post oom := by
  rw [hf, heq]; exact h

/-- Turn an 8-byte slice of the precondition back into a 64-bit cell. -/
theorem SepWP.bytes_word {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {bs : List (BitVec 8)} (v : BitVec 64)
    (h : SepWP prog target_pc s ((a ↦₆₄ v) ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus)
    (heq : bs = unpack64 v) :
    SepWP prog target_pc s P post oom := by
  rw [hf, heq, ← pointsTo64_eq_pointsToBytes]; exact h

/-- Replace an atom of the precondition by an equal one. -/
theorem SepWP.atom_congr {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (Q Q' : SepProp) (hQ : Q = Q') (h : SepWP prog target_pc s (Q' ∗ F) post oom)
    (hf : P = Q ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf, hQ]; exact h

/-- Weaken a byte slice of the precondition to a predicate it entails. -/
theorem SepWP.bytes_entails {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {bs : List (BitVec 8)} (Q : SepProp) (hent : (a ↦ₛ bs) ⊢ Q)
    (h : SepWP prog target_pc s (Q ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf]; exact SepWP.weaken_pre (sepConj_mono_left hent) h

/-- Turn an 8-byte slice of the precondition back into a 64-bit cell. -/
theorem SepWP.bytes8_cell {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {bs : List (BitVec 8)}
    (h : SepWP prog target_pc s ((a ↦₆₄ ByteSlice.readLE bs 0 8) ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus)
    (hn : bs.length = 8 := by byte_region_len) :
    SepWP prog target_pc s P post oom := by
  rw [hf, pointsToBytes8_eq_cell a bs hn]; exact h

/-- Alias for `SepWP.bytes8_cell`. -/
abbrev SepWP.bytes_cell8 := @SepWP.bytes8_cell

/-- Turn an 8-byte slice with low byte `t` into a cell holding some word with low byte `t`. -/
theorem SepWP.bytes8_cell_ex {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {bs : List (BitVec 8)} {t : BitVec 8}
    (h : ∀ w : BitVec 64, w.extractLsb' 0 8 = t → SepWP prog target_pc s ((a ↦₆₄ w) ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus)
    (hn : bs.length = 8 := by byte_region_len)
    (ht : bs.getD 0 0#8 = t) :
    SepWP prog target_pc s P post oom := by
  rw [hf, pointsToBytes8_eq_cell a bs hn]
  exact h _ (by rw [readLE8_lowByte, ht])

/-- Forget the padding bytes of a cell whose low byte is known. -/
theorem SepWP.cell_lowByte_pad {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {w : BitVec 64} {t : BitVec 8}
    (h : SepWP prog target_pc s ((a ↦₈ t) ∗ memRegion (a + 1#64) 7 ∗ F) post oom)
    (hf : P = (a ↦₆₄ w) ∗ F := by sep_focus)
    (ht : w.extractLsb' 0 8 = t) :
    SepWP prog target_pc s P post oom := by
  rw [hf]
  refine SepWP.weaken_pre ?_ h
  rw [← sepConj_assoc, ← ht]
  exact sepConj_mono_left (cell_entails_lowByte_pad a w)

/-- Fold a byte and the 7 bytes after it back into a 64-bit cell. -/
theorem SepWP.byte_tail_cell {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F1 F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a a1 : BitVec 64) {x : BitVec 8} {rest : List (BitVec 8)}
    (h : SepWP prog target_pc s ((a ↦₆₄ ByteSlice.readLE (x :: rest) 0 8) ∗ F) post oom)
    (hf1 : P = (a ↦₈ x) ∗ F1 := by sep_focus)
    (hf2 : F1 = (a1 ↦ₛ rest) ∗ F := by sep_focus)
    (ha : a + 1#64 = a1 := by bv_arith)
    (hn : rest.length = 7 := by first | rfl | simp) :
    SepWP prog target_pc s P post oom := by
  rw [hf1, hf2, ← ha, ← sepConj_assoc, ← pointsToBytes_cons,
    pointsToBytes8_eq_cell a _ (by simp only [List.length_cons, hn])]
  exact h

/-- Forget the value of a 64-bit cell of the precondition. -/
theorem SepWP.cell_forget {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {v : BitVec 64}
    (h : ∀ w : BitVec 64, SepWP prog target_pc s ((a ↦₆₄ w) ∗ F) post oom)
    (hf : P = (a ↦₆₄ v) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf]; exact h v

/-- View an 8-byte `memRegion` in the precondition as an arbitrary 64-bit cell. -/
theorem SepWP.memRegion8_cell {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (h : ∀ w : BitVec 64, SepWP prog target_pc s ((a ↦₆₄ w) ∗ F) post oom)
    (hf : P = memRegion a 8 ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.memRegion_bytes a 8 (by decide) hf fun bs hbs => ?_
  match bs, hbs with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    rw [pointsToBytes8_eq_pointsTo64]
    exact h _

/-- View a 4-byte `memRegion` in the precondition as an arbitrary 32-bit cell. -/
theorem SepWP.memRegion4_cell {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (h : ∀ w : BitVec 32, SepWP prog target_pc s ((a ↦₃₂ w) ∗ F) post oom)
    (hf : P = memRegion a 4 ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.memRegion_bytes a 4 (by decide) hf fun bs hbs => ?_
  match bs, hbs with
  | [b0, b1, b2, b3], _ =>
    have heq : [b0, b1, b2, b3] = unpack32 (b3 ++ b2 ++ b1 ++ b0) := by
      simp only [unpack32, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_slice
    rw [heq, ← pointsTo32_eq_pointsToBytes]
    exact h _

/-- Forget the contents of a 4-byte slice and view it as an arbitrary 32-bit cell. -/
theorem SepWP.bytes4_to_cell32 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {bs : List (BitVec 8)} (hbs : bs.length = 4)
    (h : ∀ w : BitVec 32, SepWP prog target_pc s ((a ↦₃₂ w) ∗ F) post oom)
    (hf : P = (a ↦ₛ bs) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.bytes_memRegion a 4 ?_ hf hbs
  exact SepWP.memRegion4_cell a h

/-- Merge two adjacent `memRegion`s in the precondition. -/
theorem SepWP.memRegion_join {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a b : BitVec 64) (n m k : Nat)
    (h : SepWP prog target_pc s (memRegion a k ∗ F) post oom)
    (hf : P = (memRegion a n ∗ memRegion b m) ∗ F := by sep_focus)
    (hb : b = a + BitVec.ofNat 64 n := by bv_lin)
    (hnm : n + m = k := by omega)
    (hk : k ≤ 2 ^ 64 := by decide) :
    SepWP prog target_pc s P post oom := by
  rw [hf, hb, ← memRegion_split a n m (by omega), hnm]
  exact h

/-- Merge two adjacent byte slices in the precondition. -/
theorem SepWP.bytes_join {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a b : BitVec 64) {xs ys : List (BitVec 8)} (zs : List (BitVec 8))
    (h : SepWP prog target_pc s ((a ↦ₛ zs) ∗ F) post oom)
    (hf : P = ((a ↦ₛ xs) ∗ (b ↦ₛ ys)) ∗ F := by sep_focus)
    (hb : b = a + BitVec.ofNat 64 xs.length := by bv_lin)
    (heq : xs ++ ys = zs) :
    SepWP prog target_pc s P post oom := by
  rw [hf, hb, ← pointsToBytes_append a xs ys, heq]
  exact h

/-- Split a byte slice `a ↦ₛ (enc ++ rest)` into `a ↦ₛ enc` and a trailing `memRegion`. -/
theorem SepWP.bytes_split_tail {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) (enc rest : List (BitVec 8)) (dstLen : Nat)
    (hr : rest.length = dstLen - enc.length)
    (h : SepWP prog target_pc s
      (((a ↦ₛ enc) ∗ memRegion (a + BitVec.ofNat 64 enc.length) (dstLen - enc.length)) ∗ F) post oom)
    (hf : P = (a ↦ₛ (enc ++ rest)) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf, pointsToBytes_append]
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right ?_)) h
  rw [← hr]
  exact pointsToBytes_entails_memRegion _ _

/-- Thread an auxiliary continuation fact `Q post oom` into a `SepWP` proof. -/
theorem SepWP.with_cont {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {Q : (State → SepProp → Prop) → (State → SepProp) → Prop}
    (hq : Q post oom) (h : Q post oom → SepWP prog target s P post oom) :
    SepWP prog target s P post oom :=
  h hq

/-- Forget three consecutive 64-bit cells into a 24-byte `memRegion`. -/
theorem SepWP.cells3_memRegion24 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {c1 c2 c3 : BitVec 64}
    (h : SepWP prog target_pc s (memRegion a 24 ∗ F) post oom)
    (hf : P = ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ c2) ∗ ((a + 16#64) ↦₆₄ c3)) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf]
  refine SepWP.weaken_pre (sepConj_mono_left ?_) h
  have heq : ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ c2) ∗ ((a + 16#64) ↦₆₄ c3)) =
      (a ↦ₛ (unpack64 c1 ++ unpack64 c2 ++ unpack64 c3)) := by
    rw [pointsToBytes_append, pointsToBytes_append]
    simp only [List.length_append, unpack64_length, Nat.reduceAdd,
      ← pointsTo64_eq_pointsToBytes, sepConj_assoc]
  rw [heq, show (24 : Nat) = (unpack64 c1 ++ unpack64 c2 ++ unpack64 c3).length by simp]
  exact pointsToBytes_entails_memRegion a _

/-- Unpack a 24-byte slice in the precondition into three consecutive 64-bit cells. -/
theorem SepWP.bytes24_cells3 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64) {rb : List (BitVec 8)} (hrb : rb.length = 24)
    (h : ∀ v1 v2 v3 : BitVec 64,
      SepWP prog target_pc s (((a ↦₆₄ v1) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v3)) ∗ F) post oom)
    (hf : P = (a ↦ₛ rb) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  have h0 : (rb.take 8).length = 8 := by simp [hrb]
  have h1 : (rb.drop 8).length = 16 := by simp [hrb]
  obtain ⟨v1, hv1⟩ := exists_unpack64_of_length_8 h0
  obtain ⟨v2, v3, _, hv23⟩ := exists_unpack64_of_length_16 h1
  have hsplit : rb = rb.take 8 ++ rb.drop 8 := (List.take_append_drop 8 rb).symm
  rw [hf, hsplit, pointsToBytes_append, h0, hv1, ← pointsTo64_eq_pointsToBytes,
    show a + BitVec.ofNat 64 8 = a + 8#64 from rfl, hv23 (a + 8#64),
    show a + 8#64 + 8#64 = a + 16#64 from by bv_omega]
  exact h v1 v2 v3

/-- Recombine a bottom `memRegion` and a shrunken `stackAt` back into `stackAt sp M`. -/
theorem SepWP.unshrink_stack {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (sp : BitVec 64) (M K : Nat) (hMK : K ≤ M) (hM : M ≤ 2 ^ 64 := by decide)
    (h : SepWP prog target_pc s (stackAt sp M ∗ F) post oom)
    (hf : P = (memRegion (sp - BitVec.ofNat 64 M) (M - K) ∗ stackAt sp K) ∗ F := by sep_focus) :
    SepWP prog target_pc s P post oom := by
  rw [hf, ← stackAt_shrink sp M K hMK hM]; exact h

/-- Re-slice three 64-bit cells at `p` into a 16-bit head and 2-byte-offset 64/16/32-bit pieces. -/
theorem SepWP.to_offset2 {prog : Program} {target : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (p : BitVec 64) {w0 w1 w2 : BitVec 64}
    (h : SepWP prog target s (((p ↦₁₆ w0.extractLsb' 0 16) ∗
      ((p + 2#64) ↦₆₄ (w1.extractLsb' 0 16 ++ w0.extractLsb' 16 48)) ∗
      ((p + 10#64) ↦₆₄ (w2.extractLsb' 0 16 ++ w1.extractLsb' 16 48)) ∗
      ((p + 18#64) ↦₁₆ w2.extractLsb' 16 16) ∗
      ((p + 20#64) ↦₃₂ w2.extractLsb' 32 32)) ∗ F) post oom)
    (hf : P = ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2)) ∗ F := by sep_focus) :
    SepWP prog target s P post oom := by
  rw [hf, triple_to_offset2]; exact h

/-- Reassemble three 64-bit cells at `p` from a 16-bit head and 2-byte-offset 64/16/32-bit pieces. -/
theorem SepWP.from_offset2 {prog : Program} {target : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (p : BitVec 64) (w0 w1 w2 : BitVec 64) {h16 t16 : BitVec 16} {u0 u1 : BitVec 64} {t32 : BitVec 32}
    (hu0 : u0 = w1.extractLsb' 0 16 ++ w0.extractLsb' 16 48)
    (hu1 : u1 = w2.extractLsb' 0 16 ++ w1.extractLsb' 16 48)
    (h : SepWP prog target s (((p ↦₆₄ (w0.extractLsb' 16 48 ++ h16)) ∗
      ((p + 8#64) ↦₆₄ w1) ∗
      ((p + 16#64) ↦₆₄ (t32 ++ t16 ++ w2.extractLsb' 0 16))) ∗ F) post oom)
    (hf : P = ((p ↦₁₆ h16) ∗ ((p + 2#64) ↦₆₄ u0) ∗ ((p + 10#64) ↦₆₄ u1) ∗
      ((p + 18#64) ↦₁₆ t16) ∗ ((p + 20#64) ↦₃₂ t32)) ∗ F := by sep_focus) :
    SepWP prog target s P post oom := by
  rw [hf, hu0, hu1, offset2_to_triple]; exact h

end ProofLib
