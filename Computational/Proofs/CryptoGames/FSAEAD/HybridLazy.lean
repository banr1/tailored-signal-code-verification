/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs

/-!
# Lazy Sampling of the Hybrid Slot

**Checked by Lean.**

Defines the slot-filling kernels `matFill` (resolving an unknown slot to a PRG challenge) and
`seedFill` (resolving an unknown slot at or past the frontier to a uniform chain key), and proves
that all hybrid game oracles commute with them.
-/

@[expose] public section

open OracleComp OracleSpec CryptoGames.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CryptoGames.FSAEAD.Thm5

variable {CK MK AD M C : Type}

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp

/-- Resolves an `.unknown` slot to a PRG challenge at `max pos h.keys.length`. -/
def matFill (pos : ℕ) (D : ℕ → ProbComp (CK × MK)) (h : HState CK MK AD M C) :
    Slot CK MK → ProbComp (Slot CK MK)
  | .unknown => Slot.mat (max pos h.keys.length) <$> D (max pos h.keys.length)
  | sl => pure sl

/-- Resolves an `.unknown` slot to a uniform chain key once `j ≤ h.keys.length`. -/
def seedFill [SampleableType CK] (j : ℕ) (h : HState CK MK AD M C) : Slot CK MK → ProbComp (Slot CK MK)
  | .unknown => if j ≤ h.keys.length then Slot.seed <$> ($ᵗ CK) else pure .unknown
  | sl => pure sl

section Prims

variable {fill : HState CK MK AD M C → Slot CK MK → ProbComp (Slot CK MK)}

theorem idem_bind (hI : Idem fill) {β : Type} (h : HS) (sl : Slot CK MK)
    (k : Slot CK MK → ProbComp β) :
    DEq (fill h sl >>= fun x => fill h x >>= k) (fill h sl >>= k) := by
  have := DEq.bind_left (hI h sl) k
  simpa only [bind_assoc] using this

@[simp] theorem getH_run : (getH : SP HS).run = fun s => pure (s.1, s) := by
  funext s; simp [getH, onH]

@[simp] theorem modifyH_run (f : HS → HS) :
    (modifyH f : SP Unit).run = fun s => pure ((), (f s.1, s.2)) := by
  funext s; simp [modifyH, onH]

@[simp] theorem sampleH_run {α : Type} (p : ProbComp α) :
    (sampleH p : SP α).run = fun s => (fun a => (a, s)) <$> p := by
  funext s; simp [sampleH]

theorem comm_getH (hI : Idem fill) : Comm fill (getH : SP HS) := by
  rintro ⟨h, sl⟩
  simp only [fillSt, fillOut, getH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind]
  exact idem_bind hI h sl _

theorem comm_modifyH (hI : Idem fill)
    (hK : ∀ h h' : HS, h.keys.length = h'.keys.length → fill h = fill h')
    (f : HS → HS) (hf : ∀ h, (f h).keys.length = h.keys.length) :
    Comm fill (modifyH f : SP Unit) := by
  rintro ⟨h, sl⟩
  simp only [fillSt, fillOut, modifyH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind, hK (f h) h (hf h)]
  exact idem_bind hI h sl _

theorem comm_sampleH (hI : Idem fill) {α : Type} (p : ProbComp α) :
    Comm fill (sampleH p : SP α) := by
  rintro ⟨h, sl⟩
  simp only [fillSt, fillOut, sampleH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind]
  refine (DEq.swap _ _ _).trans ?_
  exact DEq.bind_right _ fun a => idem_bind hI h sl _

theorem comm_at_of_fill_pure {α : Type} (x : SP α) (h : HState CK MK AD M C) (sl : Slot CK MK)
    (hf : fill h sl = pure sl) :
    DEq (fillSt fill (h, sl) >>= x.run >>= fillOut fill) (x.run (h, sl) >>= fillOut fill) := by
  simp only [fillSt, hf, map_pure, pure_bind]
  exact DEq.refl _

theorem rc_getH (hI : Idem fill) : RC fill (getH : SP HS) getH := by
  refine ⟨?_, comm_getH hI⟩
  rintro ⟨h, sl⟩
  simp only [fillSt, fillOut, getH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind]
  exact (idem_bind hI h sl _).symm

theorem rc_modifyH (hI : Idem fill)
    (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length → fill h = fill h')
    (f : HState CK MK AD M C → HState CK MK AD M C) (hf : ∀ h, (f h).keys.length = h.keys.length) :
    RC fill (modifyH f : SP Unit) (modifyH f) := by
  refine ⟨?_, comm_modifyH hI hK f hf⟩
  rintro ⟨h, sl⟩
  simp only [fillSt, fillOut, modifyH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind, hK (f h) h (hf h)]
  exact (idem_bind hI h sl _).symm

theorem rc_sampleH (hI : Idem fill) {α : Type} (p : ProbComp α) :
    RC fill (sampleH p : SP α) (sampleH p) := by
  refine ⟨?_, comm_sampleH hI p⟩
  rintro ⟨h, sl⟩
  simp only [fillSt, fillOut, sampleH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind]
  refine DEq.symm ?_
  refine (DEq.bind_right _ fun sl' => DEq.swap _ _ _).trans ?_
  exact idem_bind hI h sl _

end Prims

/-! ## Slot fills -/

section Fills

variable (G : ℕ → PRGScheme CK (CK × MK))

theorem matFill_idem (pos : ℕ) (D : ℕ → ProbComp (CK × MK)) :
    Idem (matFill (AD := AD) (M := M) (C := C) pos D) := by
  intro h sl
  cases sl <;>
    simp only [matFill, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] <;>
    exact DEq.refl _

theorem matFill_keys (pos : ℕ) (D : ℕ → ProbComp (CK × MK)) (h h' : HState CK MK AD M C)
    (e : h.keys.length = h'.keys.length) : matFill pos D h = matFill pos D h' := by
  funext sl
  cases sl <;> simp only [matFill, e]

theorem seedFill_idem [SampleableType CK] (j : ℕ) :
    Idem (seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) j) := by
  intro h sl
  cases sl with
  | unknown =>
    by_cases hj : j ≤ h.keys.length <;>
      simp only [seedFill, hj, ite_true, ite_false, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind] <;>
      exact DEq.refl _
  | _ => simp only [seedFill, pure_bind]; exact DEq.refl _

section GenStep

variable [SampleableType MK] (P : Params) (D : ℕ → ProbComp (CK × MK)) (h : HState CK MK AD M C)

theorem genStep_run_seed (w : CK) :
    (genStep G P D : SP Unit).run (h, .seed w) =
      pure ((), ({ h with keys := h.keys ++ [((G h.keys.length).gen w).2] },
        .seed ((G h.keys.length).gen w).1)) := rfl

theorem genStep_run_mat_lt (pos : ℕ) (mt : CK × MK) (hlt : h.keys.length < pos) :
    (genStep G P D : SP Unit).run (h, .mat pos mt) =
      ($ᵗ MK) >>= fun K => pure ((), ({ h with keys := h.keys ++ [K] }, .mat pos mt)) := by
  simp only [genStep, StateT.run_mk, hlt, ite_true]; rfl

theorem genStep_run_mat_ge (pos : ℕ) (mt : CK × MK) (hge : ¬ h.keys.length < pos) :
    (genStep G P D : SP Unit).run (h, .mat pos mt) =
      pure ((), ({ h with keys := h.keys ++ [mt.2] }, .seed mt.1)) := by
  simp only [genStep, StateT.run_mk, hge, ite_false]

theorem genStep_run_unknown_lt (hlt : h.keys.length < P.j) :
    (genStep G P D : SP Unit).run (h, .unknown) =
      ($ᵗ MK) >>= fun K => pure ((), ({ h with keys := h.keys ++ [K] }, .unknown)) := by
  simp only [genStep, StateT.run_mk, hlt, ite_true]; rfl

theorem genStep_run_unknown_ge (hge : ¬ h.keys.length < P.j) :
    (genStep G P D : SP Unit).run (h, .unknown) =
      D h.keys.length >>= fun mt => pure ((), ({ h with keys := h.keys ++ [mt.2] }, .seed mt.1)) := by
  simp only [genStep, StateT.run_mk, hge, ite_false]; rfl

end GenStep

section Reveal

variable [SampleableType CK] (h : HState CK MK AD M C)

theorem reveal_run_seed (w : CK) : (reveal : SP CK).run (h, .seed w) = pure (w, (h, .seed w)) :=
  rfl

theorem reveal_run_mat (pos : ℕ) (mt : CK × MK) :
    (reveal : SP CK).run (h, .mat pos mt) = ($ᵗ CK) >>= fun u => pure (u, (h, .seed u)) := rfl

theorem reveal_run_unknown :
    (reveal : SP CK).run (h, .unknown) = ($ᵗ CK) >>= fun u => pure (u, (h, .seed u)) := rfl

end Reveal

section CommSlot

variable [SampleableType MK] [SampleableType CK] (G : ℕ → PRGScheme CK (CK × MK))

theorem comm_genStep_mat (P : Params) (D : ℕ → ProbComp (CK × MK)) :
    Comm (matFill (AD := AD) (M := M) (C := C) P.j D) (genStep G P D : SP Unit) := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => exact comm_at_of_fill_pure _ _ _ rfl
  | mat pos mt => exact comm_at_of_fill_pure _ _ _ rfl
  | unknown =>
    by_cases hlt : h.keys.length < P.j
    · have h1 : max P.j h.keys.length = P.j := max_eq_left hlt.le
      have h2 : ∀ K : MK, max P.j (h.keys ++ [K]).length = P.j := fun K =>
        max_eq_left (by simp only [List.length_append, List.length_singleton]; omega)
      simp only [fillSt, fillOut, matFill, h1, h2, genStep_run_unknown_lt _ _ _ _ hlt,
        genStep_run_mat_lt _ _ _ _ _ _ hlt, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      exact DEq.swap _ _ _
    · have h1 : max P.j h.keys.length = h.keys.length := max_eq_right (by omega)
      simp only [fillSt, fillOut, matFill, h1, genStep_run_unknown_ge _ _ _ _ hlt,
        genStep_run_mat_ge _ _ _ _ _ _ (lt_irrefl _), map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp_apply]
      exact DEq.refl _

theorem comm_reveal_mat (pos : ℕ) (D : ℕ → ProbComp (CK × MK)) :
    Comm (matFill (AD := AD) (M := M) (C := C) pos D) (reveal : SP CK) := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => exact comm_at_of_fill_pure _ _ _ rfl
  | mat pos mt => exact comm_at_of_fill_pure _ _ _ rfl
  | unknown =>
    simp only [fillSt, fillOut, matFill, reveal_run_unknown, reveal_run_mat,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    exact DEq.bind_const _ _

theorem comm_genStep_seed (P : Params) (j : ℕ) (hj : P.j ≤ j) :
    Comm (seedFill (MK := MK) (AD := AD) (M := M) (C := C) j) (genStep G P (DG G) : SP Unit) := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => exact comm_at_of_fill_pure _ _ _ rfl
  | mat pos mt => exact comm_at_of_fill_pure _ _ _ rfl
  | unknown =>
    by_cases hg : j ≤ h.keys.length
    · have hlt : ¬ h.keys.length < P.j := by omega
      simp only [fillSt, fillOut, seedFill, hg, ite_true, genStep_run_unknown_ge _ _ _ _ hlt,
        genStep_run_seed, DG, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      exact DEq.refl _
    · exact comm_at_of_fill_pure _ _ _ (by simp [seedFill, hg])

theorem comm_reveal_seed (j : ℕ) :
    Comm (seedFill (MK := MK) (AD := AD) (M := M) (C := C) j) (reveal : SP CK) := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => exact comm_at_of_fill_pure _ _ _ rfl
  | mat pos mt => exact comm_at_of_fill_pure _ _ _ rfl
  | unknown =>
    by_cases hg : j ≤ h.keys.length
    · simp only [fillSt, fillOut, seedFill, hg, ite_true, reveal_run_unknown, reveal_run_seed,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      exact DEq.refl _
    · exact comm_at_of_fill_pure _ _ _ (by simp [seedFill, hg])

end CommSlot

/-! ## Oracle commutativity -/

set_option hygiene false in
macro "comm_tac" : tactic => `(tactic| repeat' (first
  | exact Comm.pure hI _
  | exact comm_getH hI
  | exact comm_modifyH hI hK _ (fun _ => rfl)
  | exact comm_sampleH hI _
  | exact hGen
  | exact hRev
  | exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  | (with_reducible refine Comm.bind ?_ fun _ => ?_)
  | split))

set_option hygiene false in
local macro "comm_step" e1:term "," e2:term : tactic => `(tactic| repeat' (first
  | exact Comm.pure hI _
  | exact comm_getH hI
  | (with_reducible exact comm_modifyH hI hK _ (fun _ => rfl))
  | exact comm_sampleH hI _
  | (with_reducible exact $e1)
  | (with_reducible exact $e2)
  | (with_reducible refine Comm.bind ?_ fun _ => ?_)
  | split))

section CommOracles

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (P : Params) (D : ℕ → ProbComp (CK × MK))
  {fill : HState CK MK AD M C → Slot CK MK → ProbComp (Slot CK MK)} (hI : Idem fill)
  (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length → fill h = fill h')
  (hGen : Comm fill (genStep G P D : StateT (HSt CK MK AD M C) ProbComp Unit))
  (hRev : Comm fill (reveal : StateT (HSt CK MK AD M C) ProbComp CK))
include hI hK hGen hRev

theorem comm_genN (n : ℕ) : Comm fill (genN G P D n : SP Unit) := by
  induction n with
  | zero => exact Comm.pure hI _
  | succ n ih => exact Comm.bind hGen fun _ => ih

theorem comm_genUpTo (i : ℕ) : Comm fill (genUpTo G P D i : SP Unit) :=
  Comm.bind (comm_getH hI) fun _ => comm_genN G P D hI hK hGen hRev _

theorem comm_encIdx (i : ℕ) (a : AD) (msg : M) :
    Comm fill (encIdxWith ideal ae P (none : Option (SpecialOps AD M C ProbComp)) i a msg) := by
  unfold encIdxWith; comm_tac

theorem comm_transmitH (q : AD × M) :
    Comm fill (transmitHWith ideal ae G P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold transmitHWith
  comm_step (comm_genUpTo G P D hI hK hGen hRev _), (comm_encIdx ideal ae G P D hI hK hGen hRev _ _ _)

theorem comm_challengeH (q : AD × M × M) :
    Comm fill (challengeHWith ideal ae G P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold challengeHWith
  comm_step (comm_genUpTo G P D hI hK hGen hRev _), (comm_encIdx ideal ae G P D hI hK hGen hRev _ _ _)

theorem comm_decIdx (hint : Option M) (i : ℕ) (a : AD) (e : C) :
    Comm fill (decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) hint i a e) := by
  unfold decIdx; comm_tac

theorem comm_receiveH (hint : Option M) (a : AD) (c : ℕ × C) :
    Comm fill (receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) hint a c) := by
  obtain ⟨i, e⟩ := c; unfold receiveH
  refine Comm.bind (comm_getH hI) fun st => ?_
  split
  · refine Comm.bind (comm_decIdx ae G P D hI hK hGen hRev _ _ _ _) fun r => ?_
    comm_tac
  · split
    · exact Comm.pure hI _
    · split
      · exact Comm.pure hI _
      · refine Comm.bind (comm_genUpTo G P D hI hK hGen hRev _) fun _ => ?_
        refine Comm.bind (comm_decIdx ae G P D hI hK hGen hRev _ _ _ _) fun r => ?_
        comm_tac

theorem comm_senderKey : Comm fill (senderKey G : SP CK) := by
  unfold senderKey; comm_tac

theorem comm_corruptSenderH (u : Unit) :
    Comm fill (corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G P u) := by
  unfold corruptSenderH; comm_step (comm_senderKey G P D hI hK hGen hRev), (comm_senderKey G P D hI hK hGen hRev)

theorem comm_corruptReceiverH (u : Unit) :
    Comm fill (corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G P u) := by
  unfold corruptReceiverH; comm_step (comm_senderKey G P D hI hK hGen hRev), (comm_senderKey G P D hI hK hGen hRev)

theorem comm_deliverH (q : AD × (ℕ × C)) :
    Comm fill (deliverH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold deliverH
  comm_step (comm_receiveH ae G maxSkip P D hI hK hGen hRev _ _ _), (comm_receiveH ae G maxSkip P D hI hK hGen hRev _ _ _)

theorem comm_injectH (q : AD × (ℕ × C)) :
    Comm fill (injectH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold injectH
  comm_step (comm_receiveH ae G maxSkip P D hI hK hGen hRev _ _ _), (comm_receiveH ae G maxSkip P D hI hK hGen hRev _ _ _)

/-- Every hybrid oracle query (without special operations) commutes with `fill`. -/
theorem comm_impl (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
    (ℕ × C)).Domain) :
    Comm fill (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) t) := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact comm_sampleH hI _
  · exact comm_transmitH ideal ae G P D hI hK hGen hRev q
  · exact comm_challengeH ideal ae G P D hI hK hGen hRev q
  · exact comm_corruptSenderH G P D hI hK hGen hRev u
  · exact comm_corruptReceiverH G P D hI hK hGen hRev u
  · exact comm_deliverH ae G maxSkip P D hI hK hGen hRev q
  · exact comm_injectH ae G maxSkip P D hI hK hGen hRev q

end CommOracles

end Fills

/-! ## Hybrid run equivalence -/

section L2

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (k : ℕ) (la : Bool)

@[simp] theorem hp_la (a t : ℕ) : (hp a t la).la = la := rfl

theorem rc_ite {fill : HState CK MK AD M C → Slot CK MK → ProbComp (Slot CK MK)} {α : Type}
    (c : Prop) {d₁ d₂ : Decidable c} {a₁ a₂ b₁ b₂ : SP α}
    (h₁ : c → RC fill a₁ a₂) (h₂ : ¬c → RC fill b₁ b₂) :
    RC fill (@ite _ c d₁ a₁ b₁) (@ite _ c d₂ a₂ b₂) := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h₁ hc
  · simp only [hc, ite_false]; exact h₂ hc

theorem kind_hp (a b t : ℕ) (st : HState CK MK AD M C) (i : ℕ) :
    kind (hp a t la) (none : Option (SpecialOps AD M C ProbComp)) st i =
      kind (hp b t la) (none : Option (SpecialOps AD M C ProbComp)) st i := by
  simp [kind, hp]

theorem rc_reveal_L2 : RC (seedFill (k + 1)) (reveal : SP CK) reveal := by
  refine ⟨?_, comm_reveal_seed (k + 1)⟩
  rintro ⟨h, sl⟩
  cases sl with
  | seed w =>
    simp only [fillSt, fillOut, seedFill, reveal_run_seed, map_pure, pure_bind]
    exact DEq.refl _
  | mat pos mt =>
    simp only [fillSt, fillOut, seedFill, reveal_run_mat, map_pure, pure_bind,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
    exact DEq.refl _
  | unknown =>
    by_cases hg : k + 1 ≤ h.keys.length
    · simp only [fillSt, fillOut, seedFill, hg, ite_true, reveal_run_seed, reveal_run_unknown,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      exact DEq.refl _
    · simp only [fillSt, fillOut, seedFill, hg, ite_false, reveal_run_unknown, map_pure,
        pure_bind, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
      exact DEq.refl _

variable (hI : Idem (seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1)))
  (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length →
    seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1) h =
      seedFill (k + 1) h')
include hI hK

set_option hygiene false in
local macro "rc_step" e1:term "," e2:term : tactic => `(tactic| repeat' (first
  | exact RC.pure hI _
  | exact rc_getH hI
  | (with_reducible exact rc_modifyH hI hK _ (fun _ => rfl))
  | exact rc_sampleH hI _
  | exact rc_reveal_L2 k
  | exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  | (with_reducible exact $e1)
  | (with_reducible exact $e2)
  | (with_reducible refine RC.bind ?_ fun _ => ?_)
  | refine rc_ite _ (fun _ => ?_) (fun _ => ?_)
  | (rw [kind_hp la k (k + 1) (k + 1) _ _]; split)
  | split))

theorem rc_senderKey_L2 : RC (seedFill (k + 1)) (senderKey G : SP CK) (senderKey G) := by
  unfold senderKey; rc_step (rc_getH hI), (rc_getH hI)

end L2

section Runs

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (A : RatchetAdversary CK MK AD M C)

theorem hOut_eq (la : Bool) :
    (hOut la : Bool × HSt CK MK AD M C → Bool) =
      fun z => (fun (a : Bool) (h : HState CK MK AD M C) =>
        if la then h.lf else (h.b == a || h.win)) z.1 z.2.1 := rfl

/-- Filling the initial slot preserves the hybrid output distribution. -/
theorem hOut_fill (P : Params) (D : ℕ → ProbComp (CK × MK))
    {fill : HState CK MK AD M C → Slot CK MK → ProbComp (Slot CK MK)} (hI : Idem fill)
    (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length → fill h = fill h')
    (hGen : Comm fill (genStep G P D : StateT (HSt CK MK AD M C) ProbComp Unit))
    (hRev : Comm fill (reveal : StateT (HSt CK MK AD M C) ProbComp CK)) (s : HSt CK MK AD M C) :
    DEq (hOut P.la <$> (fillSt fill s >>=
        (simulateQ (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp))) A).run))
      (hOut P.la <$> (simulateQ (implWith ideal ae G maxSkip P D none) A).run s) := by
  have hc := Comm.simulateQ hI (comm_impl ideal ae G maxSkip P D hI hK hGen hRev) A s
  let F := fun (a : Bool) (h : HState CK MK AD M C) => if P.la then h.lf else (h.b == a || h.win)
  rw [hOut_eq]
  exact (map_fillOut (fill := fill) F _).symm.trans
    ((DEq.map hc _).trans (map_fillOut (fill := fill) F _))

end Runs

end CryptoGames.FSAEAD.Thm5
