/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced

/-!
# Scoped Frame and Call-Site Helpers for `M2Dispatch`

Local `locals` and `stackAt` frame helpers in `MainHops.Proofs` for `main_m2` subcommand dispatch.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## 1. `locals` & `stackAt` Helpers -/

def localsBound : List (Nat × Nat × SepProp) → Nat
  | [] => 0x480
  | (o, _, _) :: _ => o

def localsEnd (off : Nat) : List (Nat × Nat × SepProp) → Nat
  | [] => off
  | (o, n, _) :: cs => localsEnd (o + n) cs

def localsCtx (fsp : BitVec 64) :
    Nat → List (Nat × Nat × SepProp) → Nat → Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [], o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ localsFrom fsp (o + n) cs₂
  | off, (o₁, n₁, P₁) :: cs₁, o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗
      localsCtx fsp (o₁ + n₁) cs₁ o n cs₂

def LocalsWF : Nat → List (Nat × Nat × SepProp) → Prop
  | off, [] => off ≤ 0x480
  | off, (o, n, _) :: cs => off ≤ o ∧ LocalsWF (o + n) cs

theorem LocalsWF.le_top {off : Nat} {cs : List (Nat × Nat × SepProp)} (h : LocalsWF off cs) :
    off ≤ 0x480 := by
  induction cs generalizing off with
  | nil => exact h
  | cons c cs ih =>
    rcases c with ⟨o, n, _⟩
    have h1 : off ≤ o := h.1
    have h2 : o + n ≤ 0x480 := ih h.2
    omega

theorem locals_nil (fsp : BitVec 64) :
    locals fsp [] = memRegion fsp 0x480 := by
  simp only [locals, localsFrom, BitVec.add_zero, Nat.sub_zero]

theorem localsFrom_focus (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    localsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ localsCtx fsp off cs₁ o n cs₂ := by
  induction cs₁ generalizing off with
  | nil => simp only [List.nil_append, localsFrom, localsCtx]; ac_rfl
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, localsFrom, localsCtx, ih (o₁ + n₁)]; ac_rfl

theorem locals_focus (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    locals fsp (cs₁ ++ (o, n, P) :: cs₂) = P ∗ localsCtx fsp 0 cs₁ o n cs₂ :=
  localsFrom_focus fsp 0 cs₁ o n P cs₂

theorem localsFrom_carve_region (fsp : BitVec 64) (off o n : Nat)
    (cs : List (Nat × Nat × SepProp))
    (hlo : off ≤ o := by decide)
    (hhi : o + n ≤ localsBound cs := by decide)
    (hbnd : localsBound cs ≤ 0x480 := by decide) :
    localsFrom fsp off cs =
      localsFrom fsp off ((o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs) := by
  have hsplit1 :
      memRegion (fsp + BitVec.ofNat 64 off) (localsBound cs - off) =
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (localsBound cs - o) := by
    refine ProofLib.memRegion_split' (n := o - off) (k := localsBound cs - o)
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hsplit2 :
      memRegion (fsp + BitVec.ofNat 64 o) (localsBound cs - o) =
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (localsBound cs - (o + n)) := by
    refine ProofLib.memRegion_split' (n := n) (k := localsBound cs - (o + n))
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  cases cs with
  | nil =>
    simp only [localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [localsFrom, hsplit1, hsplit2]
  | cons c cs' =>
    rcases c with ⟨o', n', P'⟩
    simp only [localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [localsFrom, hsplit1, hsplit2]; ac_rfl

private theorem localsFrom_carve_after (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd off cs₁ ≤ o) (hhi : o + n ≤ localsBound cs₂)
    (hbnd : localsBound cs₂ ≤ 0x480) :
    localsFrom fsp off (cs₁ ++ cs₂) =
      localsFrom fsp off (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) := by
  induction cs₁ generalizing off with
  | nil => exact localsFrom_carve_region fsp off o n cs₂ hlo hhi hbnd
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, localsFrom]; rw [ih (o₁ + n₁) hlo]

theorem locals_carve_region (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd 0 cs₁ ≤ o := by simp [localsEnd])
    (hhi : o + n ≤ localsBound cs₂ := by simp [localsBound])
    (hbnd : localsBound cs₂ ≤ 0x480 := by simp [localsBound]) :
    locals fsp (cs₁ ++ cs₂) =
      locals fsp (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) :=
  localsFrom_carve_after fsp 0 cs₁ o n cs₂ hlo hhi hbnd

theorem locals_carve_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat) (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd 0 cs₁ ≤ o := by simp [localsEnd])
    (hhi : o + 8 ≤ localsBound cs₂ := by simp [localsBound])
    (hbnd : localsBound cs₂ ≤ 0x480 := by simp [localsBound]) :
    locals fsp (cs₁ ++ cs₂) =
      ∃∗ v : BitVec 64, locals fsp (cs₁ ++ cell fsp o v :: cs₂) := by
  rw [locals_carve_region fsp cs₁ o 8 cs₂ hlo hhi hbnd,
    locals_focus fsp cs₁ o 8 _ cs₂, ProofLib.memRegion_eight, sepExists_sepConj_left]
  congr 1; funext v; exact (locals_focus fsp cs₁ o 8 _ cs₂).symm

theorem pointsTo64_entails_memRegion (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)

theorem localsFrom_to_memRegion (fsp : BitVec 64) (off : Nat)
    (cs : List (Nat × Nat × SepProp)) (hwf : LocalsWF off cs)
    (hent : ∀ o n P, (o, n, P) ∈ cs → P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n) :
    localsFrom fsp off cs ⊢ memRegion (fsp + BitVec.ofNat 64 off) (0x480 - off) := by
  induction cs generalizing off with
  | nil => exact Entails.refl _
  | cons c cs ih =>
    rcases c with ⟨o, n, P⟩
    rcases hwf with ⟨hlo, hwf'⟩
    have hP := hent o n P (.head _)
    have htail := ih (o + n) hwf' (fun o' n' P' hm => hent o' n' P' (.tail _ hm))
    simp only [localsFrom]
    refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono hP htail)) ?_
    exact Entails.of_eq (localsFrom_carve_region fsp off o n [] hlo hwf'.le_top (by decide)).symm

theorem locals_to_memRegion (fsp : BitVec 64)
    (cs : List (Nat × Nat × SepProp)) (hwf : LocalsWF 0 cs := by simp [LocalsWF])
    (hent : ∀ o n P, (o, n, P) ∈ cs → P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n) :
    locals fsp cs ⊢ memRegion fsp 0x480 := by
  simpa only [locals, BitVec.add_zero, Nat.sub_zero] using localsFrom_to_memRegion fsp 0 cs hwf hent

theorem callCellsPlaced_to_memRegion (fsp : BitVec 64) (w : CallW) :
    locals fsp (callCellsPlaced fsp w) ⊢ memRegion fsp 0x480 := by
  refine locals_to_memRegion fsp (callCellsPlaced fsp w) (by simp [LocalsWF]) ?_
  intro o n P hm
  simp only [callCellsPlaced, cell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact pointsTo64_entails_memRegion _ _

theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
