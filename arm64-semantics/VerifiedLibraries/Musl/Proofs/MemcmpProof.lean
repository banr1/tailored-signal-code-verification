/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Library.Calls
public import VerifiedLibraries.Musl.Spec
public import VerifiedLibraries.Musl.Proofs.Code
public import VerifiedLibraries.Musl.Proofs.Common
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.LoopTactics
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Verification of `memcmp` and `bcmp`

Proves `memcmpSpec`, `memcmpROSpec`, `bcmpSpec`, and `bcmpROSpec` for `musl` v1.2.5's `memcmp` and
`bcmp`, including layout-generic theorems over `memcmpWords` and `memcmpLibcaWords`, single-word
tail-call transfer for `bcmp`, and `VerifiedLibraries.muslStringLib` placement corollaries.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64
open ProofLib

/-! ## Pure `memcmpBytes` Lemmas -/

theorem memcmpBytes_self (bs : List (BitVec 8)) : memcmpBytes bs bs = 0#32 := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [memcmpBytes, ih]

theorem memcmpBytes_eq_zero_iff {bs1 bs2 : List (BitVec 8)} (hlen : bs1.length = bs2.length) :
    memcmpBytes bs1 bs2 = 0#32 ↔ bs1 = bs2 := by
  induction bs1 generalizing bs2 with
  | nil => cases bs2 <;> simp_all [memcmpBytes]
  | cons b1 rest1 ih =>
    cases bs2 with
    | nil => simp at hlen
    | cons b2 rest2 =>
      by_cases h : b1 = b2
      · subst h; simpa [memcmpBytes] using ih (by simpa using hlen)
      · simp only [memcmpBytes, h, ↓reduceIte, List.cons.injEq, false_and, iff_false]
        intro h0; exact h (by bv_omega)

/-! ## Scalar Read-Only State Preservation -/

/-- Non-GPR state preserved across scalar read-only `memcmp` and `bcmp`: memory (`sf.mem = s0.mem`),
    SIMD/FP vector registers (`sf.vregs = s0.vregs`), and `ProcessFieldsPreserved s0 sf`. -/
def MemcmpStatePreserved (s0 sf : State) : Prop :=
  sf.mem = s0.mem ∧ sf.vregs = s0.vregs ∧ ProcessFieldsPreserved s0 sf

/-- Strengthens `spec` with `MemcmpStatePreserved s0 sf` in its postcondition. -/
def withMemcmpPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜MemcmpStatePreserved s0 sf⌝ ∗ spec.post x s0 sf }

abbrev memcmpPreservingSpec := withMemcmpPreserved memcmpSpec
abbrev memcmpROPreservingSpec := withMemcmpPreserved memcmpROSpec
abbrev bcmpPreservingSpec := withMemcmpPreserved bcmpSpec
abbrev bcmpROPreservingSpec := withMemcmpPreserved bcmpROSpec

theorem subroutine_ok_drop_memcmpPreserved {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry (withMemcmpPreserved spec)) :
    subroutine_ok prog entry spec :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withMemcmpPreserved] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

private structure memcmpPres (s0 sf : State) : Prop where
  val : MemcmpStatePreserved s0 sf

private theorem memcmpPres_eq (s0 sf : State) :
    MemcmpStatePreserved s0 sf = memcmpPres s0 sf :=
  propext ⟨fun h => ⟨h⟩, fun h => h.val⟩

@[local simp, local wp_norm] private theorem memcmpPres_refl (s : State) :
    memcmpPres s s :=
  ⟨⟨rfl, rfl, ProcessFieldsPreserved.refl s⟩⟩

@[local simp, local wp_norm] private theorem memcmpPres_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    memcmpPres s0 (s.writeReg64 r v) ↔ memcmpPres s0 s := by
  constructor <;> rintro ⟨h⟩ <;> refine ⟨?_⟩ <;>
    (cases r <;> simpa [State.writeReg64, MemcmpStatePreserved, ProcessFieldsPreserved] using h)

@[local simp, local wp_norm] private theorem memcmpPres_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    memcmpPres s0 (s.writeReg32 r v) ↔ memcmpPres s0 s := by
  dsimp only [State.writeReg32]; exact memcmpPres_writeReg64 s0 s r _

@[local simp, local wp_norm] private theorem memcmpPres_writeReg (s0 s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    memcmpPres s0 (s.writeReg w r v) ↔ memcmpPres s0 s := by
  cases w <;> dsimp only [State.writeReg] <;> exact memcmpPres_writeReg64 s0 s r _

@[local simp, local wp_norm] private theorem memcmpPres_applyWriteback (s0 s : State)
    (wb : Option (Reg × BitVec 64)) :
    memcmpPres s0 (applyWriteback s wb) ↔ memcmpPres s0 s := by
  cases wb <;> dsimp only [applyWriteback]
  · exact Iff.rfl
  · exact memcmpPres_writeReg64 s0 s _ _

@[local simp, local wp_norm] private theorem memcmpPres_setPState (s0 s : State) (p : PState) :
    memcmpPres s0 (s.setPState p) ↔ memcmpPres s0 s :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

@[local simp, local wp_norm] private theorem memcmpPres_advancePC (s0 s : State) :
    memcmpPres s0 s.advancePC ↔ memcmpPres s0 s :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

@[local simp, local wp_norm] private theorem memcmpPres_setPC (s0 s : State) (pc : BitVec 64) :
    memcmpPres s0 (s.setPC pc) ↔ memcmpPres s0 s :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

/-! ## Layout-Generic `memcmp` Verification -/

private theorem memcmp_drop_step {bs1 bs2 : List (BitVec 8)} {i : Nat}
    (h1 : i < bs1.length) (h2 : i < bs2.length) :
    memcmpBytes (bs1.drop i) (bs2.drop i) =
      if bs1.getD i 0#8 = bs2.getD i 0#8 then memcmpBytes (bs1.drop (i + 1)) (bs2.drop (i + 1))
      else (bs1.getD i 0#8).zeroExtend 32 - (bs2.getD i 0#8).zeroExtend 32 := by
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]
  simp [memcmpBytes, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]

set_option hygiene false in
local macro "memcmp_loop_proof" : tactic => `(tactic| (
  obtain ⟨hlen1, hlen2⟩ : n.toNat = bs1.length ∧ n.toNat = bs2.length := by assumption
  by_cases hn0 : n = 0#64
  · subst hn0
    obtain rfl : bs1 = [] := List.length_eq_zero_iff.mp (by rw [← hlen1]; rfl)
    obtain rfl : bs2 = [] := List.length_eq_zero_iff.mp (by rw [← hlen2]; rfl)
    wp_sym_steps
    wp_done
  · have hpos : n.toNat ≠ 0 := fun h => hn0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    obtain ⟨N, hN⟩ : ∃ N, n.toNat = N + 1 := ⟨n.toNat - 1, by omega⟩
    have hNlt : N + 1 < 2 ^ 64 := hN ▸ n.isLt
    have hl1 : bs1.length = N + 1 := by omega
    have hl2 : bs2.length = N + 1 := by omega
    obtain rfl : n = BitVec.ofNat 64 (N + 1) :=
      BitVec.eq_of_toNat_eq (by rw [hN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNlt])
    clear hlen1 hlen2 hn0 hpos hN
    wp_step
    wp_loop_measure frame N (fun k st => k ≤ N ∧
      memcmpPres s0 st ∧
      st.readReg64 .x0 = s1 + BitVec.ofNat 64 (N - k) ∧
      st.readReg64 .x1 = s2 + BitVec.ofNat 64 (N - k) ∧
      st.readReg64 .x2 = BitVec.ofNat 64 (k + 1) ∧
      memcmpBytes (bs1.drop (N - k)) (bs2.drop (N - k)) = memcmpBytes bs1 bs2)
    case init => simp
    case base =>
      simp only [Nat.sub_zero] at *
      have hres : memcmpBytes (bs1.drop N) (bs2.drop N) = memcmpBytes bs1 bs2 := by assumption
      rw [memcmp_drop_step (by omega) (by omega),
        List.drop_eq_nil_of_le (by omega : bs1.length ≤ N + 1),
        List.drop_eq_nil_of_le (by omega : bs2.length ≤ N + 1)] at hres
      rw [← hres]
      by_cases heq : bs1.getD N 0#8 = bs2.getD N 0#8 <;> simp only [heq, ↓reduceIte] <;>
        (try rw [show memcmpBytes [] [] = 0#32 from rfl]) <;> wp_sym_steps <;> wp_done
    case step =>
      have hres : memcmpBytes (bs1.drop (N - (m' + 1))) (bs2.drop (N - (m' + 1))) =
          memcmpBytes bs1 bs2 := by assumption
      rw [memcmp_drop_step (by omega) (by omega)] at hres
      have hidx : N - (m' + 1) + 1 = N - m' := by omega
      by_cases heq : bs1.getD (N - (m' + 1)) 0#8 = bs2.getD (N - (m' + 1)) 0#8
      · right
        simp only [heq, ↓reduceIte, hidx] at hres
        have hx0' : s1 + BitVec.ofNat 64 (N - (m' + 1)) + 1#64 = s1 + BitVec.ofNat 64 (N - m') := by
          rw [← hidx]; bv_omega
        have hx1' : s2 + BitVec.ofNat 64 (N - (m' + 1)) + 1#64 = s2 + BitVec.ofNat 64 (N - m') := by
          rw [← hidx]; bv_omega
        have hx2' : BitVec.ofNat 64 (m' + 1 + 1) - 1#64 = BitVec.ofNat 64 (m' + 1) := by bv_omega
        wp_sym_steps
        wp_done
      · left
        simp only [heq, ↓reduceIte] at hres
        rw [← hres]
        wp_sym_steps
        wp_done))

theorem memcmpPreserving_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpWords) :
    subroutine_ok prog a memcmpPreservingSpec := by
  wp_init x s0
  rcases x with ⟨s1, s2, n, bs1, bs2⟩
  dsimp only [withMemcmpPreserved, memcmpSpec, CType.ShrSlice8, CType.Bytes, SliceLenPair,
    CType.SemType.valWf] at *
  simp only [memcmpPres_eq]
  memcmp_loop_proof

theorem memcmpROPreserving_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpWords) :
    subroutine_ok prog a memcmpROPreservingSpec := by
  wp_init x s0
  rcases x with ⟨s1, s2, n, bs1, bs2⟩
  dsimp only [withMemcmpPreserved, memcmpROSpec, RoSlice8, SliceLenPair,
    CType.SemType.valWf] at *
  simp only [memcmpPres_eq]
  memcmp_loop_proof

theorem memcmp_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpWords) :
    subroutine_ok prog a memcmpSpec :=
  subroutine_ok_drop_memcmpPreserved (memcmpPreserving_codeAt_ok prog a hc)

theorem memcmpRO_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpWords) :
    subroutine_ok prog a memcmpROSpec :=
  subroutine_ok_drop_memcmpPreserved (memcmpROPreserving_codeAt_ok prog a hc)

set_option hygiene false in
local macro "memcmp_libca_loop_proof" : tactic => `(tactic| (
  obtain ⟨hlen1, hlen2⟩ : n.toNat = bs1.length ∧ n.toNat = bs2.length := by assumption
  have hMlt : bs1.length < 2 ^ 64 := hlen1 ▸ n.isLt
  have hl2 : bs2.length = bs1.length := by omega
  obtain rfl : n = BitVec.ofNat 64 bs1.length :=
    BitVec.eq_of_toNat_eq (by rw [hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hMlt])
  clear hlen1 hlen2
  wp_step
  wp_step
  wp_loop_measure frame bs1.length (fun k st => k ≤ bs1.length ∧
    memcmpPres s0 st ∧
    st.readReg64 .x0 = s1 ∧
    st.readReg64 .x1 = s2 - 1#64 ∧
    st.readReg64 .x2 = BitVec.ofNat 64 bs1.length ∧
    st.readReg64 .x3 = BitVec.ofNat 64 (bs1.length - k) ∧
    memcmpBytes (bs1.drop (bs1.length - k)) (bs2.drop (bs1.length - k)) = memcmpBytes bs1 bs2)
  case init => simp
  case base =>
    simp only [Nat.sub_zero] at *
    have hres : memcmpBytes (bs1.drop bs1.length) (bs2.drop bs1.length) = memcmpBytes bs1 bs2 := by
      assumption
    rw [List.drop_length, List.drop_eq_nil_of_le (by omega : bs2.length ≤ bs1.length)] at hres
    rw [← hres, show memcmpBytes [] [] = 0#32 from rfl]
    wp_sym_steps
    wp_done
  case step =>
    have hres : memcmpBytes (bs1.drop (bs1.length - (m' + 1))) (bs2.drop (bs1.length - (m' + 1))) =
        memcmpBytes bs1 bs2 := by assumption
    rw [memcmp_drop_step (by omega) (by omega)] at hres
    have hidx : bs1.length - (m' + 1) + 1 = bs1.length - m' := by omega
    have hne_end : BitVec.ofNat 64 (bs1.length - (m' + 1)) ≠ BitVec.ofNat 64 bs1.length := by
      intro heq
      have h1 : (BitVec.ofNat 64 (bs1.length - (m' + 1))).toNat =
          (BitVec.ofNat 64 bs1.length).toNat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hMlt] at h1
      omega
    have hx3' : BitVec.ofNat 64 (bs1.length - (m' + 1)) + 1#64 =
        BitVec.ofNat 64 (bs1.length - m') := by
      rw [← hidx]; bv_omega
    have hea2 : (s2 - 1#64) + BitVec.ofNat 64 (bs1.length - m') =
        s2 + BitVec.ofNat 64 (bs1.length - (m' + 1)) := by
      rw [← hidx]; bv_omega
    by_cases heq : bs1.getD (bs1.length - (m' + 1)) 0#8 = bs2.getD (bs1.length - (m' + 1)) 0#8
    · right
      simp only [heq, ↓reduceIte, hidx] at hres
      wp_sym_steps
      wp_done
    · left
      simp only [heq, ↓reduceIte] at hres
      rw [← hres]
      wp_sym_steps
      wp_done))

theorem memcmpPreserving_libca_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpLibcaWords) :
    subroutine_ok prog a memcmpPreservingSpec := by
  wp_init x s0
  rcases x with ⟨s1, s2, n, bs1, bs2⟩
  dsimp only [withMemcmpPreserved, memcmpSpec, CType.ShrSlice8, CType.Bytes, SliceLenPair,
    CType.SemType.valWf] at *
  simp only [memcmpPres_eq]
  memcmp_libca_loop_proof

theorem memcmpROPreserving_libca_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpLibcaWords) :
    subroutine_ok prog a memcmpROPreservingSpec := by
  wp_init x s0
  rcases x with ⟨s1, s2, n, bs1, bs2⟩
  dsimp only [withMemcmpPreserved, memcmpROSpec, RoSlice8, SliceLenPair,
    CType.SemType.valWf] at *
  simp only [memcmpPres_eq]
  memcmp_libca_loop_proof

theorem memcmp_libca_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpLibcaWords) :
    subroutine_ok prog a memcmpSpec :=
  subroutine_ok_drop_memcmpPreserved (memcmpPreserving_libca_codeAt_ok prog a hc)

theorem memcmpRO_libca_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpLibcaWords) :
    subroutine_ok prog a memcmpROSpec :=
  subroutine_ok_drop_memcmpPreserved (memcmpROPreserving_libca_codeAt_ok prog a hc)

/-! ## Layout-Generic `bcmp` Verification -/

private theorem bcmp_tail_ok {α : Type} {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64} {spec : Spec α}
    (hrange : Obj.BranchInRange (a + 0x0#64) (resolve "memcmp"))
    (hwords : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hcallee : subroutine_ok prog (resolve "memcmp") spec)
    (hpre_pc : ∀ x s, spec.pre x (s.setPC (resolve "memcmp")) = spec.pre x s)
    (hpost_pc : ∀ x s sf, spec.post x (s.setPC (resolve "memcmp")) sf = spec.post x s sf)
    (hpanic : ∀ x s sf, spec.onPanic x s sf = ⌜False⌝)
    (hexit : ∀ x c s sf, spec.onExit x c s sf = ⌜False⌝)
    (hoom : ∀ x s sf, spec.onOom x (s.setPC (resolve "memcmp")) sf = spec.onOom x s sf) :
    subroutine_ok prog a spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hf := Obj.fetch_patchCalls_b (r := (0, "memcmp")) hwords rfl rfl (by decide) (by decide)
    hrange
  simp only [BitVec.add_zero, ← hpc] at hf
  apply reaches_outcome_step hrun hf
  dsimp only [Program.evalInst, execInstWithSvc]
  rw [show s0.pc + (resolve "memcmp" - s0.pc) = resolve "memcmp" by bv_omega]
  exact reaches_outcome_of_reaches_pc
    (reaches_pc_tailcall_subroutine hcallee x x rfl hrun rfl rfl (CalleeSavedPreserved.rfl s0)
      (by rw [hpre_pc]; exact hpre) (fun sf _ _ _ _ hq => hpost_pc x s0 sf ▸ hq) hsp
      (fun _ _ hp => by rw [hpanic] at hp; exact not_satisfies_false_sepConj hp)
      (fun _ _ _ he => by rw [hexit] at he; exact not_satisfies_false_sepConj he)
      (fun sf _ ho => hoom x s0 sf ▸ ho))
    (fun _ _ ho => ho)

theorem bcmpPreserving_patchCalls_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (a + 0x0#64) (resolve "memcmp"))
    (hwords : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : subroutine_ok prog (resolve "memcmp") memcmpPreservingSpec) :
    subroutine_ok prog a bcmpPreservingSpec :=
  bcmp_tail_ok hrange hwords hmemcmp (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem bcmpROPreserving_patchCalls_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (a + 0x0#64) (resolve "memcmp"))
    (hwords : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : subroutine_ok prog (resolve "memcmp") memcmpROPreservingSpec) :
    subroutine_ok prog a bcmpROPreservingSpec :=
  bcmp_tail_ok hrange hwords hmemcmp (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem bcmp_patchCalls_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (a + 0x0#64) (resolve "memcmp"))
    (hwords : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : subroutine_ok prog (resolve "memcmp") memcmpSpec) :
    subroutine_ok prog a bcmpSpec :=
  bcmp_tail_ok hrange hwords hmemcmp (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem bcmpRO_patchCalls_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (a + 0x0#64) (resolve "memcmp"))
    (hwords : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : subroutine_ok prog (resolve "memcmp") memcmpROSpec) :
    subroutine_ok prog a bcmpROSpec :=
  bcmp_tail_ok hrange hwords hmemcmp (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

/-! ## Placement Corollaries -/

private theorem memcmp_image_hasWords (pl : Obj.Placement)
    (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    (muslStringProg pl hooks).hasWords ((muslStringProg pl hooks).fnAddr "memcmp")
      memcmpLibcaWords :=
  muslStringProg_hasWords_relocFree (name := "memcmp") hP rfl (by decide +kernel)

theorem memcmpPreserving_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcmp")
      memcmpPreservingSpec :=
  memcmpPreserving_libca_codeAt_ok _ _ (memcmp_image_hasWords pl hooks hP)

theorem memcmpROPreserving_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcmp")
      memcmpROPreservingSpec :=
  memcmpROPreserving_libca_codeAt_ok _ _ (memcmp_image_hasWords pl hooks hP)

theorem memcmp_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcmp") memcmpSpec :=
  subroutine_ok_drop_memcmpPreserved (memcmpPreserving_image_ok pl hooks hP)

theorem memcmpRO_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcmp") memcmpROSpec :=
  subroutine_ok_drop_memcmpPreserved (memcmpROPreserving_image_ok pl hooks hP)

private theorem bcmp_image_hasWords_and_range (pl : Obj.Placement)
    (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    let prog := muslStringProg pl hooks
    let resolve := VerifiedLibraries.muslStringLib.text.resolve pl
    prog.hasWords (prog.fnAddr "bcmp")
        (Obj.patchCalls bcmpCalls bcmpWords (prog.fnAddr "bcmp") resolve) ∧
      Obj.BranchInRange (prog.fnAddr "bcmp" + 0x0#64) (resolve "memcmp") := by
  have ⟨hw, hrel⟩ := muslStringProg_hasWords_of_checkSegment (hooks := hooks)
    (name := "bcmp") (ws := bcmpWords) (R := bcmpLibcaRelocs) hP rfl (by decide +kernel)
  have hpatch : Obj.patchRelocs bcmpLibcaRelocs bcmpWords
      ((muslStringProg pl hooks).fnAddr "bcmp") (VerifiedLibraries.muslStringLib.text.resolve pl) =
      Obj.patchCalls bcmpCalls bcmpWords
        ((muslStringProg pl hooks).fnAddr "bcmp") (VerifiedLibraries.muslStringLib.text.resolve pl) := by
    simp [Obj.patchRelocs, Obj.patchCalls, Obj.patchRelocWord, Obj.addSignedAddr,
      bcmpLibcaRelocs, bcmpCalls, bcmpWords]
  have hr := hrel { off := 0, kind := .jump26, sym := "memcmp", addend := 0 }
    (by simp [bcmpLibcaRelocs])
  simp only [Obj.CodeRelocInRange, Obj.addSignedAddr, BitVec.add_zero] at hr
  refine ⟨hpatch ▸ hw, ?_⟩
  simpa [BitVec.add_zero] using hr

theorem bcmpPreserving_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp")
      bcmpPreservingSpec := by
  have ⟨hw, hrange⟩ := bcmp_image_hasWords_and_range pl hooks hP
  refine bcmpPreserving_patchCalls_ok _ _ (VerifiedLibraries.muslStringLib.text.resolve pl) hrange hw ?_
  rw [muslStringLib_resolve_sym (hooks := hooks) rfl]
  exact memcmpPreserving_image_ok pl hooks hP

theorem bcmpROPreserving_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp")
      bcmpROPreservingSpec := by
  have ⟨hw, hrange⟩ := bcmp_image_hasWords_and_range pl hooks hP
  refine bcmpROPreserving_patchCalls_ok _ _ (VerifiedLibraries.muslStringLib.text.resolve pl) hrange hw ?_
  rw [muslStringLib_resolve_sym (hooks := hooks) rfl]
  exact memcmpROPreserving_image_ok pl hooks hP

theorem bcmp_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp") bcmpSpec :=
  subroutine_ok_drop_memcmpPreserved (bcmpPreserving_image_ok pl hooks hP)

theorem bcmpRO_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp") bcmpROSpec :=
  subroutine_ok_drop_memcmpPreserved (bcmpROPreserving_image_ok pl hooks hP)

end VerifiedLibraries.Musl
