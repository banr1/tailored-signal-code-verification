/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.CallAndFrame

/-!
# Stack, Heap, and Slice Helpers for `main_m2` Dispatch

Stack `locals` split/merge lemmas, heap/layout unpackers, `CliInputsOk` argument-slice bounds, and
tail arithmetic helpers for `main_m2` subcommand dispatch.
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

/-! ## 1. Stack `locals` Split and Merge Lemmas -/

/-- Untouched part of `main`'s `0x480`-byte locals outside `[0x40..0x50)`, `[0x58..0x60)`, and `[0x1b8..0x1d8)`. -/
def m2LocalsRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x40 ∗ memRegion (fsp + 0x50#64) 8 ∗
    memRegion (fsp + 0x60#64) 0x158 ∗ memRegion (fsp + 0x1d8#64) 0x2a8

theorem locals_split_m2 (fsp : BitVec 64) :
    locals fsp [] =
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
          memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp := by
  have h1 := locals_carve_cell fsp [] 0x40 []; dsimp only [List.nil_append] at h1; rw [h1]
  congr 1; funext w3
  have h2 := locals_carve_cell fsp [cell fsp 0x40 w3] 0x48 []
  dsimp only [List.nil_append, List.cons_append] at h2; rw [h2]
  congr 1; funext w4
  have h3 := locals_carve_cell fsp [cell fsp 0x40 w3, cell fsp 0x48 w4] 0x58 []
  dsimp only [List.nil_append, List.cons_append] at h3; rw [h3]
  congr 1; funext w1
  have h4 := locals_carve_region fsp [cell fsp 0x40 w3, cell fsp 0x48 w4, cell fsp 0x58 w1] 0x1b8 32 []
  dsimp only [List.nil_append, List.cons_append] at h4; rw [h4]
  dsimp only [locals, localsFrom, cell, m2LocalsRest]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj]
  ac_rfl

theorem locals_merge_call (fsp : BitVec 64) (w : CallW) :
    ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗ ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
      memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ⊢
      locals fsp (callCellsPlaced fsp w) := by
  have heq := locals_carve_region fsp (callCellsPlaced fsp w) 0x1b8 32 []
  dsimp only [List.nil_append, List.cons_append] at heq
  rw [heq]
  dsimp only [callCellsPlaced, List.cons_append, List.nil_append, locals, localsFrom, cell, m2LocalsRest]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem locals_merge_memRegion (fsp : BitVec 64) (w3 w4 w1 : BitVec 64) :
    ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
      memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ⊢
      memRegion fsp 0x480 :=
  Entails.trans (locals_merge_call fsp ⟨0, w1, 0, w3, w4, 0, 0⟩)
    (callCellsPlaced_to_memRegion fsp _)

/-! ## 2. Heap & Layout Unpacking Helpers -/

theorem sliceArray_entails_memRegion
    (ps : List (BitVec 64 × List (BitVec 8))) (base : BitVec 64) (rem : Nat)
    (hle : ps.length * 16 + rem ≤ 2 ^ 64) :
    arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 base ps ∗
      memRegion (base + BitVec.ofNat 64 (ps.length * 16)) rem ⊢
      memRegion base (ps.length * 16 + rem) := by
  induction ps generalizing base with
  | nil =>
    have h0 : BitVec.ofNat 64 (0 * 16) = 0#64 := rfl
    dsimp only [arrayAt, List.length_nil]
    rw [h0, BitVec.add_zero, Nat.zero_mul, Nat.zero_add, emp_sepConj]
    exact Entails.refl _
  | cons pb ps ih =>
    simp only [List.length_cons] at hle
    dsimp only [arrayAt, sliceRefAt, List.length_cons]
    have h16 : (base ↦₆₄ pb.1) ∗ ((base + 8#64) ↦₆₄ BitVec.ofNat 64 pb.2.length) ⊢
        memRegion base 16 := by
      rw [show (16 : Nat) = 8 + 8 by rfl, ProofLib.memRegion_split base 8 8 (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion base pb.1)
        (pointsTo64_entails_memRegion (base + 8#64) _)
    have hshift : base + BitVec.ofNat 64 ((ps.length + 1) * 16) =
        (base + 16#64) + BitVec.ofNat 64 (ps.length * 16) := by
      bv_omega
    rw [hshift]
    have hih := ih (base + 16#64) (by omega)
    have hcomb : ((base ↦₆₄ pb.1) ∗ ((base + 8#64) ↦₆₄ BitVec.ofNat 64 pb.2.length)) ∗
        (arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 (base + 16#64) ps ∗
          memRegion ((base + 16#64) + BitVec.ofNat 64 (ps.length * 16)) rem) ⊢
        memRegion base (16 + (ps.length * 16 + rem)) := by
      rw [ProofLib.memRegion_split base 16 (ps.length * 16 + rem) (by omega)]
      exact sepConj_mono h16 hih
    have heq : (ps.length + 1) * 16 + rem = 16 + (ps.length * 16 + rem) := by omega
    rw [heq]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) hcomb

theorem pure_elim_entails {φ : Prop} {P Q : SepProp} (h : φ → (P ⊢ Q)) :
    ⌜φ⌝ ∗ P ⊢ Q :=
  Entails.pure_left h

theorem pure_intro_entails {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q :=
  Entails.pure_right hφ h

theorem exists_elim_entails {α : Type _} {F : α → SepProp} {Q : SepProp}
    (h : ∀ x, F x ⊢ Q) : (∃∗ x, F x) ⊢ Q :=
  Entails.sepExists_elim h

theorem exists_intro_entails {α : Type _} {P : SepProp} {F : α → SepProp}
    (x : α) (h : P ⊢ F x) : P ⊢ ∃∗ y, F y :=
  Entails.sepExists_right x h

theorem argsBuf_to_dealloc (A : RustAlloc) {cap ptr : BitVec 64}
    (ps : List (BitVec 64 × List (BitVec 8))) (hcap : cap ≠ 0#64) :
    argsBuf A cap ptr ps ⊢
      ⌜cap.toNat * 16 < 2 ^ 63 ∧ LayoutOk (cap.toNat * 16) 8⌝ ∗
        A.live ptr (cap.toNat * 16) 8 ∗ memRegion ptr (cap.toNat * 16) := by
  have h0 : cap ≠ 0 := hcap
  dsimp only [argsBuf, vecBuf]
  refine pure_elim_entails fun ⟨hlen, hlt, _⟩ => ?_
  simp only [h0, ↓reduceIte]
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc0 => hcap (BitVec.eq_of_toNat_eq hc0))
  have hlay : LayoutOk (cap.toNat * 16) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  refine pure_intro_entails ⟨hlt, hlay⟩ ?_
  have hmr := sliceArray_entails_memRegion ps ptr ((cap.toNat - ps.length) * 16) (by omega)
  have hsum : ps.length * 16 + (cap.toNat - ps.length) * 16 = cap.toNat * 16 := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hlen]
  rw [hsum] at hmr
  exact sepConj_mono_right hmr

theorem ownedBytes_to_dealloc (A : RustAlloc) {cap ptr len : BitVec 64}
    (bs : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    ownedBytes A cap ptr len bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ LayoutOk cap.toNat 1⌝ ∗
        A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have h0 : cap ≠ 0 := hcap
  dsimp only [ownedBytes]
  refine pure_elim_entails fun ⟨_, hlen, hlt, _⟩ => ?_
  simp only [h0, ↓reduceIte]
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc0 => hcap (BitVec.eq_of_toNat_eq hc0))
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  refine pure_intro_entails ⟨hlt, hlay⟩ ?_
  have hmr : (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
    have hsum : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hlen
    conv => rhs; rw [← hsum, ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)
  exact sepConj_mono_right hmr

theorem protocolAddressAt_to_words (A : RustAlloc) {g : AddrGhost} {av : AddrV} (a : BitVec 64)
    (hname : g.name.bytes = av.name) (hdev : g.device = av.device) :
    protocolAddressAt A g a ⊢
      ∃∗ devw : BitVec 64,
        ⌜g.name.cap ≠ 0xffffffffffffffff#64⌝ ∗
          (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 av.name.length) ∗
          ((a + 24#64) ↦₆₄ devw) ∗
          addrWords A av g.name.cap g.name.ptr (BitVec.ofNat 64 av.name.length) devw := by
  dsimp only [protocolAddressAt, vecGhostAt, vecU8At, vecHeader]
  have hmr7 : memRegion (a + 25#64) 7 =
      ∃∗ b7, ∃∗ b6, ∃∗ b5, ∃∗ b4, ∃∗ b3, ∃∗ b2, ∃∗ b1,
        (a + 25#64) ↦₈ b1 ∗ ((a + 26#64) ↦₈ b2 ∗ ((a + 27#64) ↦₈ b3 ∗
          ((a + 28#64) ↦₈ b4 ∗ ((a + 29#64) ↦₈ b5 ∗ ((a + 30#64) ↦₈ b6 ∗
            (a + 31#64) ↦₈ b7))))) := by
    rw [ProofLib.memRegion_split (a + 25#64) 1 6 (by decide),
        ProofLib.memRegion_split _ 1 5 (by decide),
        ProofLib.memRegion_split _ 1 4 (by decide),
        ProofLib.memRegion_split _ 1 3 (by decide),
        ProofLib.memRegion_split _ 1 2 (by decide),
        ProofLib.memRegion_split _ 1 1 (by decide)]
    simp only [ProofLib.memRegion_one, sepExists_sepConj_right, sepExists_sepConj_left,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hname, hdev, hmr7]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceAdd]
  refine exists_elim_entails fun b7 => exists_elim_entails fun b6 =>
    exists_elim_entails fun b5 => exists_elim_entails fun b4 =>
    exists_elim_entails fun b3 => exists_elim_entails fun b2 =>
    exists_elim_entails fun b1 => ?_
  let devw : BitVec 64 := b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ av.device
  refine exists_intro_entails devw ?_
  have hw8 :
      ((a + 24#64) ↦₈ av.device) ∗ ((a + 25#64) ↦₈ b1) ∗ ((a + 26#64) ↦₈ b2) ∗
        ((a + 27#64) ↦₈ b3) ∗ ((a + 28#64) ↦₈ b4) ∗ ((a + 29#64) ↦₈ b5) ∗
        ((a + 30#64) ↦₈ b6) ∗ ((a + 31#64) ↦₈ b7) =
      ((a + 24#64) ↦₆₄ devw) := by
    have hp8 := ProofLib.pointsToBytes8_eq_pointsTo64 (a + 24#64) av.device b1 b2 b3 b4 b5 b6 b7
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hp8
    exact hp8
  refine Entails.trans (Entails.of_eq (show
      (((a ↦₆₄ g.name.cap ∗ (a + 8#64) ↦₆₄ g.name.ptr ∗
          (a + 16#64) ↦₆₄ BitVec.ofNat 64 av.name.length) ∗
        ⌜av.name.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (if g.name.cap = 0 then emp
         else A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ av.name) ∗
           memRegion (g.name.ptr + BitVec.ofNat 64 av.name.length)
             (g.name.cap.toNat - av.name.length))) ∗
      ((a + 24#64) ↦₈ av.device ∗ ((a + 25#64) ↦₈ b1 ∗ ((a + 26#64) ↦₈ b2 ∗
        ((a + 27#64) ↦₈ b3 ∗ ((a + 28#64) ↦₈ b4 ∗ ((a + 29#64) ↦₈ b5 ∗
          ((a + 30#64) ↦₈ b6 ∗ (a + 31#64) ↦₈ b7)))))))) =
      ⌜av.name.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (((a + 24#64) ↦₈ av.device ∗ (a + 25#64) ↦₈ b1 ∗ (a + 26#64) ↦₈ b2 ∗
          (a + 27#64) ↦₈ b3 ∗ (a + 28#64) ↦₈ b4 ∗ (a + 29#64) ↦₈ b5 ∗
          (a + 30#64) ↦₈ b6 ∗ (a + 31#64) ↦₈ b7) ∗
         (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 av.name.length) ∗
         (if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ av.name) ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 av.name.length)
              (g.name.cap.toNat - av.name.length))) by ac_rfl)) ?_
  refine pure_elim_entails fun ⟨hlen, hlt, hptr⟩ => ?_
  rw [hw8]
  have hcap_ne : g.name.cap ≠ 0xffffffffffffffff#64 := by
    intro heq; rw [heq] at hlt; simp at hlt
  have hdev_eq : devw.setWidth 8 = av.device := by dsimp only [devw]; bv_bits
  dsimp only [addrWords, ownedBytes]
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜g.name.cap ≠ 0xffffffffffffffff#64⌝ ∗
        ⌜BitVec.ofNat 64 av.name.length = BitVec.ofNat 64 av.name.length ∧
            av.name.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ⌜devw.setWidth 8 = av.device⌝ ∗
        ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 av.name.length) ∗
          ((a + 24#64) ↦₆₄ devw) ∗
          (if g.name.cap = 0 then emp
           else A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ av.name) ∗
             memRegion (g.name.ptr + BitVec.ofNat 64 av.name.length)
               (g.name.cap.toNat - av.name.length))) =
      ⌜g.name.cap ≠ 0xffffffffffffffff#64⌝ ∗
        (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 av.name.length) ∗
        ((a + 24#64) ↦₆₄ devw) ∗
        (⌜BitVec.ofNat 64 av.name.length = BitVec.ofNat 64 av.name.length ∧
            av.name.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          (if g.name.cap = 0 then emp
           else A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ av.name) ∗
             memRegion (g.name.ptr + BitVec.ofNat 64 av.name.length)
               (g.name.cap.toNat - av.name.length))) ∗
        ⌜devw.setWidth 8 = av.device⌝ by ac_rfl))
  exact pure_intro_entails hcap_ne
    (pure_intro_entails ⟨rfl, hlen, hlt, hptr⟩
      (pure_intro_entails hdev_eq (Entails.of_eq (by ac_rfl))))

/-! ## 3. `CliInputsOk` Argument Bounds & Slice Unpackers -/

theorem bytesOfString_nonempty_ascii {a : String} (ha : PrintableAsciiArg a) :
    bytesOfString a ≠ [] ∧ ∀ b ∈ bytesOfString a, b ≠ 0#8 ∧ b.toNat < 128 := by
  obtain ⟨hne, hasc⟩ := ha
  dsimp only [bytesOfString]
  refine ⟨?_, ?_⟩
  · intro hnil; rw [List.map_eq_nil_iff] at hnil; exact hne (String.ext hnil)
  · intro b hb
    rw [List.mem_map] at hb; obtain ⟨c, hc, rfl⟩ := hb
    obtain ⟨hc0, hc128⟩ := hasc c hc
    have htn : (BitVec.ofNat 8 c.toNat).toNat = c.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.toNat < 256)]
    refine ⟨fun h0 => ?_, by omega⟩
    rw [h0] at htn; simp at htn; omega

theorem argvFits_bounds {argv : List String} (hfit : ArgvFitsInitialStack argv) :
    argv.length ≤ 1820 ∧ ∀ a ∈ argv, (bytesOfString a).length ≤ 16384 := by
  dsimp only [ArgvFitsInitialStack] at hfit
  have hlen : argv.length ≤ 1820 := by
    have h9 : 9 * argv.length ≤ (argv.map fun a => a.length + 1 + 8).sum := by
      clear hfit
      induction argv with
      | nil => simp
      | cons a tail ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
    omega
  refine ⟨hlen, fun a ha => ?_⟩
  have hmem : a.length + 1 + 8 ≤ (argv.map fun x => x.length + 1 + 8).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hbs : (bytesOfString a).length = a.length := by simp [bytesOfString]; rfl
  omega

theorem cliInputsOk_elem {i : Inputs} {ps : List (BitVec 64 × List (BitVec 8))}
    (hok : CliInputsOk i) (hps : ps.map (·.2) = i.argv.map bytesOfString)
    {pb : BitVec 64 × List (BitVec 8)} (hmem : pb ∈ ps) :
    pb.2 ≠ [] ∧ pb.2.length ≤ 16384 ∧ ∀ b ∈ pb.2, b ≠ 0#8 ∧ b.toNat < 128 := by
  have hmem2 : pb.2 ∈ ps.map (·.2) := List.mem_map.mpr ⟨pb, hmem, rfl⟩
  rw [hps, List.mem_map] at hmem2
  obtain ⟨a, ha, hba⟩ := hmem2
  obtain ⟨hne, hasc⟩ := bytesOfString_nonempty_ascii (hok.1 a ha)
  obtain ⟨_, hlen⟩ := argvFits_bounds hok.2
  rw [← hba]
  exact ⟨hne, hlen a ha, hasc⟩

theorem cStrAt_split (p : BitVec 64) (bs : List (BitVec 8)) :
    cStrAt p bs = (p ↦ₛ bs) ∗ ((p + BitVec.ofNat 64 bs.length) ↦₈ 0#8) :=
  ProofLib.pointsToBytes_snoc p bs 0#8

theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace :=
  ⟨by simp [allocFailedIn, h], ⟨[allocFailedEvent], h.symm⟩⟩

theorem panic_of_address {s0 s1 sf : State} {F R' : SepProp} {Qp : State → SepProp → Prop}
    (htr : s1.trace = s0.trace)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hm : sf.mem ⊨ (⌜allocFailedIn s1 sf⌝ ∗ anyHeap) ∗ R') :
    Qp sf ((⌜allocFailedIn s1 sf⌝ ∗ anyHeap) ∗ F) := by
  have hassoc : (⌜allocFailedIn s1 sf⌝ ∗ anyHeap) ∗ R' =
      ⌜allocFailedIn s1 sf⌝ ∗ (anyHeap ∗ R') := by ac_rfl
  rw [hassoc, satisfies_pure_sepConj] at hm
  obtain ⟨hm1, -⟩ := hm
  have h0 : allocFailedIn s0 sf := by unfold allocFailedIn at hm1 ⊢; rwa [htr] at hm1
  exact hpanic sf _ h0

theorem cmn1_false {x : BitVec 64} (h : x ≠ 0xffffffffffffffff#64) :
    (x + 1#64 == 0#64) = false := by
  apply beq_false_of_ne; intro heq; apply h; bv_omega

theorem hi32_or_lo32 (p : BitVec 64) :
    ((p &&& 0xffffffff00000000#64) ||| ((p.setWidth 32).setWidth 64)) = p := by
  bv_bits

theorem pointsTo64_zero_split32 (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  have h8 := (ProofLib.pointsToBytes8_eq_pointsTo64 a 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8).trans
    (congrArg (a ↦₆₄ ·) (by decide : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8) = 0#64))
  have h4a := (ProofLib.pointsToBytes4_eq_pointsTo32 a 0#8 0#8 0#8 0#8).trans
    (congrArg (a ↦₃₂ ·) (by decide : (0#8 ++ 0#8 ++ 0#8 ++ 0#8) = 0#32))
  have h4b := (ProofLib.pointsToBytes4_eq_pointsTo32 (a + 4#64) 0#8 0#8 0#8 0#8).trans
    (congrArg ((a + 4#64) ↦₃₂ ·) (by decide : (0#8 ++ 0#8 ++ 0#8 ++ 0#8) = 0#32))
  rw [← h8, show [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] =
      [0#8, 0#8, 0#8, 0#8] ++ [0#8, 0#8, 0#8, 0#8] from rfl,
    ProofLib.pointsToBytes_append, show ([0#8, 0#8, 0#8, 0#8] : List (BitVec 8)).length = 4 from rfl,
    h4a, h4b]

theorem pointsTo64_one_split32 (a : BitVec 64) :
    (a ↦₆₄ 1#64) = (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  have h8 := (ProofLib.pointsToBytes8_eq_pointsTo64 a 1#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8).trans
    (congrArg (a ↦₆₄ ·) (by decide : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8) = 1#64))
  have h4a := (ProofLib.pointsToBytes4_eq_pointsTo32 a 1#8 0#8 0#8 0#8).trans
    (congrArg (a ↦₃₂ ·) (by decide : (0#8 ++ 0#8 ++ 0#8 ++ 1#8) = 1#32))
  have h4b := (ProofLib.pointsToBytes4_eq_pointsTo32 (a + 4#64) 0#8 0#8 0#8 0#8).trans
    (congrArg ((a + 4#64) ↦₃₂ ·) (by decide : (0#8 ++ 0#8 ++ 0#8 ++ 0#8) = 0#32))
  rw [← h8, show [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] =
      [1#8, 0#8, 0#8, 0#8] ++ [0#8, 0#8, 0#8, 0#8] from rfl,
    ProofLib.pointsToBytes_append, show ([1#8, 0#8, 0#8, 0#8] : List (BitVec 8)).length = 4 from rfl,
    h4a, h4b]

theorem pointsTo32_pair_entails_memRegion8 (a : BitVec 64) (v0 v1 : BitVec 32) :
    (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1) ⊢ memRegion a 8 := by
  rw [show (8 : Nat) = 4 + 4 by rfl, ProofLib.memRegion_split a 4 4 (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion a v0)
    (pointsTo32_entails_memRegion (a + 4#64) v1)

theorem bytes4_eq_pointsTo32 (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3]) = (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) :=
  ProofLib.pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3

theorem bytes6_eq_pointsTo32_16 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5]) =
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₁₆ (b5 ++ b4)) := by
  rw [show [b0, b1, b2, b3, b4, b5] = [b0, b1, b2, b3] ++ [b4, b5] from rfl,
    ProofLib.pointsToBytes_append, show ([b0, b1, b2, b3] : List (BitVec 8)).length = 4 from rfl,
    ProofLib.pointsToBytes4_eq_pointsTo32, ProofLib.pointsToBytes2_eq_pointsTo16]

def argsBufTail (A : RustAlloc) (cap ptr : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  ⌜ps.length ≤ cap.toNat ∧ cap.toNat * 16 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr (cap.toNat * 16) 8 ∗
    memRegion (ptr + BitVec.ofNat 64 (ps.length * 16)) ((cap.toNat - ps.length) * 16)

theorem argsBuf_two_eq (A : RustAlloc) {cap ptr : BitVec 64}
    (pb1 pb2 : BitVec 64 × List (BitVec 8)) (hcap : cap ≠ 0#64) :
    argsBuf A cap ptr [pb1, pb2] =
      (ptr ↦₆₄ pb1.1) ∗ ((ptr + 8#64) ↦₆₄ BitVec.ofNat 64 pb1.2.length) ∗
      ((ptr + 16#64) ↦₆₄ pb2.1) ∗ ((ptr + 24#64) ↦₆₄ BitVec.ofNat 64 pb2.2.length) ∗
      argsBufTail A cap ptr [pb1, pb2] := by
  have h0 : cap ≠ 0 := hcap
  dsimp only [argsBuf, vecBuf, arrayAt, sliceRefAt, argsBufTail]
  simp only [h0, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  ac_rfl

theorem argsBuf_three_eq (A : RustAlloc) {cap ptr : BitVec 64}
    (pb1 pb2 pb3 : BitVec 64 × List (BitVec 8)) (hcap : cap ≠ 0#64) :
    argsBuf A cap ptr [pb1, pb2, pb3] =
      (ptr ↦₆₄ pb1.1) ∗ ((ptr + 8#64) ↦₆₄ BitVec.ofNat 64 pb1.2.length) ∗
      ((ptr + 16#64) ↦₆₄ pb2.1) ∗ ((ptr + 24#64) ↦₆₄ BitVec.ofNat 64 pb2.2.length) ∗
      ((ptr + 32#64) ↦₆₄ pb3.1) ∗ ((ptr + 40#64) ↦₆₄ BitVec.ofNat 64 pb3.2.length) ∗
      argsBufTail A cap ptr [pb1, pb2, pb3] := by
  have h0 : cap ≠ 0 := hcap
  dsimp only [argsBuf, vecBuf, arrayAt, sliceRefAt, argsBufTail]
  simp only [h0, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  ac_rfl

theorem argsBuf_two_cons (A : RustAlloc) {cap ptr : BitVec 64}
    (pb1 pb2 : BitVec 64 × List (BitVec 8)) (hcap : cap ≠ 0#64) (R : SepProp) :
    (ptr ↦₆₄ pb1.1) ∗ ((ptr + 8#64) ↦₆₄ BitVec.ofNat 64 pb1.2.length) ∗
      ((ptr + 16#64) ↦₆₄ pb2.1) ∗ ((ptr + 24#64) ↦₆₄ BitVec.ofNat 64 pb2.2.length) ∗
      argsBufTail A cap ptr [pb1, pb2] ∗ R =
    argsBuf A cap ptr [pb1, pb2] ∗ R := by
  rw [argsBuf_two_eq A pb1 pb2 hcap]; ac_rfl

theorem argsBuf_three_cons (A : RustAlloc) {cap ptr : BitVec 64}
    (pb1 pb2 pb3 : BitVec 64 × List (BitVec 8)) (hcap : cap ≠ 0#64) (R : SepProp) :
    (ptr ↦₆₄ pb1.1) ∗ ((ptr + 8#64) ↦₆₄ BitVec.ofNat 64 pb1.2.length) ∗
      ((ptr + 16#64) ↦₆₄ pb2.1) ∗ ((ptr + 24#64) ↦₆₄ BitVec.ofNat 64 pb2.2.length) ∗
      ((ptr + 32#64) ↦₆₄ pb3.1) ∗ ((ptr + 40#64) ↦₆₄ BitVec.ofNat 64 pb3.2.length) ∗
      argsBufTail A cap ptr [pb1, pb2, pb3] ∗ R =
    argsBuf A cap ptr [pb1, pb2, pb3] ∗ R := by
  rw [argsBuf_three_eq A pb1 pb2 pb3 hcap]; ac_rfl

/-! ## 4. Pure Tail Cell & Arithmetic Helpers -/

theorem cells4_to_memRegion_32 (a : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      memRegion a 32 := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
    ProofLib.memRegion_split a 8 (8 + (8 + 8)) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 (8 + 8) (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_split (a + 16#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) v1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) v2)
        (pointsTo64_entails_memRegion (a + 24#64) v3)))

theorem lsl4_toNat {v : BitVec 64} (hlt : v.toNat * 16 < 2 ^ 63) :
    (v <<< 4).toNat = v.toNat * 16 := by bv_omega

theorem zext32_idemp (w28 w21 : BitVec 64) :
    (w28 ||| ((((w21.setWidth 32).setWidth 64).setWidth 32).setWidth 64)) =
      (w28 ||| ((w21.setWidth 32).setWidth 64)) := by bv_bits

theorem zext32_lt (w21 : BitVec 64) :
    ((w21.setWidth 32).setWidth 64).toNat < 2 ^ 32 := by bv_omega

theorem fsp_align_of_spAligned {s0 : State} (h : s0.spAligned = true) :
    (s0.sp - BitVec.ofNat 64 mainFrameSize) &&& 15#64 = 0#64 := by
  have h1 := ProofLib.spAligned_sub s0.sp 0x4e0#64 h
  simpa only [State.spAligned, mainFrameSize, beq_iff_eq] using h1

theorem perm_parseFail_pre (Loc V B M S P R : SepProp) :
    Loc ∗ (V ∗ B ∗ M ∗ S ∗ P ∗ R) ⊢ V ∗ B ∗ M ∗ Loc ∗ S ∗ P ∗ R :=
  Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
