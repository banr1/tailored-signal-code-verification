/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import ProofLib.SepLogic.WPp

/-!
# Pure, Spatial, and Call Helpers for `main` M2 Collect

Input bounds, modular arithmetic, stack-frame splitters, `argsBuf` / `argvAtP` / `vec16At` spatial
focusing and push bridges, and `SepWPp` call wrappers for `main`'s `Vec<&str>` collection loop.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## 1. Input Bounds & Modular Arithmetic Helpers -/

theorem ps_length_eq {ps : List (BitVec 64 × List (BitVec 8))} {argv : List String}
    (hps : ps.map (·.2) = argv.map bytesOfString) : ps.length = argv.length := by
  have h := congrArg List.length hps
  simpa only [List.length_map] using h

theorem bytesOfString_length (s : String) : (bytesOfString s).length = s.length := by
  simp [bytesOfString, String.length_toList]

theorem bytesOfString_ascii {s : String} (hs : PrintableAsciiArg s) :
    ∀ b ∈ bytesOfString s, b.toNat < 128 := by
  rintro b hb
  simp only [bytesOfString, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have ⟨_, hlt⟩ := hs.2 c hc
  rw [BitVec.toNat_ofNat]
  omega

private theorem sum_argv_ge_nine : (xs : List String) →
    9 * xs.length ≤ (xs.map fun a => a.length + 1 + 8).sum
  | [] => by simp
  | a :: tl => by
    have ih := sum_argv_ge_nine tl
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem mem_le_list_sum {xs : List Nat} {x : Nat} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · have := ih hmem; omega

theorem argv_len_le {i : Inputs} (hok : CliInputsOk i) : i.argv.length ≤ 1820 := by
  have h1 := sum_argv_ge_nine i.argv
  have h2 : (i.argv.map fun a => a.length + 1 + 8).sum ≤ 16384 := hok.2
  omega

theorem ps_getElem_bounds {i : Inputs} {ps : List (BitVec 64 × List (BitVec 8))}
    (hok : CliInputsOk i) (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (k : Nat) (hk : k < ps.length) :
    (∀ b ∈ ps[k].2, b.toNat < 128) ∧ ps[k].2.length ≤ 16384 := by
  have hlen := ps_length_eq hps
  have hki : k < i.argv.length := by omega
  have hbs : ps[k].2 = bytesOfString i.argv[k] := by
    have hmap := congrArg (fun l => l[k]?) hps
    simp only [List.getElem?_map, getElem?_pos ps k hk, getElem?_pos i.argv k hki,
      Option.map_some, Option.some.injEq] at hmap
    exact hmap
  rw [hbs]
  have hmem : i.argv[k] ∈ i.argv := List.getElem_mem hki
  refine ⟨bytesOfString_ascii (hok.1 _ hmem), ?_⟩
  rw [bytesOfString_length]
  have hterm : i.argv[k].length + 1 + 8 ∈ i.argv.map (fun a => a.length + 1 + 8) :=
    List.mem_map_of_mem hmem
  have hle := mem_le_list_sum hterm
  have hfits : (i.argv.map fun a => a.length + 1 + 8).sum ≤ 16384 := hok.2
  omega

theorem add_mul16_beq (buf : BitVec 64) {a b : Nat}
    (ha : 16 * a < 2 ^ 64) (hb : 16 * b < 2 ^ 64) :
    ((buf + BitVec.ofNat 64 (16 * a)) == (buf + BitVec.ofNat 64 (16 * b))) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [decide_eq_false hab, beq_eq_false_iff_ne]
    intro heq
    have hcancel : BitVec.ofNat 64 (16 * a) = BitVec.ofNat 64 (16 * b) := by
      have hsub := congrArg (fun z => z - buf) heq
      have h1 : buf + BitVec.ofNat 64 (16 * a) - buf = BitVec.ofNat 64 (16 * a) := by bv_omega
      have h2 : buf + BitVec.ofNat 64 (16 * b) - buf = BitVec.ofNat 64 (16 * b) := by bv_omega
      rwa [h1, h2] at hsub
    have ht := congrArg BitVec.toNat hcancel
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
    exact hab (by omega)

theorem ofNat_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [decide_eq_false hab, beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
    exact hab ht

theorem vcap_add_one_beq_zero_false {vcap : BitVec 64} (h : 16 * vcap.toNat < 2 ^ 63) :
    (vcap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  have hv : vcap.toNat + 1 < 2 ^ 64 := by omega
  change (vcap.toNat + 1 % 2 ^ 64) % 2 ^ 64 = 0 at ht
  rw [Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.mod_eq_of_lt hv] at ht
  omega

theorem vcap_beq_max_false {vcap : BitVec 64} (h : 16 * vcap.toNat < 2 ^ 63) :
    (vcap == 0xffffffffffffffff#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  subst heq
  change 16 * (2 ^ 64 - 1) < 2 ^ 63 at h
  omega

/-! ## 2. Stack Alignment, Locals Splitters, and Stack Budget Splitters -/

theorem spAligned_sub_mainFrameSize (sp : BitVec 64) :
    ((sp - BitVec.ofNat 64 mainFrameSize) &&& 15#64 == 0#64) = (sp &&& 15#64 == 0#64) := by
  change ((sp - 0x4e0#64) &&& 15#64 == 0#64) = (sp &&& 15#64 == 0#64)
  by_cases h : (sp &&& 15#64) = 0#64
  · have h' : ((sp - 0x4e0#64) &&& 15#64) = 0#64 := by bv_bits
    rw [beq_iff_eq.mpr h, beq_iff_eq.mpr h']
  · have h' : ((sp - 0x4e0#64) &&& 15#64) ≠ 0#64 := by
      intro hc
      apply h
      bv_bits
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

theorem stackAt_split_ge' (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

theorem memRegion_24_words (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem words_to_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_words]
  exact Entails.sepExists_right w2
    (Entails.sepExists_right w1 (Entails.sepExists_right w0 (Entails.refl _)))

/-- Exact partition of `locals fsp []` (`memRegion fsp 0x480`) around `M2Collect`'s two 24-byte
stack slots `fsp + 0x1b8` (`from_utf8` sret) and `fsp + 0x310` (`Vec<&str>` header). -/
theorem locals_nil_split_m2 (fsp : BitVec 64) :
    locals fsp [] =
      memRegion fsp 0x1b8 ∗
      memRegion (fsp + 0x1b8#64) 24 ∗
      memRegion (fsp + 0x1d0#64) 0x140 ∗
      memRegion (fsp + 0x310#64) 24 ∗
      memRegion (fsp + 0x328#64) 0x158 := by
  simp only [locals, localsFrom, BitVec.add_zero, Nat.sub_zero]
  rw [show (0x480 : Nat) = 0x1b8 + 0x2c8 by rfl, ProofLib.memRegion_split fsp 0x1b8 0x2c8 (by decide),
      show (0x2c8 : Nat) = 24 + 0x2b0 by rfl,
      ProofLib.memRegion_split (fsp + 0x1b8#64) 24 0x2b0 (by decide),
      show (0x2b0 : Nat) = 0x140 + 0x170 by rfl,
      ProofLib.memRegion_split (fsp + 0x1b8#64 + 24#64) 0x140 0x170 (by decide),
      show (0x170 : Nat) = 24 + 0x158 by rfl,
      ProofLib.memRegion_split (fsp + 0x1b8#64 + 24#64 + 0x140#64) 24 0x158 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## 3. `argvAtP`, `argsBuf`, and `vec16At` Spatial Bridges -/

/-- Remaining frame of `argvAtP a ps` with `ps[k].1 ↦ₛ ps[k].2` extracted for reading. -/
def argvAtPRest : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → Nat → SepProp
  | a, [], _ => a ↦₆₄ 0#64
  | a, (p, s) :: rest, 0 =>
    (a ↦₆₄ p) ∗ ((p + BitVec.ofNat 64 s.length) ↦ₛ [0#8]) ∗ argvAtP (a + 8#64) rest
  | a, (p, s) :: rest, k + 1 =>
    (a ↦₆₄ p) ∗ cStrAt p s ∗ argvAtPRest (a + 8#64) rest k

theorem argvAtP_focus (a : BitVec 64) :
    (ps : List (BitVec 64 × List (BitVec 8))) → (k : Nat) → (hk : k < ps.length) →
    argvAtP a ps = (ps[k].1 ↦ₛ ps[k].2) ∗ argvAtPRest a ps k
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | (p, s) :: rest, 0, _ => by
    simp only [argvAtP, argvAtPRest, cStrAt, List.getElem_cons_zero, pointsToBytes_append]
    ac_rfl
  | (p, s) :: rest, k + 1, hk => by
    have hk' : k < rest.length := Nat.lt_of_succ_lt_succ hk
    simp only [argvAtP, argvAtPRest, List.getElem_cons_succ, argvAtP_focus (a + 8#64) rest k hk']
    ac_rfl

/-- Remaining frame of `arrayAt (sliceRefAt ...) 16 a ps` with slot `k` extracted for reading. -/
def arrayAtSliceRest : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → Nat → SepProp
  | _, [], _ => emp
  | a, _ :: rest, 0 =>
    arrayAt (fun pb addr => sliceRefAt addr pb.1 pb.2.length) 16 (a + 16#64) rest
  | a, pb :: rest, k + 1 =>
    sliceRefAt a pb.1 pb.2.length ∗ arrayAtSliceRest (a + 16#64) rest k

theorem arrayAt_slice_focus (a : BitVec 64) :
    (ps : List (BitVec 64 × List (BitVec 8))) → (k : Nat) → (hk : k < ps.length) →
    arrayAt (fun pb addr => sliceRefAt addr pb.1 pb.2.length) 16 a ps =
      ((a + BitVec.ofNat 64 (16 * k)) ↦₆₄ ps[k].1) ∗
      (((a + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
      arrayAtSliceRest a ps k
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | (p, s) :: rest, 0, _ => by
    simp only [arrayAt, arrayAtSliceRest, sliceRefAt, Nat.mul_zero,
      show BitVec.ofNat 64 16 = 16#64 by rfl, show BitVec.ofNat 64 0 = 0#64 by rfl,
      BitVec.add_zero, List.getElem_cons_zero]
    ac_rfl
  | (p, s) :: rest, k + 1, hk => by
    have hk' : k < rest.length := Nat.lt_of_succ_lt_succ hk
    have ih := arrayAt_slice_focus (a + 16#64) rest k hk'
    have hoff : a + 16#64 + BitVec.ofNat 64 (16 * k) = a + BitVec.ofNat 64 (16 * (k + 1)) := by
      rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_add]
      congr 2; omega
    simp only [arrayAt, arrayAtSliceRest, show BitVec.ofNat 64 16 = 16#64 by rfl,
      List.getElem_cons_succ]
    rw [ih, hoff]
    ac_rfl

/-- Remaining frame of `argsBuf A cap buf ps` with element `k` extracted for reading. -/
def argsBufRest (A : RustAlloc) (cap buf : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) (k : Nat) : SepProp :=
  ⌜cap ≠ 0 ∧ ps.length ≤ cap.toNat ∧ cap.toNat * 16 < 2 ^ 63 ∧ buf ≠ 0⌝ ∗
    A.live buf (cap.toNat * 16) 8 ∗
    arrayAtSliceRest buf ps k ∗
    memRegion (buf + BitVec.ofNat 64 (ps.length * 16)) ((cap.toNat - ps.length) * 16)

theorem argsBuf_focus (A : RustAlloc) (cap buf : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) (k : Nat) (hk : k < ps.length) :
    argsBuf A cap buf ps =
      ((buf + BitVec.ofNat 64 (16 * k)) ↦₆₄ ps[k].1) ∗
      (((buf + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
      argsBufRest A cap buf ps k := by
  unfold argsBuf vecBuf argsBufRest
  by_cases hcap : cap = 0
  · subst hcap
    have hnot : ¬ ps.length ≤ (0 : BitVec 64).toNat := by
      change ¬ ps.length ≤ 0
      omega
    simp only [hnot, false_and, ne_eq, not_true_eq_false]
    apply Entails.antisymm
    · exact Entails.pure_left False.elim
    · rw [show (((buf + BitVec.ofNat 64 (16 * k)) ↦₆₄ ps[k].1) ∗
          (((buf + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
          ⌜False⌝ ∗ A.live buf ((0 : BitVec 64).toNat * 16) 8 ∗
          arrayAtSliceRest buf ps k ∗
          memRegion (buf + BitVec.ofNat 64 (ps.length * 16))
            (((0 : BitVec 64).toNat - ps.length) * 16)) =
          ⌜False⌝ ∗ (((buf + BitVec.ofNat 64 (16 * k)) ↦₆₄ ps[k].1) ∗
            (((buf + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
            A.live buf ((0 : BitVec 64).toNat * 16) 8 ∗ arrayAtSliceRest buf ps k ∗
            memRegion (buf + BitVec.ofNat 64 (ps.length * 16))
              (((0 : BitVec 64).toNat - ps.length) * 16)) by ac_rfl]
      exact Entails.pure_left False.elim
  · simp only [hcap, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    rw [arrayAt_slice_focus buf ps k hk]
    ac_rfl

/-- 16-byte raw representation of a `(ptr, len)` slice entry in memory. -/
def sliceBytes (pb : BitVec 64 × List (BitVec 8)) : List (BitVec 8) :=
  unpack64 pb.1 ++ unpack64 (BitVec.ofNat 64 pb.2.length)

/-- Flat `16 * ps.length`-byte representation of `ps` for `vec16At` across `reserve16`. -/
def flatSliceBytes (ps : List (BitVec 64 × List (BitVec 8))) : List (BitVec 8) :=
  ps.flatMap sliceBytes

theorem sliceBytes_length (pb : BitVec 64 × List (BitVec 8)) :
    (sliceBytes pb).length = 16 := by
  simp [sliceBytes, unpack64_length]

theorem flatSliceBytes_length : (ps : List (BitVec 64 × List (BitVec 8))) →
    (flatSliceBytes ps).length = 16 * ps.length
  | [] => rfl
  | pb :: rest => by
    simp only [flatSliceBytes, List.flatMap_cons, List.length_append, sliceBytes_length,
      List.length_cons]
    have ih := flatSliceBytes_length rest
    dsimp [flatSliceBytes] at ih
    omega

theorem sliceRefAt_eq_pointsToBytes (pb : BitVec 64 × List (BitVec 8)) (a : BitVec 64) :
    sliceRefAt a pb.1 pb.2.length = (a ↦ₛ sliceBytes pb) := by
  unfold sliceRefAt sliceBytes
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]

theorem arrayAt_sliceRefAt_eq_pointsToBytes :
    (ps : List (BitVec 64 × List (BitVec 8))) → (a : BitVec 64) →
    arrayAt (fun pb addr => sliceRefAt addr pb.1 pb.2.length) 16 a ps = (a ↦ₛ flatSliceBytes ps)
  | [], a => by simp [arrayAt, flatSliceBytes]
  | pb :: rest, a => by
    have ih := arrayAt_sliceRefAt_eq_pointsToBytes rest (a + 16#64)
    simp only [arrayAt, show BitVec.ofNat 64 16 = 16#64 by rfl]
    rw [ih, sliceRefAt_eq_pointsToBytes]
    unfold flatSliceBytes
    simp only [List.flatMap_cons, pointsToBytes_append, sliceBytes_length]

theorem arrayAt_append1 {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    (xs : List α) → (x : α) → (base : BitVec 64) →
    arrayAt elem stride base (xs ++ [x]) =
      arrayAt elem stride base xs ∗ elem x (base + BitVec.ofNat 64 (stride * xs.length))
  | [], x, base => by
    simp only [List.nil_append, arrayAt, List.length_nil, Nat.mul_zero,
      show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, emp_sepConj, sepConj_emp]
  | y :: ys, x, base => by
    have ih := arrayAt_append1 elem stride ys x (base + BitVec.ofNat 64 stride)
    have hoff : base + BitVec.ofNat 64 stride + BitVec.ofNat 64 (stride * ys.length) =
        base + BitVec.ofNat 64 (stride * (y :: ys).length) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    simp only [List.cons_append, arrayAt]
    rw [ih, hoff, sepConj_assoc]

/-- Pack `vecHeader + argsBuf` (with `cap ≠ 0`) into `vec16At` for `reserve16Spec.pre`. -/
theorem argsBuf_to_vec16At (A : RustAlloc) (v cap ptr : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) (hcap : cap ≠ 0) :
    (vecHeader v cap ptr (BitVec.ofNat 64 ps.length) ∗ argsBuf A cap ptr ps) ⊢
      vec16At A v cap ptr (flatSliceBytes ps) := by
  unfold argsBuf vecBuf vec16At
  have hlen := flatSliceBytes_length ps
  have hdiv : (flatSliceBytes ps).length / 16 = ps.length := by rw [hlen]; omega
  have hmod : (flatSliceBytes ps).length % 16 = 0 := by rw [hlen]; omega
  have hmul : 16 * cap.toNat = cap.toNat * 16 := Nat.mul_comm _ _
  have hmul_ps : 16 * ps.length = ps.length * 16 := Nat.mul_comm _ _
  simp only [hcap, ↓reduceIte, arrayAt_sliceRefAt_eq_pointsToBytes]
  rw [hdiv, hmod, hlen, hmul, hmul_ps]
  rw [sepConj_comm (vecHeader v cap ptr (BitVec.ofNat 64 ps.length)), sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨hle, hlt63, hptr⟩
  have hsub : cap.toNat * 16 - ps.length * 16 = (cap.toNat - ps.length) * 16 := by omega
  rw [hsub]
  rw [sepConj_comm _ (vecHeader v cap ptr (BitVec.ofNat 64 ps.length))]
  apply sepConj_mono_right
  exact Entails.pure_right ⟨rfl, by omega, hlt63, hptr⟩ (Entails.refl _)

/-- Unpack `vec16At` back into `vecHeader + argsBuf` after `reserve16Spec.post`. -/
theorem vec16At_to_argsBuf (A : RustAlloc) (v cap' p' : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8)))
    (hfit : (flatSliceBytes ps).length / 16 + 1 ≤ cap'.toNat) :
    vec16At A v cap' p' (flatSliceBytes ps) ⊢
      ⌜cap' ≠ 0 ∧ ps.length < cap'.toNat⌝ ∗
        vecHeader v cap' p' (BitVec.ofNat 64 ps.length) ∗
        argsBuf A cap' p' ps := by
  have hlen := flatSliceBytes_length ps
  have hdiv : (flatSliceBytes ps).length / 16 = ps.length := by rw [hlen]; omega
  have hmod : (flatSliceBytes ps).length % 16 = 0 := by rw [hlen]; omega
  have hlt : ps.length < cap'.toNat := by omega
  have hcap : cap' ≠ 0 := by intro h0; rw [h0] at hlt; change ps.length < 0 at hlt; omega
  unfold vec16At argsBuf vecBuf
  have hmul : 16 * cap'.toNat = cap'.toNat * 16 := Nat.mul_comm _ _
  have hmul_ps : 16 * ps.length = ps.length * 16 := Nat.mul_comm _ _
  simp only [hcap, ↓reduceIte, arrayAt_sliceRefAt_eq_pointsToBytes]
  rw [hdiv, hmod, hlen, hmul, hmul_ps]
  rw [sepConj_comm (vecHeader v cap' p' (BitVec.ofNat 64 ps.length)), sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨_, _, hlt63, hptr⟩
  apply Entails.pure_right ⟨hcap, hlt⟩
  rw [sepConj_comm _ (vecHeader v cap' p' (BitVec.ofNat 64 ps.length))]
  apply sepConj_mono_right
  apply Entails.pure_right ⟨Nat.le_of_lt hlt, hlt63, hptr⟩
  have hsub : cap'.toNat * 16 - ps.length * 16 = (cap'.toNat - ps.length) * 16 := by omega
  rw [hsub]
  exact Entails.refl _

/-- Assemble initial `argsBuf A 4#64 vptr [pb0]` right after `__rust_alloc(64, 8)` + `stp`. -/
theorem argsBuf_init_cap4 (A : RustAlloc) (vptr : BitVec 64)
    (pb0 : BitVec 64 × List (BitVec 8)) (hvptr : vptr ≠ 0) :
    (A.live vptr 64 8 ∗ (vptr ↦₆₄ pb0.1) ∗ ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 pb0.2.length) ∗
      memRegion (vptr + 16#64) 48) ⊢
      argsBuf A 4#64 vptr [pb0] := by
  unfold argsBuf vecBuf
  simp only [show (4#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte, arrayAt, sepConj_emp, sliceRefAt,
    List.length_singleton, show (4#64 : BitVec 64).toNat = 4 by rfl, show 4 * 16 = 64 by rfl,
    show 1 * 16 = 16 by rfl, show (4 - 1) * 16 = 48 by rfl, show BitVec.ofNat 64 16 = 16#64 by rfl]
  apply Entails.pure_right ⟨by decide, by decide, hvptr⟩
  exact Entails.of_eq (by ac_rfl)

/-- Split `argsBuf A cap ptr ps_done` when `ps_done.length < cap.toNat` to expose the next
16-byte writable two-word slot at `ptr + BitVec.ofNat 64 (16 * ps_done.length)`. -/
theorem argsBuf_push_split (A : RustAlloc) (cap ptr : BitVec 64)
    (ps_done : List (BitVec 64 × List (BitVec 8))) (hlen_lt : ps_done.length < cap.toNat) :
    argsBuf A cap ptr ps_done ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜cap ≠ 0 ∧ cap.toNat * 16 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 16) 8 ∗
        arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 ptr ps_done ∗
        ((ptr + BitVec.ofNat 64 (16 * ps_done.length)) ↦₆₄ w0) ∗
        (((ptr + BitVec.ofNat 64 (16 * ps_done.length)) + 8#64) ↦₆₄ w1) ∗
        memRegion (ptr + BitVec.ofNat 64 ((ps_done.length + 1) * 16))
          ((cap.toNat - (ps_done.length + 1)) * 16) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change ps_done.length < 0 at hlen_lt; omega
  unfold argsBuf vecBuf
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left
  rintro ⟨_, hcap_lt, hptr⟩
  have hsplit_len : (cap.toNat - ps_done.length) * 16 =
      16 + (cap.toNat - (ps_done.length + 1)) * 16 := by
    have : cap.toNat - ps_done.length = 1 + (cap.toNat - (ps_done.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : ps_done.length * 16 = 16 * ps_done.length := Nat.mul_comm _ _
  have hoff :
      ptr + BitVec.ofNat 64 (16 * ps_done.length) + BitVec.ofNat 64 16 =
        ptr + BitVec.ofNat 64 ((ps_done.length + 1) * 16) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hsplit_len, hmul,
      ProofLib.memRegion_split (ptr + BitVec.ofNat 64 (16 * ps_done.length)) 16 _ (by omega),
      hoff,
      show (16 : Nat) = 8 + 8 by rfl,
      ProofLib.memRegion_split (ptr + BitVec.ofNat 64 (16 * ps_done.length)) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_right w1
  apply Entails.sepExists_right w0
  apply Entails.pure_right ⟨hcap, hcap_lt, hptr⟩
  exact Entails.of_eq (by ac_rfl)

/-- Reassemble `argsBuf A cap ptr (ps_done ++ [pb])` after storing `pb` at slot `ps_done.length`. -/
theorem argsBuf_push_reassemble (A : RustAlloc) (cap ptr : BitVec 64)
    (ps_done : List (BitVec 64 × List (BitVec 8))) (pb : BitVec 64 × List (BitVec 8))
    (hlen_lt : ps_done.length < cap.toNat) (hcap_lt : cap.toNat * 16 < 2 ^ 63) (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 16) 8 ∗
      arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 ptr ps_done ∗
      ((ptr + BitVec.ofNat 64 (16 * ps_done.length)) ↦₆₄ pb.1) ∗
      (((ptr + BitVec.ofNat 64 (16 * ps_done.length)) + 8#64) ↦₆₄ BitVec.ofNat 64 pb.2.length) ∗
      memRegion (ptr + BitVec.ofNat 64 ((ps_done.length + 1) * 16))
        ((cap.toNat - (ps_done.length + 1)) * 16)) ⊢
      argsBuf A cap ptr (ps_done ++ [pb]) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change ps_done.length < 0 at hlen_lt; omega
  unfold argsBuf vecBuf
  simp only [hcap, ↓reduceIte, List.length_append, List.length_singleton, arrayAt_append1]
  apply Entails.pure_right ⟨by omega, hcap_lt, hptr⟩
  unfold sliceRefAt
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Pure `SepWPp`, Callee-Saved, and Loop Frame Helpers (`M2Steps` / `M2Entry`) -/

namespace M2Steps

theorem sp_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

theorem sp_setMem_setPC (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

theorem readReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

theorem readReg64_setMem_setPC (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

theorem readReg32_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

theorem readReg32_setMem_setPC (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

theorem readReg_setPC (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem readReg_setMem_setPC (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem sepWPp_mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hPP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) : SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hPP) hm) hL

theorem sepWPp_mono_pre_sp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {F : BitVec 64 → SepProp} {fsp : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsp : s.sp = fsp) (hPP : P ⊢ F fsp) (h : SepWPp prog ret s (F s.sp) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_mono_pre (hsp ▸ hPP) h

theorem sepWPp_pure_elim {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) : SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_exists_elim {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog ret s (P x) Q Qp oom) : SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

def fspOf (s0 : State) : BitVec 64 := s0.sp - BitVec.ofNat 64 mainFrameSize

@[simp, arm64_norm ↓, wp_norm ↓]
theorem fspOf_def (s0 : State) : fspOf s0 = s0.sp - BitVec.ofNat 64 mainFrameSize := rfl

theorem ofNat_beq_bv {k : Nat} (vcap : BitVec 64) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k == vcap) = decide (k = vcap.toNat) := by
  have hv : BitVec.ofNat 64 vcap.toNat = vcap := by simp
  conv => lhs; rhs; rw [← hv]
  exact ofNat_beq_ofNat hk vcap.isLt

theorem entail_with_frame (F : SepProp) {A B P Q : SepProp}
    (hAB : A ⊢ B)
    (hP : P = A ∗ F := by
      simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]; try ac_rfl)
    (hQ : B ∗ F = Q := by
      simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]; try ac_rfl) :
    P ⊢ Q := by
  rw [hP, ← hQ]
  exact sepConj_mono_left hAB

theorem cs_x19 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 19#5) = s1.readReg64 (.gpr 19#5) := h.1
theorem cs_x20 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 20#5) = s1.readReg64 (.gpr 20#5) := h.2.1
theorem cs_x21 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 21#5) = s1.readReg64 (.gpr 21#5) := h.2.2.1
theorem cs_x22 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 22#5) = s1.readReg64 (.gpr 22#5) := h.2.2.2.1
theorem cs_x23 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 23#5) = s1.readReg64 (.gpr 23#5) := h.2.2.2.2.1
theorem cs_x24 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 24#5) = s1.readReg64 (.gpr 24#5) := h.2.2.2.2.2.1
theorem cs_x25 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 25#5) = s1.readReg64 (.gpr 25#5) := h.2.2.2.2.2.2.1
theorem cs_x26 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 26#5) = s1.readReg64 (.gpr 26#5) := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 27#5) = s1.readReg64 (.gpr 27#5) := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 28#5) = s1.readReg64 (.gpr 28#5) := h.2.2.2.2.2.2.2.2.2.1
theorem cs_fp {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 .fp = s1.readReg64 .fp := h.2.2.2.2.2.2.2.2.2.2.1

theorem calleeSavedVRegs_preserve {s1 s2 s0 : State}
    (h1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) (hcs : CalleeSavedPreserved s1 s2) :
    calleeSavedVRegs s2 = calleeSavedVRegs s0 :=
  hcs.2.2.2.2.2.2.2.2.2.2.2.trans h1

/-- Invariant spatial frame carried unchanged around `M2Collect`'s loop (`[sp + 0x310 .. +24)` split out). -/
abbrev m2LoopMem (A : RustAlloc) (s0 : State) (stk n : Nat)
    (buf p0 : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (Statics : SepProp) : SepProp :=
  argsBuf A (BitVec.ofNat 64 n) buf ps ∗
    argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x1b8 ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64) 24 ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1d0#64) 0x140 ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x328#64) 0x158 ∗
    mainSaved s0 ∗
    stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
    A.pool ∗
    Statics

theorem pointsTo64_zero_eq_pair32 (a : BitVec 64) :
    (a ↦₆₄ 0#64) = ((a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32)) :=
  (ProofLib.pointsTo32_pair a 0#32 0#32).symm

end M2Steps

/-- Offset `k` inside `main` relative to `entry` (`entry + BitVec.ofNat 64 k`, matching `mPc`). -/
@[simp, wp_norm] abbrev m2At (entry : BitVec 64) (k : Nat) : BitVec 64 := entry + BitVec.ofNat 64 k

namespace M2Entry

theorem memRegion_64_head_words (a : BitVec 64) :
    memRegion a 64 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w0) ∗ memRegion (a + 16#64) 48) := by
  conv => lhs; rw [show (64 : Nat) = 8 + (8 + 48) by rfl]
  rw [ProofLib.memRegion_split a 8 (8 + 48) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 48 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

end M2Entry

end CryptoVerification.SignalSession.Cli.MainHops
