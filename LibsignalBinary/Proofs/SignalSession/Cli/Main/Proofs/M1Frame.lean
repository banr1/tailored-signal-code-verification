/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout

/-!
# Frame, `argvAt`, and `argsBuf` Helpers for `main` Hop M1

Pure input/capacity arithmetic, stack-frame opening/closing lemmas, and `argvAt` / `argvAtP` /
`argsBuf` loop-accumulation helpers for `main`'s Hop M1 (`M+0x00 → M+0xc0`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. `CliInputsOk`, `PrintableAsciiArg`, and `ArgvFitsInitialStack` arithmetic facts -/

private theorem argvFits_sum_ge (argv : List String) :
    9 * argv.length ≤ (argv.map fun a => a.length + 1 + 8).sum := by
  induction argv with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem argvFits_length_le {argv : List String} (h : ArgvFitsInitialStack argv) :
    argv.length ≤ 1820 := by
  unfold ArgvFitsInitialStack at h
  have hge := argvFits_sum_ge argv
  omega

theorem argOk_no_nul {a : String} (ha : PrintableAsciiArg a) :
    ∀ b ∈ bytesOfString a, b ≠ 0#8 := by
  intro b hb
  unfold bytesOfString at hb
  rcases List.mem_map.mp hb with ⟨c, hc_mem, rfl⟩
  have ⟨hpos, hlt⟩ := ha.2 c hc_mem
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.toNat < 256)] at ht
  change c.toNat = 0 at ht
  omega

theorem argv_no_nul_at {argv : List String} (hok : ∀ a ∈ argv, PrintableAsciiArg a)
    {ps_done ps_rest : List (BitVec 64 × List (BitVec 8))}
    {pk : BitVec 64} {sk : List (BitVec 8)}
    (hps : (ps_done ++ (pk, sk) :: ps_rest).map (·.2) = argv.map bytesOfString) :
    ∀ b ∈ sk, b ≠ 0#8 := by
  have hmem : sk ∈ (ps_done ++ (pk, sk) :: ps_rest).map (·.2) := by simp
  rw [hps] at hmem
  rcases List.mem_map.mp hmem with ⟨a, ha_mem, rfl⟩
  exact argOk_no_nul (hok a ha_mem)

/-! ## 2. BitVec / capacity arithmetic for `M+0x20 .. M+0x9c` -/

theorem argc_sxtw_eq {n : Nat} (hn : n ≤ 1820) :
    (BitVec.ofNat 32 (n + 1)).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h32 : n + 1 < 2 ^ 32 := by omega
  have hmsb : (BitVec.ofNat 32 (n + 1)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
    omega
  rw [BitVec.toNat_signExtend, hmsb]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64), Nat.add_zero]

theorem ofNat_succ_beq_zero {n : Nat} (hn : n ≤ 1820) :
    (BitVec.ofNat 64 (n + 1) == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)] at ht
  change n + 1 = 0 at ht
  omega

theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem ofNat_lsr_60 {n : Nat} (hn : n ≤ 1820) :
    BitVec.ofNat 64 n >>> 60 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (by omega : n < 2 ^ 60)

theorem ofNat_shl_4 {n : Nat} (hn : n ≤ 1820) :
    BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 16 * n < 2 ^ 64),
    Nat.shiftLeft_eq]
  have hmul : n * 2 ^ 4 = 16 * n := by omega
  rw [hmul, Nat.mod_eq_of_lt (by omega : 16 * n < 2 ^ 64)]

theorem ofNat_shl_3 {k : Nat} (hk : k ≤ 1820) :
    BitVec.ofNat 64 k <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64),
    Nat.shiftLeft_eq]
  have hmul : k * 2 ^ 3 = 8 * k := by omega
  rw [hmul, Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64)]

theorem ofNat_16_ule_max {n : Nat} (hn : n ≤ 1820) :
    (0x7ffffffffffffff8#64).ult (BitVec.ofNat 64 (16 * n)) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  have h1 : (0x7ffffffffffffff8#64).toNat = 9223372036854775800 := by decide
  have h2 : (BitVec.ofNat 64 (16 * n)).toNat = 16 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * n < 2 ^ 64)]
  rw [h1, h2]
  omega

theorem ofNat_16_beq_zero {n : Nat} (h0 : 0 < n) (hn : n ≤ 1820) :
    (BitVec.ofNat 64 (16 * n) == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * n < 2 ^ 64)] at ht
  change 16 * n = 0 at ht
  omega

theorem ofNat_16_toNat {n : Nat} (hn : n ≤ 1820) :
    (BitVec.ofNat 64 (16 * n)).toNat = 16 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * n < 2 ^ 64)]

theorem layoutOk_argsBuf {n : Nat} (h0 : 0 < n) (hn : n ≤ 1820) :
    LayoutOk (16 * n) 8 :=
  ⟨by omega, ⟨3, rfl⟩, by omega⟩

theorem argc_cmp_two {n : Nat} (h0 : 0 < n) (hn : n ≤ 1820) :
    (BitVec.ofNat 32 (n + 1)).ult 2#32 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 32)]
  change ¬ (n + 1 < 2)
  omega

theorem loop_cmp_ne_true {n k : Nat} (hlt : k + 1 < n) (hn : n ≤ 1820) :
    (BitVec.ofNat 64 n == BitVec.ofNat 64 (k + 1)) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)] at ht
  omega

theorem fsp_spAligned {s0 s : State} (hsp0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize) :
    s.spAligned = true := by
  simp only [State.spAligned, beq_iff_eq] at hsp0 ⊢
  rw [hsp]
  change (s0.sp - 1248#64) &&& 15#64 = 0#64
  apply BitVec.eq_of_toNat_eq
  have h15 : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  replace hsp0 := congrArg BitVec.toNat hsp0
  rw [h15] at hsp0
  change s0.sp.toNat % 16 = 0 at hsp0
  rw [h15, BitVec.toNat_sub, BitVec.toNat_ofNat]
  change ((2 ^ 64 - 1248 % 2 ^ 64 + s0.sp.toNat) % 2 ^ 64) % 16 = 0
  omega

/-! ## 3. Stack & `mainFrame` opening / closing helpers -/

theorem cells_12_eq (b : BitVec 64) :
    cells b 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        (b ↦₆₄ v0) ∗ ((b + 0x08#64) ↦₆₄ v1) ∗
        ((b + 0x10#64) ↦₆₄ v2) ∗ ((b + 0x18#64) ↦₆₄ v3) ∗
        ((b + 0x20#64) ↦₆₄ v4) ∗ ((b + 0x28#64) ↦₆₄ v5) ∗
        ((b + 0x30#64) ↦₆₄ v6) ∗ ((b + 0x38#64) ↦₆₄ v7) ∗
        ((b + 0x40#64) ↦₆₄ v8) ∗ ((b + 0x48#64) ↦₆₄ v9) ∗
        ((b + 0x50#64) ↦₆₄ v10) ∗ ((b + 0x58#64) ↦₆₄ v11)) := by
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem stackAt_main_open (sp0 : BitVec 64) {stk : Nat}
    (hstk : mainFrameSize ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    stackAt sp0 stk =
      stackAt (sp0 - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        (∃∗ v_sp0 : BitVec 64, (sp0 - BitVec.ofNat 64 mainFrameSize) ↦₆₄ v_sp0) ∗
        memRegion ((sp0 - BitVec.ofNat 64 mainFrameSize) + 8#64) 0x478 ∗
        cells (sp0 - 0x60#64) 12 := by
  have hstk_ge96 : 0x60 ≤ stk := by unfold mainFrameSize at hstk; omega
  have h1 := ProofLib.stackAt_split_cells sp0 (stk - 0x60) 12 (by omega)
  have heq1 : (stk - 0x60) + 8 * 12 = stk := by omega
  rw [heq1] at h1
  have h3 : stackAt (sp0 - 0x60#64) (stk - 0x60) =
      stackAt (sp0 - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        memRegion (sp0 - BitVec.ofNat 64 mainFrameSize) 0x480 := by
    unfold stackAt
    have hlen : stk - 0x60 = (stk - mainFrameSize) + 0x480 := by
      unfold mainFrameSize at hstk ⊢; omega
    have hbase : (sp0 - 0x60#64) - BitVec.ofNat 64 (stk - 0x60) =
        (sp0 - BitVec.ofNat 64 mainFrameSize) - BitVec.ofNat 64 (stk - mainFrameSize) := by
      have : stk - 0x60 = (stk - mainFrameSize) + 0x480 := hlen
      unfold mainFrameSize; rw [this, BitVec.ofNat_add]; bv_omega
    have hmid : (sp0 - BitVec.ofNat 64 mainFrameSize) - BitVec.ofNat 64 (stk - mainFrameSize) +
        BitVec.ofNat 64 (stk - mainFrameSize) = sp0 - BitVec.ofNat 64 mainFrameSize := by
      bv_omega
    rw [hbase, hlen,
      ProofLib.memRegion_split
        ((sp0 - BitVec.ofNat 64 mainFrameSize) - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize) 0x480 (by unfold mainFrameSize at hstk; omega),
      hmid]
  have h8 : memRegion (sp0 - BitVec.ofNat 64 mainFrameSize) 0x480 =
      (∃∗ v_sp0 : BitVec 64, (sp0 - BitVec.ofNat 64 mainFrameSize) ↦₆₄ v_sp0) ∗
        memRegion ((sp0 - BitVec.ofNat 64 mainFrameSize) + 8#64) 0x478 := by
    rw [show (0x480 : Nat) = 8 + 0x478 by rfl,
      ProofLib.memRegion_split (sp0 - BitVec.ofNat 64 mainFrameSize) 8 0x478 (by decide),
      ProofLib.memRegion_eight]
  rw [h1, h3, h8]
  ac_rfl

theorem zero_store_entails_memRegion_480 (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 0x478 ⊢ memRegion fsp 0x480 := by
  rw [show (0x480 : Nat) = 8 + 0x478 by rfl,
    ProofLib.memRegion_split fsp 8 0x478 (by decide),
    ProofLib.memRegion_eight]
  exact sepConj_mono_left (Entails.sepExists_intro 0#64)

theorem locals_nil_eq (fsp : BitVec 64) :
    locals fsp [] = memRegion fsp 0x480 := by
  simp [locals, localsFrom]

theorem subStack_split_extHook (fsp : BitVec 64) {stk hookStack resStack : Nat}
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63) :
    stackAt fsp (stk - mainFrameSize) =
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        ((stk - mainFrameSize) - extHookStack) ∗
        stackAt fsp extHookStack := by
  have hle : extHookStack ≤ stk - mainFrameSize := by omega
  have h := ProofLib.stackAt_split_bottom fsp extHookStack
    ((stk - mainFrameSize) - extHookStack) (by omega)
  have heq : extHookStack + ((stk - mainFrameSize) - extHookStack) = stk - mainFrameSize := by
    omega
  simpa only [heq] using h

theorem subStack_split_hook (fsp : BitVec 64) {stk hookStack resStack : Nat}
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63) :
    stackAt fsp (stk - mainFrameSize) =
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        ((stk - mainFrameSize) - hookStack) ∗
        stackAt fsp hookStack := by
  have hle : hookStack ≤ stk - mainFrameSize := by omega
  have h := ProofLib.stackAt_split_bottom fsp hookStack
    ((stk - mainFrameSize) - hookStack) (by omega)
  have heq : hookStack + ((stk - mainFrameSize) - hookStack) = stk - mainFrameSize := by
    omega
  simpa only [heq] using h

/-! ## 4. `argvAt` ↔ `argvAtP` and `argsBuf` loop accumulation helpers -/

theorem argvAt_entails_argvAtP (a : BitVec 64) (ss : List (List (BitVec 8))) :
    argvAt a ss ⊢
      ∃∗ ps : List (BitVec 64 × List (BitVec 8)), ⌜ps.map (·.2) = ss⌝ ∗ argvAtP a ps := by
  induction ss generalizing a with
  | nil =>
    exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _))
  | cons s ss ih =>
    simp only [argvAt]
    apply Entails.sepExists_elim
    intro p
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (ih (a + 8#64)))) ?_
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro ps
    refine Entails.trans (Entails.of_eq (by ac_rfl)) ?_
    apply Entails.pure_left
    rintro rfl
    exact Entails.sepExists_right ((p, s) :: ps)
      (Entails.pure_right rfl (Entails.of_eq (by simp only [argvAtP]; ac_rfl)))

def argvAtPPrefix : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp
  | _, [] => emp
  | a, (p, s) :: ps => (a ↦₆₄ p) ∗ cStrAt p s ∗ argvAtPPrefix (a + 8#64) ps

theorem argvAtP_append (a : BitVec 64) (xs ys : List (BitVec 64 × List (BitVec 8))) :
    argvAtP a (xs ++ ys) =
      argvAtPPrefix a xs ∗ argvAtP (a + BitVec.ofNat 64 (8 * xs.length)) ys := by
  induction xs generalizing a with
  | nil =>
    simp only [List.nil_append, argvAtPPrefix, List.length_nil, Nat.mul_zero,
      BitVec.add_zero, emp_sepConj]
  | cons x xs ih =>
    rcases x with ⟨p, s⟩
    simp only [List.cons_append, argvAtP, argvAtPPrefix, List.length_cons, ih (a + 8#64)]
    have haddr : a + 8#64 + BitVec.ofNat 64 (8 * xs.length) =
        a + BitVec.ofNat 64 (8 * (xs.length + 1)) := by
      have : 8 * (xs.length + 1) = 8 + 8 * xs.length := by omega
      rw [this, BitVec.ofNat_add]
      bv_omega
    rw [haddr]
    ac_rfl

def argsBufPartial (A : RustAlloc) (n : Nat) (buf : BitVec 64)
    (ps_done : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  A.live buf (16 * n) 8 ∗
    arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps_done ∗
    memRegion (buf + BitVec.ofNat 64 (16 * ps_done.length)) (16 * (n - ps_done.length))

theorem argsBufPartial_zero (A : RustAlloc) (n : Nat) (buf : BitVec 64) :
    A.live buf (16 * n) 8 ∗ memRegion buf (16 * n) = argsBufPartial A n buf [] := by
  simp only [argsBufPartial, arrayAt, List.length_nil, Nat.mul_zero, Nat.sub_zero,
    BitVec.add_zero, emp_sepConj]

theorem arrayAt_snoc {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (xs : List α) (x : α) :
    arrayAt elem stride base (xs ++ [x]) =
      arrayAt elem stride base xs ∗ elem x (base + BitVec.ofNat 64 (stride * xs.length)) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.nil_append, arrayAt, List.length_nil, Nat.mul_zero,
      BitVec.add_zero, emp_sepConj, sepConj_emp]
  | cons hd tl ih =>
    simp only [List.cons_append, arrayAt, List.length_cons, ih (base + BitVec.ofNat 64 stride)]
    have haddr : base + BitVec.ofNat 64 stride + BitVec.ofNat 64 (stride * tl.length) =
        base + BitVec.ofNat 64 (stride * (tl.length + 1)) := by
      rw [Nat.mul_succ stride tl.length, Nat.add_comm (stride * tl.length) stride, BitVec.ofNat_add]
      bv_omega
    rw [haddr]
    ac_rfl

theorem argsBufPartial_open_slot (A : RustAlloc) {n : Nat} (buf : BitVec 64)
    (ps_done : List (BitVec 64 × List (BitVec 8)))
    (hlt : ps_done.length < n) (hn : n ≤ 1820) :
    argsBufPartial A n buf ps_done =
      A.live buf (16 * n) 8 ∗
        arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps_done ∗
        (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
          ((buf + BitVec.ofNat 64 (16 * ps_done.length)) ↦₆₄ w0) ∗
          ((buf + BitVec.ofNat 64 (16 * ps_done.length) + 8#64) ↦₆₄ w1)) ∗
        memRegion (buf + BitVec.ofNat 64 (16 * (ps_done.length + 1)))
          (16 * (n - (ps_done.length + 1))) := by
  unfold argsBufPartial
  set base := buf + BitVec.ofNat 64 (16 * ps_done.length)
  have hrem : 16 * (n - ps_done.length) = 16 + 16 * (n - (ps_done.length + 1)) := by omega
  have hfit : 16 + 16 * (n - (ps_done.length + 1)) ≤ 2 ^ 64 := by omega
  have h16 : memRegion base 16 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1)) := by
    rw [show (16 : Nat) = 8 + 8 by rfl,
      ProofLib.memRegion_split base 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  have haddr : base + 16#64 = buf + BitVec.ofNat 64 (16 * (ps_done.length + 1)) := by
    have : 16 * (ps_done.length + 1) = 16 * ps_done.length + 16 := by omega
    simp only [base, this, BitVec.ofNat_add]
    bv_omega
  rw [hrem, ProofLib.memRegion_split base 16 (16 * (n - (ps_done.length + 1))) hfit, h16, haddr]

theorem argsBufPartial_close_slot (A : RustAlloc) (n : Nat) (buf : BitVec 64)
    (ps_done : List (BitVec 64 × List (BitVec 8))) (pk : BitVec 64) (sk : List (BitVec 8)) :
    A.live buf (16 * n) 8 ∗
      arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps_done ∗
      sliceRefAt (buf + BitVec.ofNat 64 (16 * ps_done.length)) pk sk.length ∗
      memRegion (buf + BitVec.ofNat 64 (16 * (ps_done.length + 1)))
        (16 * (n - (ps_done.length + 1))) =
      argsBufPartial A n buf (ps_done ++ [(pk, sk)]) := by
  unfold argsBufPartial
  rw [arrayAt_snoc (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps_done (pk, sk),
    List.length_append, List.length_singleton]
  ac_rfl

theorem argsBufPartial_finish (A : RustAlloc) {n : Nat} {buf : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    (h0 : 0 < n) (hn : n ≤ 1820) (hbuf : buf ≠ 0#64) (hlen : ps.length = n) :
    argsBufPartial A n buf ps ⊢ argsBuf A (BitVec.ofNat 64 n) buf ps := by
  unfold argsBufPartial argsBuf vecBuf
  have hn64 : n < 2 ^ 64 := by omega
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have hne0 : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [htoNat] at ht
    change n = 0 at ht
    omega
  have hmul : n * 16 = 16 * n := by omega
  simp only [htoNat, hlen, hne0, ↓reduceIte, hmul, Nat.sub_self, Nat.zero_mul, Nat.mul_zero]
  exact Entails.pure_right ⟨Nat.le_refl n, by omega, hbuf⟩ (Entails.refl _)

end CryptoVerification.SignalSession.Cli.MainHops
