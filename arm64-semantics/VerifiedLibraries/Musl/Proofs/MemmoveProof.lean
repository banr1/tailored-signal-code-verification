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
public import VerifiedLibraries.Musl.Proofs.MemmoveSym

/-!
# Verification of `memmove`

Proves `memmoveSpec` for `musl`'s `memmove` (`memmove_patchCalls_ok` and
`memmove_image_ok_of_memcpy`) by combining the symbolic execution in `MemmoveSym` with the
disjoint-range tail call to `memcpy`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64
open ProofLib

/-! ## Pure Overlap and Separation-Logic Split Lemmas -/

theorem moveBytes_eq_listMove (buf : List (BitVec 8)) (d o len : Nat) :
    moveBytes buf d o len = ProofLib.listMove buf d o len := rfl

theorem mm_fwd_safe_of_not_ule {base dst src : BitVec 64} {buf : List (BitVec 8)}
    {d o len : Nat}
    (hdst : dst = base + BitVec.ofNat 64 d) (hsrc : src = base + BitVec.ofNat 64 o)
    (_hd_le : d + len ≤ buf.length) (ho_le : o + len ≤ buf.length)
    (hbase_le : base.toNat + buf.length ≤ 2 ^ 64) (hbuf_lt : buf.length < 2 ^ 63)
    (hcmp : BitVec.ule src dst = false) :
    d ≤ o ∨ o + len ≤ d := by
  subst hdst hsrc
  simp only [BitVec.ule, decide_eq_false_iff_not] at hcmp
  bv_omega

theorem mm_bwd_safe_of_ule {base dst src : BitVec 64} {buf : List (BitVec 8)}
    {d o len : Nat}
    (hdst : dst = base + BitVec.ofNat 64 d) (hsrc : src = base + BitVec.ofNat 64 o)
    (hd_le : d + len ≤ buf.length) (ho_le : o + len ≤ buf.length)
    (hbase_le : base.toNat + buf.length ≤ 2 ^ 64) (hbuf_lt : buf.length < 2 ^ 63)
    (hcmp : BitVec.ule src dst = true) :
    o ≤ d ∨ d + len ≤ o := by
  subst hdst hsrc
  simp only [BitVec.ule, decide_eq_true_eq] at hcmp
  bv_omega

theorem mm_offset_eq_of_ptr_eq {base : BitVec 64} {buf : List (BitVec 8)} {d o len : Nat}
    (hd_le : d + len ≤ buf.length) (ho_le : o + len ≤ buf.length)
    (hbuf_lt : buf.length < 2 ^ 63)
    (heq : base + BitVec.ofNat 64 d = base + BitVec.ofNat 64 o) : d = o := by
  bv_omega

theorem disjoint_of_sub_ule {base dst src n : BitVec 64} {buf : List (BitVec 8)}
    {d o : Nat}
    (hdst : dst = base + BitVec.ofNat 64 d) (hsrc : src = base + BitVec.ofNat 64 o)
    (hd_le : d + n.toNat ≤ buf.length) (ho_le : o + n.toNat ≤ buf.length)
    (_hbase_le : base.toNat + buf.length ≤ 2 ^ 64) (hbuf_lt : buf.length < 2 ^ 63)
    (hule : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true) :
    d + n.toNat ≤ o ∨ o + n.toNat ≤ d := by
  subst hdst hsrc
  have hsh : -(n <<< (1 : Nat)) = 0#64 - (n + n) := by bv_bits
  rw [hsh] at hule
  simp only [BitVec.ule, decide_eq_true_eq] at hule
  bv_omega

theorem pointsToBytes_split_disjoint (base : BitVec 64) (buf : List (BitVec 8)) (d o len : Nat)
    (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length)
    (hdisj : d + len ≤ o ∨ o + len ≤ d) :
    ∃ Frame : SepProp,
      ((base ↦ₛ buf) ⊢
        memRegion (base + BitVec.ofNat 64 d) len ∗
        (((base + BitVec.ofNat 64 o) ↦ₛ (buf.drop o).take len) ∗ Frame)) ∧
      ((((base + BitVec.ofNat 64 d) ↦ₛ (buf.drop o).take len) ∗
        (((base + BitVec.ofNat 64 o) ↦ₛ (buf.drop o).take len) ∗ Frame)) =
       (base ↦ₛ moveBytes buf d o len)) := by
  have hframe_ex : ∃ Frame : SepProp,
      ((base ↦ₛ buf.take d) ∗
        ((base + BitVec.ofNat 64 (d + len)) ↦ₛ buf.drop (d + len))) =
      (((base + BitVec.ofNat 64 o) ↦ₛ (buf.drop o).take len) ∗ Frame) := by
    rcases hdisj with hdo | hod
    · have hsp := pointsToBytes_split3 (base + BitVec.ofNat 64 (d + len))
        (buf.drop (d + len)) (o - (d + len)) len (by rw [List.length_drop]; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hdo, List.drop_drop,
        Nat.add_sub_of_le hdo] at hsp
      exact ⟨_, by rw [hsp, sepConj_left_comm]⟩
    · have hsp := pointsToBytes_split3 base (buf.take d) o len
        (by rw [List.length_take_of_le (by omega)]; exact hod)
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)] at hsp
      exact ⟨_, by rw [hsp, sepConj_assoc]⟩
  obtain ⟨Frame, hFrame⟩ := hframe_ex
  refine ⟨Frame, ?_, ?_⟩
  · rw [pointsToBytes_split3 base buf d len hd, hFrame]
    have hent := pointsToBytes_entails_memRegion (base + BitVec.ofNat 64 d) ((buf.drop d).take len)
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)] at hent
    exact sepConj_mono hent (Entails.refl _)
  · rw [← hFrame, moveBytes_eq_listMove]
    exact pointsToBytes_listMove base buf d o len hd ho

/-! ## Pre/Post Extraction and Reconstruction for `memmoveSpec` -/

theorem memmove_pre_extract {dst src n base : BitVec 64} {buf : List (BitVec 8)} {d o : Nat}
    {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ memmoveSpec.pre (dst, src, n, base, buf, d, o) s0 ∗ R) :
    (s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = n ∧
      dst = base + BitVec.ofNat 64 d ∧
      src = base + BitVec.ofNat 64 o ∧
      (d + n.toNat ≤ buf.length ∧ o + n.toNat ≤ buf.length) ∧
      (base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63)) ∧
    (s0.mem ⊨ (base ↦ₛ buf) ∗ R) := by
  simp only [memmoveSpec, CType.InteriorPtr, sepConj_assoc, emp_sepConj, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hdst, hsrc, _, hd_le, ho_le, hbase_le, hbuf_lt⟩, hmem⟩ := hpre
  exact ⟨⟨hx0, hx1, hx2, hdst, hsrc, ⟨hd_le, ho_le⟩, ⟨hbase_le, hbuf_lt⟩⟩, hmem⟩

theorem memmove_post_of_moved {dst src n base : BitVec 64} {buf : List (BitVec 8)}
    {d o : Nat} {s0 sf : State} {R : SepProp}
    (hmem : sf.mem ⊨ (base ↦ₛ ProofLib.listMove buf d o n.toNat) ∗ R)
    (hx0 : sf.readReg64 .x0 = dst) :
    sf.mem ⊨ memmoveSpec.post (dst, src, n, base, buf, d, o) s0 sf ∗ R := by
  have hgoal : sf.mem ⊨ ⌜sf.readReg64 .x0 = dst⌝ ∗
      ((base ↦ₛ moveBytes buf d o n.toNat) ∗ R) := by
    rw [satisfies_pure_sepConj, moveBytes_eq_listMove]
    exact ⟨hx0, hmem⟩
  simpa [memmoveSpec, sepConj_assoc] using hgoal

theorem memmove_reaches_of_sepWP {prog : Program} {s0 s : State} {base dst : BitVec 64}
    {bs buf : List (BitVec 8)} {d o len : Nat} {R : SepProp} {Q : State → Prop}
    (hwp : SepWP prog (s0.readReg64 .lr) s (base ↦ₛ bs)
      (sepPost (MmExit s0 dst) (base ↦ₛ ProofLib.listMove buf d o len)))
    (hm : s.mem ⊨ (base ↦ₛ bs) ∗ R)
    (hloc : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      MmExit s0 dst sf → sf.mem ⊨ (base ↦ₛ ProofLib.listMove buf d o len) ∗ R → Q sf) :
    reaches_pc prog (s0.readReg64 .lr) s Q := by
  refine reaches_pc_mono (hwp.to_reaches_pc hm) ?_
  intro sf hpc hrun ⟨P_f, hmf, hex, hent⟩
  exact hloc sf hpc hrun hex (Satisfies.mono (sepConj_mono_left hent) hmf)

private theorem mm_tailcall_frame {dst src n base : BitVec 64} {buf : List (BitVec 8)} {d o : Nat}
    {s0 s_call : State} {R : SepProp}
    (hdst : dst = base + BitVec.ofNat 64 d) (hsrc : src = base + BitVec.ofNat 64 o)
    (hd_le : d + n.toNat ≤ buf.length) (ho_le : o + n.toNat ≤ buf.length)
    (hdisj : d + n.toNat ≤ o ∨ o + n.toNat ≤ d)
    (hmem0 : s0.mem ⊨ (base ↦ₛ buf) ∗ R) (hmem_c : s_call.mem = s0.mem)
    (hx0 : s_call.readReg64 .x0 = dst) (hx1 : s_call.readReg64 .x1 = src)
    (hx2 : s_call.readReg64 .x2 = n) :
    ∃ F : SepProp,
      (s_call.mem ⊨ memcpySpec.pre (dst, src, n, (buf.drop o).take n.toNat) s_call ∗ F) ∧
      ∀ sf : State,
        (sf.mem ⊨ memcpySpec.post (dst, src, n, (buf.drop o).take n.toNat) s_call sf ∗ F) →
        sf.mem ⊨ memmoveSpec.post (dst, src, n, base, buf, d, o) s0 sf ∗ R := by
  subst hdst hsrc
  obtain ⟨Frame, hent, hjoin⟩ := pointsToBytes_split_disjoint base buf d o n.toNat hd_le ho_le hdisj
  have hlen : ((buf.drop o).take n.toNat).length = n.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  refine ⟨Frame ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [memcpySpec, CType.ShrSlice8, CType.SliceLen, sepConj_assoc, satisfies_pure_sepConj]
    rw [hmem_c, hlen]
    exact ⟨⟨hx0, hx1, hx2, trivial, rfl⟩,
      Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hent) hmem0) (by ac_rfl)⟩
  · simp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    simp only [memmoveSpec, CType.InteriorPtr, sepConj_assoc, emp_sepConj, satisfies_pure_sepConj]
    refine ⟨hpost.1.2, ?_⟩
    rw [← hjoin]
    exact Satisfies.of_eq hpost.2 (by ac_rfl)

/-! ## Code Fetch Bundle (`MemmoveFetch`) from `patchCalls` -/

set_option linter.literalFetch false in
def MemmoveFetch (prog : Program) (a mc : BitVec 64) : Prop :=
  MemmoveCode prog a ∧
  prog.fetch (a + 0x68#64) =
    some (.b (mc - (a + 0x68#64)))

private theorem mm_hasWords_sub {prog : Program} {a : BitVec 64} {L M : List (BitVec 32)} (k : Nat)
    (h : prog.hasWords a L) (hk : k + M.length ≤ L.length) (hk' : k < L.length)
    (hM : ∀ i (hi : i < M.length), L[k + i]? = some M[i]) :
    prog.hasWords (a + BitVec.ofNat 64 (4 * k)) M := by
  unfold Program.hasWords Program.hasWordsOff at *
  obtain ⟨hb, hr, h1, h2⟩ := h
  have hoff : (a + BitVec.ofNat 64 (4 * k) - prog.base).toNat = (a - prog.base).toNat + 4 * k := by
    have e : a + BitVec.ofNat 64 (4 * k) - prog.base = (a - prog.base) + BitVec.ofNat 64 (4 * k) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hoff]
  refine ⟨by omega, fun i hi => ?_, ?_, ?_⟩
  · have hki : k + i < L.length := by omega
    rw [show (a - prog.base).toNat + 4 * k + 4 * i = (a - prog.base).toNat + 4 * (k + i) by omega,
      hr (k + i) hki]
    have h' := hM i hi
    rw [List.getElem?_eq_getElem hki] at h'
    simpa using h'
  all_goals
    rw [List.all_eq_true] at *
    intro x hx
    by_cases c : (a - prog.base).toNat + 4 * k ≤ x.2 ∧
        x.2 < (a - prog.base).toNat + 4 * k + 4 * M.length
    · have c' : (a - prog.base).toNat ≤ x.2 ∧ x.2 < (a - prog.base).toNat + 4 * L.length := by
        omega
      first
      | (have := h1 x hx
         simp only [c'.1, c'.2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at this
         simp [this])
      | (have := h2 x hx
         simp only [c'.1, c'.2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at this
         simp [this])
    · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      left; omega

private theorem mm_patchCalls_getElem? {calls : List (Nat × String)}
    {words : List (BitVec 32)} {a : BitVec 64} {resolve : String → BitVec 64} {j : Nat}
    (hj : calls.find? (·.1 == 4 * j) = none) :
    (Obj.patchCalls calls words a resolve)[j]? = words[j]? := by
  simp only [Obj.patchCalls, List.getElem?_mapIdx, hj]
  cases words[j]? <;> rfl

private theorem memmoveWordsA_spec : ∀ i < 26, memmoveLibcaWords[i]? = memmoveWordsA[i]? := by
  decide +kernel

private theorem memmoveWordsB_spec : ∀ i < 47, memmoveLibcaWords[27 + i]? = memmoveWordsB[i]? := by
  decide +kernel

private theorem memmoveCalls_find_none :
    ∀ j < 74, j ≠ 26 → memmoveLibcaCalls.find? (·.1 == 4 * j) = none := by
  decide +kernel

private theorem memmoveCode_of_hasWords {prog : Program} {a : BitVec 64} {L : List (BitVec 32)}
    (h : prog.hasWords a L) (hlen : L.length = 74)
    (hL : ∀ j < 74, j ≠ 26 → L[j]? = memmoveLibcaWords[j]?) : MemmoveCode prog a := by
  have hA : memmoveWordsA.length = 26 := rfl
  have hB : memmoveWordsB.length = 47 := rfl
  refine ⟨?_, ?_⟩
  · show prog.hasWords a memmoveWordsA
    have h0 := mm_hasWords_sub (M := memmoveWordsA) 0 h (by omega) (by omega) fun i hi => by
      rw [Nat.zero_add, hL i (by omega) (by omega), memmoveWordsA_spec i (by omega),
        List.getElem?_eq_getElem hi]
    simpa using h0
  · show prog.hasWords (a + 0x6c#64) memmoveWordsB
    have h27 := mm_hasWords_sub (M := memmoveWordsB) 27 h (by omega) (by omega) fun i hi => by
      rw [hL _ (by omega) (by omega), memmoveWordsB_spec i (by omega),
        List.getElem?_eq_getElem hi]
    simpa using h27

theorem memmoveFetch_of_patchCalls {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0x68#64) (resolve "memcpy"))
    (hwords : prog.hasWords a (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords a resolve)) :
    MemmoveFetch prog a (resolve "memcpy") :=
  ⟨memmoveCode_of_hasWords hwords (by rw [Obj.patchCalls, List.length_mapIdx]; rfl)
      fun j hj hj26 => mm_patchCalls_getElem? (memmoveCalls_find_none j hj hj26),
    Obj.fetch_patchCalls_b (r := (104, "memcpy")) hwords rfl rfl (by decide +kernel)
      (by decide +kernel) hrange⟩

/-! ## Top-Level Symbolic Execution Dispatch (`memmove_core_reaches`) -/

theorem memmove_core_reaches (prog : Program) (a mc : BitVec 64)
    (hf : MemmoveFetch prog a mc)
    {dst src n base : BitVec 64} {buf : List (BitVec 8)} {d o : Nat}
    (s0 : State) (R : SepProp) (Post : State → Prop)
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : s0.readReg64 .x2 = n)
    (hdst : dst = base + BitVec.ofNat 64 d) (hsrc : src = base + BitVec.ofNat 64 o)
    (hd_le : d + n.toNat ≤ buf.length) (ho_le : o + n.toNat ≤ buf.length)
    (hbase_le : base.toNat + buf.length ≤ 2 ^ 64) (hbuf_lt : buf.length < 2 ^ 63)
    (hmem0 : s0.mem ⊨ (base ↦ₛ buf) ∗ R)
    (h_tailcall : (d + n.toNat ≤ o ∨ o + n.toNat ≤ d) →
      ∀ s_call : State, s_call.pc = mc → s_call.status = .Running →
        s_call.readReg64 .x0 = dst → s_call.readReg64 .x1 = src → s_call.readReg64 .x2 = n →
        s_call.mem = s0.mem → s_call.sp = s0.sp → s_call.symtab = s0.symtab →
        s_call.readReg64 .lr = s0.readReg64 .lr → CalleeSavedPreserved s0 s_call →
        reaches_pc prog (s0.readReg64 .lr) s_call Post)
    (h_local : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      MmExit s0 dst sf → sf.mem ⊨ (base ↦ₛ ProofLib.listMove buf d o n.toNat) ∗ R → Post sf) :
    reaches_pc prog (s0.readReg64 .lr) s0 Post := by
  obtain ⟨hc, hf_b⟩ := hf
  have ⟨hcA, _⟩ := hc
  have h_disj_imp : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true →
      d + n.toNat ≤ o ∨ o + n.toNat ≤ d :=
    disjoint_of_sub_ule hdst hsrc hd_le ho_le hbase_le hbuf_lt
  have hx2n : n = BitVec.ofNat 64 n.toNat := by simp
  have h_ret : (dst == src) = true → ∀ s : State, s.pc = a + 0x120#64 → s.status = .Running →
      s.mem = s0.mem → s.readReg64 .x7 = dst → s.sp = s0.sp →
      s.readReg64 .lr = s0.readReg64 .lr → CalleeSavedPreserved s0 s →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
    intro heq s hpc' hrun' hmem' hx7' hsp' hlr' hcs'
    subst hdst hsrc
    obtain rfl := mm_offset_eq_of_ptr_eq hd_le ho_le hbuf_lt (beq_iff_eq.mp heq)
    refine memmove_reaches_of_sepWP
      (memmove_ret prog a hc s0 s base buf _ _ (mm_listMove_self hd_le).symm
        hpc' hrun' hx7' hsp' hlr' hcs') ?_ h_local
    rwa [hmem']
  have h_fwd : BitVec.ule src dst = false → ∀ s : State, s.pc = a + 0x38#64 →
      s.status = .Running → s.mem = s0.mem →
      s.readReg64 .x7 = dst → s.readReg64 .x0 = dst → s.readReg64 .x4 = src →
      s.readReg64 .x2 = n → s.readReg64 .x3 = n → s.readReg64 .x5 = src - n →
      s.sp = s0.sp → s.readReg64 .lr = s0.readReg64 .lr → CalleeSavedPreserved s0 s →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
    intro hcmp s hpc' hrun' hmem' hx7' hx0' hx4' hx2' hx3' hx5' hsp' hlr' hcs'
    subst hdst hsrc
    refine memmove_reaches_of_sepWP
      (memmove_fwd_entry (hc := hc) (hd := hd_le) (ho := ho_le) (hbuf := hbuf_lt)
        (hfwd := mm_fwd_safe_of_not_ule rfl rfl hd_le ho_le hbase_le hbuf_lt hcmp)
        (hrun := hrun') (hx7 := hx7') (hsp := hsp') (hlr := hlr') (hcs := hcs')
        (hpc := hpc') (hx0 := hx0') (hx4 := hx4') (hx2 := hx2'.trans hx2n)
        (hx3 := hx3'.trans hx2n)
        (hx5 := hx5'.trans (congrArg (base + BitVec.ofNat 64 o - ·) hx2n))) ?_ h_local
    rwa [mm_mmSet_empty, hmem']
  have h_bwd : BitVec.ule src dst = true → ∀ s : State, s.pc = a + 0xbc#64 →
      s.status = .Running → s.mem = s0.mem →
      s.readReg64 .x7 = dst → s.readReg64 .x4 = src → s.readReg64 .x3 = n →
      s.sp = s0.sp → s.readReg64 .lr = s0.readReg64 .lr → CalleeSavedPreserved s0 s →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
    intro hcmp s hpc' hrun' hmem' hx7' hx4' hx3' hsp' hlr' hcs'
    subst hdst hsrc
    refine memmove_reaches_of_sepWP
      (memmove_bwd_entry (hc := hc) (hd := hd_le) (ho := ho_le) (hbuf := hbuf_lt)
        (hbwd := mm_bwd_safe_of_ule rfl rfl hd_le ho_le hbase_le hbuf_lt hcmp)
        (hrun := hrun') (hx7 := hx7') (hx4 := hx4') (hsp := hsp') (hlr := hlr') (hcs := hcs')
        (hpc := hpc') (hx3 := hx3'.trans hx2n)) ?_ h_local
    rwa [mm_mmSet_empty, hmem']
  clear hdst hsrc h_local hmem0 hx2n
  by_cases heq : (dst == src) = true
  · iterate 5 arm64_step
  have heq_f : (dst == src) = false := Bool.eq_false_iff.mpr heq
  by_cases hule : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true
  ·
    have hdisj := h_disj_imp hule
    iterate 11 arm64_step
    apply h_tailcall hdisj _
    · simp [arm64_norm]; bv_omega
    · simp [arm64_norm, hrun]
    · simp [arm64_norm, hx0]
    · simp [arm64_norm, hx1]
    · simp [arm64_norm, hx2]
    · rfl
    · simp [arm64_norm]
    · rfl
    · simp [arm64_norm]
    · simp (config := { decide := true }) only [arm64_norm]
  have hule_f : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = false :=
    Bool.eq_false_iff.mpr hule
  by_cases hcs : BitVec.ule src dst = true
  · iterate 14 arm64_step
  · have hcs_f : BitVec.ule src dst = false := Bool.eq_false_iff.mpr hcs
    iterate 14 arm64_step

/-! ## `subroutine_ok` Proofs (`memmove_fetch_ok`, `memmove_patchCalls_ok`) -/

theorem memmove_fetch_ok (prog : Program) (a mc : BitVec 64)
    (hf : MemmoveFetch prog a mc)
    (hmemcpy : subroutine_ok prog mc memcpySpec) :
    subroutine_ok prog a memmoveSpec := by
  apply subroutine_ok_outcome_intro
  intro ⟨dst, src, n, base, buf, d, o⟩ R s0 hpc hrun hpre hal
  refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
  obtain ⟨⟨hx0, hx1, hx2, hdst, hsrc, ⟨hd_le, ho_le⟩, ⟨hbase_le, hbuf_lt⟩⟩,
    hmem0⟩ := memmove_pre_extract hpre
  refine memmove_core_reaches prog a mc hf s0 R
    (SubroutinePost memmoveSpec (dst, src, n, base, buf, d, o) R s0)
    hpc hrun hx0 hx1 hx2 hdst hsrc hd_le ho_le hbase_le hbuf_lt hmem0 ?_ ?_
  · intro hdisj s_call hpc_c hrun_c hx0_c hx1_c hx2_c hmem_c hsp_c _ hlr_c hcs_c
    obtain ⟨F, hpre_c, hjoin⟩ :=
      mm_tailcall_frame hdst hsrc hd_le ho_le hdisj hmem0 hmem_c hx0_c hx1_c hx2_c
    exact reaches_pc_tailcall_subroutine hmemcpy _ (dst, src, n, base, buf, d, o)
      hpc_c hrun_c hlr_c hsp_c hcs_c hpre_c (fun sf _ _ _ _ h => hjoin sf h) hal
  · intro sf _hpc_f _hrun_f ⟨hx0_f, hsp_f, hcs_f⟩ hmem_f
    exact ⟨memmove_post_of_moved (src := src) (s0 := s0) hmem_f hx0_f, hsp_f, hcs_f⟩

theorem memmove_patchCalls_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (a + 0x68#64) (resolve "memcpy"))
    (hwords : prog.hasWords a (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords a resolve))
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpySpec) :
    subroutine_ok prog a memmoveSpec :=
  memmove_fetch_ok prog a (resolve "memcpy")
    (memmoveFetch_of_patchCalls hrange hwords) hmemcpy

/-! ## `VerifiedLibraries.muslStringLib` Placement Corollary -/

theorem memmove_image_ok_of_memcpy (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (hmemcpy : subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcpy") memcpySpec) :
    subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memmove") memmoveSpec := by
  have ⟨hw, hrel⟩ := muslStringProg_hasWords_of_checkSegment (hooks := hooks) (name := "memmove")
    (ws := memmoveLibcaWords) (R := memmoveLibcaRelocs) hP rfl (by decide +kernel)
  have hres : VerifiedLibraries.muslStringLib.text.resolve pl "memcpy" =
      (muslStringProg pl hooks).fnAddr "memcpy" :=
    muslStringLib_resolve_sym (hooks := hooks) (name := "memcpy") rfl
  have hpatch : Obj.patchRelocs memmoveLibcaRelocs memmoveLibcaWords
      ((muslStringProg pl hooks).fnAddr "memmove")
      (VerifiedLibraries.muslStringLib.text.resolve pl) =
    Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords
      ((muslStringProg pl hooks).fnAddr "memmove")
      (VerifiedLibraries.muslStringLib.text.resolve pl) := by
    simp [Obj.patchRelocs, Obj.patchCalls, Obj.patchRelocWord, Obj.addSignedAddr,
      memmoveLibcaRelocs, memmoveLibcaCalls, memmoveLibcaWords]
  rw [hpatch] at hw
  have hrange : Obj.BranchInRange
      ((muslStringProg pl hooks).fnAddr "memmove" + 0x68#64)
      (VerifiedLibraries.muslStringLib.text.resolve pl "memcpy") := by
    have hr := hrel { off := 104, kind := .jump26, sym := "memcpy", addend := 0 }
      (by simp [memmoveLibcaRelocs])
    simpa [Obj.CodeRelocInRange, Obj.addSignedAddr] using hr
  exact memmove_patchCalls_ok (muslStringProg pl hooks)
    ((muslStringProg pl hooks).fnAddr "memmove")
    (VerifiedLibraries.muslStringLib.text.resolve pl)
    hrange hw (by rwa [hres])

end VerifiedLibraries.Musl
