/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Proofs.RawVecGrow
public import VerifiedLibraries.RustStd.Proofs.StdinProbeRead
public import ProofLib.Process.OracleEq

/-!
# Stdin `read_to_end` Capacity Sequences

Preservation of `oracle` and `symtab` across hook-free `Syscall.standard` steps
(`stdin_sepWP_carry_oracle_symtab`), pure lemmas over `rteCap`, `rteCaps`, `rteFinalCap`,
`allocSeqPool`, and `AllocSeqFits`, and `rustSmallProbeReadStdin_ok'` with `do_reserve_and_handle`
discharged.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd.Io

open Arm64 Arm64.Obj Arm64.Process ProofLib VerifiedLibraries.Musl
  ProofLib.StdStartup VerifiedLibraries.RustStd

/-! ## `oracle` and `symtab` preservation -/

section OracleSymtab

/-- Supply `sf.oracle = s0.oracle` and `sf.symtab = s0.symtab` at the postcondition state `sf`
    of any `SepWP` proof on a hook-free `Syscall.standard` program `P`. -/
theorem stdin_sepWP_carry_oracle_symtab {P : Program} (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none) {target_pc : BitVec 64} {s0 : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP P target_pc s0 Pre
      (fun sf P_f => sf.oracle = s0.oracle → sf.symtab = s0.symtab → post sf P_f) oom) :
    SepWP P target_pc s0 Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sf, hsteps, hout⟩ := SepWP.to_reaches_pc h hm hL
  refine ⟨sf, hsteps, hout.imp ?_ id⟩
  rintro ⟨hpc, hrun, P_f, hmf, hp⟩
  exact ⟨hpc, hrun, P_f, hmf,
    hp (Steps.oracle_eq_of_standard hsvc hext hsteps) hsteps.symtab_eq⟩

end OracleSymtab

/-! ## Capacity-sequence lemmas -/

private theorem getLast?_snoc {α : Type} : ∀ (xs : List α) (a : α),
    (xs ++ [a]).getLast? = some a
  | [], a => rfl
  | b :: bs, a => by
    cases bs with
    | nil => rfl
    | cons c cs => exact getLast?_snoc (c :: cs) a

theorem stdin_take_append_drop_take {α : Type} :
    ∀ (xs : List α) (a b : Nat), xs.take a ++ (xs.drop a).take b = xs.take (a + b)
  | [], _, _ => by simp
  | _ :: _, 0, b => by simp
  | x :: xs, a + 1, b => by
    rw [Nat.add_right_comm]
    simp [List.take_succ_cons, List.drop_succ_cons, stdin_take_append_drop_take xs a b]

theorem rteCap_zero (r : Nat) : rteCap r 0 = max 8 (min 32 r) := rfl

theorem rteCap_succ (r i : Nat) : rteCap r (i + 1) = max (2 * rteCap r i) (rteCap r i + 32) := rfl

theorem rteCap_ge_linear (r : Nat) : ∀ i, 8 + 32 * i ≤ rteCap r i
  | 0 => by rw [rteCap_zero]; omega
  | i + 1 => by
    have ih := rteCap_ge_linear r i
    rw [rteCap_succ]; omega

theorem rteCap_pos (r i : Nat) : 0 < rteCap r i := by
  have := rteCap_ge_linear r i; omega

theorem rteCap_strictMono (r : Nat) : ∀ {j i}, j < i → rteCap r j < rteCap r i
  | j, i + 1, h => by
    have hstep : rteCap r i < rteCap r (i + 1) := by rw [rteCap_succ]; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · exact Nat.lt_trans (rteCap_strictMono r hlt) hstep
    · exact hstep

theorem rteCap_mono (r : Nat) {j i : Nat} (h : j ≤ i) : rteCap r j ≤ rteCap r i := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · exact Nat.le_of_lt (rteCap_strictMono r hlt)
  · exact Nat.le_refl _

theorem rteCap_succ_lt_u64 {r i : Nat} (h : rteCap r i < 2 ^ 63) :
    rteCap r (i + 1) < 2 ^ 64 := by
  rw [rteCap_succ]; omega

theorem rustVecGrowCap_zero_probe (r : Nat) :
    rustVecGrowCap 0 0 (min 32 r) = rteCap r 0 := by
  unfold rustVecGrowCap rteCap; omega

private def rteFilterPred (r i : Nat) : Bool :=
  decide (i = 0 ∨ rteCap r (i - 1) ≤ r)

private theorem rteFilterPred_antitone (r : Nat) {j i : Nat} (hle : j ≤ i)
    (hi : rteFilterPred r i = true) : rteFilterPred r j = true := by
  simp only [rteFilterPred, decide_eq_true_eq] at hi ⊢
  by_cases hj0 : j = 0
  · exact Or.inl hj0
  · rcases hi with rfl | hle_r
    · omega
    · exact Or.inr (Nat.le_trans (rteCap_mono r (by omega)) hle_r)

private theorem range_filter_eq_range_length (p : Nat → Bool)
    (hanti : ∀ {j i}, j ≤ i → p i = true → p j = true) :
    ∀ m, (List.range m).filter p = List.range (((List.range m).filter p).length)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    have ih := range_filter_eq_range_length p hanti m
    by_cases hpm : p m = true
    · have hall : (List.range m).filter p = List.range m := by
        rw [List.filter_eq_self]
        intro x hx
        exact hanti (Nat.le_of_lt (List.mem_range.mp hx)) hpm
      simp only [hpm, ↓reduceIte, hall, List.length_append, List.length_range,
        List.length_singleton, List.range_succ]
    · simp only [hpm, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      exact ih

theorem rteCaps_zero : rteCaps 0 = [] := rfl

private theorem rteCaps_eq_filter {r : Nat} (hr0 : r ≠ 0) :
    rteCaps r = ((List.range (r + 1)).filter (rteFilterPred r)).map (rteCap r) := by
  unfold rteCaps
  simp only [hr0, ↓reduceIte]
  rfl

theorem rteCaps_eq_map_range {r : Nat} (hr : 0 < r) :
    rteCaps r = (List.range (rteCaps r).length).map (rteCap r) := by
  have hr0 : r ≠ 0 := by omega
  have hdef := rteCaps_eq_filter hr0
  have hlen : (rteCaps r).length = ((List.range (r + 1)).filter (rteFilterPred r)).length := by
    rw [hdef, List.length_map]
  calc rteCaps r
    _ = ((List.range (r + 1)).filter (rteFilterPred r)).map (rteCap r) := hdef
    _ = (List.range (((List.range (r + 1)).filter (rteFilterPred r)).length)).map (rteCap r) :=
        congrArg (List.map (rteCap r))
          (range_filter_eq_range_length (rteFilterPred r) (rteFilterPred_antitone r) (r + 1))
    _ = (List.range (rteCaps r).length).map (rteCap r) := by rw [hlen]

theorem rteCaps_length_pos {r : Nat} (hr : 0 < r) : 0 < (rteCaps r).length := by
  have hr0 : r ≠ 0 := by omega
  rw [rteCaps_eq_filter hr0, List.length_map]
  have hmem : 0 ∈ (List.range (r + 1)).filter (rteFilterPred r) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr (by omega), by simp [rteFilterPred]⟩
  exact List.length_pos_of_mem hmem

theorem rteCaps_mem_iff_lt_length {r : Nat} (hr : 0 < r) {i : Nat} :
    i < (rteCaps r).length ↔ (i = 0 ∨ rteCap r (i - 1) ≤ r) := by
  have hr0 : r ≠ 0 := by omega
  have hdef : (rteCaps r).length = ((List.range (r + 1)).filter (rteFilterPred r)).length := by
    rw [rteCaps_eq_filter hr0, List.length_map]
  have hfilt := range_filter_eq_range_length (rteFilterPred r) (rteFilterPred_antitone r) (r + 1)
  constructor
  · intro hi
    rw [hdef] at hi
    have hmem : i ∈ List.range (((List.range (r + 1)).filter (rteFilterPred r)).length) :=
      List.mem_range.mpr hi
    rw [← hfilt, List.mem_filter] at hmem
    simpa [rteFilterPred] using hmem.2
  · intro hcond
    have hir : i < r + 1 := by
      rcases hcond with rfl | hle
      · omega
      · have hlin := rteCap_ge_linear r (i - 1); omega
    have hmem : i ∈ (List.range (r + 1)).filter (rteFilterPred r) := by
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr hir, by simpa [rteFilterPred] using hcond⟩
    rw [hfilt, List.mem_range] at hmem
    rwa [hdef]

theorem rteCaps_succ_lt_iff {r : Nat} (hr : 0 < r) (i : Nat) :
    i + 1 < (rteCaps r).length ↔ rteCap r i ≤ r := by
  rw [rteCaps_mem_iff_lt_length hr]
  simp

theorem rteCap_le_two_mul_add_32 {r i : Nat} (hr : 0 < r) (hi : i < (rteCaps r).length) :
    rteCap r i ≤ 2 * r + 32 := by
  cases i with
  | zero => rw [rteCap_zero]; omega
  | succ j =>
    rcases (rteCaps_mem_iff_lt_length hr).mp hi with h0 | hle
    · omega
    · simp only [Nat.add_sub_cancel] at hle
      rw [rteCap_succ]; omega

theorem rteCaps_succ_eq_length_of_lt {r i : Nat} (hr : 0 < r)
    (hi : i < (rteCaps r).length) (hgt : r < rteCap r i) :
    i + 1 = (rteCaps r).length := by
  have hnlt : ¬ (i + 1 < (rteCaps r).length) := by
    rw [rteCaps_succ_lt_iff hr]; omega
  omega

theorem rteCaps_take_eq {r : Nat} (hr : 0 < r) {k : Nat} (hk : k ≤ (rteCaps r).length) :
    (rteCaps r).take k = (List.range k).map (rteCap r) := by
  rw [rteCaps_eq_map_range hr, ← List.map_take, List.take_range, Nat.min_eq_left hk]

theorem rteCaps_take_one {r : Nat} (hr : 0 < r) :
    (rteCaps r).take 1 = [rteCap r 0] := by
  rw [rteCaps_take_eq hr (rteCaps_length_pos hr)]; rfl

theorem rteCaps_take_succ {r i : Nat} (hr : 0 < r) (hi : i < (rteCaps r).length) :
    (rteCaps r).take (i + 1) = (rteCaps r).take i ++ [rteCap r i] := by
  rw [rteCaps_take_eq hr (by omega), rteCaps_take_eq hr (by omega),
      List.range_succ, List.map_append, List.map_singleton]

theorem rteFinalCap_zero : rteFinalCap 0 = 0 := rfl

theorem rteFinalCap_of_last {r i : Nat} (hr : 0 < r)
    (hi : i + 1 = (rteCaps r).length) :
    rteFinalCap r = rteCap r i := by
  unfold rteFinalCap
  rw [rteCaps_eq_map_range hr, ← hi, List.range_succ, List.map_append, List.map_singleton,
      getLast?_snoc]
  rfl

/-! ## `allocSeqPool` and `AllocSeqFits` stepping lemmas -/

private theorem allocSeqPool_go_append {oom : State → State → Prop}
    (A : RustStdAlloc oom) (align : Nat) :
    ∀ (xs : List Nat) (lb lk prev next : Nat),
      allocSeqPool.go A align lb lk prev (xs ++ [next]) =
        let p := allocSeqPool.go A align lb lk prev xs
        (p.1 + A.cost next align - A.cost (xs.getLast?.getD prev) align, p.2)
  | [], lb, lk, prev, next => rfl
  | c :: cs, lb, lk, prev, next => by
    simp only [List.cons_append, allocSeqPool.go]
    rw [allocSeqPool_go_append A align cs (lb + A.cost c align - A.cost prev align) lk c next]
    cases cs <;> rfl

theorem allocSeqPool_singleton {oom : State → State → Prop}
    (A : RustStdAlloc oom) (align lb lk c : Nat) :
    allocSeqPool A align lb lk [c] = (lb + A.cost c align, lk + 1) := rfl

theorem allocSeqPool_take_one {oom : State → State → Prop}
    (A : RustStdAlloc oom) {r : Nat} (hr : 0 < r) (lb lk : Nat) :
    allocSeqPool A 1 lb lk ((rteCaps r).take 1) =
      (rustVecGrowLb A lb 0 (rteCap r 0), rustVecGrowLk lk 0) := by
  rw [rteCaps_take_one hr]
  simp [allocSeqPool, allocSeqPool.go, rustVecGrowLb, rustVecGrowLk]

theorem allocSeqPool_take_step {oom : State → State → Prop}
    (A : RustStdAlloc oom) {r i : Nat} (hr : 0 < r)
    (hi : i + 1 < (rteCaps r).length) (lb lk : Nat) :
    let p := allocSeqPool A 1 lb lk ((rteCaps r).take (i + 1))
    allocSeqPool A 1 lb lk ((rteCaps r).take (i + 2)) =
      (rustVecGrowLb A p.1 (rteCap r i) (rteCap r (i + 1)),
       rustVecGrowLk p.2 (rteCap r i)) := by
  have htake1 : (rteCaps r).take (i + 1) =
      rteCap r 0 :: ((List.range i).map fun k => rteCap r (k + 1)) := by
    rw [rteCaps_take_eq hr (by omega), List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  have htake2 : (rteCaps r).take (i + 2) = (rteCaps r).take (i + 1) ++ [rteCap r (i + 1)] :=
    rteCaps_take_succ hr hi
  have hlast : (((List.range i).map fun k => rteCap r (k + 1)).getLast?.getD (rteCap r 0)) =
      rteCap r i := by
    cases i with
    | zero => rfl
    | succ j =>
      rw [List.range_succ, List.map_append, List.map_singleton, getLast?_snoc]
      rfl
  have hcpos : ¬ (rteCap r i = 0) := Nat.ne_of_gt (rteCap_pos r i)
  dsimp only
  rw [htake2, htake1, List.cons_append, allocSeqPool, allocSeqPool,
      allocSeqPool_go_append, hlast]
  simp [rustVecGrowLb, rustVecGrowLk, hcpos]

private theorem allocSeqFits_go_split {oom : State → State → Prop}
    (A : RustStdAlloc oom) (align : Nat) :
    ∀ (xs ys : List Nat) (lb lk prev next : Nat),
      AllocSeqFits.go A align lb lk prev (xs ++ next :: ys) →
      let p := allocSeqPool.go A align lb lk prev xs
      A.CanAlloc p.1 p.2 next align
  | [], _, _, _, _, _, h => h.1
  | c :: cs, ys, lb, lk, prev, next, h =>
    allocSeqFits_go_split A align cs ys (lb + A.cost c align - A.cost prev align) lk c next h.2

theorem allocSeqFits_head {oom : State → State → Prop}
    (A : RustStdAlloc oom) {r lb lk : Nat} (hr : 0 < r)
    (hfits : AllocSeqFits A 1 lb lk (rteCaps r)) :
    A.CanAlloc lb lk (rteCap r 0) 1 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (rteCaps_length_pos hr))
  rw [rteCaps_eq_map_range hr, hm, List.range_succ_eq_map, List.map_cons] at hfits
  exact hfits.1

theorem allocSeqFits_step {oom : State → State → Prop}
    (A : RustStdAlloc oom) {r i lb lk : Nat} (hr : 0 < r)
    (hi : i + 1 < (rteCaps r).length)
    (hfits : AllocSeqFits A 1 lb lk (rteCaps r)) :
    let p := allocSeqPool A 1 lb lk ((rteCaps r).take (i + 1))
    A.CanAlloc p.1 p.2 (rteCap r (i + 1)) 1 := by
  have htake1 : (rteCaps r).take (i + 1) =
      rteCap r 0 :: ((List.range i).map fun k => rteCap r (k + 1)) := by
    rw [rteCaps_take_eq hr (by omega), List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  have hsplit : rteCaps r =
      (rteCaps r).take (i + 1) ++ rteCap r (i + 1) :: (rteCaps r).drop (i + 2) := by
    conv => lhs; rw [← List.take_append_drop (i + 2) (rteCaps r)]
    rw [rteCaps_take_succ hr hi, List.append_assoc, List.singleton_append]
  rw [hsplit, htake1, List.cons_append] at hfits
  dsimp only
  rw [htake1, allocSeqPool]
  exact allocSeqFits_go_split A 1 _ _ (lb + A.cost (rteCap r 0) 1) (lk + 1) (rteCap r 0)
    (rteCap r (i + 1)) hfits.2

theorem RteOomPt.of_probe {r : Nat} (hr : 0 < r) :
    RteOomPt r (min 32 r) := by
  by_cases h8 : r < 8
  · exact Or.inl ⟨hr, h8, by omega⟩
  · refine Or.inr ⟨0, ?_, ?_⟩ <;> (rw [rteCap_zero]; omega)

theorem RteOomPt.of_grow {r i : Nat} (hle : rteCap r i ≤ r) :
    RteOomPt r (rteCap r i) :=
  Or.inr ⟨i, rfl, hle⟩

/-! ## `rustSmallProbeReadStdin_ok'` -/

/-- `rustSmallProbeReadStdin_okWhere` with `hreserve` (`do_reserve_and_handle`) discharged via
    `rustDoReserveAndHandle_okWhere` (`--gc-sections`-compatible). -/
theorem rustSmallProbeReadStdin_okWhere' {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {keep : Nat → Bool}
    (hk12 : keep 12 = true := by decide) (hk14 : keep 14 = true := by decide)
    (hk22 : keep 22 = true := by decide)
    {P : Program} {reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : 64 + 48 + Rust.hookStack ≤ reserveStack ∧ 144 + reserveStack ≤ 2 ^ 64 := by decide)
    (hread : subroutine_ok P (rustStdIoMultiLib.resolve mpl "read")
      (rustStdIoMultiLib.withCodeLoadedWhere keep mpl muslReadStdin32Spec))
    (hmemcpy : subroutine_ok P (rustStdIoMultiLib.resolve mpl "memcpy")
      (rustStdIoMultiLib.withCodeLoadedWhere keep mpl stdMemcpySpec))
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr mpl smallProbeReadStdinSym)
      (rustStdIoMultiLib.withCodeLoadedWhere keep mpl (rustSmallProbeReadStdinSpec A reserveStack)) :=
  rustSmallProbeReadStdin_okWhere A hpl hk14 hext ⟨by omega, hstk.2⟩ hread hmemcpy
    (rustDoReserveAndHandle_okWhere A hpl hk12 hk22 hext ⟨hstk.1, by omega⟩ hshim halloc hrealloc)

/-- `rustSmallProbeReadStdin_ok` with `hreserve` (`do_reserve_and_handle`) discharged via
    `rustDoReserveAndHandle_ok`. -/
theorem rustSmallProbeReadStdin_ok' {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {P : Program} {reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : 64 + 48 + Rust.hookStack ≤ reserveStack ∧ 144 + reserveStack ≤ 2 ^ 64 := by decide)
    (hread : subroutine_ok P (rustStdIoMultiLib.resolve mpl "read")
      (rustStdIoMultiLib.withCodeLoaded mpl muslReadStdin32Spec))
    (hmemcpy : subroutine_ok P (rustStdIoMultiLib.resolve mpl "memcpy")
      (rustStdIoMultiLib.withCodeLoaded mpl stdMemcpySpec))
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr mpl smallProbeReadStdinSym)
      (rustStdIoMultiLib.withCodeLoaded mpl (rustSmallProbeReadStdinSpec A reserveStack)) :=
  rustSmallProbeReadStdin_ok A hpl hext ⟨by omega, hstk.2⟩ hread hmemcpy
    (rustDoReserveAndHandle_ok A hpl hext ⟨hstk.1, by omega⟩ hshim halloc hrealloc)

end VerifiedLibraries.RustStd.Io
