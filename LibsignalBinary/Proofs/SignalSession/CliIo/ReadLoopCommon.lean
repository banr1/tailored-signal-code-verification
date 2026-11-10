/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
public import LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow
public import VerifiedLibraries.RustStd.Proofs.StdinCapSeq
public import ProofLib.Process.OracleEq

/-!
# Shared Doubling-Capacity, Stack-Probe, and Frame Infrastructure

Shared capacity-doubling arithmetic (`cliIoCap`, `cliIoReadCaps`), allocator-pool telescoping,
`oracle`/`symtab` process-frame transport, and `4096`-byte stack-buffer probe splits for
`signal_session_io::read_stdin` (`STDIN_CAP = 2^20`) and `signal_session_io::read_file`
(`FILE_CAP = 2^21`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.RustStd (
  RustStdAlloc NullAllowed PoolPreserved AllocCallPreserved IoFrame IoCallFrame StdErrnoCell
  vecHeader ioVecBuf ioResultVecOk
  AllocSeqFits allocSeqPool allocVecGrowLb allocVecGrowLk
)

/-! ## 1. `oracle` & `symtab` Transport Across `Syscall.standard` + Allocator-Hook Programs -/

/-- Every extern hook installed in `prog` preserves `State.oracle` and `State.symtab`.
    Holds vacuously when `∀ pc, prog.externAt? pc = none`, and also holds when `prog`
    installs allocator hooks (`allocHook0` / `RustStdAllocHooks`). -/
def ExternPreservesOracleSymtab (prog : Program) : Prop :=
  ∀ pc fn, prog.externAt? pc = some fn → ∀ s, (fn s).oracle = s.oracle ∧ (fn s).symtab = s.symtab

theorem ExternPreservesOracleSymtab.of_no_extern {prog : Program}
    (hext : ∀ pc, prog.externAt? pc = none) : ExternPreservesOracleSymtab prog :=
  fun pc _ he => by rw [hext pc] at he; cases he

theorem Step.oracle_symtab_eq_of_standard {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (hext : ExternPreservesOracleSymtab prog) {s s' : State} (h : Step prog s s') :
    s'.oracle = s.oracle ∧ s'.symtab = s.symtab := by
  refine ⟨?_, h.symtab_eq⟩
  cases h with
  | exec _ _ => exact evalInst_oracle_of_standard hsvc _ _
  | halt_unmapped _ _ _ => rfl
  | extern _ he _ _ => exact (hext _ _ he _).1
  | extern_fault _ _ _ => rfl

theorem Steps.oracle_symtab_eq_of_standard {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (hext : ExternPreservesOracleSymtab prog) {s0 sf : State} (h : Steps prog s0 sf) :
    sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab := by
  induction h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step h1 _ ih =>
    have h1' := Step.oracle_symtab_eq_of_standard hsvc hext h1
    exact ⟨ih.1.trans h1'.1, ih.2.trans h1'.2⟩

/-- Supply `sf.oracle = s0.oracle` and `sf.symtab = s0.symtab` at the postcondition state `sf`
    of any `SepWP` proof on a `Syscall.standard` program satisfying `ExternPreservesOracleSymtab`. -/
theorem cliIo_sepWP_carry_oracle_symtab {P : Program} (hsvc : P.svc = Syscall.standard)
    (hext : ExternPreservesOracleSymtab P) {target_pc : BitVec 64} {s0 : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP P target_pc s0 Pre
      (fun sf P_f => sf.oracle = s0.oracle → sf.symtab = s0.symtab → post sf P_f) oom) :
    SepWP P target_pc s0 Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sf, hsteps, hout⟩ := SepWP.to_reaches_pc h hm hL
  refine ⟨sf, hsteps, hout.imp ?_ id⟩
  rintro ⟨hpc, hrun, P_f, hmf, hp⟩
  have hos := Steps.oracle_symtab_eq_of_standard hsvc hext hsteps
  exact ⟨hpc, hrun, P_f, hmf, hp hos.1 hos.2⟩

theorem poolPreserved_of_syscall {s s' : State} (h : SyscallPreserved s s') :
    PoolPreserved s s' :=
  ⟨h.2.2.brkStart_eq, h.2.2.brk_eq, h.1⟩

theorem poolPreserved_of_stdState {s s' : State} (h : StdStatePreserved s s') :
    PoolPreserved s s' :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩

theorem poolPreserved_of_allocCall {s s' : State} (h : AllocCallPreserved s s')
    (hbrk : s'.brk = s.brk) : PoolPreserved s s' :=
  ⟨h.2.2.2.2.1, hbrk, h.2.2.2.1⟩

theorem ioFrame_trans {s0 s1 s2 : State} (h01 : IoFrame s0 s1) (h12 : IoFrame s1 s2) :
    IoFrame s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.trans h01.2⟩

theorem ioFrame_of_stdState {s s' : State} (h : StdStatePreserved s s') : IoFrame s s' :=
  ⟨h.2.1, h.2.2.2.1⟩

theorem ioFrame_of_allocCall {s s' : State} (h : AllocCallPreserved s s') : IoFrame s s' :=
  ⟨h.2.1, h.2.2.1⟩

/-! ## 2. Doubling Capacity Sequence (`cliIoCap`, `cliIoCapIdx`, `cliIoReadCaps`, `cliIoFinalCap`) -/

/-- Exponent `8` (`4096 * 2^8 = 1,048,576 = 2^20`) for `signal_session_io::read_stdin`. -/
abbrev cliIoStdinCapExp : Nat := 8

/-- Byte cap `STDIN_CAP = 1,048,576` (`1 MiB`) of `signal_session_io::read_stdin`. -/
abbrev cliIoStdinCap : Nat := 1048576

/-- Exponent `9` (`4096 * 2^9 = 2,097,152 = 2^21`) for `signal_session_io::read_file`. -/
abbrev cliIoFileCapExp : Nat := 9

/-- Byte cap `FILE_CAP = 2,097,152` (`2 MiB`) of `signal_session_io::read_file`. -/
abbrev cliIoFileCap : Nat := 2097152

/-- The `j`-th `Vec<u8>` buffer capacity (`4096 * 2^j`) in `signal_session_io`'s doubling schedule. -/
def cliIoCap (j : Nat) : Nat := 4096 * 2 ^ j

theorem cliIoCap_zero : cliIoCap 0 = 4096 := rfl

theorem cliIoCap_succ (j : Nat) : cliIoCap (j + 1) = 2 * cliIoCap j := by
  unfold cliIoCap
  rw [Nat.pow_succ]
  omega

theorem cliIoStdinCap_eq : cliIoCap cliIoStdinCapExp = cliIoStdinCap := rfl

theorem cliIoFileCap_eq : cliIoCap cliIoFileCapExp = cliIoFileCap := rfl

theorem cliIoCap_ge_4096 : ∀ j : Nat, 4096 ≤ cliIoCap j
  | 0 => Nat.le_refl 4096
  | j + 1 => by
    have ih := cliIoCap_ge_4096 j
    rw [cliIoCap_succ]
    omega

theorem cliIoCap_pos (j : Nat) : 0 < cliIoCap j := by
  have := cliIoCap_ge_4096 j
  omega

theorem cliIoCap_dvd_4096 (j : Nat) : 4096 ∣ cliIoCap j :=
  ⟨2 ^ j, rfl⟩

theorem cliIoCap_strictMono : ∀ {i j : Nat}, i < j → cliIoCap i < cliIoCap j
  | i, j + 1, h => by
    have hstep : cliIoCap j < cliIoCap (j + 1) := by
      have := cliIoCap_pos j
      rw [cliIoCap_succ]
      omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · exact Nat.lt_trans (cliIoCap_strictMono hlt) hstep
    · exact hstep

theorem cliIoCap_mono {i j : Nat} (h : i ≤ j) : cliIoCap i ≤ cliIoCap j := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · exact Nat.le_of_lt (cliIoCap_strictMono hlt)
  · exact Nat.le_refl _

theorem cliIoCap_le_fileCap {j : Nat} (hj : j ≤ 9) : cliIoCap j ≤ 2097152 :=
  cliIoCap_mono hj

theorem cliIoCap_lt_pow62 {j : Nat} (hj : j ≤ 9) : cliIoCap j < 2 ^ 62 :=
  Nat.lt_of_le_of_lt (cliIoCap_le_fileCap hj) (by decide)

theorem cliIoCap_lt_pow63 {j : Nat} (hj : j ≤ 9) : cliIoCap j < 2 ^ 63 :=
  Nat.lt_of_le_of_lt (cliIoCap_le_fileCap hj) (by decide)

theorem cliIoCap_lt_pow64 {j : Nat} (hj : j ≤ 9) : cliIoCap j < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (cliIoCap_le_fileCap hj) (by decide)

theorem not_nullAllowed_cliIoCap {j : Nat} (hj : j ≤ 9) : ¬ NullAllowed (cliIoCap j) 1 := by
  have hle : cliIoCap j ≤ 2097152 := cliIoCap_le_fileCap hj
  have hpow : 2097153 ≤ 2 ^ 62 := by decide
  unfold NullAllowed
  omega

/-- Index `j ∈ [0, K]` of the final doubling capacity `4096 * 2^j` reached on `r > 0` input bytes
    under cap `4096 * 2^K`. -/
def cliIoCapIdx : Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, r => if r ≤ cliIoCap K then cliIoCapIdx K r else K + 1

theorem cliIoCapIdx_le : ∀ (K r : Nat), cliIoCapIdx K r ≤ K
  | 0, _ => Nat.le_refl 0
  | K + 1, r => by
    unfold cliIoCapIdx
    split
    · exact Nat.le_succ_of_le (cliIoCapIdx_le K r)
    · exact Nat.le_refl _

theorem le_cliIoCap_cliIoCapIdx : ∀ {K r : Nat}, r ≤ cliIoCap K → r ≤ cliIoCap (cliIoCapIdx K r)
  | 0, _, hr => hr
  | K + 1, r, hr => by
    unfold cliIoCapIdx
    split
    · rename_i hle
      exact le_cliIoCap_cliIoCapIdx hle
    · exact hr

theorem cliIoCap_pred_lt_of_pos : ∀ {K r : Nat}, 0 < cliIoCapIdx K r →
    cliIoCap (cliIoCapIdx K r - 1) < r
  | 0, _, hpos => absurd hpos (Nat.not_lt_zero 0)
  | K + 1, r, hpos => by
    unfold cliIoCapIdx at hpos ⊢
    split at hpos
    · rename_i hle
      simp only [hle, ↓reduceIte]
      exact cliIoCap_pred_lt_of_pos hpos
    · rename_i hgt
      simp only [hgt, ↓reduceIte, Nat.add_sub_cancel]
      omega

theorem cliIoCapIdx_eq_of_bounds {K r j : Nat} (hj : j ≤ K)
    (hlo : j = 0 ∨ cliIoCap (j - 1) < r) (hhi : r ≤ cliIoCap j) :
    cliIoCapIdx K r = j := by
  have hr_le_max : r ≤ cliIoCap K := Nat.le_trans hhi (cliIoCap_mono hj)
  have hle1 : r ≤ cliIoCap (cliIoCapIdx K r) := le_cliIoCap_cliIoCapIdx hr_le_max
  have hj_le : j ≤ cliIoCapIdx K r := by
    rcases hlo with rfl | hgt
    · exact Nat.zero_le _
    · refine Classical.byContradiction fun hnot => ?_
      have hlt_idx : cliIoCapIdx K r ≤ j - 1 := by omega
      have hcap_le := cliIoCap_mono hlt_idx
      have := Nat.lt_of_lt_of_le hgt (Nat.le_trans hle1 hcap_le)
      exact Nat.lt_irrefl _ this
  have hidx_le : cliIoCapIdx K r ≤ j := by
    by_cases hp : 0 < cliIoCapIdx K r
    · have hgt := cliIoCap_pred_lt_of_pos hp
      refine Classical.byContradiction fun hnot => ?_
      have hge_pred : j ≤ cliIoCapIdx K r - 1 := by omega
      have := Nat.lt_of_le_of_lt (cliIoCap_mono hge_pred) (Nat.lt_of_lt_of_le hgt hhi)
      exact Nat.lt_irrefl _ this
    · omega
  omega

theorem cliIoCapIdx_of_gt_max : ∀ {K r : Nat}, cliIoCap K < r → cliIoCapIdx K r = K
  | 0, _, _ => rfl
  | K + 1, r, hgt => by
    have hgtK : ¬ (r ≤ cliIoCap K) := by
      have := cliIoCap_mono (show K ≤ K + 1 by omega)
      omega
    simp [cliIoCapIdx, hgtK]

theorem cliIoCapIdx_cap_self (K : Nat) : cliIoCapIdx K (cliIoCap K) = K := by
  refine cliIoCapIdx_eq_of_bounds (Nat.le_refl K) ?_ (Nat.le_refl _)
  by_cases hK : K = 0
  · exact Or.inl hK
  · exact Or.inr (cliIoCap_strictMono (by omega : K - 1 < K))

/-- Ordered list of buffer capacities requested by `read_stdin` (`K = 8`) or `read_file` (`K = 9`)
    on an input of `r` bytes: `[]` when `r = 0`, otherwise `[4096, 8192, ..., 4096 * 2^m]` where
    `m = cliIoCapIdx K r`. -/
def cliIoReadCaps (K r : Nat) : List Nat :=
  if r = 0 then []
  else (List.range (cliIoCapIdx K r + 1)).map cliIoCap

/-- Final `Vec<u8>` capacity on `Ok` return (`r ≤ cliIoCap K`): `0` when `r = 0`, otherwise
    `cliIoCap (cliIoCapIdx K r)`. -/
def cliIoFinalCap (K r : Nat) : Nat :=
  if r = 0 then 0 else cliIoCap (cliIoCapIdx K r)

theorem cliIoFinalCap_zero (K : Nat) : cliIoFinalCap K 0 = 0 := rfl

theorem cliIoFinalCap_pos {K r : Nat} (hr : 0 < r) :
    cliIoFinalCap K r = cliIoCap (cliIoCapIdx K r) := by
  unfold cliIoFinalCap
  have hr0 : r ≠ 0 := by omega
  simp [hr0]

/-! ## 3. `allocSeqPool` & `AllocSeqFits` Exact Telescoping -/

theorem allocSeqPool_go_step {oom : State → State → Prop} (A : RustStdAlloc oom)
    (align lb0 lk prev c : Nat) (cs : List Nat) :
    allocSeqPool.go A align (lb0 + A.cost prev align) lk prev (c :: cs) =
      allocSeqPool.go A align (lb0 + A.cost c align) lk c cs := by
  have htel : lb0 + A.cost prev align + A.cost c align - A.cost prev align =
      lb0 + A.cost c align := by omega
  conv => lhs; unfold allocSeqPool.go
  rw [htel]

theorem allocSeqPool_go_map_range {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb0 lk : Nat) :
    ∀ (start count : Nat),
      allocSeqPool.go A 1 (lb0 + A.cost (cliIoCap start) 1) lk (cliIoCap start)
        ((List.range' (start + 1) count).map cliIoCap) =
        (lb0 + A.cost (cliIoCap (start + count)) 1, lk)
  | start, 0 => by simp [allocSeqPool.go]
  | start, count + 1 => by
    simp only [List.range'_succ, List.map_cons]
    rw [allocSeqPool_go_step]
    simpa [Nat.add_assoc, Nat.add_comm 1 count] using
      allocSeqPool_go_map_range A lb0 lk (start + 1) count

theorem allocSeqPool_map_range_succ {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb lk j : Nat) :
    allocSeqPool A 1 lb lk ((List.range (j + 1)).map cliIoCap) =
      (lb + A.cost (cliIoCap j) 1, lk + 1) := by
  rw [List.range_eq_range', List.range'_succ, List.map_cons]
  unfold allocSeqPool
  simpa using allocSeqPool_go_map_range A lb (lk + 1) 0 j

theorem allocSeqPool_cliIoReadCaps_zero {oom : State → State → Prop} (A : RustStdAlloc oom)
    (K lb lk : Nat) :
    allocSeqPool A 1 lb lk (cliIoReadCaps K 0) = (lb, lk) := rfl

theorem allocSeqPool_cliIoReadCaps_pos {oom : State → State → Prop} (A : RustStdAlloc oom)
    {K r : Nat} (hr : 0 < r) (lb lk : Nat) :
    allocSeqPool A 1 lb lk (cliIoReadCaps K r) =
      (lb + A.cost (cliIoCap (cliIoCapIdx K r)) 1, lk + 1) := by
  have hr0 : r ≠ 0 := by omega
  unfold cliIoReadCaps
  simp only [hr0, ↓reduceIte]
  exact allocSeqPool_map_range_succ A lb lk (cliIoCapIdx K r)

theorem allocVecGrowLb_from_zero {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb newCap : Nat) :
    allocVecGrowLb A lb 0 newCap = lb + A.cost newCap 1 := rfl

theorem allocVecGrowLk_from_zero (lk : Nat) :
    allocVecGrowLk lk 0 = lk + 1 := rfl

theorem allocVecGrowLb_telescopes {oom : State → State → Prop} (A : RustStdAlloc oom)
    {oldCap newCap : Nat} (hold : 0 < oldCap) (lb : Nat) :
    allocVecGrowLb A (lb + A.cost oldCap 1) oldCap newCap = lb + A.cost newCap 1 := by
  have hne : oldCap ≠ 0 := by omega
  simp only [allocVecGrowLb, hne, ↓reduceIte]
  omega

theorem allocVecGrowLk_from_pos {oldCap : Nat} (hold : 0 < oldCap) (lk : Nat) :
    allocVecGrowLk (lk + 1) oldCap = lk + 1 := by
  have hne : oldCap ≠ 0 := by omega
  simp [allocVecGrowLk, hne]

theorem dealloc_cancel_lb {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb sz al : Nat) :
    lb + A.cost sz al - A.cost sz al = lb :=
  Nat.add_sub_cancel lb (A.cost sz al)

theorem dealloc_cancel_lk (lk : Nat) : (lk + 1) - 1 = lk := rfl

private theorem allocSeqFits_go_canAlloc {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb0 lk : Nat) :
    ∀ (start count k : Nat), k < count →
      AllocSeqFits.go A 1 (lb0 + A.cost (cliIoCap start) 1) lk (cliIoCap start)
        ((List.range' (start + 1) count).map cliIoCap) →
      A.CanAlloc (lb0 + A.cost (cliIoCap (start + k)) 1) lk (cliIoCap (start + k + 1)) 1
  | _, 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | start, count + 1, 0, _, hf => by
    simp only [List.range'_succ, List.map_cons, AllocSeqFits.go] at hf
    simpa using hf.1
  | start, count + 1, k + 1, hk, hf => by
    simp only [List.range'_succ, List.map_cons, AllocSeqFits.go] at hf
    have htel : lb0 + A.cost (cliIoCap start) 1 + A.cost (cliIoCap (start + 1)) 1 -
        A.cost (cliIoCap start) 1 = lb0 + A.cost (cliIoCap (start + 1)) 1 := by omega
    rw [htel] at hf
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using
      allocSeqFits_go_canAlloc A lb0 lk (start + 1) count k (Nat.lt_of_succ_lt_succ hk) hf.2

theorem AllocSeqFits_canAlloc_zero {oom : State → State → Prop} {A : RustStdAlloc oom}
    {K r lb lk : Nat} (hr : 0 < r)
    (hf : AllocSeqFits A 1 lb lk (cliIoReadCaps K r)) :
    A.CanAlloc lb lk 4096 1 := by
  have hr0 : r ≠ 0 := by omega
  unfold cliIoReadCaps at hf
  simp only [hr0, ↓reduceIte, List.range_eq_range', List.range'_succ, List.map_cons,
    AllocSeqFits] at hf
  exact hf.1

theorem AllocSeqFits_canAlloc_succ {oom : State → State → Prop} {A : RustStdAlloc oom}
    {K r lb lk j : Nat} (hr : 0 < r) (hj : j + 1 ≤ cliIoCapIdx K r)
    (hf : AllocSeqFits A 1 lb lk (cliIoReadCaps K r)) :
    A.CanAlloc (lb + A.cost (cliIoCap j) 1) (lk + 1) (cliIoCap (j + 1)) 1 := by
  have hr0 : r ≠ 0 := by omega
  unfold cliIoReadCaps at hf
  simp only [hr0, ↓reduceIte, List.range_eq_range', List.range'_succ, List.map_cons,
    AllocSeqFits] at hf
  simpa using allocSeqFits_go_canAlloc A lb (lk + 1) 0 (cliIoCapIdx K r) j hj hf.2

theorem AllocSeqFits_of_true {oom : State → State → Prop} (A : RustStdAlloc oom)
    (hcan : ∀ b k sz al, A.CanAlloc b k sz al) (align lb lk : Nat) :
    ∀ cs : List Nat, AllocSeqFits A align lb lk cs
  | [] => trivial
  | c :: cs => ⟨hcan _ _ _ _, go (lb + A.cost c align) (lk + 1) c cs⟩
where
  go (b k prev : Nat) : ∀ cs : List Nat, AllocSeqFits.go A align b k prev cs
    | [] => trivial
    | c :: cs => ⟨hcan _ _ _ _, go (b + A.cost c align - A.cost prev align) k c cs⟩

/-! ## 4. Loop-Step Chunk Arithmetic & `BitVec` Branch Reductions -/

/-- Bytes requested per `read` call: `min (capMax + 1 - len) 4096`. -/
def wantBytes (capMax len : Nat) : Nat := min (capMax + 1 - len) 4096

theorem wantBytes_pos {capMax len : Nat} (hlen : len ≤ capMax) :
    0 < wantBytes capMax len := by
  unfold wantBytes; omega

theorem wantBytes_le_4096 (capMax len : Nat) : wantBytes capMax len ≤ 4096 :=
  Nat.min_le_right _ _

theorem wantBytes_le_sub (capMax len : Nat) : wantBytes capMax len ≤ capMax + 1 - len :=
  Nat.min_le_left _ _

theorem wantBytes_at_max (capMax : Nat) : wantBytes capMax capMax = 1 := by
  unfold wantBytes; omega

theorem wantBytes_eq_4096_of_dvd {K len : Nat} (hdvd : 4096 ∣ len) (hlt : len < cliIoCap K) :
    wantBytes (cliIoCap K) len = 4096 := by
  rcases hdvd with ⟨q, rfl⟩
  rcases cliIoCap_dvd_4096 K with ⟨m, hm⟩
  have hqm : q + 1 ≤ m := by omega
  have hgap : 4096 ≤ cliIoCap K - 4096 * q := by
    rw [hm]
    have : 4096 * (q + 1) ≤ 4096 * m := Nat.mul_le_mul_left 4096 hqm
    omega
  unfold wantBytes
  omega

/-- Over-cap (`len + n > cliIoCap K`) with `4096`-aligned intermediate lengths can occur ONLY at
    `len = cliIoCap K` with `n = 1` and `cliIoCap K < r`. -/
theorem overCap_forces_eq_max {K r len n : Nat}
    (hlen_le : len ≤ min r (cliIoCap K))
    (hdvd_imp : len < r → 4096 ∣ len)
    (hn_eq : n = min (r - len) (wantBytes (cliIoCap K) len))
    (hn_pos : 0 < n)
    (hover : cliIoCap K < len + n) :
    len = cliIoCap K ∧ n = 1 ∧ cliIoCap K < r := by
  have hlen_lt_r : len < r := by omega
  have hdvd : 4096 ∣ len := hdvd_imp hlen_lt_r
  have hlen_le_max : len ≤ cliIoCap K := Nat.le_trans hlen_le (Nat.min_le_right _ _)
  by_cases hlt_max : len < cliIoCap K
  · rcases hdvd with ⟨q, rfl⟩
    rcases cliIoCap_dvd_4096 K with ⟨m, hm⟩
    have hqm : q + 1 ≤ m := by omega
    have h4096 : 4096 * q + 4096 ≤ cliIoCap K := by
      rw [hm]
      have : 4096 * (q + 1) ≤ 4096 * m := Nat.mul_le_mul_left 4096 hqm
      omega
    have hn_le : n ≤ 4096 := by
      rw [hn_eq]
      exact Nat.le_trans (Nat.min_le_right _ _) (wantBytes_le_4096 _ _)
    omega
  · have hlen_eq : len = cliIoCap K := by omega
    subst hlen_eq
    have hw : wantBytes (cliIoCap K) (cliIoCap K) = 1 := wantBytes_at_max _
    rw [hw] at hn_eq
    exact ⟨rfl, by omega, by omega⟩

/-- Preserves `len' < r → 4096 ∣ len'` across an in-cap read step (`len' = len + n ≤ cliIoCap K`). -/
theorem dvd_4096_preserved {K r len n : Nat}
    (_hlen_le : len ≤ min r (cliIoCap K))
    (hdvd_imp : len < r → 4096 ∣ len)
    (hn_eq : n = min (r - len) (wantBytes (cliIoCap K) len))
    (hn_pos : 0 < n)
    (hle_max : len + n ≤ cliIoCap K)
    (hlt_r : len + n < r) :
    4096 ∣ (len + n) := by
  have hlen_lt_r : len < r := by omega
  have hdvd : 4096 ∣ len := hdvd_imp hlen_lt_r
  have hlt_max : len < cliIoCap K := by omega
  have hw : wantBytes (cliIoCap K) len = 4096 := wantBytes_eq_4096_of_dvd hdvd hlt_max
  rw [hw] at hn_eq
  have hn_4096 : n = 4096 := by omega
  rw [hn_4096]
  exact Nat.dvd_add hdvd (Nat.dvd_refl 4096)

/-- When `len' = len + n ≤ cliIoCap j` (`0 < len`), the capacity index stays `j`. -/
theorem no_grow_capIdx_eq {K len len' : Nat}
    (_hlen_pos : 0 < len) (hle : len ≤ len')
    (hle_cap : len' ≤ cliIoCap (cliIoCapIdx K len)) :
    cliIoCapIdx K len' = cliIoCapIdx K len := by
  let j := cliIoCapIdx K len
  refine cliIoCapIdx_eq_of_bounds (cliIoCapIdx_le K len) ?_ hle_cap
  by_cases hj0 : j = 0
  · exact Or.inl hj0
  · exact Or.inr (Nat.lt_of_lt_of_le (cliIoCap_pred_lt_of_pos (by omega)) hle)

/-- When `cliIoCap j < len + n ≤ cliIoCap K` (`n ≤ 4096`, `len ≤ cliIoCap j`, `len + n ≤ r`),
    doubling advances by exactly one step `j → j + 1`. -/
theorem grow_step_bounds {K r j len n : Nat}
    (hK9 : K ≤ 9)
    (_hj : j ≤ K)
    (hlen_le_cap : len ≤ cliIoCap j)
    (hn_le_4096 : n ≤ 4096)
    (hn_le_rem : len + n ≤ r)
    (hle_max : len + n ≤ cliIoCap K)
    (hgt : cliIoCap j < len + n) :
    j + 1 ≤ K ∧ j + 1 ≤ cliIoCapIdx K r ∧ cliIoCapIdx K (len + n) = j + 1 ∧
      len + n ≤ cliIoCap (j + 1) ∧ ¬ NullAllowed (cliIoCap (j + 1)) 1 := by
  have hj_lt_K : j < K := by
    refine Classical.byContradiction fun hnot => ?_
    have hge : K ≤ j := by omega
    have := cliIoCap_mono hge
    omega
  have hj1_le_K : j + 1 ≤ K := hj_lt_K
  have h4096 : 4096 ≤ cliIoCap j := cliIoCap_ge_4096 j
  have hle_j1 : len + n ≤ cliIoCap (j + 1) := by
    rw [cliIoCap_succ]; omega
  have hidx_eq : cliIoCapIdx K (len + n) = j + 1 :=
    cliIoCapIdx_eq_of_bounds hj1_le_K (Or.inr hgt) hle_j1
  have hj1_le_r : j + 1 ≤ cliIoCapIdx K r := by
    by_cases hr_max : r ≤ cliIoCap K
    · have hr_le := le_cliIoCap_cliIoCapIdx hr_max
      have hlt_cap : cliIoCap j < cliIoCap (cliIoCapIdx K r) :=
        Nat.lt_of_lt_of_le hgt (Nat.le_trans hn_le_rem hr_le)
      refine Classical.byContradiction fun hnot => ?_
      have hle_idx : cliIoCapIdx K r ≤ j := by omega
      have := cliIoCap_mono hle_idx
      omega
    · rw [cliIoCapIdx_of_gt_max (by omega : cliIoCap K < r)]
      exact hj1_le_K
  exact ⟨hj1_le_K, hj1_le_r, hidx_eq, hle_j1, not_nullAllowed_cliIoCap (by omega)⟩

theorem bit63_eq_zero_of_lt {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hd : n / 2 ^ 63 = 0 := Nat.div_eq_of_lt hlt
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

theorem bv64_ult_ofNat_true {a b : Nat} (hab : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
  have ha : a < 2 ^ 64 := Nat.lt_trans hab hb
  simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hab]

theorem bv64_ult_ofNat_false {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
  have hb : b < 2 ^ 64 := Nat.lt_of_le_of_lt hba ha
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

theorem bv64_beq_ofNat_false {a b : Nat} (hne : a ≠ b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
  refine beq_false_of_ne fun heq => hne ?_
  have hto := congrArg BitVec.toNat heq
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hto

theorem bv64_shiftLeft1_ofNat {a : Nat} (ha : 2 * a < 2 ^ 64) :
    (BitVec.ofNat 64 a) <<< 1 = BitVec.ofNat 64 (2 * a) := by
  have ha1 : a < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha1,
    Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm a 2,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem bv64_sub_ofNat {a b : Nat} (hba : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have hsplit : a = b + (a - b) := (Nat.add_sub_of_le hba).symm
  conv => lhs; arg 1; rw [hsplit]
  rw [BitVec.ofNat_add]
  bv_lin

theorem wantBytes_csel_bv {capMax len : Nat} (_hlen : len ≤ capMax)
    (hmax1 : capMax + 1 < 2 ^ 64) :
    (if (BitVec.ofNat 64 (capMax + 1 - len)).ult 4096#64 = true
     then BitVec.ofNat 64 (capMax + 1 - len)
     else 4096#64) = BitVec.ofNat 64 (wantBytes capMax len) := by
  have hsub_lt : capMax + 1 - len < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hmax1
  have h4096_eq : (4096#64 : BitVec 64) = BitVec.ofNat 64 4096 := rfl
  have h4096_lt : 4096 < 2 ^ 64 := by decide
  rw [h4096_eq]
  unfold wantBytes
  by_cases hlt : capMax + 1 - len < 4096
  · rw [bv64_ult_ofNat_true hlt h4096_lt]
    simp [Nat.min_eq_left (Nat.le_of_lt hlt)]
  · rw [bv64_ult_ofNat_false (by omega : 4096 ≤ capMax + 1 - len) hsub_lt]
    simp [Nat.min_eq_right (by omega : 4096 ≤ capMax + 1 - len)]

/-! ## 5. Saved-Register Slots, `4096`-B Stack Probe Splits, & `Vec` Buffer Bridges -/

section StackHelpers
arm64_proof_prelude

/-- 12 callee-saved register slots (`[s0.sp - 96, s0.sp)`) shared by `read_stdin` (`block[0]`)
    and `read_file` (`block[3]`). -/
def cliIoSavedRegs12 (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

/-- Expose the 8-byte stack-probe word at `base + 32` inside a `4096`-byte stack buffer. -/
theorem memRegion4096_split_probe32 (base : BitVec 64) :
    memRegion base 4096 =
      memRegion base 32 ∗
        (∃∗ w : BitVec 64, (base + 32#64) ↦₆₄ w) ∗
        memRegion (base + 40#64) 4056 := by
  rw [memRegion_split_le base 32 4096 (by decide) (by decide),
    memRegion_split_le (base + 32#64) 8 4064 (by decide) (by decide),
    show (8 : Nat) = 8 * 1 by decide,
    memRegion_cells (base + 32#64) 1 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, bv_lin_norm]

/-- Refold the 8-byte stack-probe word at `base + 32` back into `memRegion base 4096`. -/
theorem memRegion4096_refold_probe32 (base : BitVec 64) (w : BitVec 64) :
    memRegion base 32 ∗ ((base + 32#64) ↦₆₄ w) ∗ memRegion (base + 40#64) 4056 ⊢
      memRegion base 4096 := by
  rw [memRegion4096_split_probe32 base]
  refine sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w (Entails.refl _)))

/-- Split `stackAt sp stackBytes` (`4224 ≤ stackBytes ≤ 2^64`) for `read_stdin` (`block[0]`):
    - `stackAt (sp - 4224) (stackBytes - 4224)` below the loop `sp`,
    - `memRegion (sp - 4224) 4096` (the `4096`-byte stack read buffer at `sp - 0x1080`),
    - `vecHeader (sp - 128) st0 st1 st2` (`24`-byte `finish_grow` out-slot at `x29 - 0x20`),
    - `(sp - 104) ↦₆₄ st3` (`8`-byte pad at `x29 - 0x08`), and
    - `12` saved-register cells at `[sp - 96, sp)`. -/
theorem cliIoReadStdin_stack_split (sp : BitVec 64) {stackBytes : Nat}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) :
    stackAt sp stackBytes =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3,
      ∃∗ r0, ∃∗ r1, ∃∗ r2, ∃∗ r3, ∃∗ r4, ∃∗ r5,
      ∃∗ r6, ∃∗ r7, ∃∗ r8, ∃∗ r9, ∃∗ r10, ∃∗ r11,
        stackAt (sp - 4224#64) (stackBytes - 4224) ∗
        memRegion (sp - 4224#64) 4096 ∗
        vecHeader (sp - 128#64) st0 st1 st2 ∗
        ((sp - 104#64) ↦₆₄ st3) ∗
        (((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗
          ((sp - 80#64) ↦₆₄ r2) ∗ ((sp - 72#64) ↦₆₄ r3) ∗
          ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
          ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗
          ((sp - 32#64) ↦₆₄ r8) ∗ ((sp - 24#64) ↦₆₄ r9) ∗
          ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11)) := by
  have heq_sb : stackBytes = (stackBytes - 128) + 8 * 16 := by omega
  conv => lhs; rw [heq_sb]
  rw [stackAt_split_cells sp (stackBytes - 128) 16 (by omega)]
  have hbot : stackAt (sp - BitVec.ofNat 64 (8 * 16)) (stackBytes - 128) =
      stackAt (sp - 4224#64) (stackBytes - 4224) ∗ memRegion (sp - 4224#64) 4096 := by
    have h128 : sp - BitVec.ofNat 64 (8 * 16) = sp - 128#64 := rfl
    rw [h128]
    unfold ProofLib.stackAt
    have h4224 : sp - 128#64 - BitVec.ofNat 64 (stackBytes - 128) =
        sp - 4224#64 - BitVec.ofNat 64 (stackBytes - 4224) := by
      have hsplit : stackBytes - 128 = (stackBytes - 4224) + 4096 := by omega
      rw [hsplit, BitVec.ofNat_add]
      bv_lin
    rw [h4224,
      memRegion_split_le (sp - 4224#64 - BitVec.ofNat 64 (stackBytes - 4224))
        (stackBytes - 4224) (stackBytes - 128) (by omega) (by omega)]
    have h4096_sz : stackBytes - 128 - (stackBytes - 4224) = 4096 := by omega
    have h4096_addr : sp - 4224#64 - BitVec.ofNat 64 (stackBytes - 4224) +
        BitVec.ofNat 64 (stackBytes - 4224) = sp - 4224#64 := by bv_lin
    rw [h4096_sz, h4096_addr]
  rw [hbot]
  dsimp only [cells, vecHeader]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_right,
    bv_lin_norm, sepConj_assoc]

/-- Refold `read_stdin`'s frame back into `stackAt s0.sp stackBytes`. -/
theorem cliIoReadStdin_stack_refold (s0 : State) {stackBytes : Nat}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (st0 st1 st2 st3 : BitVec 64) :
    stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ⊢
      stackAt s0.sp stackBytes := by
  rw [cliIoReadStdin_stack_split s0.sp hlo hhi]
  dsimp only [cliIoSavedRegs12]
  exact Entails.sepExists_right st0 <| Entails.sepExists_right st1 <|
    Entails.sepExists_right st2 <| Entails.sepExists_right st3 <|
    Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 28#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 27#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 26#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) <|
    by sep_entail

/-- Split `stackAt sp stackBytes` (`8320 ≤ stackBytes ≤ 2^64`) for `read_file` (`block[3]`):
    - `stackAt (sp - 8320) (stackBytes - 8320)` below the loop `sp`,
    - `memRegion (sp - 8320) 4096` (the `4096`-byte C-string path buffer at `sp - 0x2080`),
    - `memRegion (sp - 4224) 4096` (the `4096`-byte chunk buffer at `sp - 0x1080`),
    - `vecHeader (sp - 128) st0 st1 st2` (`24`-byte `finish_grow` out-slot at `x29 - 0x20`),
    - `(sp - 104) ↦₆₄ st3` (`8`-byte pad at `x29 - 0x08`), and
    - `12` saved-register cells at `[sp - 96, sp)`. -/
theorem cliIoReadFile_stack_split (sp : BitVec 64) {stackBytes : Nat}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) :
    stackAt sp stackBytes =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3,
      ∃∗ r0, ∃∗ r1, ∃∗ r2, ∃∗ r3, ∃∗ r4, ∃∗ r5,
      ∃∗ r6, ∃∗ r7, ∃∗ r8, ∃∗ r9, ∃∗ r10, ∃∗ r11,
        stackAt (sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (sp - 8320#64) 4096 ∗
        memRegion (sp - 4224#64) 4096 ∗
        vecHeader (sp - 128#64) st0 st1 st2 ∗
        ((sp - 104#64) ↦₆₄ st3) ∗
        (((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗
          ((sp - 80#64) ↦₆₄ r2) ∗ ((sp - 72#64) ↦₆₄ r3) ∗
          ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
          ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗
          ((sp - 32#64) ↦₆₄ r8) ∗ ((sp - 24#64) ↦₆₄ r9) ∗
          ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11)) := by
  have heq_sb : stackBytes = (stackBytes - 128) + 8 * 16 := by omega
  conv => lhs; rw [heq_sb]
  rw [stackAt_split_cells sp (stackBytes - 128) 16 (by omega)]
  have hbot : stackAt (sp - BitVec.ofNat 64 (8 * 16)) (stackBytes - 128) =
      stackAt (sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (sp - 8320#64) 4096 ∗ memRegion (sp - 4224#64) 4096 := by
    have h128 : sp - BitVec.ofNat 64 (8 * 16) = sp - 128#64 := rfl
    rw [h128]
    unfold ProofLib.stackAt
    have h8320 : sp - 128#64 - BitVec.ofNat 64 (stackBytes - 128) =
        sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320) := by
      have hsplit : stackBytes - 128 = (stackBytes - 8320) + 8192 := by omega
      rw [hsplit, BitVec.ofNat_add]
      bv_lin
    rw [h8320,
      memRegion_split_le (sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
        (stackBytes - 8320) (stackBytes - 128) (by omega) (by omega)]
    have h8192_sz : stackBytes - 128 - (stackBytes - 8320) = 8192 := by omega
    have h8320_addr : sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320) +
        BitVec.ofNat 64 (stackBytes - 8320) = sp - 8320#64 := by bv_lin
    rw [h8192_sz, h8320_addr,
      memRegion_split_le (sp - 8320#64) 4096 8192 (by decide) (by decide)]
    have h4224_addr : sp - 8320#64 + BitVec.ofNat 64 4096 = sp - 4224#64 := by bv_lin
    rw [h4224_addr]
  rw [hbot]
  dsimp only [cells, vecHeader]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_right,
    bv_lin_norm, sepConj_assoc]

/-- Refold `read_file`'s frame back into `stackAt s0.sp stackBytes`. -/
theorem cliIoReadFile_stack_refold (s0 : State) {stackBytes : Nat}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (st0 st1 st2 st3 : BitVec 64) :
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ⊢
      stackAt s0.sp stackBytes := by
  rw [cliIoReadFile_stack_split s0.sp hlo hhi]
  dsimp only [cliIoSavedRegs12]
  exact Entails.sepExists_right st0 <| Entails.sepExists_right st1 <|
    Entails.sepExists_right st2 <| Entails.sepExists_right st3 <|
    Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 28#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 27#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 26#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) <|
    by sep_entail

/-- Introduce an empty `ioVecBuf A 0#64 ptr []` (`ptr ≠ 0#64`). -/
theorem ioVecBuf_zero_intro {oom : State → State → Prop} (A : RustStdAlloc oom)
    {ptr : BitVec 64} (hptr : ptr ≠ 0#64) :
    emp ⊢ ioVecBuf A 0#64 ptr [] := by
  unfold ioVecBuf
  have hlt : (0#64 : BitVec 64).toNat < 2 ^ 63 := by decide
  rw [pure_sepConj_of_true ⟨Nat.le_refl 0, hlt, hptr⟩]
  simp only [↓reduceIte]
  exact Entails.refl emp

/-- Forget `bs` inside a positive-capacity `ioVecBuf` into `A.live ptr cap 1 ∗ memRegion ptr cap`
    for `__rust_dealloc`. -/
theorem ioVecBuf_entails_dealloc_mem {oom : State → State → Prop} (A : RustStdAlloc oom)
    {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (_hpos : 0 < cap) (hlt : cap < 2 ^ 63) :
    ioVecBuf A (BitVec.ofNat 64 cap) ptr bs ⊢ A.live ptr cap 1 ∗ memRegion ptr cap := by
  have hlt64 : cap < 2 ^ 64 := Nat.lt_trans hlt (by decide)
  have hto : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne : BitVec.ofNat 64 cap ≠ 0#64 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [hto] at this
    simp at this
    omega
  unfold ioVecBuf
  simp only [hto, hne, ↓reduceIte]
  refine Entails.pure_left fun ⟨hbs_le, _, _⟩ => ?_
  refine sepConj_mono_right ?_
  rw [memRegion_split_le ptr bs.length cap hbs_le (Nat.le_of_lt hlt64)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-- Convert `vecHeader sret 0xFFFFFFFFFFFFFFFF#64 p l` into the 24-byte `Err(())` layout
    `(sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16`. -/
theorem vecHeader_to_err_sret (sret p l : BitVec 64) :
    vecHeader sret 0xFFFFFFFFFFFFFFFF#64 p l ⊢
      (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16 := by
  unfold vecHeader
  refine sepConj_mono_right ?_
  rw [show (16 : Nat) = 8 * 2 by decide, memRegion_cells (sret + 8#64) 2 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right, bv_lin_norm]
  exact Entails.sepExists_right p (Entails.sepExists_right l (Entails.refl _))

theorem take_append_drop_take {α : Type} :
    ∀ (xs : List α) (len k : Nat), xs.take len ++ (xs.drop len).take k = xs.take (len + k)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: xs, len + 1, k => by
    simp [Nat.succ_add, take_append_drop_take xs len k]

theorem chunk_take_self {α : Type} (xs : List α) (n : Nat) :
    xs.take n = xs.take (xs.take n).length := by
  rw [List.length_take]
  by_cases h : n ≤ xs.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by omega), List.take_length]

/-- Unfold a positive-capacity `ioVecBuf` (`0 < cap < 2 ^ 63`). -/
theorem ioVecBuf_unpack_pos {oom : State → State → Prop} (A : RustStdAlloc oom)
    {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (hpos : 0 < cap) (hlt : cap < 2 ^ 63) :
    ioVecBuf A (BitVec.ofNat 64 cap) ptr bs =
      (⌜bs.length ≤ cap ∧ cap < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (A.live ptr cap 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length))) := by
  have hlt64 : cap < 2 ^ 64 := Nat.lt_trans hlt (by decide)
  have hto : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne : BitVec.ofNat 64 cap ≠ 0#64 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [hto] at this
    simp at this
    omega
  unfold ioVecBuf
  simp only [hto, hne, ↓reduceIte]

/-- Repack `ioVecBuf` after `memcpy(ptr + len, sp, chunk)` appends `chunk = (rem.drop len).take want`. -/
theorem ioVecBuf_repack_chunk {oom : State → State → Prop} (A : RustStdAlloc oom)
    {cap len want : Nat} {ptr : BitVec 64} {rem chunk : List (BitVec 8)}
    (hpos : 0 < cap) (hlt : cap < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hchunk : chunk = (rem.drop len).take want) :
    A.live ptr cap 1 ∗
      (ptr ↦ₛ rem.take len) ∗
      ((ptr + BitVec.ofNat 64 len) ↦ₛ chunk) ∗
      memRegion (ptr + BitVec.ofNat 64 (len + chunk.length)) (cap - (len + chunk.length)) ⊢
    ioVecBuf A (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) := by
  have happ : rem.take len ++ chunk = rem.take (len + chunk.length) := by
    rw [hchunk]
    conv => lhs; arg 2; rw [chunk_take_self (rem.drop len) want]
    rw [← hchunk]
    exact take_append_drop_take rem len chunk.length
  have htake_len : (rem.take len).length = len := List.length_take_of_le (by omega)
  have htake_len' : (rem.take (len + chunk.length)).length = len + chunk.length :=
    List.length_take_of_le hlen_r
  rw [ioVecBuf_unpack_pos A hpos hlt,
    pure_sepConj_of_true ⟨by rw [htake_len']; exact hlen_cap, hlt, hptr⟩,
    htake_len', ← happ,
    pointsToBytes_append ptr (rem.take len) chunk, htake_len]
  sep_entail

/-- Repack the `4096`-byte stack read buffer after `read` + `memcpy`. -/
theorem stackBuf4096_repack {buf : BitVec 64} {want : Nat} {chunk oldBuf : List (BitVec 8)}
    (hwant : want ≤ 4096) (hold : oldBuf.length = want) (hchunk : chunk.length ≤ want) :
    (buf ↦ₛ chunk) ∗
      ((buf + BitVec.ofNat 64 chunk.length) ↦ₛ oldBuf.drop chunk.length) ∗
      memRegion (buf + BitVec.ofNat 64 want) (4096 - want) ⊢
    memRegion buf 4096 := by
  have happ_len : (chunk ++ oldBuf.drop chunk.length).length = want := by
    simp [List.length_append, List.length_drop, hold]
    omega
  rw [← sepConj_assoc, ← pointsToBytes_append buf chunk (oldBuf.drop chunk.length)]
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion buf _)) ?_
  rw [happ_len, ← memRegion_split buf want (4096 - want) (by omega),
    show want + (4096 - want) = 4096 by omega]
  exact Entails.refl _

end StackHelpers

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
