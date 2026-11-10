/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib
public import ProofLib.SepLogic.CFG
public import ProofLib.SepLogic.WPp

/-!
# Loop and CFG Combinator Tests

Tests the continuation-in-context counter, well-founded, list-peeling, multi-cutpoint, and
panic-aware `SepWP` / `SepWPp` loop combinators and loop tactics (`wp_loop_measure`,
`wp_loop_list`, `wp_nested_loop`, `wp_call`, `wp_done`, `wp_steps`).
-/

@[expose] public section

namespace Testing.LoopCFGCombinators

open Arm64 ProofLib

set_option maxHeartbeats 400000
arm64_proof_prelude

/-! ## Counted CPS Loop -/

@[simp, arm64_norm] def count_loop_addr : BitVec 64 := 0x50000#64

/-- Counted accumulator subroutine at `0x50000`:
    * `0x50000`: `cbz x1, 0x50010`
    * `0x50004`: `add x0, x0, x2`
    * `0x50008`: `sub x1, x1, #1`
    * `0x5000c`: `b   0x50000`
    * `0x50010`: `ret` -/
def countLoopCode : FnCode :=
  .atAddr "count_loop" count_loop_addr
    ("b4000081 " ++ -- 0x50000: cbz x1, 0x50010
     "8b020000 " ++ -- 0x50004: add x0, x0, x2
     "d1000421 " ++ -- 0x50008: sub x1, x1, #1
     "17fffffd " ++ -- 0x5000c: b 0x50000
     "d65f03c0")    -- 0x50010: ret

@[simp]
def iterAdd (rem : Nat) (acc stride : BitVec 64) : BitVec 64 :=
  match rem with
  | 0 => acc
  | k + 1 => iterAdd k (acc + stride) stride

theorem count_loop_nat_cps_test (prog : Program) (h_code : countLoopCode.holds prog)
    (s0 : State) (rem : Nat) (acc stride : BitVec 64)
    (hrem : rem < 2 ^ 63)
    (hpc : s0.pc = 0x50000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rem)
    (hx2 : s0.readReg64 .x2 = stride) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = iterAdd rem acc stride ∧ sf.sp = s0.sp) emp) := by
  let Inv : Nat → BitVec 64 → State → Prop := fun k curAcc st =>
    k < 2 ^ 63 ∧
    st.readReg64 .x0 = curAcc ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x2 = stride ∧
    st.sp = s0.sp ∧
    st.readReg64 .lr = s0.readReg64 .lr
  let post : Nat → BitVec 64 → State → SepProp → Prop := fun k curAcc =>
    sepPost (fun sf => sf.readReg64 .x0 = iterAdd k curAcc stride ∧ sf.sp = s0.sp) emp
  refine SepWP.loop_nat_cps (fun _ _ _ => emp) Inv post
    (rem0 := rem) (g0 := acc) hpc hrun (Entails.refl _)
    ⟨hrem, hx0, hx1, hx2, rfl, rfl⟩ ?_ ?_
  · intro curAcc st hpc_s hrun_s ⟨_, hx0_s, hx1_s, _, hsp_s, hlr_s⟩
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
    exact ⟨⟨by simp [wp_norm, arm64_norm, hx0_s], hsp_s⟩, Entails.refl emp⟩
  · intro k curAcc st hpc_s hrun_s ⟨hk, hx0_s, hx1_s, hx2_s, hsp_s, hlr_s⟩ next
    have hk_nz : BitVec.ofNat 64 (k + 1) ≠ 0#64 := by bv_omega
    wp_step
    wp_if hcond
    · exact absurd hcond hk_nz
    · wp_step; wp_step; wp_step
      refine next (curAcc + stride) _
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_s])
        ⟨by omega,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]; bv_omega,
         by simp [wp_norm, arm64_norm, hx2_s],
         by simp [wp_norm, arm64_norm, hsp_s],
         by simp [wp_norm, arm64_norm, hlr_s]⟩

/-! ## Multi-Exit `do-while` Probe Loop -/

@[simp, arm64_norm] def probe_loop_addr : BitVec 64 := 0x51000#64

/-- Rotated (`do-while`) + mid-loop early-exit subroutine at `0x51000`:
    * `0x51000` (head): `add x0, x0, #1`
    * `0x51004`:        `cbz x2, 0x51010`
    * `0x51008`:        `sub x1, x1, #1`
    * `0x5100c`:        `cbnz x1, 0x51000`
    * `0x51010` (exit): `ret` -/
def probeLoopCode : FnCode :=
  .atAddr "probe_loop" probe_loop_addr
    ("91000400 " ++ -- 0x51000: add x0, x0, #1
     "b4000062 " ++ -- 0x51004: cbz x2, 0x51010
     "d1000421 " ++ -- 0x51008: sub x1, x1, #1
     "b5ffffa1 " ++ -- 0x5100c: cbnz x1, 0x51000
     "d65f03c0")    -- 0x51010: ret

@[simp]
def probeModel (rem : Nat) (acc flag : BitVec 64) : BitVec 64 :=
  if flag = 0#64 then
    acc + 1#64
  else
    match rem with
    | 0 => acc + 1#64
    | m' + 1 => probeModel m' (acc + 1#64) flag

theorem loop_wf_do_while_probe_test (prog : Program) (h_code : probeLoopCode.holds prog)
    (s0 : State) (rem : Nat) (acc flag : BitVec 64)
    (hrem : rem < 2 ^ 63 - 1)
    (hpc : s0.pc = 0x51000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (rem + 1))
    (hx2 : s0.readReg64 .x2 = flag) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = probeModel rem acc flag) emp) := by
  let Inv : (Nat × BitVec 64) → State → Prop := fun (m, curAcc) st =>
    m < 2 ^ 63 - 1 ∧
    st.readReg64 .x0 = curAcc ∧
    st.readReg64 .x1 = BitVec.ofNat 64 (m + 1) ∧
    st.readReg64 .x2 = flag ∧
    st.readReg64 .lr = s0.readReg64 .lr
  let post : (Nat × BitVec 64) → State → SepProp → Prop := fun (m, curAcc) =>
    sepPost (fun sf => sf.readReg64 .x0 = probeModel m curAcc flag) emp
  refine SepWP.loop_wf (fun g _ => g.1) (fun _ _ => emp) Inv post
    (g0 := (rem, acc)) hpc hrun (Entails.refl _) ⟨hrem, hx0, hx1, hx2, rfl⟩ ?_
  rintro ⟨m, curAcc⟩ st hpc_s hrun_s ⟨hm, hx0_s, hx1_s, hx2_s, hlr_s⟩ next
  wp_steps
  wp_if hexit
  · wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
    refine ⟨?_, Entails.refl emp⟩
    unfold probeModel
    simp [wp_norm, arm64_norm, hexit]
  · wp_steps
    wp_if hback
    ·
      have hm_pos : 0 < m := by bv_omega
      have hm_eq : m - 1 + 1 = m := by omega
      exact SepWP.loop_back next (m - 1, curAcc + 1#64) (by omega)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_s])
        ⟨by omega,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hm_eq]; bv_omega,
         by simp [wp_norm, arm64_norm, hx2_s],
         by simp [wp_norm, arm64_norm, hlr_s]⟩
        emp (by sep_frame)
        (by
          intro sf P_f _ _ ⟨hr, hQ⟩
          refine ⟨?_, by rw [sepConj_emp]; exact hQ⟩
          cases m with
          | zero => omega
          | succ m' =>
            unfold probeModel
            simpa [hexit] using hr)
    ·
      have hm0 : m = 0 := by bv_omega
      subst hm0
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
      refine ⟨?_, Entails.refl emp⟩
      unfold probeModel
      simp [wp_norm, arm64_norm, hexit]

/-! ## List-Peeling Loop -/

@[simp, arm64_norm] def slice_sum_addr : BitVec 64 := 0x52000#64

/-- Word-array sum subroutine at `0x52000`:
    * `0x52000`: `cbz x1, 0x52018`
    * `0x52004`: `ldr x3, [x0]`
    * `0x52008`: `add x2, x2, x3`
    * `0x5200c`: `add x0, x0, #8`
    * `0x52010`: `sub x1, x1, #1`
    * `0x52014`: `b   0x52000`
    * `0x52018`: `ret` -/
def sliceSumCode : FnCode :=
  .atAddr "slice_sum" slice_sum_addr
    ("b40000c1 " ++ -- 0x52000: cbz x1, 0x52018
     "f9400003 " ++ -- 0x52004: ldr x3, [x0]
     "8b030042 " ++ -- 0x52008: add x2, x2, x3
     "91002000 " ++ -- 0x5200c: add x0, x0, #8
     "d1000421 " ++ -- 0x52010: sub x1, x1, #1
     "17fffffb " ++ -- 0x52014: b 0x52000
     "d65f03c0")    -- 0x52018: ret

@[simp]
def sumWords (xs : List (BitVec 64)) (acc : BitVec 64) : BitVec 64 :=
  match xs with
  | [] => acc
  | x :: rest => sumWords rest (acc + x)

theorem loop_list_peel_cps_test (prog : Program) (h_code : sliceSumCode.holds prog)
    (s0 : State) (ptr : BitVec 64) (xs : List (BitVec 64))
    (acc : BitVec 64) (hlen : xs.length < 2 ^ 63)
    (hpc : s0.pc = 0x52000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 xs.length)
    (hx2 : s0.readReg64 .x2 = acc) :
    SepWP prog (s0.readReg64 .lr) s0 (pointsToWords64 ptr xs)
      (sepPost (fun sf => sf.readReg64 .x2 = sumWords xs acc) (pointsToWords64 ptr xs)) := by
  let Inv : List (BitVec 64) → (BitVec 64 × BitVec 64) → State → Prop :=
    fun rem g st =>
      rem.length < 2 ^ 63 ∧
      st.readReg64 .x0 = g.1 ∧
      st.readReg64 .x1 = BitVec.ofNat 64 rem.length ∧
      st.readReg64 .x2 = g.2 ∧
      st.readReg64 .lr = s0.readReg64 .lr
  let post : List (BitVec 64) → (BitVec 64 × BitVec 64) → State → SepProp → Prop :=
    fun rem g =>
      sepPost (fun sf => sf.readReg64 .x2 = sumWords rem g.2) (pointsToWords64 g.1 rem)
  refine SepWP.loop_list_peel_cps (fun rem g _ => pointsToWords64 g.1 rem) Inv post
    (xs0 := xs) (g0 := (ptr, acc)) hpc hrun (Entails.refl _) ⟨hlen, hx0, hx1, hx2, rfl⟩ ?_ ?_
  · rintro ⟨curPtr, curAcc⟩ st hpc_s hrun_s ⟨_, _, hx1_s, hx2_s, hlr_s⟩
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
    exact ⟨by simp [wp_norm, arm64_norm, hx2_s], Entails.refl _⟩
  · rintro x rest ⟨curPtr, curAcc⟩ st hpc_s hrun_s ⟨hlen_c, hx0_s, hx1_s, hx2_s, hlr_s⟩ next
    have hlen_c' : rest.length + 1 < 2 ^ 63 := by simpa using hlen_c
    have hnz : BitVec.ofNat 64 (rest.length + 1) ≠ 0#64 := by
      intro hz
      have h1 := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat] at h1
      omega
    dsimp only
    rw [pointsToWords64_cons]
    wp_step
    wp_if hcond
    · exact absurd hcond hnz
    · wp_step; wp_step; wp_step; wp_step; wp_step
      refine next (curPtr + 8#64, curAcc + x) _ (curPtr ↦₆₄ x)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_s])
        ⟨by omega,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]; bv_omega,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hlr_s]⟩
        (by sep_frame) ?_
      intro sf P_f _ _ ⟨hr, hQ⟩
      refine ⟨hr, ?_⟩
      dsimp only
      rw [pointsToWords64_cons]
      exact Entails.trans (sepConj_mono_left hQ) (by sep_frame)

/-! ## Panic-Aware `SepWPp` Loop -/

theorem sepWPp_loop_wf_test (prog : Program) (h_code : countLoopCode.holds prog)
    (s0 : State) (rem : Nat) (acc stride : BitVec 64)
    (hrem : rem < 2 ^ 63)
    (hpc : s0.pc = 0x50000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rem)
    (hx2 : s0.readReg64 .x2 = stride) :
    SepWPp prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = iterAdd rem acc stride ∧ sf.sp = s0.sp) emp)
      (fun _ _ => False) := by
  let Inv : (Nat × BitVec 64) → State → Prop := fun (k, curAcc) st =>
    k < 2 ^ 63 ∧
    st.readReg64 .x0 = curAcc ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x2 = stride ∧
    st.sp = s0.sp ∧
    st.readReg64 .lr = s0.readReg64 .lr
  let Q : (Nat × BitVec 64) → State → SepProp → Prop := fun (k, curAcc) =>
    sepPost (fun sf => sf.readReg64 .x0 = iterAdd k curAcc stride ∧ sf.sp = s0.sp) emp
  refine SepWPp.loop_wf (fun g _ => g.1) (fun _ _ => emp) Inv Q (fun _ _ => False)
    (g0 := (rem, acc)) hpc hrun (Entails.refl _) ⟨hrem, hx0, hx1, hx2, rfl, rfl⟩ ?_
  rintro ⟨k, curAcc⟩ st hpc_s hrun_s ⟨hk, hx0_s, hx1_s, hx2_s, hsp_s, hlr_s⟩ next
  cases k with
  | zero =>
    refine SepWPp.of_sepWP_ret ?_
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
    exact ⟨⟨by simp [wp_norm, arm64_norm, hx0_s], hsp_s⟩, Entails.refl emp⟩
  | succ k' =>
    have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
    refine SepWPp.bind_sepWP (mid_pc := 0x50000#64) (P1 := emp) (Q1 := emp) (F := emp)
      (Inv1 := Inv (k', curAcc + stride)) ?_ (by sep_frame) ?_
    · wp_step
      wp_if hcond
      · exact absurd hcond hk_nz
      · wp_step; wp_step; wp_step
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
        exact ⟨⟨by omega,
                by simp [wp_norm, arm64_norm],
                by simp [wp_norm, arm64_norm]; bv_omega,
                by simp [wp_norm, arm64_norm, hx2_s],
                by simp [wp_norm, arm64_norm, hsp_s],
                by simp [wp_norm, arm64_norm, hlr_s]⟩,
               Entails.refl emp⟩
    · intro s1 hpc1 hrun1 hinv1
      exact SepWPp.loop_back next (k', curAcc + stride) (by omega) hpc1 hrun1 hinv1

/-! ## Two-Cutpoint List-Peeling Loop -/

@[simp, arm64_norm] def latch_loop_addr : BitVec 64 := 0x53000#64
@[simp, arm64_norm] def latch_cut_addr : BitVec 64 := 0x53008#64

/-- Non-empty slice accumulator at `0x53000` split across `head_pc = 0x53000` and `latch_pc = 0x53008`:
    * `0x53000` (head):  `ldr x3, [x0]`
    * `0x53004`:         `add x2, x2, x3`
    * `0x53008` (latch): `add x0, x0, #8`
    * `0x5300c`:         `sub x1, x1, #1`
    * `0x53010`:         `cbnz x1, 0x53000`
    * `0x53014` (exit):  `ret` -/
def latchSumCode : FnCode :=
  .atAddr "latch_sum" latch_loop_addr
    ("f9400003 " ++ -- 0x53000: ldr x3, [x0]
     "8b030042 " ++ -- 0x53004: add x2, x2, x3
     "91002000 " ++ -- 0x53008: add x0, x0, #8
     "d1000421 " ++ -- 0x5300c: sub x1, x1, #1
     "b5ffff81 " ++ -- 0x53010: cbnz x1, 0x53000
     "d65f03c0")    -- 0x53014: ret

theorem loop_list_peel_latch_test (prog : Program) (h_code : latchSumCode.holds prog)
    (s0 : State) (ptr : BitVec 64) (x0_elem : BitVec 64) (rest0 : List (BitVec 64))
    (acc : BitVec 64) (hlen : rest0.length + 1 < 2 ^ 63)
    (hpc : s0.pc = latch_loop_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (rest0.length + 1))
    (hx2 : s0.readReg64 .x2 = acc) :
    SepWP prog (s0.readReg64 .lr) s0 (pointsToWords64 ptr (x0_elem :: rest0))
      (sepPost (fun sf => sf.readReg64 .x2 = sumWords (x0_elem :: rest0) acc)
        (pointsToWords64 ptr (x0_elem :: rest0))) := by
  let step : BitVec 64 → (BitVec 64 × BitVec 64) → (BitVec 64 × BitVec 64) :=
    fun x g => (g.1 + 8#64, g.2 + x)
  let P_head : BitVec 64 → List (BitVec 64) → (BitVec 64 × BitVec 64) → SepProp :=
    fun x rest g => pointsToWords64 g.1 (x :: rest)
  let P_latch : BitVec 64 → List (BitVec 64) → (BitVec 64 × BitVec 64) → SepProp :=
    fun x rest g => pointsToWords64 (g.1 - 8#64) (x :: rest)
  let F_peel : BitVec 64 → (BitVec 64 × BitVec 64) → SepProp :=
    fun x g => (g.1 ↦₆₄ x)
  let Q_out : List (BitVec 64) → (BitVec 64 × BitVec 64) → SepProp :=
    fun xs g => pointsToWords64 g.1 xs
  let Inv_head : BitVec 64 → List (BitVec 64) → (BitVec 64 × BitVec 64) → State → Prop :=
    fun _ rest g st =>
      rest.length + 1 < 2 ^ 63 ∧
      st.readReg64 .x0 = g.1 ∧
      st.readReg64 .x1 = BitVec.ofNat 64 (rest.length + 1) ∧
      st.readReg64 .x2 = g.2 ∧
      st.readReg64 .lr = s0.readReg64 .lr
  let Inv_latch : BitVec 64 → List (BitVec 64) → (BitVec 64 × BitVec 64) → State → Prop :=
    fun _ rest g st =>
      rest.length + 1 < 2 ^ 63 ∧
      st.readReg64 .x0 = g.1 - 8#64 ∧
      st.readReg64 .x1 = BitVec.ofNat 64 (rest.length + 1) ∧
      st.readReg64 .x2 = g.2 ∧
      st.readReg64 .lr = s0.readReg64 .lr
  let Post_out : List (BitVec 64) → (BitVec 64 × BitVec 64) → State → Prop :=
    fun xs g sf => sf.readReg64 .x2 = sumWords xs g.2
  refine SepWP.loop_list_peel_latch (head_pc := latch_loop_addr) (latch_pc := latch_cut_addr)
    (exit_pc := s0.readReg64 .lr) step P_head P_latch F_peel Q_out Inv_head Inv_latch Post_out
    ?hbody ?hlatch_nil ?hlatch_cons ?hreassemble ?hpost_imp
    (fun _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
    x0_elem rest0 (ptr, acc) s0
    hpc hrun ⟨hlen, hx0, hx1, hx2, rfl⟩
  case hbody =>
    rintro x rest ⟨curPtr, curAcc⟩ st hpc_s hrun_s ⟨hlen_c, hx0_s, hx1_s, hx2_s, hlr_s⟩
    dsimp only [P_head, P_latch, step] at *
    rw [pointsToWords64_cons]
    refine SepWP.bind_sepPost (mid_pc := 0x53004#64)
      (P1 := (curPtr ↦₆₄ x)) (Q1 := (curPtr ↦₆₄ x)) (F := pointsToWords64 (curPtr + 8#64) rest)
      (Inv1 := fun s1 =>
        s1.readReg64 .x0 = curPtr ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 (rest.length + 1) ∧
        s1.readReg64 .x2 = curAcc ∧
        s1.readReg64 .x3 = x ∧
        s1.readReg64 .lr = s0.readReg64 .lr)
      ?_ (by sep_frame) ?_
    · wp_step
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
      exact ⟨⟨by simp [wp_norm, arm64_norm, hx0_s],
              by simp [wp_norm, arm64_norm, hx1_s],
              by simp [wp_norm, arm64_norm, hx2_s],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm, hlr_s]⟩,
             Entails.refl _⟩
    · intro s1 hpc1 hrun1 ⟨hx0_1, hx1_1, hx2_1, hx3_1, hlr_1⟩
      wp_step
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) ?_
      refine ⟨⟨hlen_c,
               by simp [wp_norm, arm64_norm, hx0_1],
               by simp [wp_norm, arm64_norm, hx1_1],
               by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm, hlr_1]⟩,
              ?_⟩
      have hptr_sub : curPtr + 8#64 - 8#64 = curPtr := by bv_omega
      rw [hptr_sub, pointsToWords64_cons]
      sep_frame
  case hlatch_nil =>
    rintro x ⟨curPtr, curAcc⟩ sm hpcm hrunm ⟨_, hx0_m, hx1_m, hx2_m, hlr_m⟩
    have hptr_sub : curPtr + 8#64 - 8#64 = curPtr := by bv_omega
    dsimp only [P_latch, Q_out, Post_out, step] at *
    rw [hptr_sub] at hx0_m ⊢
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunm]) ?_
    exact ⟨by simp [wp_norm, arm64_norm, hx2_m], Entails.refl _⟩
  case hlatch_cons =>
    rintro x y rest ⟨curPtr, curAcc⟩ sm hpcm hrunm ⟨hlen_m, hx0_m, hx1_m, hx2_m, hlr_m⟩
    dsimp only [P_latch, P_head, F_peel, step] at *
    simp only [List.length_cons] at hlen_m hx1_m
    have hptr_sub : curPtr + 8#64 - 8#64 = curPtr := by bv_omega
    have hnz : BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64 ≠ 0#64 := by bv_omega
    rw [hptr_sub] at hx0_m ⊢
    rw [pointsToWords64_cons]
    wp_step; wp_step; wp_step
    wp_if hcond
    · refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrunm]) ?_
      exact ⟨⟨by omega,
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm]; bv_omega,
              by simp [wp_norm, arm64_norm, hx2_m],
              by simp [wp_norm, arm64_norm, hlr_m]⟩,
             by sep_frame⟩
    · exact absurd hcond hnz
  case hreassemble =>
    intro x y rest ⟨curPtr, _⟩
    dsimp only [Q_out, F_peel, step]
    rw [pointsToWords64_cons (a := curPtr)]
    sep_frame
  case hpost_imp =>
    intro x y rest ⟨_, curAcc⟩ sf hp
    exact hp

/-! ## Multi-Cutpoint Mutual CFG -/

@[simp, arm64_norm] def even_cut_addr : BitVec 64 := 0x54000#64
@[simp, arm64_norm] def odd_cut_addr : BitVec 64 := 0x54010#64

/-- Mutual two-cutpoint state machine (`even_cut_addr = 0x54000`, `odd_cut_addr = 0x54010`):
    * `0x54000` (even): `cbz x1, 0x54020`; `add x0, x0, #1`; `sub x1, x1, #1`; `b 0x54010`
    * `0x54010` (odd):  `cbz x1, 0x54020`; `add x0, x0, #2`; `sub x1, x1, #1`; `b 0x54000`
    * `0x54020` (exit): `ret` -/
def parityCfgCode : FnCode :=
  .atAddr "parity_cfg" even_cut_addr
    ("b4000101 " ++ -- 0x54000: cbz x1, 0x54020
     "91000400 " ++ -- 0x54004: add x0, x0, #1
     "d1000421 " ++ -- 0x54008: sub x1, x1, #1
     "14000001 " ++ -- 0x5400c: b 0x54010
     "b4000081 " ++ -- 0x54010: cbz x1, 0x54020
     "91000800 " ++ -- 0x54014: add x0, x0, #2
     "d1000421 " ++ -- 0x54018: sub x1, x1, #1
     "17fffff9 " ++ -- 0x5401c: b 0x54000
     "d65f03c0")    -- 0x54020: ret

@[simp]
def parityModel : Nat → Bool → BitVec 64 → BitVec 64
  | 0, _, acc => acc
  | k + 1, false, acc => parityModel k true (acc + 1#64)
  | k + 1, true, acc => parityModel k false (acc + 2#64)

theorem cfg_fixpoint_wf_cps_test (prog : Program) (h_code : parityCfgCode.holds prog)
    (s0 : State) (rem : Nat) (acc : BitVec 64)
    (hrem : rem < 2 ^ 63)
    (hpc : s0.pc = even_cut_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rem) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = parityModel rem false acc) emp) := by
  let cut_pc : (Bool × Nat × BitVec 64) → BitVec 64 :=
    fun (isOdd, _, _) => if isOdd then odd_cut_addr else even_cut_addr
  let Inv : (Bool × Nat × BitVec 64) → State → Prop :=
    fun (_, k, curAcc) st =>
      k < 2 ^ 63 ∧
      st.readReg64 .x0 = curAcc ∧
      st.readReg64 .x1 = BitVec.ofNat 64 k ∧
      st.readReg64 .lr = s0.readReg64 .lr
  let post : (Bool × Nat × BitVec 64) → State → SepProp → Prop :=
    fun (isOdd, k, curAcc) =>
      sepPost (fun sf => sf.readReg64 .x0 = parityModel k isOdd curAcc) emp
  refine SepWP.cfg_fixpoint_wf_cps cut_pc (fun (_, k, _) _ => k) (fun _ _ => emp) Inv post
    (l0 := (false, rem, acc)) hpc hrun (Entails.refl _) ⟨hrem, hx0, hx1, rfl⟩ ?_
  rintro ⟨isOdd, k, curAcc⟩ st hpc_s hrun_s ⟨hk, hx0_s, hx1_s, hlr_s⟩ next
  cases isOdd
  · dsimp only [cut_pc] at *
    cases k with
    | zero =>
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
      exact ⟨by simp [wp_norm, arm64_norm, hx0_s], Entails.refl emp⟩
    | succ k' =>
      have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
      wp_step
      wp_if hcond
      · exact absurd hcond hk_nz
      · wp_step; wp_step; wp_step
        exact next (true, k', curAcc + 1#64) _ (by simp)
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun_s])
          ⟨by omega,
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm]; bv_omega,
           by simp [wp_norm, arm64_norm, hlr_s]⟩
  · dsimp only [cut_pc] at *
    cases k with
    | zero =>
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
      exact ⟨by simp [wp_norm, arm64_norm, hx0_s], Entails.refl emp⟩
    | succ k' =>
      have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
      wp_step
      wp_if hcond
      · exact absurd hcond hk_nz
      · wp_step; wp_step; wp_step
        exact next (false, k', curAcc + 2#64) _ (by simp)
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun_s])
          ⟨by omega,
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm]; bv_omega,
           by simp [wp_norm, arm64_norm, hlr_s]⟩

/-! ## Panic-Aware `SepWPp` Loop with Non-Empty Panic Postcondition -/

@[simp, arm64_norm] def checked_loop_addr : BitVec 64 := 0x55000#64
@[simp, arm64_norm] def panic_stub_addr : BitVec 64 := 0x55018#64

/-- Checked loop at `0x55000` that jumps to a `Rust.panicked` stub at `0x55018` when `x2 = 0`:
    * `0x55000`: `cbz x1, 0x55014`
    * `0x55004`: `cbz x2, 0x55018`
    * `0x55008`: `add x0, x0, #1`
    * `0x5500c`: `sub x1, x1, #1`
    * `0x55010`: `b   0x55000`
    * `0x55014`: `ret` -/
def checkedLoopCode : FnCode :=
  .atAddr "checked_loop" checked_loop_addr
    ("b40000a1 " ++ -- 0x55000: cbz x1, 0x55014
     "b40000a2 " ++ -- 0x55004: cbz x2, 0x55018
     "91000400 " ++ -- 0x55008: add x0, x0, #1
     "d1000421 " ++ -- 0x5500c: sub x1, x1, #1
     "17fffffc " ++ -- 0x55010: b 0x55000
     "d65f03c0")    -- 0x55014: ret

theorem sepWPp_loop_wf_panic_test (prog : Program) (h_code : checkedLoopCode.holds prog)
    (h_panic : prog.externAt? panic_stub_addr = some Rust.panicked)
    (s0 : State) (buf : BitVec 64) (v : BitVec 64) (rem : Nat) (acc flag : BitVec 64)
    (hrem : rem < 2 ^ 63)
    (hpc : s0.pc = checked_loop_addr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rem)
    (hx2 : s0.readReg64 .x2 = flag) :
    SepWPp prog (s0.readReg64 .lr) s0 (buf ↦₆₄ v)
      (sepPost (fun sf => sf.readReg64 .x0 = iterAdd rem acc 1#64) (buf ↦₆₄ v))
      (sepPost (fun sp => sp.readReg64 .x2 = 0#64) (buf ↦₆₄ v)) := by
  let Inv : (Nat × BitVec 64) → State → Prop := fun (k, curAcc) st =>
    k < 2 ^ 63 ∧
    st.readReg64 .x0 = curAcc ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x2 = flag ∧
    st.readReg64 .lr = s0.readReg64 .lr
  let Q : (Nat × BitVec 64) → State → SepProp → Prop := fun (k, curAcc) =>
    sepPost (fun sf => sf.readReg64 .x0 = iterAdd k curAcc 1#64) (buf ↦₆₄ v)
  let Qp : State → SepProp → Prop :=
    sepPost (fun sp => sp.readReg64 .x2 = 0#64) (buf ↦₆₄ v)
  refine SepWPp.loop_wf (fun g _ => g.1) (fun _ _ => buf ↦₆₄ v) Inv Q Qp
    (g0 := (rem, acc)) hpc hrun (Entails.refl _) ⟨hrem, hx0, hx1, hx2, rfl⟩ ?_
  rintro ⟨k, curAcc⟩ st hpc_s hrun_s ⟨hk, hx0_s, hx1_s, hx2_s, hlr_s⟩ next
  cases k with
  | zero =>
    refine SepWPp.of_sepWP_ret ?_
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
    exact ⟨by simp [wp_norm, arm64_norm, hx0_s], Entails.refl _⟩
  | succ k' =>
    have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
    by_cases hflag : flag = 0#64
    ·
      subst hflag
      refine SepWPp.bind_sepWP (mid_pc := panic_stub_addr)
        (P1 := emp) (Q1 := emp) (F := (buf ↦₆₄ v))
        (Inv1 := fun s1 => s1.readReg64 .x2 = 0#64) ?_ (by sep_frame) ?_
      · wp_step
        wp_if hcond
        · exact absurd hcond hk_nz
        · wp_step
          refine SepWP.done (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun_s]) ?_
          exact ⟨by simp [wp_norm, arm64_norm, hx2_s], Entails.refl emp⟩
      · intro s1 hpc1 hrun1 hx2_1
        rw [emp_sepConj]
        refine SepWPp.panic hrun1 (hpc1 ▸ h_panic) ?_
        exact ⟨hx2_1, Entails.refl _⟩
    ·
      refine SepWPp.bind_sepWP (mid_pc := checked_loop_addr)
        (P1 := emp) (Q1 := emp) (F := (buf ↦₆₄ v))
        (Inv1 := Inv (k', curAcc + 1#64)) ?_ (by sep_frame) ?_
      · wp_step
        wp_if hcond
        · exact absurd hcond hk_nz
        · wp_step
          wp_if hcond2
          · exact absurd hcond2 hflag
          · wp_step; wp_step; wp_step
            refine SepWP.done (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hrun_s]) ?_
            exact ⟨⟨by omega,
                    by simp [wp_norm, arm64_norm],
                    by simp [wp_norm, arm64_norm]; bv_omega,
                    by simp [wp_norm, arm64_norm, hx2_s],
                    by simp [wp_norm, arm64_norm, hlr_s]⟩,
                   Entails.refl emp⟩
      · intro s1 hpc1 hrun1 hinv1
        rw [emp_sepConj]
        exact SepWPp.loop_back next (k', curAcc + 1#64) (by omega) hpc1 hrun1 hinv1

/-! ## Loop Tactic Front-Ends -/

/-- `wp_loop_measure frame` on `countLoopCode`: `frame` threads `sp`, `lr`, and callee-saved
    registers across the loop invariant. -/
theorem wp_loop_measure_count_test (prog : Program) (h_code : countLoopCode.holds prog)
    (s0 : State) (rem : Nat) (acc stride : BitVec 64)
    (hrem : rem < 2 ^ 63)
    (hpc : s0.pc = 0x50000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rem)
    (hx2 : s0.readReg64 .x2 = stride) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = iterAdd rem acc stride ∧ sf.sp = s0.sp) emp) := by
  wp_loop_measure frame rem (fun k st =>
    k < 2 ^ 63 ∧ st.readReg64 .x1 = BitVec.ofNat 64 k ∧ st.readReg64 .x2 = stride ∧
      iterAdd k (st.readReg64 .x0) stride = iterAdd rem acc stride)
  case base =>
    simp only [iterAdd] at *
    wp_steps
    wp_done
  case step =>
    right
    have hk_nz : BitVec.ofNat 64 (m' + 1) ≠ 0#64 := by bv_omega
    simp only [iterAdd] at *
    wp_steps
    wp_done

/-- `wp_loop_list` on `countLoopCode`, indexed by a list of `rem` unit cursors. -/
theorem wp_loop_list_count_test (prog : Program) (h_code : countLoopCode.holds prog)
    (s0 : State) (xs : List Unit) (acc stride : BitVec 64)
    (hlen : xs.length < 2 ^ 63)
    (hpc : s0.pc = 0x50000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 xs.length)
    (hx2 : s0.readReg64 .x2 = stride) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = iterAdd xs.length acc stride) emp) := by
  wp_loop_list xs (fun l st =>
    l.length < 2 ^ 63 ∧ st.readReg64 .x1 = BitVec.ofNat 64 l.length ∧
      st.readReg64 .x2 = stride ∧ st.readReg64 .lr = s0.readReg64 .lr ∧
      iterAdd l.length (st.readReg64 .x0) stride = iterAdd xs.length acc stride)
  case nil =>
    simp only [List.length_nil, iterAdd] at *
    wp_steps
    wp_done
  case cons =>
    right
    simp only [List.length_cons, iterAdd] at *
    have hk_nz : BitVec.ofNat 64 (rest.length + 1) ≠ 0#64 := by bv_omega
    wp_steps
    wp_done

-- Negative: `wp_loop_measure` refuses a loop header that is still an unresolved conditional
-- branch (here the `cbz x1` at `0x50000` was stepped without knowing `x1`).
/--
error: loop tactic: the current PC is an unresolved conditional branch, so the loop header cannot be determined:
  condition: (s0.readReg64 (Reg.gpr 1#5) == 0#64) = true
  then PC:   0x50010#64
  else PC:   0x50004#64
hint: `wp_step` / `wp_steps` already stepped the loop header's entry branch (`cbz` / `b.cond`), so `wp_loop_measure` / `wp_loop_list` / `wp_nested_loop` must be called at `head_pc` before stepping the header branch; otherwise, if both branches are reachable, split with `wp_if hcond` (or `wp_if_join <join_pc> <inv>`), or if only one branch is feasible, prove `have hcond : <cond> = true := by bv_omega` (or `= false`) before `wp_steps` / `wp_sym_steps` (or simplify the current PC with `wp_simp_pre [hcond]`)
-/
#guard_msgs (error, drop info, drop warning) in
example (prog : Program) (h_code : countLoopCode.holds prog) (s0 : State)
    (hpc : s0.pc = 0x50000#64) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (sepPost (fun _ => True) emp) := by
  wp_step
  wp_loop_measure 0 (fun _ _ => True)

@[simp, arm64_norm] def nested_loop_addr : BitVec 64 := 0x5a000#64

/-- Nested counting loop at `0x5a000` (adds `rows * cols` to `x0`):
    * `0x5a000` (outer head): `cbz x1, 0x5a020`
    * `0x5a004`:              `mov x3, x2`
    * `0x5a008` (inner head): `cbz x3, 0x5a018`
    * `0x5a00c`:              `add x0, x0, #1`
    * `0x5a010`:              `sub x3, x3, #1`
    * `0x5a014`:              `b   0x5a008`
    * `0x5a018` (inner exit): `sub x1, x1, #1`
    * `0x5a01c`:              `b   0x5a000`
    * `0x5a020` (exit):       `ret` -/
def nestedLoopCode : FnCode :=
  .atAddr "nested_loop" nested_loop_addr
    ("b4000101 " ++ -- 0x5a000: cbz x1, 0x5a020
     "aa0203e3 " ++ -- 0x5a004: mov x3, x2
     "b4000083 " ++ -- 0x5a008: cbz x3, 0x5a018
     "91000400 " ++ -- 0x5a00c: add x0, x0, #1
     "d1000463 " ++ -- 0x5a010: sub x3, x3, #1
     "17fffffd " ++ -- 0x5a014: b 0x5a008
     "d1000421 " ++ -- 0x5a018: sub x1, x1, #1
     "17fffff9 " ++ -- 0x5a01c: b 0x5a000
     "d65f03c0")    -- 0x5a020: ret

/-- Inner-loop model of `nestedLoopCode`: add `1` to `a`, `j` times. -/
@[simp]
def innerAdd : Nat → BitVec 64 → BitVec 64
  | 0, a => a
  | j + 1, a => innerAdd j (a + 1#64)

/-- Outer-loop model of `nestedLoopCode`: run the inner loop `k` times. -/
@[simp]
def outerAdd (cols : Nat) : Nat → BitVec 64 → BitVec 64
  | 0, a => a
  | k + 1, a => outerAdd cols k (innerAdd cols a)

/-- `wp_nested_loop` on `nestedLoopCode`, closing the inner loop with a nested
    `wp_loop_measure`. -/
theorem wp_nested_loop_test (prog : Program) (h_code : nestedLoopCode.holds prog)
    (s0 : State) (rows cols : Nat) (acc : BitVec 64)
    (hrows : rows < 2 ^ 63) (hcols : cols < 2 ^ 63)
    (hpc : s0.pc = 0x5a000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 rows)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 cols) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = outerAdd cols rows acc) emp) := by
  wp_nested_loop rows 0x5a008#64 0x5a018#64
    (fun k st => k < 2 ^ 63 ∧ st.readReg64 .x2 = BitVec.ofNat 64 cols ∧
      st.readReg64 .lr = s0.readReg64 .lr ∧ st.readReg64 .x1 = BitVec.ofNat 64 k ∧
      outerAdd cols k (st.readReg64 .x0) = outerAdd cols rows acc)
    (fun k st => k + 1 < 2 ^ 63 ∧ st.readReg64 .x2 = BitVec.ofNat 64 cols ∧
      st.readReg64 .lr = s0.readReg64 .lr ∧ st.readReg64 .x1 = BitVec.ofNat 64 (k + 1) ∧
      st.readReg64 .x3 = BitVec.ofNat 64 cols ∧
      outerAdd cols k (innerAdd cols (st.readReg64 .x0)) = outerAdd cols rows acc)
    (fun k st => k + 1 < 2 ^ 63 ∧ st.readReg64 .x2 = BitVec.ofNat 64 cols ∧
      st.readReg64 .lr = s0.readReg64 .lr ∧ st.readReg64 .x1 = BitVec.ofNat 64 (k + 1) ∧
      outerAdd cols k (st.readReg64 .x0) = outerAdd cols rows acc)
  case done =>
    simp only [outerAdd] at *
    wp_steps
    wp_done
  case enter =>
    right; right
    have hk_nz : BitVec.ofNat 64 (k + 1) ≠ 0#64 := by bv_omega
    simp only [outerAdd] at *
    wp_steps
    wp_done
  case inner =>
    wp_loop_measure cols (fun j st' => j < 2 ^ 63 ∧ k + 1 < 2 ^ 63 ∧
      st'.readReg64 .x2 = BitVec.ofNat 64 cols ∧ st'.readReg64 .lr = s0.readReg64 .lr ∧
      st'.readReg64 .x1 = BitVec.ofNat 64 (k + 1) ∧ st'.readReg64 .x3 = BitVec.ofNat 64 j ∧
      outerAdd cols k (innerAdd j (st'.readReg64 .x0)) = outerAdd cols rows acc)
    case base =>
      simp only [innerAdd] at *
      wp_steps
      wp_done
    case step =>
      right
      have hj_nz : BitVec.ofNat 64 (m' + 1) ≠ 0#64 := by bv_omega
      simp only [innerAdd] at *
      wp_steps
      wp_done
  case latch =>
    have hk_sub : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by bv_omega
    wp_steps
    wp_done

/-! ## `wp_call`, `wp_done`, and `wp_steps` Behavior Tests -/

section TacticBehaviorImprovements

@[simp, arm64_norm] def beh_callee_addr : BitVec 64 := 0x5b000#64
@[simp, arm64_norm] def beh_caller_addr : BitVec 64 := 0x5b100#64
@[simp, arm64_norm] def beh_branch_addr : BitVec 64 := 0x5b200#64

/-- Simple callee at `0x5b000`: `mov x0, #7; ret`. -/
def behCalleeCode : FnCode :=
  .atAddr "beh_callee" beh_callee_addr
    ("d28000e0 " ++ -- 0x5b000: mov x0, #7
     "d65f03c0")    -- 0x5b004: ret

/-- Caller at `0x5b100`: `mov x1, #1; bl 0x5b000; ret` (without `stp`/`ldp` so `sp` stays `s0.sp`). -/
def behCallerCode : FnCode :=
  .atAddr "beh_caller" beh_caller_addr
    ("d2800021 " ++ -- 0x5b100: mov x1, #1
     "97ffffbf " ++ -- 0x5b104: bl 0x5b000 (offset -0x104 = -65 insns)
     "d65f03c0")    -- 0x5b108: ret

/-- Conditional branch fixture at `0x5b200`:
    * `0x5b200`: `cbz x0, 0x5b20c`
    * `0x5b204`: `mov x0, #1`
    * `0x5b208`: `ret`
    * `0x5b20c`: `mov x0, #2`
    * `0x5b210`: `ret` -/
def behBranchCode : FnCode :=
  .atAddr "beh_branch" beh_branch_addr
    ("b4000060 " ++ -- 0x5b200: cbz x0, 0x5b20c
     "d2800020 " ++ -- 0x5b204: mov x0, #1
     "d65f03c0 " ++ -- 0x5b208: ret
     "d2800040 " ++ -- 0x5b20c: mov x0, #2
     "d65f03c0")    -- 0x5b210: ret

abbrev behCalleeSpec : Spec Unit :=
  Spec.split (fun u _ => u = ()) (fun _ => emp)
    (fun _ s0 sf => sf.readReg64 .x0 = 7#64 ∧ sf.sp = s0.sp) (fun _ => emp)

-- `wp_call` steps to the `BL` target `0x5b000` when `proofLib.wpCallAutoStep` is enabled.
example (prog : Program) (h_code : behCallerCode.holds prog) (s0 : State)
    (hpc : s0.pc = beh_caller_addr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h_callee : subroutine_ok prog beh_callee_addr behCalleeSpec) :
    SepWP prog 0x5b108#64 s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 7#64) emp) := by
  wp_call h_callee ()
  wp_done

-- Bare `wp_call` resolves `h_callee` from local context.
example (prog : Program) (h_code : behCallerCode.holds prog) (s0 : State)
    (hpc : s0.pc = beh_caller_addr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h_callee : subroutine_ok prog beh_callee_addr behCalleeSpec) :
    SepWP prog 0x5b108#64 s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 7#64) emp) := by
  wp_call
  wp_done

-- Bare `wp_call` resolves a `@[callee_spec]`-registered contract from the environment.
@[callee_spec]
theorem beh_callee_ok (prog : Program) (h_callee_code : behCalleeCode.holds prog) :
    subroutine_ok prog beh_callee_addr behCalleeSpec := by
  wp_init _u s0
  wp_steps
  wp_done

example (prog : Program) (h_code : behCallerCode.holds prog)
    (h_callee_code : behCalleeCode.holds prog) (s0 : State)
    (hpc : s0.pc = beh_caller_addr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true) :
    SepWP prog 0x5b108#64 s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 7#64) emp) := by
  wp_call
  wp_done

-- `wp_call h_wrong` suggests the matching local or registered contract in its error hint.
/--
error: wp_call: call target address does not match callee entry: h_wrong is the wrong contract (expected entry 0x5b000#64 ("beh_callee") / got 0x5b200#64 ("beh_branch"))
  call target PC: 0x5b000#64 (callee: "beh_callee")
  callee entry:   0x5b200#64 (callee: "beh_branch")
  raw target PC:  beh_callee_addr
  raw callee:     beh_branch_addr
hint: ensure execution has stepped to the `BL` call site (`wp_steps` / `wp_sym_steps`) and pass the contract matching the call target PC; did you mean `wp_call h_right`?
-/
#guard_msgs (error, drop info) in
example (prog : Program) (ret_pc : BitVec 64) (s : State)
    (hpc : s.pc = beh_callee_addr) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc)
    (h_right : subroutine_ok prog beh_callee_addr behCalleeSpec)
    (h_wrong : subroutine_ok prog beh_branch_addr behCalleeSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 7#64) := by
  wp_call h_wrong

-- `wp_done` selects the matching `SepWP` arm of an `Or` goal by matching `s.pc` against `target_pc`.
example (prog : Program) (s : State)
    (hpc : s.pc = 0x5b008#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = 7#64) :
    SepWP prog 0x5b000#64 s emp (fun sf _ => sf.readReg64 .x0 = 0#64) ∨
    SepWP prog 0x5b004#64 s emp (fun sf _ => sf.readReg64 .x0 = 1#64) ∨
    SepWP prog 0x5b008#64 s emp (fun sf _ => sf.readReg64 .x0 = 7#64) := by
  wp_done

-- `wp_done` unfolds `calleeSavedVRegs` equalities to prove individual SIMD lane preservation (`q8`).
example (prog : Program) (pc : BitVec 64) (s0 sf : State)
    (hpc : sf.pc = pc) (hrun : sf.status = .Running)
    (hvcs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWP prog pc sf emp
      (fun st _ => (st.readVReg128 8#5).truncate 64 = (s0.readVReg128 8#5).truncate 64) := by
  wp_done

-- `wp_done` decides an `ite` PC whose condition is constrained by local hypotheses.
example (prog : Program) (s : State)
    (hpc : s.pc = if (s.readReg64 .x0 == 0#64) = true then 0x5b20c#64 else 0x5b204#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = 5#64) :
    SepWP prog 0x5b204#64 s emp (fun sf _ => sf.readReg64 .x0 = 5#64) := by
  wp_done

-- `wp_steps (split := true)` splits an unresolved conditional branch and steps both arms.
example (prog : Program) (h_code : behBranchCode.holds prog) (s0 : State)
    (hpc : s0.pc = beh_branch_addr) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp
      (sepPost (fun sf => sf.readReg64 .x0 = 1#64 ∨ sf.readReg64 .x0 = 2#64) emp) := by
  wp_steps (split := true)
  · wp_done
  · wp_done

-- `wp_call` discharges `s.spAligned = true` from `s.sp = s0.sp - 48#64` and `s0.spAligned = true`.
example (prog : Program) (ret_pc : BitVec 64) (s0 s : State)
    (hpc : s.pc = beh_callee_addr) (hrun : s.status = .Running)
    (hinv : s.sp = s0.sp - 48#64 ∧ s0.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog beh_callee_addr behCalleeSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 7#64) := by
  wp_call h_callee ()
  wp_done

end TacticBehaviorImprovements

end Testing.LoopCFGCombinators
