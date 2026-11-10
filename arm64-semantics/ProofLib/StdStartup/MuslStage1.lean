/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.MuslStage1Init
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics

/-!
# `musl` Stage-1 Startup Contracts

Symbolic `SepWP` contracts for the `__init_libc` auxiliary-vector and program-name scans, the
post-TLS fast path, epilogues, and the top-level `muslStage1` startup theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib Stage1Internal

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

/-! ## Auxiliary Vector Scan -/

private theorem auxvScan38_foldl_len (entries : List (BitVec 64 × BitVec 64)) (acc : List (BitVec 64)) :
    (entries.foldl (fun a (t, v) => if t.toNat < 38 then a.set t.toNat v else a) acc).length = acc.length := by
  induction entries generalizing acc with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨t, v⟩; simp only [List.foldl_cons]; split <;> simp [ih]

theorem auxvScan38_length (entries : List (BitVec 64 × BitVec 64)) :
    (auxvScan38 entries).length = 38 := by
  unfold auxvScan38; rw [auxvScan38_foldl_len]; simp

private theorem auxv_scan_loop {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (entries : List (BitVec 64 × BitVec 64)) (curPtr auxPtr : BitVec 64) (acc : List (BitVec 64))
    {s : State} (F : SepProp)
    (hno0 : ∀ p ∈ entries, p.1 ≠ 0#64) (hlen : acc.length = 38)
    (hpc : s.pc = L.initLibcAddr + 0x68#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = curPtr) (hx4 : s.readReg64 .x4 = auxPtr) :
    SepWP P (L.initLibcAddr + 0x84#64) s
      (((curPtr ↦₆₄* ((entries ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        (auxPtr ↦₆₄* acc)) ∗ F)
      (fun sf Q =>
        sf.pc = L.initLibcAddr + 0x84#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x4 = auxPtr ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .lr = s.readReg64 .lr ∧
        StdStatePreserved s sf ∧
        Q = (((curPtr ↦₆₄* ((entries ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
              (auxPtr ↦₆₄* entries.foldl (fun a (t, v) => if t.toNat < 38 then a.set t.toNat v else a) acc)) ∗ F)) := by
  have hi25 := fetch_at 25 0x64#64 hc; have hi26 := fetch_at 26 0x68#64 hc
  have hi27 := fetch_at 27 0x6c#64 hc; have hi28 := fetch_at 28 0x70#64 hc
  have hi29 := fetch_at 29 0x74#64 hc; have hi30 := fetch_at 30 0x78#64 hc
  have hi31 := fetch_at 31 0x7c#64 hc; have hi32 := fetch_at 32 0x80#64 hc
  induction entries generalizing curPtr acc s F with
  | nil =>
    simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.foldl_nil]
    rw [pointsToWords64_cons, pointsToWords64_cons, pointsToWords64_nil]
    wp_steps 2
    refine SepWP.done (by simp (config := { decide := true }) only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    refine ⟨by simp (config := { decide := true }) only [arm64_norm],
      by simp only [arm64_norm, hrun], by simp only [arm64_norm],
      by simp only [arm64_norm, hx4], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      mk_stdPres (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [projSB_pc, projSB_w64]) (fun _ => rfl), rfl⟩
  | cons p ps ih =>
    rcases p with ⟨t, v⟩
    have ht0 : (t == 0#64) = false := beq_eq_false_iff_ne.mpr (hno0 (t, v) (List.mem_cons_self ..))
    have hcur16 : curPtr + 8#64 + 8#64 = curPtr + 16#64 := by bv_lin
    conv => arg 4; simp only [List.cons_append, List.flatMap_cons, List.nil_append]
    rw [pointsToWords64_cons, pointsToWords64_cons, hcur16]
    apply SepWP.cut (mid := L.initLibcAddr + 0x74#64)
    wp_steps 3
    refine SepWP.done (by simp (config := { decide := true }) only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    by_cases hlt : t.toNat < 38
    · have hult : (37#64).ult t = false := by simp [BitVec.ult]; omega
      have hsh_t : t <<< 3 = BitVec.ofNat 64 (8 * t.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      apply SepWP.cut (mid := L.initLibcAddr + 0x68#64)
      rw [pointsToWords64_focus auxPtr acc t.toNat (by omega)]
      wp_steps 2; wp_str64 hi31 m1 hm1; wp_steps 2
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      have hupd : ((auxPtr + BitVec.ofNat 64 (8 * t.toNat)) ↦₆₄ v) ∗
          (pointsToArray 8 (· ↦₆₄ ·) auxPtr (acc.take t.toNat) ∗
           pointsToArray 8 (· ↦₆₄ ·) (auxPtr + BitVec.ofNat 64 (8 * (t.toNat + 1))) (acc.drop (t.toNat + 1))) =
          (auxPtr ↦₆₄* acc.set t.toNat v) := by
        rw [pointsToArray_update 8 (· ↦₆₄ ·) auxPtr acc t.toNat v (by omega), ← pointsToWords64_eq_pointsToArray]
      refine SepWP.weaken_pre (P' := (((curPtr + 16#64) ↦₆₄* ((ps ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        (auxPtr ↦₆₄* acc.set t.toNat v)) ∗ ?F_lt) (by rw [← hupd]; sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih (curPtr + 16#64) (acc.set t.toNat v) ?F_lt
          (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) (by simp [hlen]) ?_ ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun]
        · simp (config := { decide := true }) only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx4]
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hx20_f, hx21_f, hx29_f, hlr_f, hstd_f, rfl⟩
        have hpres : StdStatePreserved s sf := by
          refine StdStatePreserved.trans ?_ hstd_f
          exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64, projSB_ps])
            (fun a => by simp only [wp_norm, arm64_norm, hm1])
        refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f, hx4_f,
          by simpa [wp_norm, arm64_norm] using hx20_f, by simpa [wp_norm, arm64_norm] using hx21_f,
          by simpa [wp_norm, arm64_norm] using hx29_f, by simpa [wp_norm, arm64_norm] using hlr_f, hpres, ?_⟩
        simp only [List.cons_append, List.flatMap_cons, List.nil_append, List.foldl_cons, hlt, ↓reduceIte]
        rw [pointsToWords64_cons, pointsToWords64_cons, hcur16]; ac_rfl
    · have hult : (37#64).ult t = true := by simp [BitVec.ult]; omega
      apply SepWP.cut (mid := L.initLibcAddr + 0x68#64)
      wp_steps 2
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre (P' := (((curPtr + 16#64) ↦₆₄* ((ps ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        (auxPtr ↦₆₄* acc)) ∗ ?F_hi) (by sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih (curPtr + 16#64) acc ?F_hi
          (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) hlen ?_ ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun]
        · simp (config := { decide := true }) only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx4]
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hx20_f, hx21_f, hx29_f, hlr_f, hstd_f, rfl⟩
        have hpres : StdStatePreserved s sf := by
          refine StdStatePreserved.trans ?_ hstd_f
          exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_w64, projSB_ps]) (fun _ => rfl)
        refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f, hx4_f,
          by simpa [wp_norm, arm64_norm] using hx20_f, by simpa [wp_norm, arm64_norm] using hx21_f,
          by simpa [wp_norm, arm64_norm] using hx29_f, by simpa [wp_norm, arm64_norm] using hlr_f, hpres, ?_⟩
        simp only [List.cons_append, List.flatMap_cons, List.nil_append, List.foldl_cons, hlt, ↓reduceIte]
        rw [pointsToWords64_cons, pointsToWords64_cons, hcur16]; ac_rfl

theorem initLibc_auxv_scan {P : Program} {L : StdBinaryLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s2 : State} {F : SepProp}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (hpc2 : s2.pc = L.initLibcAddr + 0x68#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = sl.sp0 - 0x1c0#64)
    (hx0 : s2.readReg64 .x0 = sl.auxvTableAddr)
    (hx4 : s2.readReg64 .x4 = sl.sp0 - 0x160#64)
    (hx20 : s2.readReg64 .x20 = sl.argvAddrs.getD 0 0#64)
    (hx21 : s2.readReg64 .x21 = L.libcAddr &&& 0xfffffffffffff000#64)
    (hx29 : s2.readReg64 .x29 = sl.sp0 - 0x1c0#64)
    (hal16 : sl.sp0.toNat % 16 = 0)
    (hauxv_no0 : ∀ p ∈ sl.auxvEntries, p.1 ≠ 0#64)
    (hauxv_hwcap : (auxvScan38 sl.auxvEntries).getD 16 0#64 = inputs.init.auxv.hwcap)
    (hauxv_pagesz : (auxvScan38 sl.auxvEntries).getD 6 0#64 = 4096#64) :
    SepWP P (L.initLibcAddr + 0xac#64) s2
      ((((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (L.hwcapAddr ↦₆₄ 0#64) ∗ (L.sysinfoAddr ↦₆₄ 0#64) ∗
        ((L.libcAddr + 0x30#64) ↦₆₄ 0#64)) ∗ F)
      (fun s3 Q =>
        s3.pc = L.initLibcAddr + 0xac#64 ∧ s3.status = .Running ∧
        s3.sp = sl.sp0 - 0x1c0#64 ∧
        s3.readReg64 .x4 = sl.sp0 - 0x160#64 ∧
        s3.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 ∧
        s3.readReg64 .x21 = L.libcAddr &&& 0xfffffffffffff000#64 ∧
        s3.readReg64 .x29 = sl.sp0 - 0x1c0#64 ∧
        StdStatePreserved s2 s3 ∧
        Q = ((((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗
              (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
              (L.hwcapAddr ↦₆₄ inputs.init.auxv.hwcap) ∗
              (L.sysinfoAddr ↦₆₄ (auxvScan38 sl.auxvEntries).getD 32 0#64) ∗
              ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ F)) := by
  have hi33 := fetch_at 33 0x84#64 hc; have hi34 := fetch_at 34 0x88#64 hc
  have hi35 := fetch_at 35 0x8c#64 hc; have hi36 := fetch_at 36 0x90#64 hc
  have hi37 := fetch_at 37 0x94#64 hc; have hi38 := fetch_at 38 0x98#64 hc
  have hi39 := fetch_at 39 0x9c#64 hc; have hi40 := fetch_at 40 0xa0#64 hc
  have hi41 := fetch_at 41 0xa4#64 hc; have hi42 := fetch_at 42 0xa8#64 hc
  have hsp0_al : (sl.sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr (align16_and_15 hal16)
  have hhw_pg := page_add_lo12_eq L.hwcapAddr
  have hsys_pg := page_add_lo12_eq L.sysinfoAddr
  have hlibc_pg := page_add_trunc12_eq L.libcAddr
  have haux_len := auxvScan38_length sl.auxvEntries
  have ha32 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 32) = sl.sp0 - 0x1c0#64 + 0x160#64 := by bv_lin
  have ha16 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 16) = sl.sp0 - 0x1c0#64 + 0xe0#64 := by bv_lin
  have ha6 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 6) = sl.sp0 - 0x1c0#64 + 0x90#64 := by bv_lin
  conv => arg 4; rw [encodeAuxvBytes_eq_flatMap_bytesLE, ← pointsToWords64_eq_pointsToBytesLE]
  apply SepWP.cut (mid := L.initLibcAddr + 0x84#64)
  refine SepWP.weaken_pre (P' := (((sl.auxvTableAddr ↦₆₄* ((sl.auxvEntries ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
    ((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64)) ∗ ?F_ax)) (by sep_frame) ?_
  apply SepWP.mono
  case h =>
    exact auxv_scan_loop hc sl.auxvEntries sl.auxvTableAddr (sl.sp0 - 0x160#64) (List.replicate 38 0#64)
      ?F_ax hauxv_no0 (by simp) hpc2 hrun2 hx0 hx4
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro sa Q hpc_a hrun_a ⟨_, _, hsp_a, hx4_a, hx20_a, hx21_a, hx29_a, _, hstd_a, rfl⟩
  have hsp_a' : sa.sp = sl.sp0 - 0x1c0#64 := hsp_a.trans hsp2
  have hx20_a' : sa.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 := hx20_a.trans hx20
  have hx21_a' : sa.readReg64 .x21 = L.libcAddr &&& 0xfffffffffffff000#64 := hx21_a.trans hx21
  have hx29_a' : sa.readReg64 .x29 = sl.sp0 - 0x1c0#64 := hx29_a.trans hx29
  change SepWP P (L.initLibcAddr + 0xac#64) sa
    (((sl.auxvTableAddr ↦₆₄* ((sl.auxvEntries ++ [(AuxvTag.null, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
      ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries)) ∗ _) _
  rw [pointsToWords64_eq_pointsToBytesLE, ← encodeAuxvBytes_eq_flatMap_bytesLE]
  apply SepWP.cut (mid := L.initLibcAddr + 0x94#64)
  rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 32 (by omega), ha32]
  wp_steps 2
  rw [← ha32, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 32 (by omega)]
  rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 16 (by omega), ha16]
  wp_step
  rw [← ha16, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 16 (by omega)]
  wp_str64 hi36 m1 hm1
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun_a]) ?_
  apply SepWP.cut (mid := L.initLibcAddr + 0xa0#64)
  refine SepWP.mono (post := fun sb Qb =>
    sb.pc = L.initLibcAddr + 0xa0#64 ∧ sb.status = .Running ∧
    sb.sp = sl.sp0 - 0x1c0#64 ∧ sb.readReg64 .x4 = sl.sp0 - 0x160#64 ∧
    sb.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 ∧
    sb.readReg64 .x21 = L.libcAddr &&& 0xfffffffffffff000#64 ∧
    sb.readReg64 .x29 = sl.sp0 - 0x1c0#64 ∧ StdStatePreserved s2 sb ∧
    Qb = (((sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
      ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗
      (L.hwcapAddr ↦₆₄ inputs.init.auxv.hwcap) ∗
      (L.sysinfoAddr ↦₆₄ (auxvScan38 sl.auxvEntries).getD 32 0#64) ∗
      ((L.libcAddr + 0x30#64) ↦₆₄ 0#64)) ∗ F)) ?_ ?_
  · by_cases hsys : (auxvScan38 sl.auxvEntries).getD 32 0#64 = 0#64
    · rw [hsys]
      wp_step
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun_a]) ?_
      refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_a],
        by simp only [wp_norm, arm64_norm, hsp_a'], by simp only [wp_norm, arm64_norm, hx4_a],
        by simp only [wp_norm, arm64_norm, hx20_a'], by simp only [wp_norm, arm64_norm, hx21_a'],
        by simp only [wp_norm, arm64_norm, hx29_a'],
        hstd_a.trans (mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
          (fun a => by simp only [wp_norm, arm64_norm, hm1])), by ac_rfl⟩
    · have hsys_f : ((auxvScan38 sl.auxvEntries).getD 32 0#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hsys
      wp_steps 2; wp_str64 hi39 m2 hm2
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun_a]) ?_
      refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_a],
        by simp only [wp_norm, arm64_norm, hsp_a'], by simp only [wp_norm, arm64_norm, hx4_a],
        by simp only [wp_norm, arm64_norm, hx20_a'], by simp only [wp_norm, arm64_norm, hx21_a'],
        by simp only [wp_norm, arm64_norm, hx29_a'],
        hstd_a.trans (mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
          (fun a => by simp only [wp_norm, arm64_norm, hm2, hm1])), by ac_rfl⟩
  · rintro sb Qb _ _ ⟨hpc_b, hrun_b, hsp_b, hx4_b, hx20_b, hx21_b, hx29_b, hstd_b, rfl⟩
    rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 6 (by omega), ha6]
    wp_steps 2
    rw [← ha6, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 6 (by omega)]
    wp_str64 hi42 m3 hm3
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun_b]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_b],
      by simp only [wp_norm, arm64_norm, hsp_b], by simp only [wp_norm, arm64_norm, hx4_b],
      by simp only [wp_norm, arm64_norm, hx20_b], by simp only [wp_norm, arm64_norm, hx21_b],
      by simp only [wp_norm, arm64_norm, hx29_b],
      hstd_b.trans (mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
        (fun a => by simp only [wp_norm, arm64_norm, hm3])), by ac_rfl⟩

/-! ## Program Name Scan -/

private theorem progname_scan_loop {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (bs : List (BitVec 8)) (curPtr best : BitVec 64) {s : State} (F : SepProp)
    (hno0 : 0#8 ∉ bs)
    (hpc : s.pc = L.initLibcAddr + 0xec#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = curPtr + 1#64) (hx2 : s.readReg64 .x2 = L.prognameAddr) :
    SepWP P (L.initLibcAddr + 0x104#64) s
      (((curPtr ↦ᵣ (bs ++ [0#8])) ∗ (L.prognameAddr ↦₆₄ best)) ∗ F)
      (fun sf Q =>
        sf.pc = L.initLibcAddr + 0x104#64 ∧ sf.status = .Running ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x4 = s.readReg64 .x4 ∧
        StdStatePreserved s sf ∧
        Q = (((curPtr ↦ᵣ (bs ++ [0#8])) ∗ (L.prognameAddr ↦₆₄ scanSlashPtr curPtr best bs)) ∗ F)) := by
  have hi58 := fetch_at 58 0xe8#64 hc; have hi59 := fetch_at 59 0xec#64 hc
  have hi60 := fetch_at 60 0xf0#64 hc; have hi61 := fetch_at 61 0xf4#64 hc
  have hi62 := fetch_at 62 0xf8#64 hc; have hi63 := fetch_at 63 0xfc#64 hc
  have hi64 := fetch_at 64 0x100#64 hc
  induction bs generalizing curPtr best s F with
  | nil =>
    have hcur_m1 : curPtr + 1#64 + (-1#64 : BitVec 64) = curPtr := by bv_lin
    conv => arg 4; rw [List.nil_append, pointsToBytesRO_cons, pointsToBytesRO_nil]
    wp_steps 2
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm, hrun], by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_w64]) (fun _ => rfl), ?_⟩
    simp only [scanSlashPtr, List.nil_append, pointsToBytesRO_cons, pointsToBytesRO_nil]
  | cons b rest ih =>
    have hcur_m1 : curPtr + 1#64 + (-1#64 : BitVec 64) = curPtr := by bv_lin
    have hb0 : b ≠ 0#8 := fun h => hno0 (h ▸ List.mem_cons_self ..)
    have hb32 : (b.zeroExtend 32 == 0#32) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; exact hb0 (by simpa using congrArg (BitVec.truncate 8) h)
    have hb64 : (b.zeroExtend 64 == 0#64) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; exact hb0 (by simpa using congrArg (BitVec.truncate 8) h)
    conv => arg 4; rw [List.cons_append, pointsToBytesRO_cons]
    by_cases hslash : (b == 0x2f#8) = true
    · have hb_eq : b = 0x2f#8 := beq_iff_eq.mp hslash
      subst hb_eq
      apply SepWP.cut (mid := L.initLibcAddr + 0xec#64)
      wp_steps 4; wp_str64 hi63 m1 hm1; wp_steps 2
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre (P' := ((((curPtr + 1#64) ↦ᵣ (rest ++ [0#8])) ∗
        (L.prognameAddr ↦₆₄ (curPtr + 1#64))) ∗ ?F_sl)) (by sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih (curPtr + 1#64) (curPtr + 1#64) ?F_sl
          (fun hm => hno0 (List.mem_cons_of_mem _ hm)) ?_ ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx2]
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hstd_f, rfl⟩
        have hpres : StdStatePreserved s sf := by
          refine StdStatePreserved.trans ?_ hstd_f
          exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64, projSB_ps])
            (fun a => by simp only [wp_norm, arm64_norm, hm1])
        refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f,
          by simpa [wp_norm, arm64_norm] using hx4_f, hpres, ?_⟩
        simp only [scanSlashPtr, ↓reduceIte, beq_self_eq_true, List.cons_append, pointsToBytesRO_cons]
        ac_rfl
    · have hslash_f : (b == 0x2f#8) = false := Bool.eq_false_iff.mpr hslash
      have hne32 : (b.zeroExtend 32 == 0x2f#32) = false := by
        simp only [beq_eq_false_iff_ne]; intro h
        exact (beq_eq_false_iff_ne.mp hslash_f) (by simpa using congrArg (BitVec.truncate 8) h)
      apply SepWP.cut (mid := L.initLibcAddr + 0xec#64)
      wp_steps 5
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre (P' := ((((curPtr + 1#64) ↦ᵣ (rest ++ [0#8])) ∗
        (L.prognameAddr ↦₆₄ best)) ∗ ?F_ns)) (by sep_frame) ?_
      apply SepWP.mono
      case h =>
        refine ih (curPtr + 1#64) best ?F_ns
          (fun hm => hno0 (List.mem_cons_of_mem _ hm)) ?_ ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hrun]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx2]
      case hoom => exact fun _ _ _ ho => ho
      case himp =>
        rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hstd_f, rfl⟩
        have hpres : StdStatePreserved s sf := by
          refine StdStatePreserved.trans ?_ hstd_f
          exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_w64, projSB_ps]) (fun _ => rfl)
        refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f,
          by simpa [wp_norm, arm64_norm] using hx4_f, hpres, ?_⟩
        simp only [scanSlashPtr, hslash_f, Bool.false_eq_true, ↓reduceIte, List.cons_append, pointsToBytesRO_cons]
        ac_rfl

theorem initLibc_progname_to_tls {P : Program} {L : StdBinaryLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s3 : State} {F : SepProp}
    (hc : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (hpc3 : s3.pc = L.initLibcAddr + 0xac#64) (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = sl.sp0 - 0x1c0#64)
    (hx4 : s3.readReg64 .x4 = sl.sp0 - 0x160#64)
    (hx20 : s3.readReg64 .x20 = sl.argvAddrs.getD 0 0#64)
    (hargv0_ne0 : sl.argvAddrs.getD 0 0#64 ≠ 0#64)
    (hargv0_no0 : 0#8 ∉ inputs.argv.getD 0 [])
    (hargv0_dup : ∃ pad : List (BitVec 8),
      ((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗
        ((sl.argvAddrs.getD 0 0#64) ↦ᵣ (inputs.argv.getD 0 [] ++ [0#8] ++ pad))) =
      (sl.argvBase ↦ᵣ sl.upperStrBytes))
    (_hne_tls : L.initLibcAddr + 0x108#64 ≠ L.staticInitTlsAddr) :
    SepWP P L.staticInitTlsAddr s3
      (((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ StdGotGlobals L ∗
        (L.prognameFullAddr ↦₆₄ 0#64) ∗ (L.prognameAddr ↦₆₄ 0#64)) ∗ F)
      (fun st Q =>
        let argv0Addr := sl.argvAddrs.getD 0 0#64
        let argv0Bytes := inputs.argv.getD 0 []
        st.pc = L.staticInitTlsAddr ∧ st.status = .Running ∧
        st.sp = sl.sp0 - 0x1c0#64 ∧
        st.readReg64 .x0 = sl.sp0 - 0x160#64 ∧
        st.readReg64 .lr = L.initLibcAddr + 0x10c#64 ∧
        StdStatePreserved s3 st ∧
        Q = (((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ StdGotGlobals L ∗
              (L.prognameFullAddr ↦₆₄ argv0Addr) ∗
              (L.prognameAddr ↦₆₄ scanSlashPtr argv0Addr argv0Addr argv0Bytes)) ∗ F)) := by
  have hi43 := fetch_at 43 0xac#64 hc; have hi44 := fetch_at 44 0xb0#64 hc
  have hi45 := fetch_at 45 0xb4#64 hc; have hi46 := fetch_at 46 0xb8#64 hc
  have hi47 := fetch_at 47 0xbc#64 hc; have hi48 := fetch_at 48 0xc0#64 hc
  have hi49 := fetch_at 49 0xc4#64 hc; have hi50 := fetch_at 50 0xc8#64 hc
  have hi51 := fetch_at 51 0xcc#64 hc; have hi52 := fetch_at 52 0xd0#64 hc
  have hi65 := fetch_at 65 0x104#64 hc; have hi66 := fetch_at 66 0x108#64 hc
  have ha0_f : (sl.argvAddrs.getD 0 0#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hargv0_ne0
  have hgot40 := page_add_lo12_eq (L.gotAddr + 0x40#64)
  have hgot48 := page_add_lo12_eq (L.gotAddr + 0x48#64)
  obtain ⟨pad, hdup⟩ := hargv0_dup
  apply SepWP.cut (mid := L.initLibcAddr + 0xec#64)
  conv => arg 4; dsimp only [StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]
  wp_steps 6; wp_str64 hi49 m1 hm1; wp_step; wp_str64 hi51 m2 hm2; wp_step
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun3]) ?_
  conv => arg 4; rw [← hdup, pointsToBytesRO_append]
  apply SepWP.cut (mid := L.initLibcAddr + 0x104#64)
  refine SepWP.weaken_pre (P' := ((((sl.argvAddrs.getD 0 0#64) ↦ᵣ (inputs.argv.getD 0 [] ++ [0#8])) ∗
    (L.prognameAddr ↦₆₄ sl.argvAddrs.getD 0 0#64)) ∗ ?F_pg)) (by sep_frame) ?_
  apply SepWP.mono
  case h =>
    refine progname_scan_loop hc (inputs.argv.getD 0 []) (sl.argvAddrs.getD 0 0#64)
      (sl.argvAddrs.getD 0 0#64) ?F_pg hargv0_no0 ?_ ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hrun3]
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm]
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro spg Q hpc_p hrun_p ⟨_, _, hsp_p, hx4_p, hstd_p, rfl⟩
  have hpres_p : StdStatePreserved s3 spg := by
    refine StdStatePreserved.trans ?_ hstd_p
    exact mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_mem, projSB_w64])
      (fun a => by simp only [wp_norm, arm64_norm, hm2, hm1])
  apply SepWP.cut (mid := L.initLibcAddr + 0x108#64)
  wp_step
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun_p]) ?_
  wp_step; rw [add_sub_pc]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_p]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_p],
    by simpa [wp_norm, arm64_norm, hsp3] using hsp_p,
    by simp only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    hpres_p.trans (mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_w64]) (fun _ => rfl)), ?_⟩
  conv => rhs; rw [← hdup, pointsToBytesRO_append]
  dsimp only [StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]
  ac_rfl

/-! ## Post-TLS Epilogue and Stage-1 Entry -/

private theorem cons64_entails (a b v : BitVec 64) (n : Nat)
    (hab : a + 8#64 = b := by bv_lin) (hn : 8 ≤ n := by decide) (hlen : n ≤ 2 ^ 64 := by decide) :
    ((a ↦₆₄ v) ∗ memRegion b (n - 8)) ⊢ memRegion a n := by
  rw [← hab]; exact memRegion_cons a v hn hlen

theorem stage1_stack_entails_memRegion (sp0 : BitVec 64) (s0 s1 : State) (ws : List (BitVec 64))
    (hlen : ws.length = 38) :
    (InitSavedFrame sp0 s1 ∗ ((sp0 - 0x160#64) ↦₆₄* ws) ∗ LsmSavedFrame sp0 s0) ⊢
      memRegion (sp0 - 0x1c0#64) 0x1c0 := by
  have h_init : InitSavedFrame sp0 s1 ⊢ memRegion (sp0 - 0x1c0#64) 0x60 := by
    rw [show InitSavedFrame sp0 s1 =
      ((sp0 - 0x1c0#64) ↦₆₄ s1.readReg64 .x29) ∗ (((sp0 - 0x1b8#64) ↦₆₄ s1.readReg64 .lr) ∗
      (((sp0 - 0x1b0#64) ↦₆₄ s1.readReg64 .x19) ∗ (((sp0 - 0x1a8#64) ↦₆₄ s1.readReg64 .x20) ∗
      (((sp0 - 0x1a0#64) ↦₆₄ s1.readReg64 .x21) ∗ memRegion (sp0 - 0x198#64) 0x38)))) by
      dsimp only [InitSavedFrame]]
    refine Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right
      (Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right
        (cons64_entails _ _ _ 64)) (cons64_entails _ _ _ 72)))
        (cons64_entails _ _ _ 80))) (cons64_entails _ _ _ 88))) (cons64_entails _ _ _ 0x60)
  have h_lsm : LsmSavedFrame sp0 s0 ⊢ memRegion (sp0 - 0x30#64) 0x30 := by
    rw [show LsmSavedFrame sp0 s0 =
      ((sp0 - 0x30#64) ↦₆₄ 0#64) ∗ (((sp0 - 0x28#64) ↦₆₄ 0#64) ∗
      (((sp0 - 0x20#64) ↦₆₄ s0.readReg64 .x19) ∗ (((sp0 - 0x18#64) ↦₆₄ s0.readReg64 .x20) ∗
      (((sp0 - 0x10#64) ↦₆₄ s0.readReg64 .x21) ∗ memRegion (sp0 - 0x08#64) 8)))) by
      dsimp only [LsmSavedFrame]]
    refine Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right
      (Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right
        (cons64_entails _ _ _ 16)) (cons64_entails _ _ _ 24)))
        (cons64_entails _ _ _ 32))) (cons64_entails _ _ _ 40))) (cons64_entails _ _ _ 0x30)
  have h_aux : ((sp0 - 0x160#64) ↦₆₄* ws) ⊢ memRegion (sp0 - 0x160#64) 0x130 := by
    simpa [hlen] using pointsToWords64_entails_memRegion ws (sp0 - 0x160#64) (by rw [hlen]; decide)
  rw [memRegion_split_le (sp0 - 0x1c0#64) 0x60 0x1c0 (by decide) (by decide),
      show (0x1c0 - 0x60 : Nat) = 0x160 from rfl,
      show sp0 - 0x1c0#64 + BitVec.ofNat 64 0x60 = sp0 - 0x160#64 by bv_lin,
      memRegion_split_le (sp0 - 0x160#64) 0x130 0x160 (by decide) (by decide),
      show (0x160 - 0x130 : Nat) = 0x30 from rfl,
      show sp0 - 0x160#64 + BitVec.ofNat 64 0x130 = sp0 - 0x30#64 by bv_lin,
      show InitSavedFrame sp0 s1 ∗ ((sp0 - 0x160#64) ↦₆₄* ws) ∗ LsmSavedFrame sp0 s0 =
        InitSavedFrame sp0 s1 ∗ (((sp0 - 0x160#64) ↦₆₄* ws) ∗ LsmSavedFrame sp0 s0) by ac_rfl]
  exact sepConj_mono h_init (sepConj_mono h_aux h_lsm)

theorem initLibc_post_tls_to_stage2 {P : Program} {L : StdBinaryLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s0 s1 st' : State} {F : SepProp}
    (hc_init : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (hc_lsm : hasInstrs P L.libcStartMainAddr (libcStartMainInstrs L))
    (hdummy1 : P.hasWords L.dummy1Addr dummy1Words)
    (hpc : st'.pc = L.initLibcAddr + 0x10c#64) (hrun : st'.status = .Running)
    (hsp : st'.sp = sl.sp0 - 0x1c0#64)
    (hal16 : sl.sp0.toNat % 16 = 0)
    (hlr_1 : s1.readReg64 .lr = L.libcStartMainAddr + 0x2c#64)
    (hx19_1 : s1.readReg64 .x19 = sl.argvTableAddr)
    (hx20_1 : s1.readReg32 .x20 = BitVec.ofNat 32 inputs.argv.length)
    (hx21_1 : s1.readReg64 .x21 = L.cMainAddr)
    (huid : (auxvScan38 sl.auxvEntries).getD 11 0#64 = (auxvScan38 sl.auxvEntries).getD 12 0#64)
    (hgid : (auxvScan38 sl.auxvEntries).getD 13 0#64 = (auxvScan38 sl.auxvEntries).getD 14 0#64)
    (hsec : (auxvScan38 sl.auxvEntries).getD 23 0#64 = 0#64)
    (_hne_stage2 : L.libcStartMainAddr + 0x50#64 ≠ L.libcStartMainStage2Addr) :
    SepWP P L.libcStartMainStage2Addr st'
      ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗
        LsmSavedFrame sl.sp0 s0) ∗ F)
      (fun sf Q =>
        sf.pc = L.libcStartMainStage2Addr ∧ sf.status = .Running ∧
        sf.sp = sl.sp0 ∧
        sf.readReg64 .x0 = L.cMainAddr ∧
        sf.readReg32 .x1 = BitVec.ofNat 32 inputs.argv.length ∧
        sf.readReg64 .x2 = sl.argvTableAddr ∧
        StdStatePreserved st' sf ∧
        Q = ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗
              LsmSavedFrame sl.sp0 s0) ∗ F)) := by
  have hi67 := fetch_at 67 0x10c#64 hc_init; have hi68 := fetch_at 68 0x110#64 hc_init
  have hi69 := fetch_at 69 0x114#64 hc_init; have hi70 := fetch_at 70 0x118#64 hc_init
  have hi71 := fetch_at 71 0x11c#64 hc_init; have hi91 := fetch_at 91 0x16c#64 hc_init
  have hi92 := fetch_at 92 0x170#64 hc_init; have hi93 := fetch_at 93 0x174#64 hc_init
  have hi94 := fetch_at 94 0x178#64 hc_init; have hi95 := fetch_at 95 0x17c#64 hc_init
  have hi96 := fetch_at 96 0x180#64 hc_init; have hi114 := fetch_at 114 0x1c8#64 hc_init
  have hi115 := fetch_at 115 0x1cc#64 hc_init; have hi116 := fetch_at 116 0x1d0#64 hc_init
  have hi117 := fetch_at 117 0x1d4#64 hc_init; have hd0 := fetch_dummy1 hdummy1
  have hl11 := fetch_at 11 0x2c#64 hc_lsm; have hl12 := fetch_at 12 0x30#64 hc_lsm
  have hl13 := fetch_at 13 0x34#64 hc_lsm; have hl14 := fetch_at 14 0x38#64 hc_lsm
  have hl15 := fetch_at 15 0x3c#64 hc_lsm; have hl16 := fetch_at 16 0x40#64 hc_lsm
  have hl17 := fetch_at 17 0x44#64 hc_lsm; have hl18 := fetch_at 18 0x48#64 hc_lsm
  have hl19 := fetch_at 19 0x4c#64 hc_lsm; have hl20 := fetch_at 20 0x50#64 hc_lsm
  have _hne_d1 : L.initLibcAddr + 0x110#64 ≠ L.dummy1Addr := pc_ne_of_fetch_ne hi68 hd0
  have _hne_d2 : L.dummy1Addr ≠ L.initLibcAddr + 0x114#64 := pc_ne_of_fetch_ne hd0 hi69
  have _hne_ret : L.initLibcAddr + 0x1d4#64 ≠ L.libcStartMainAddr + 0x2c#64 := pc_ne_of_fetch_ne hi117 hl11
  have hsp0_al : (sl.sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr (align16_and_15 hal16)
  have haux_len := auxvScan38_length sl.auxvEntries
  have ha25 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 25) = sl.sp0 - 0x1c0#64 + 0x128#64 := by bv_lin
  have ha11 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 11) = sl.sp0 - 0x1c0#64 + 0xb8#64 := by bv_lin
  have ha13 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 13) = sl.sp0 - 0x1c0#64 + 0xc8#64 := by bv_lin
  have ha23 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 23) = sl.sp0 - 0x1c0#64 + 0x118#64 := by bv_lin
  have hstg2_pg := page_add_trunc12_eq L.libcStartMainStage2Addr
  apply SepWP.cut (mid := L.dummy1Addr)
  rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 25 (by omega), ha25]; wp_step
  rw [← ha25, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 25 (by omega)]
  apply SepWP.cut (mid := L.initLibcAddr + 0x110#64)
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  wp_step; rw [add_sub_pc]; refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  apply SepWP.cut (mid := L.initLibcAddr + 0x114#64); wp_step
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  have hf11 : ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) =
      ((sl.sp0 - 0x1c0#64 + 0xb8#64) ↦₆₄ (auxvScan38 sl.auxvEntries).getD 12 0#64) ∗ (((sl.sp0 - 0x1c0#64 + 0xb8#64) + 8#64) ↦₆₄ (auxvScan38 sl.auxvEntries).getD 12 0#64) ∗
      (((sl.sp0 - 0x160#64) ↦₆₄* (auxvScan38 sl.auxvEntries).take 11) ∗ ((((sl.sp0 - 0x1c0#64 + 0xb8#64) + 8#64) + 8#64) ↦₆₄* (auxvScan38 sl.auxvEntries).drop 13)) := by
    rw [pointsToWords64_focus_pair (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 11 (by omega), ha11, huid]
  have hf13 : ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) =
      ((sl.sp0 - 0x1c0#64 + 0xc8#64) ↦₆₄ (auxvScan38 sl.auxvEntries).getD 14 0#64) ∗ (((sl.sp0 - 0x1c0#64 + 0xc8#64) + 8#64) ↦₆₄ (auxvScan38 sl.auxvEntries).getD 14 0#64) ∗
      (((sl.sp0 - 0x160#64) ↦₆₄* (auxvScan38 sl.auxvEntries).take 13) ∗ ((((sl.sp0 - 0x1c0#64 + 0xc8#64) + 8#64) + 8#64) ↦₆₄* (auxvScan38 sl.auxvEntries).drop 15)) := by
    rw [pointsToWords64_focus_pair (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 13 (by omega), ha13, hgid]
  have hf23 : ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) = ((sl.sp0 - 0x1c0#64 + 0x118#64) ↦₆₄ 0#64) ∗
      (pointsToArray 8 (· ↦₆₄ ·) (sl.sp0 - 0x160#64) ((auxvScan38 sl.auxvEntries).take 23) ∗ pointsToArray 8 (· ↦₆₄ ·) (sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 24)) ((auxvScan38 sl.auxvEntries).drop 24)) := by
    rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 23 (by omega), ha23, hsec]
  apply SepWP.cut (mid := L.initLibcAddr + 0x16c#64); (conv => arg 4; rw [hf11]); wp_steps 3; (conv => arg 4; rw [← hf11])
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  apply SepWP.cut (mid := L.initLibcAddr + 0x1c8#64); (conv => arg 4; rw [hf13]); wp_steps 3; (conv => arg 4; rw [← hf13, hf23]); wp_steps 3; (conv => arg 4; rw [← hf23])
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  apply SepWP.cut (mid := L.libcStartMainAddr + 0x2c#64); (conv => arg 4; dsimp only [InitSavedFrame, LsmSavedFrame]); wp_steps 3
  apply SepWP.cut (mid := L.initLibcAddr + 0x1d4#64)
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  wp_step; refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  apply SepWP.cut (mid := L.libcStartMainAddr + 0x50#64); wp_steps 9
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  wp_step; refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun], by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm], by simpa [wp_norm, arm64_norm, State.readReg32] using hx20_1, by simp only [wp_norm, arm64_norm],
    mk_stdPres (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp only [projSB_pc, projSB_w64, projSB_ps]) (fun _ => rfl),
    by dsimp only [InitSavedFrame, LsmSavedFrame]⟩

/-- Complete `musl` stage-1 startup theorem (`_start` -> `_start_c` -> `__libc_start_main` ->
    `__init_libc` -> `__libc_start_main_stage2`), parameterized over `hTls` for `__init_tls`. -/
theorem muslStage1 {P : Program} {img : ElfImage} {L : StdBinaryLayout} {inputs : ProcessInputs} {s0 : State}
    {PreTls PostTls F : SepProp} {PTls : State → State → Prop}
    (hinfo : InitialStackInfo img inputs s0) (hvalid : inputs.Valid)
    (hc_start : hasInstrs P L.startAddr (startInstrs L)) (hc_startC : hasInstrs P L.startCAddr (startCInstrs L))
    (hc_lsm : hasInstrs P L.libcStartMainAddr (libcStartMainInstrs L)) (hc_init : hasInstrs P L.initLibcAddr (initLibcInstrs L))
    (hdummy1 : P.hasWords L.dummy1Addr dummy1Words) (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hTls : ∀ (st : State) (FTls : SepProp), st.pc = L.staticInitTlsAddr → st.status = .Running →
      st.sp = (StackLayout.of img inputs).sp0 - 0x1c0#64 → st.readReg64 .x0 = (StackLayout.of img inputs).sp0 - 0x160#64 →
      st.readReg64 .lr = L.initLibcAddr + 0x10c#64 → StdStatePreserved s0 st →
      SepWP P (L.initLibcAddr + 0x10c#64) st (((((StackLayout.of img inputs).sp0 - 0x160#64) ↦₆₄* auxvScan38 (StackLayout.of img inputs).auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗ (L.sysinfoAddr ↦₆₄ (auxvScan38 (StackLayout.of img inputs).auxvEntries).getD 32 0#64) ∗ PreTls) ∗ FTls)
        (fun st' Q => st'.pc = L.initLibcAddr + 0x10c#64 ∧ st'.status = .Running ∧ st'.sp = (StackLayout.of img inputs).sp0 - 0x1c0#64 ∧ PTls st st' ∧
          (Q ⊢ ((((StackLayout.of img inputs).sp0 - 0x160#64) ↦₆₄* auxvScan38 (StackLayout.of img inputs).auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗ (L.sysinfoAddr ↦₆₄ (auxvScan38 (StackLayout.of img inputs).auxvEntries).getD 32 0#64) ∗ PostTls) ∗ FTls)))
    (hstart_eq : img.entry = L.startAddr := by rfl) (_hne_memset : L.initLibcAddr + 0x28#64 ≠ L.memsetAddr := by decide)
    (_hne_tls : L.initLibcAddr + 0x108#64 ≠ L.staticInitTlsAddr := by decide) (_hne_stage2 : L.libcStartMainAddr + 0x50#64 ≠ L.libcStartMainStage2Addr := by decide) :
    let sl := StackLayout.of img inputs
    SepWP P L.libcStartMainStage2Addr s0
      ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPre L ∗ StdGotGlobals L ∗ (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ PreTls) ∗ F)
      (sepPost
        (fun sf => sf.sp = sl.sp0 ∧ sf.readReg64 .x0 = L.cMainAddr ∧
          sf.readReg32 .x1 = BitVec.ofNat 32 inputs.argv.length ∧ sf.readReg64 .x2 = sl.argvTableAddr ∧
          ∃ st st', StdStatePreserved s0 st ∧ PTls st st' ∧ StdStatePreserved st' sf)
        ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPost L inputs sl ∗ StdGotGlobals L ∗
          (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
          (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
          (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ PostTls) ∗ F)) := by
  dsimp only; let sl := StackLayout.of img inputs; have ⟨hargc_lo, hargc_hi, henvp_hi⟩ := hinfo.argc_bounds
  have hargv_len : sl.argvAddrs.length = inputs.argv.length := hinfo.argvAddrs_length
  have henvp_len : sl.envpAddrs.length = inputs.envp.length := hinfo.envpAddrs_length
  have henvp_eq : sl.envpTableAddr = sl.sp0 + BitVec.ofNat 64 (8 * (inputs.argv.length + 2)) := by
    simp only [StackLayout.envpTableAddr, StackLayout.argc, hargv_len]
  have hauxv_eq : sl.auxvTableAddr = sl.envpTableAddr + BitVec.ofNat 64 (8 * (inputs.envp.length + 1)) := by
    simp only [StackLayout.auxvTableAddr, StackLayout.envpTableAddr, StackLayout.argc, StackLayout.envc, hargv_len, henvp_len, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have henvp_no0 : ∀ p ∈ sl.envpAddrs, p ≠ 0#64 := fun p hp => by obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp; exact hinfo.envpAddr_ne_zero (henvp_len ▸ hi)
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr; rw [← hinfo.auxvEntries_eq] at hwf_aux
  have hscan := auxvScan38_mkAuxvEntries img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr; rw [← hinfo.auxvEntries_eq] at hscan
  rcases hscan with ⟨haux_len, _, _, _, hs6, _, hs11, hs12, hs13, hs14, _, hs16, hs23, _, _, _⟩
  have gd : ∀ {xs : List (BitVec 64)} {k : Nat} {v : BitVec 64}, xs[k]? = some v → xs.getD k 0#64 = v := fun h => by rw [List.getD, h]; rfl
  have h0_lt : 0 < inputs.argv.length := (by omega); have h0_lt' : 0 < sl.argvAddrs.length := by omega
  have ha0_eq : sl.argvAddrs.getD 0 0#64 = sl.argvAddrs[0]'h0_lt' := by simp [List.getD, getElem?_pos, h0_lt']
  have hv0_eq : inputs.argv.getD 0 [] = inputs.argv[0]'h0_lt := by simp [List.getD, getElem?_pos, h0_lt]
  obtain ⟨pad, hargv0_no0', _, _, _, hdup'⟩ := hinfo.dup_argv_cstr_padded hvalid.1 h0_lt
  conv => arg 4; rw [memRegion_split_le (sl.sp0 - 0x1c0#64) 0x190 0x1c0 (by decide) (by decide), show (0x1c0 - 0x190 : Nat) = 0x30 from rfl, show sl.sp0 - 0x1c0#64 + BitVec.ofNat 64 0x190 = sl.sp0 - 0x30#64 by bv_lin]
  conv => arg 4; dsimp only [Stage1GlobalsPre]
  apply SepWP.cut (mid := L.initLibcAddr); refine SepWP.weaken_pre (P' := (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ StdGotGlobals L ∗ memRegion (sl.sp0 - 0x30#64) 0x30) ∗ ?F1)) (by sep_frame) ?_
  apply SepWP.mono
  case h => exact start_to_initLibc_call (inputs := inputs) hc_start hc_startC hc_lsm hc_init hinfo.s0_sp (hinfo.s0_pc.trans hstart_eq) hinfo.s0_status hinfo.sp0_align16 hargc_lo hargc_hi hargv_len henvp_eq rfl
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro s1 _ _ _ ⟨hpc1, hrun1, hsp1, hlr1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, _, hstd01, rfl⟩
  apply SepWP.cut (mid := L.initLibcAddr + 0x68#64); refine SepWP.weaken_pre (P' := ((memRegion (sl.sp0 - 0x1c0#64) 0x190 ∗ StdGotGlobals L ∗ (L.environAddr ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ 0#64) ∗ (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64]))) ∗ ?F2)) (by sep_frame) ?_
  apply SepWP.mono
  case h => exact initLibc_prologue_envp (inputs := inputs) hc_init ops hpc1 hrun1 hsp1 hx0_1 hx1_1 hinfo.sp0_align16 henvp_len henvp_hi henvp_no0 hauxv_eq _hne_memset
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro s2 _ _ _ ⟨hpc2, hrun2, hsp2, hx0_2, hx4_2, hx20_2, hx21_2, hx29_2, hstd12, rfl⟩
  apply SepWP.cut (mid := L.initLibcAddr + 0xac#64); refine SepWP.weaken_pre (P' := ((((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗ (L.hwcapAddr ↦₆₄ 0#64) ∗ (L.sysinfoAddr ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 0#64)) ∗ ?F3)) (by sep_frame) ?_
  apply SepWP.mono
  case h => exact initLibc_auxv_scan (inputs := inputs) hc_init hpc2 hrun2 hsp2 hx0_2 hx4_2 hx20_2 hx21_2 hx29_2 hinfo.sp0_align16 (fun p hp => (hwf_aux.2.2 p.1 p.2 hp).1) (gd hs16) (gd hs6)
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro s3 _ _ _ ⟨hpc3, hrun3, hsp3, hx4_3, hx20_3, _, _, hstd23, rfl⟩
  apply SepWP.cut (mid := L.staticInitTlsAddr); refine SepWP.weaken_pre (P' := (((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ StdGotGlobals L ∗ (L.prognameFullAddr ↦₆₄ 0#64) ∗ (L.prognameAddr ↦₆₄ 0#64)) ∗ ?F4)) (by sep_frame) ?_
  apply SepWP.mono
  case h => exact initLibc_progname_to_tls (inputs := inputs) hc_init hpc3 hrun3 hsp3 hx4_3 hx20_3 (ha0_eq ▸ hinfo.argvAddr_ne_zero h0_lt) (hv0_eq ▸ hargv0_no0') ⟨pad, by rwa [ha0_eq, hv0_eq]⟩ _hne_tls
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro st _ _ _ ⟨hpct, hrunt, hspt, hx0_t, hlr_t, hstd3t, rfl⟩; have hstd0t : StdStatePreserved s0 st := hstd01.trans (hstd12.trans (hstd23.trans hstd3t))
  conv => arg 4; dsimp only [StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]
  apply SepWP.cut (mid := L.initLibcAddr + 0x10c#64); refine SepWP.weaken_pre (P' := ((((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗ (L.sysinfoAddr ↦₆₄ (auxvScan38 sl.auxvEntries).getD 32 0#64) ∗ PreTls) ∗ ?F5)) (by sep_frame) ?_
  apply SepWP.mono
  case h => exact hTls st ?F5 hpct hrunt hspt hx0_t hlr_t hstd0t
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro st' _ _ _ ⟨hpct', hrunt', hspt', hPTls, hent_tls⟩; refine SepWP.weaken_pre hent_tls ?_
  refine SepWP.weaken_pre (P' := ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ LsmSavedFrame sl.sp0 s0) ∗ ?F6)) (by sep_frame) ?_
  apply SepWP.mono
  case h => exact initLibc_post_tls_to_stage2 (inputs := inputs) hc_init hc_lsm hdummy1 hpct' hrunt' hspt' hinfo.sp0_align16 hlr1 hx19_1 hx20_1 hx21_1 ((gd hs11).trans (gd hs12).symm) ((gd hs13).trans (gd hs14).symm) (gd hs23) _hne_stage2
  case hoom => exact fun _ _ _ ho => ho
  case himp =>
  rintro sf _ _ _ ⟨_, _, hspf, hx0f, hx1f, hx2f, hstdtf, rfl⟩; refine ⟨⟨hspf, hx0f, hx1f, hx2f, st, st', hstd0t, hPTls, hstdtf⟩, ?_⟩
  refine Entails.trans (sepConj_mono_left (stage1_stack_entails_memRegion sl.sp0 s0 s1 (auxvScan38 sl.auxvEntries) haux_len)) ?_
  dsimp only [Stage1GlobalsPost, StdGotGlobals, StdBinaryLayout.gotAtoms, rwAtomListSep, RwAtom.toSepProp]; sep_frame

end ProofLib.StdStartup
