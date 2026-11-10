/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

@[expose] public section

set_option autoImplicit false

/-!
# musl Exit Path and Hook-Free Addresses Above Image Code

Verifies musl's post-`main` exit sequence (`B + 0x854` -> `exit` at `B + 0xb48` ->
`libc_exit_fini` -> `_Exit` at `B + 0xb64`, invoking `exit_group` with `w0` sign-extended)
symbolically in page-aligned musl base `B`:

- `externAt?_ofImage_eq_none_of_ge` and `muslHookFree_ofImage`: `Program.ofImage img E`
  has no extern hooks at or above `img.base + img.code.length`.
- `musl_exit_ofImage`: from any `Returned sm sr` with `lr = B + 0x854`, 48 stack bytes
  below `sp`, and equal `__fini_array_start` / `__fini_array_end` `.got` words
  (`muslFiniFr B`), execution reaches `.Exited (signExtend 64 w0)` with unchanged
  filesystem and trace.
-/

namespace CryptoVerification.SignalSession.MuslExit

open Arm64 ProofLib

/-! ## Hook-Free Range Above Image Code -/

/-- Every extern stub of a loaded image lies inside its code. -/
theorem stub_lt_code {li : Obj.LinkedImage} {img : Obj.Image} (h : Obj.Loads li img)
    {n : String} {o : Nat} (hmem : (n, o) ∈ img.stubs) : o + 4 ≤ img.code.length := by
  obtain ⟨hcode, -, hstubs⟩ := ProofLib.ObjectLoad.Loads.canonical h
  have hwf := ProofLib.ObjectLoad.Loads.wellFormed h
  simp only [Obj.LinkedImage.wellFormed, Bool.and_eq_true] at hwf
  have hall := hwf.1.2
  rw [List.all_eq_true] at hall
  rw [hstubs] at hmem
  have := hall _ hmem
  simp only [decide_eq_true_eq] at this
  rw [hcode]
  exact this

/-- `Program.ofImage img E` has no extern hook at any non-wrapping `pc ≥ img.base + img.code.length`. -/
theorem externAt?_ofImage_eq_none_of_ge {li : Obj.LinkedImage} {img : Obj.Image}
    (h : Obj.Loads li img) (E : String → Option (State → State)) {pc : BitVec 64}
    (hpc : img.base.toNat + img.code.length ≤ pc.toNat) :
    (Program.ofImage img E).externAt? pc = none := by
  have hle : img.base ≤ pc := by
    rw [BitVec.le_def]; omega
  have hoff : (pc - img.base).toNat = pc.toNat - img.base.toNat := BitVec.toNat_sub_of_le hle
  simp only [Program.externAt?, Program.hookAtOff?, Program.ofImage, hoff]
  have e1 : (img.stubs.findSome? fun (n, o) =>
      if o == pc.toNat - img.base.toNat then E n else none) = none := by
    rw [List.findSome?_eq_none_iff]
    rintro ⟨n, o⟩ hmem
    have := stub_lt_code h hmem
    have hne : (o == pc.toNat - img.base.toNat) = false := by
      rw [beq_eq_false_iff_ne]; omega
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
  have e2 : (img.symbols.findSome? fun (n, o) =>
      if o == pc.toNat - img.base.toNat then (none : Option (State → State)) else none) =
      none := by
    rw [List.findSome?_eq_none_iff]
    rintro ⟨n, o⟩ _
    simp only [ite_self]
  rw [e1, e2]
  rfl

/-- Range-form `MuslHookFree` for `Program.ofImage img E` when `img.base + img.code.length ≤ lo`. -/
theorem muslHookFree_ofImage {li : Obj.LinkedImage} {img : Obj.Image}
    (h : Obj.Loads li img) (E : String → Option (State → State)) {lo hi : BitVec 64}
    (hlo : img.base.toNat + img.code.length ≤ lo.toNat) :
    ∀ pc, lo ≤ pc → pc < hi → ((Program.ofImage img E).externAt? pc).isNone = true := by
  intro pc hpc _
  rw [BitVec.le_def] at hpc
  rw [externAt?_ofImage_eq_none_of_ge h E (by omega)]
  rfl

/-- List-form `MuslHookFree` for `Program.ofImage img E` when every `pc ∈ pcs` lies at or above `img.base + img.code.length`. -/
theorem muslHookFree_list_ofImage {li : Obj.LinkedImage} {img : Obj.Image}
    (h : Obj.Loads li img) (E : String → Option (State → State)) {pcs : List (BitVec 64)}
    (hpcs : ∀ pc ∈ pcs, img.base.toNat + img.code.length ≤ pc.toNat) :
    ∀ pc ∈ pcs, ((Program.ofImage img E).externAt? pc).isNone = true := by
  intro pc hpc
  rw [externAt?_ofImage_eq_none_of_ge h E (hpcs pc hpc)]
  rfl

/-! ## Exit-Path Instruction Fetches and Stepping -/

/-- The decoded musl exit-path instructions at musl text base `B`. -/
def MuslExitFetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x854#64) = some (Arm64.Instr.bl 0x00000000000002f4#64) ∧
  Q.fetch (B + 0xb00#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0xb04#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0xb08#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0xb0c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x13#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xb10#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xb14#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000030#64)) ∧
  Q.fetch (B + 0xb18#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000038#64)) ∧
  Q.fetch (B + 0xb1c#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xb20#64) = some (Arm64.Instr.bCond (Arm64.CondCode.LS) 0x000000000000001c#64) ∧
  Q.fetch (B + 0xb3c#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0xb40#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0xb44#64) = some (Arm64.Instr.b 0xffffffffffffffbc#64) ∧
  Q.fetch (B + 0xb48#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xfffffffffffffff0#64)) ∧
  Q.fetch (B + 0xb4c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xb50#64) = some (Arm64.Instr.bl 0xffffffffffffffb0#64) ∧
  Q.fetch (B + 0xb54#64) = some (Arm64.Instr.bl 0xffffffffffffffb0#64) ∧
  Q.fetch (B + 0xb58#64) = some (Arm64.Instr.bl 0xffffffffffffffa8#64) ∧
  Q.fetch (B + 0xb5c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xb60#64) = some (Arm64.Instr.bl 0x0000000000000004#64) ∧
  Q.fetch (B + 0xb64#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.SBFM) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x00#5) 0 31) ∧
  Q.fetch (B + 0xb68#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x08#5) 0x005e#16 0) ∧
  Q.fetch (B + 0xb6c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xb70#64) = some (Arm64.Instr.system false 0x0000#16)

def muslFiniFr (B : BitVec 64) : SepProp :=
  ∃∗ F, ((B + 0x2030#64) ↦₆₄ᵣ F) ∗ ((B + 0x2038#64) ↦₆₄ᵣ F)

theorem musl_exit_wp (Q : Program) (B : BitVec 64) (hf : MuslExitFetch Q B)
    (hB : B &&& 0xfff#64 = 0#64)
    (s : State) (hpc : s.pc = B + 0x854#64) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (F : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    SepWP Q (B + 0xb70#64) s
      (((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗ ((s.sp - 32#64) ↦₆₄ v2) ∗
       ((s.sp - 24#64) ↦₆₄ v3) ∗ ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5) ∗
       ((B + 0x2030#64) ↦₆₄ᵣ F) ∗ ((B + 0x2038#64) ↦₆₄ᵣ F))
      (fun sf _ => sf.readReg64 .x0 = ((s.readReg64 .x0).setWidth 32).signExtend 64 ∧
        sf.readReg64 .x8 = 94#64 ∧ sf.fs = s.fs ∧ sf.trace = s.trace) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, -⟩ := hf
  iterate 25 wp_step
  wp_done

theorem step_of_externAt_eq {P₁ P₂ : Program} {s s' : State}
    (hpc : P₁.externAt? s.pc = P₂.externAt? s.pc) (hsvc : P₁.svc = P₂.svc := by rfl)
    (hs : Step P₁ s s') : Step P₂ s s' := by
  have hf : P₁.fetchMem s.mem s.pc = P₂.fetchMem s.mem s.pc := by
    unfold Program.fetchMem; rw [hpc]
  cases hs with
  | exec hr hfe =>
    have hev : P₁.evalInst = P₂.evalInst := by
      funext inst st; unfold Program.evalInst; rw [hsvc]
    rw [hev]; exact .exec hr (hf ▸ hfe)
  | halt_unmapped hr hfe he => exact .halt_unmapped hr (hf ▸ hfe) (hpc ▸ he)
  | extern hr he hk hsy => exact .extern hr (hpc ▸ he) hk hsy
  | extern_fault hr he hn => exact .extern_fault hr (hpc ▸ he) hn

theorem steps_of_externAt_eq {P Q : Program} (h : ∀ pc, Q.externAt? pc = P.externAt? pc)
    (hsvc : Q.svc = P.svc := by rfl)
    {s sf : State} (hs : Steps Q s sf) : Steps P s sf := by
  induction hs with
  | refl => exact .refl _
  | step h1 _ ih => exact .step (step_of_externAt_eq (h _) hsvc h1) ih

theorem stack48_cells (sp : BitVec 64) :
    stackAt sp 48 = ∃∗ v0, ((sp - 48#64) ↦₆₄ v0) ∗ ∃∗ v1, ((sp - 40#64) ↦₆₄ v1) ∗
      ∃∗ v2, ((sp - 32#64) ↦₆₄ v2) ∗ ∃∗ v3, ((sp - 24#64) ↦₆₄ v3) ∗
      ∃∗ v4, ((sp - 16#64) ↦₆₄ v4) ∗ ∃∗ v5, ((sp - 8#64) ↦₆₄ v5) := by
  rw [show (48 : Nat) = 8 * 6 from rfl, stackAt_eq_cells sp 6]
  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
    sepConj_emp]

theorem musl_exit_steps {P Q : Program} {B : BitVec 64}
    (hPQ : ∀ pc, Q.externAt? pc = P.externAt? pc) (hf : MuslExitFetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) {s : State} (hL : Q.CodeLoaded s.mem)
    (hpc : s.pc = B + 0x854#64) (hrun : s.status = .Running) (hal : s.spAligned = true)
    {R : SepProp} (hm : s.mem ⊨ stackAt s.sp 48 ∗ muslFiniFr B ∗ R)
    (hQsvc : Q.svc = Syscall.standard := by rfl) (hPsvc : P.svc = Syscall.standard := by rfl) :
    ∃ sx, Steps P s sx ∧
      sx.status = .Exited (((s.readReg64 .x0).setWidth 32).signExtend 64) ∧
      sx.fs = s.fs ∧ sx.trace = s.trace := by
  rw [stack48_cells, muslFiniFr] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨F, v0, v1, v2, v3, v4, v5, hm⟩ := hm
  have hwp := musl_exit_wp Q B hf hB s hpc hrun hal F v0 v1 v2 v3 v4 v5
  unfold SepWP at hwp
  rcases hwp R (by simp only [sepConj_assoc] at hm ⊢; exact hm) hL with
    ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, -, hx0, hx8, hfs, htr⟩ | ⟨-, hoom⟩⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsvc⟩ := hf
    have hLf : Q.CodeLoaded sf.mem := Steps.codeLoaded hsteps hL
    have hfm : P.fetchMem sf.mem sf.pc = some (.system false 0#16) := by
      rw [← hpcf] at hsvc
      have h1 := Program.fetchMem_of_fetch hLf hsvc
      unfold Program.fetchMem at h1 ⊢
      rw [← hPQ]; exact h1
    have hevP : P.evalInst (.system false 0#16) sf =
        sf.setStatus (.Exited (sf.readReg64 .x0)) := by
      unfold Program.evalInst execInstWithSvc
      rw [hPsvc]
      change evalSvc execSyscall sf = _
      unfold evalSvc
      dsimp only
      rw [execSyscall_exit_group _ hx8]
      rcases sf with ⟨_, _, _, _, _, ⟨_⟩, _, _, _, _, _, _, _, _, _, _, _⟩
      simp [State.setStatus]
    refine ⟨_, (steps_of_externAt_eq hPQ (hQsvc.trans hPsvc.symm) hsteps).trans
      (Steps.step (Step.exec hrunf hfm) (.refl _)), ?_, ?_, ?_⟩
    · rw [hevP]; simp [hx0]
    · rw [hevP]; simpa using hfs
    · rw [hevP]; simpa using htr
  · simp at hoom

/-! ## Auxiliary Program `muslProg` -/

/-- Program combining `P`'s extern hooks at the same absolute addresses with musl `code` based at `B`. -/
def muslProg (P : Program) (B : BitVec 64) (code : List (BitVec 8)) : Program where
  base := B
  code := code
  stubs := P.stubs.map fun (n, o) => (n, ((P.base + BitVec.ofNat 64 o) - B).toNat)
  externs := P.externs

theorem findSome?_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.findSome? f = l.findSome? g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.findSome?_cons, List.findSome?_cons, h x (List.mem_cons_self ..)]
    rw [findSome?_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem off_beq_iff (Pb B pc : BitVec 64) (o : Nat) (ho : o < 2 ^ 64) :
    ((((Pb + BitVec.ofNat 64 o) - B).toNat == (pc - B).toNat) =
      (o == (pc - Pb).toNat)) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h; bv_omega
  · intro h; bv_omega

/-- `muslProg P B code` has the hooks of `P`, at every PC. -/
theorem muslProg_externAt? (P : Program) (B : BitVec 64) (code : List (BitVec 8))
    (hst : ∀ x ∈ P.stubs, x.2 < 2 ^ 64) (hov : ∀ n, P.overrides n = none) (pc : BitVec 64) :
    (muslProg P B code).externAt? pc = P.externAt? pc := by
  have e2 : P.symbols.findSome? (fun x : String × Nat =>
      if x.2 == (pc - P.base).toNat then P.overrides x.1 else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x _
    simp only [hov, ite_self]
  unfold Program.externAt? Program.hookAtOff?
  dsimp only [muslProg]
  rw [List.findSome?_nil, Option.or_none, e2, Option.or_none, List.findSome?_map]
  apply findSome?_congr'
  rintro ⟨n, o⟩ hmem
  show (if ((P.base + BitVec.ofNat 64 o - B).toNat == (pc - B).toNat) = true then P.externs n
      else none) = if (o == (pc - P.base).toNat) = true then P.externs n else none
  rw [off_beq_iff P.base B pc o (hst _ hmem)]

/-- Away from hooks, `muslProg P B code` fetches at `B + k` what the hookless program
`{ code }` (base 0) fetches at `k`. -/
theorem muslProg_fetch_add (P : Program) (B : BitVec 64) (code : List (BitVec 8))
    (k : BitVec 64) (hx : (muslProg P B code).externAt? (B + k) = none) :
    (muslProg P B code).fetch (B + k) = ({ code } : Program).fetch k := by
  have hx0 : ({ code } : Program).externAt? k = none := rfl
  have hsub : ((B + k) - B).toNat = k.toNat := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  unfold Program.fetch
  rw [hx, hx0]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  show (Program.readWordOff _ ((B + k) - B).toNat).bind decode =
    (Program.readWordOff _ (k - 0#64).toNat).bind decode
  rw [hsub, BitVec.sub_zero]
  rfl

/-- `MuslExitFetch` moves from the hookless `{ code }` (base 0) to `muslProg P B code`, when no
PC `B + k` with `k < 0xb74` is a hook PC. -/
theorem muslExitFetch_muslProg (P : Program) (B : BitVec 64) (code : List (BitVec 8))
    (hx : ∀ k : BitVec 64, k.toNat < 0xb74 → (muslProg P B code).externAt? (B + k) = none)
    (hf : MuslExitFetch ({ code } : Program) 0#64) : MuslExitFetch (muslProg P B code) B := by
  have e : ∀ k : BitVec 64, k.toNat < 0xb74 →
      (muslProg P B code).fetch (B + k) = ({ code } : Program).fetch (0#64 + k) := by
    intro k hk
    rw [BitVec.zero_add]
    exact muslProg_fetch_add P B code k (hx k hk)
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23⟩ := hf
  exact ⟨(e _ (by decide)).trans f0, (e _ (by decide)).trans f1, (e _ (by decide)).trans f2,
    (e _ (by decide)).trans f3, (e _ (by decide)).trans f4, (e _ (by decide)).trans f5,
    (e _ (by decide)).trans f6, (e _ (by decide)).trans f7, (e _ (by decide)).trans f8,
    (e _ (by decide)).trans f9, (e _ (by decide)).trans f10, (e _ (by decide)).trans f11,
    (e _ (by decide)).trans f12, (e _ (by decide)).trans f13, (e _ (by decide)).trans f14,
    (e _ (by decide)).trans f15, (e _ (by decide)).trans f16, (e _ (by decide)).trans f17,
    (e _ (by decide)).trans f18, (e _ (by decide)).trans f19, (e _ (by decide)).trans f20,
    (e _ (by decide)).trans f21, (e _ (by decide)).trans f22, (e _ (by decide)).trans f23⟩

/-! ## Exit Path for `Program.ofImage img E` -/

/-- From a return state with `lr = B + 0x854`, 16-byte-aligned `sp`, 48 stack bytes below `sp`,
and `muslFiniFr B`, `Program.ofImage img E` steps through musl's exit path to
`.Exited (signExtend 64 w0)` without modifying the filesystem or trace. -/
theorem musl_exit_ofImage {li : Obj.LinkedImage} {img : Obj.Image} (himg : Obj.Loads li img)
    (E : String → Option (State → State)) {B : BitVec 64} {code : List (BitVec 8)}
    (hB : B &&& 0xfff#64 = 0#64) (hend : img.base.toNat + img.code.length ≤ B.toNat)
    (hnw : B.toNat + 0xb74 ≤ 2 ^ 64)
    (hf : MuslExitFetch ({ code } : Program) 0#64)
    {sm sr : State} (hL : ({ base := B, code } : Program).CodeLoaded sm.mem)
    (hlr : sm.readReg64 .lr = B + 0x854#64) (hal : sm.spAligned = true)
    (hsteps : Steps (Program.ofImage img E) sm sr) (hret : Returned sm sr)
    (hm : sr.mem ⊨ stackAt sm.sp 48 ∗ muslFiniFr B ∗ anyHeap) :
    ∃ sx, Steps (Program.ofImage img E) sr sx ∧
      sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
      sx.fs = sr.fs ∧ sx.trace = sr.trace := by
  obtain ⟨hpc, hsp, hrun⟩ := hret
  have hst : ∀ x ∈ (Program.ofImage img E).stubs, x.2 < 2 ^ 64 := by
    rintro ⟨n, o⟩ hmem
    have h1 := stub_lt_code himg hmem
    have h2 := B.isLt
    simp only at h1 ⊢
    omega
  have hPQ : ∀ pc, (muslProg (Program.ofImage img E) B code).externAt? pc =
      (Program.ofImage img E).externAt? pc :=
    muslProg_externAt? _ B code hst (fun _ => rfl)
  have hfQ : MuslExitFetch (muslProg (Program.ofImage img E) B code) B := by
    refine muslExitFetch_muslProg _ B code (fun k hk => ?_) hf
    rw [hPQ]
    apply externAt?_ofImage_eq_none_of_ge himg E
    have : (B + k).toNat = B.toNat + k.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    omega
  have hLQ : (muslProg (Program.ofImage img E) B code).CodeLoaded sr.mem :=
    Steps.codeLoaded hsteps (hL.of_base_code rfl rfl)
  have hal' : sr.spAligned = true := by
    simp only [State.spAligned, hsp] at hal ⊢; exact hal
  rw [← hsp] at hm
  exact musl_exit_steps hPQ hfQ hB hLQ (hpc.trans hlr) hrun hal' hm

end CryptoVerification.SignalSession.MuslExit
