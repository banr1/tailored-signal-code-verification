/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPre
public import ProofLib.StdStartup.StartupCompose

/-!
# Stage-1 and Stage-2 Startup Proof

Proves placement-generic machine-code execution of `musl` Stage-1 and Stage-2 startup from `_start`
through `__libc_start_main`, `__init_libc`, static TLS initialization, and `__libc_start_init` to
`c_main` over `(C : HbCliLayout)` and `(S : HbStartupLayout)`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

/-! ## `HbMatchesImage` Program-Header and `PT_TLS` Extraction Helpers -/

private theorem hbCheckPhdrTable_entry {C : HbCliLayout} (h : checkHbPhdrTable C = true)
    {i : Nat} (hi : i < C.std.phnum) :
    let off := i * 56; let ptype := listReadU32LE C.std.phdrBytes off
    let pvaddr := listReadU64LE C.std.phdrBytes (off + 16); let pfilesz := listReadU64LE C.std.phdrBytes (off + 32)
    let pmemsz := listReadU64LE C.std.phdrBytes (off + 40); let palign := listReadU64LE C.std.phdrBytes (off + 48)
    ptype ≠ 2 ∧ (ptype = 6 → pvaddr = C.std.phdrAddr.toNat) ∧ (ptype = 0x6474e551 → pmemsz = 0) ∧
    (i = C.std.tlsPhdrIdx → ptype = 7 ∧ pvaddr = C.std.tlsImageAddr.toNat ∧ pfilesz = 0x30 ∧ pmemsz = 0x50 ∧ palign = 8) ∧
    (i ≠ C.std.tlsPhdrIdx → ptype ≠ 7) := by
  unfold checkHbPhdrTable at h; simp only [Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.2 i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hall
  obtain ⟨⟨⟨hp2, hp6⟩, hpstk⟩, htls⟩ := hall; refine ⟨hp2, ?_, ?_, ?_, ?_⟩
  · intro h6; simp only [h6, ↓reduceIte, beq_iff_eq] at hp6; exact hp6
  · intro hstk; simp only [hstk, ↓reduceIte, beq_iff_eq] at hpstk; exact hpstk
  · rintro rfl; simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at htls
    obtain ⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩ := htls; exact ⟨t1, t2, t3, t4, t5⟩
  · intro hne; simp only [hne, ↓reduceIte, bne_iff_ne, ne_eq] at htls; exact htls

private theorem hbCheckPhdrTable_hdr {C : HbCliLayout} (h : checkHbPhdrTable C = true) :
    0 < C.std.phnum ∧ C.std.phdrAddr.toNat % 8 = 0 ∧ C.std.phdrBytes.length = C.std.phnum * 56 ∧
    0 < C.std.tlsPhdrIdx ∧ C.std.tlsPhdrIdx < C.std.phnum ∧ C.std.tlsImageAddr.toNat % 8 = 0 ∧
    listReadU32LE C.std.phdrBytes 0 = 6 ∧ listReadU64LE C.std.phdrBytes 16 = C.std.phdrAddr.toNat := by
  have hraw := h; unfold checkHbPhdrTable at hraw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hraw
  obtain ⟨⟨⟨⟨⟨⟨⟨hpos, hal⟩, hlen⟩, hlt⟩, htal⟩, hp0⟩, hpv0⟩, _⟩ := hraw
  refine ⟨hpos, hal, hlen, Classical.byContradiction fun hz => ?_, hlt, htal, hp0, hpv0⟩
  have h7 := ((hbCheckPhdrTable_entry h hpos).2.2.2.1 (by omega : 0 = C.std.tlsPhdrIdx)).1
  rw [Nat.zero_mul, hp0] at h7; omega

private theorem hbMatchesImage_phdr_end {C : HbCliLayout} {S : HbStartupLayout} {img : ElfImage}
    (hm : HbMatchesImage C S img = true) : C.std.phdrAddr.toNat + C.std.phnum * 56 < 2 ^ 64 := by
  obtain ⟨hwf, _, _, _, _, _, hphdr, roSeg, _, _, _, hro, _, _, _, _, _, hroC, _, _⟩ := HbMatchesImage.unpack hm
  have hhdr := hbCheckPhdrTable_hdr hphdr; obtain ⟨hro_idx, rfl⟩ := List.getElem?_eq_some_iff.mp hro
  have ⟨_, _, _, _, hseg_all⟩ := wellFormed_segments_bounds hwf
  have ⟨_, hro_end, _⟩ := hseg_all img.segments[C.roSegIdx] (List.getElem_mem hro_idx)
  unfold checkHbRoSegment at hroC; simp only [Bool.and_eq_true] at hroC
  have hsl := List.all_eq_true.mp hroC.2 (C.std.phdrAddr, C.std.phdrBytes) (by unfold hbRoSegSlices; simp)
  unfold checkSegSlice at hsl; simp only [Bool.and_eq_true, decide_eq_true_eq] at hsl
  have hlen := hhdr.2.2.1; have h1 := hsl.1.2; omega

/-! ## Static TLS Initialization (`hbCopyTls_ok` and `hbStaticInitTls_ok`) -/

private def HbDtvZero (td : BitVec 64) : SepProp :=
  ((td + 0xc0#64) ↦₆₄ 0#64) ∗ ((td + 0x130#64) ↦₆₄ 0#64) ∗ ((td + 0x138#64) ↦₆₄ 0#64)

def HbDtvInit (td : BitVec 64) : SepProp :=
  ((td + 0xc0#64) ↦₆₄ (td + 0x130#64)) ∗ ((td + 0x130#64) ↦₆₄ 1#64) ∗ ((td + 0x138#64) ↦₆₄ (td + 0xd8#64))

def HbBuiltinTlsPad (td : BitVec 64) : SepProp :=
  ((td + 0x2c#64) ↦ₛ List.replicate 0x4c 0#8) ∗ ((td + 0x80#64) ↦ₛ List.replicate 0x18 0#8) ∗
  ((td + 0xa0#64) ↦ₛ List.replicate 0x20 0#8) ∗ ((td + 0xc8#64) ↦ₛ List.replicate 0x10 0#8) ∗
  ((td + 0x108#64) ↦ₛ List.replicate 0x18 0#8) ∗ ((td + 0x128#64) ↦₆₄ 0#64) ∗
  ((td + 0x140#64) ↦ₛ List.replicate 0x10 0#8)

def HbMainTlsInit (L : StdBinaryLayout) : SepProp :=
  (L.mainTlsAddr ↦₆₄ 0#64) ∗ ((L.mainTlsAddr + 0x08#64) ↦₆₄ L.tlsImageAddr) ∗
  ((L.mainTlsAddr + 0x10#64) ↦₆₄ 0x30#64) ∗ ((L.mainTlsAddr + 0x18#64) ↦₆₄ 0x50#64) ∗
  ((L.mainTlsAddr + 0x20#64) ↦₆₄ 8#64) ∗ ((L.mainTlsAddr + 0x28#64) ↦₆₄ 0x10#64)

def HbLibcTlsInit (L : StdBinaryLayout) : SepProp :=
  ((L.libcAddr + 0x10#64) ↦₆₄ L.mainTlsAddr) ∗ ((L.libcAddr + 0x18#64) ↦₆₄ 0x140#64) ∗
  ((L.libcAddr + 0x20#64) ↦₆₄ 8#64) ∗ ((L.libcAddr + 0x28#64) ↦₆₄ 1#64)

def HbTlsState (L : StdBinaryLayout) (sysinfoVal : BitVec 64) : SepProp :=
  StdTdInit L sysinfoVal ∗ HbDtvInit L.builtinTlsAddr ∗
  ((L.builtinTlsAddr + 0xd8#64) ↦ₛ hbTdataBytes) ∗ HbBuiltinTlsPad L.builtinTlsAddr ∗
  HbMainTlsInit L ∗ HbLibcTlsInit L

private theorem hbBuiltinTls_zero_split (td : BitVec 64) :
    (td ↦ₛ List.replicate 0x150 0#8) =
      StdTdZero td ∗ HbDtvZero td ∗ ((td + 0x24#64) ↦₃₂ 0#32) ∗
      ((td + 0xd8#64) ↦ₛ List.replicate 0x30 0#8) ∗ ((td + 0x120#64) ↦₆₄ 0#64) ∗ HbBuiltinTlsPad td := by
  rw [show (0x150 : Nat) = 8 + 0x148 from rfl, pointsToBytes_replicate_split td 8 0x148 0#8,
      pointsToBytes_replicate_split_off td 0x08 8 0x140 0#8, pointsToBytes_replicate_split_off td 0x10 8 0x138 0#8,
      pointsToBytes_replicate_split_off td 0x18 8 0x130 0#8, pointsToBytes_replicate_split_off td 0x20 4 0x12c 0#8,
      pointsToBytes_replicate_split_off td 0x24 4 0x128 0#8, pointsToBytes_replicate_split_off td 0x28 4 0x124 0#8,
      pointsToBytes_replicate_split_off td 0x2c 0x4c 0xd8 0#8, pointsToBytes_replicate_split_off td 0x78 8 0xd0 0#8,
      pointsToBytes_replicate_split_off td 0x80 0x18 0xb8 0#8, pointsToBytes_replicate_split_off td 0x98 8 0xb0 0#8,
      pointsToBytes_replicate_split_off td 0xa0 0x20 0x90 0#8, pointsToBytes_replicate_split_off td 0xc0 8 0x88 0#8,
      pointsToBytes_replicate_split_off td 0xc8 0x10 0x78 0#8, pointsToBytes_replicate_split_off td 0xd8 0x30 0x48 0#8,
      pointsToBytes_replicate_split_off td 0x108 0x18 0x30 0#8, pointsToBytes_replicate_split_off td 0x120 8 0x28 0#8,
      pointsToBytes_replicate_split_off td 0x128 8 0x20 0#8, pointsToBytes_replicate_split_off td 0x130 8 0x18 0#8,
      pointsToBytes_replicate_split_off td 0x138 8 0x10 0#8]
  simp only [StdTdZero, HbDtvZero, HbBuiltinTlsPad, pointsToBytes_replicate4_zero, pointsToBytes_replicate8_zero]; ac_rfl

private theorem hb_satisfies_memRegion_words64 {m : Memory} {base : BitVec 64} (n : Nat) {Rest : SepProp}
    (hn : 8 * n ≤ 2 ^ 64) (hm : m ⊨ memRegion base (8 * n) ∗ Rest) :
    ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ (base ↦₆₄* ws) ∗ Rest) := by
  have hm' := Satisfies.mono (sepConj_mono_left (memRegion_entails_pointsToWords64 n base hn)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨ws, hws⟩ := hm'; rw [sepConj_assoc, satisfies_pure_sepConj] at hws; exact ⟨ws, hws.1, hws.2⟩

private theorem hb_satisfies_words64_memRegion {m : Memory} {base : BitVec 64} (ws : List (BitVec 64))
    {Rest : SepProp} (hn : 8 * ws.length ≤ 2 ^ 64) (hm : m ⊨ (base ↦₆₄* ws) ∗ Rest) :
    m ⊨ memRegion base (8 * ws.length) ∗ Rest :=
  Satisfies.mono (sepConj_mono_left (pointsToWords64_entails_memRegion ws base hn)) hm

@[simp] private theorem hbStaticInitTlsInstrs_length (L : StdBinaryLayout) : (hbStaticInitTlsInstrs L).length = 108 := by simp [hbStaticInitTlsInstrs]
@[simp] private theorem hbLibcStartMainInstrs_length (L : StdBinaryLayout) : (hbLibcStartMainInstrs L).length = 21 := by simp [hbLibcStartMainInstrs, libcStartMainInstrs]
@[simp] private theorem hbInitLibcPreInstrs_length (C : HbCliLayout) (S : HbStartupLayout) : (hbInitLibcPreInstrs C S).length = 53 := by simp [hbInitLibcPreInstrs, initLibcInstrs]

private theorem hb_hasInstrs_fetch_at {P : Program} {base : BitVec 64} {instrs : List Instr}
    (h : hasInstrs P base instrs) (i : Nat) (off : BitVec 64) (inst : Instr)
    (hi : i < instrs.length) (hoff : BitVec.ofNat 64 (4 * i) = off) (hinst : instrs[i]'hi = inst) :
    P.fetch (base + off) = some inst := by rw [← hoff, ← hinst]; exact h i hi

private theorem hb_hasInstrs_fetch_at0 {P : Program} {base : BitVec 64} {instrs : List Instr}
    (h : hasInstrs P base instrs) (inst : Instr) (hi : 0 < instrs.length) (hinst : instrs[0]'hi = inst) :
    P.fetch base = some inst := by rw [← hinst]; simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h 0 hi

@[local simp] private theorem hb_mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).mem = s.mem := by cases r <;> rfl
@[local simp] private theorem hb_mem_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).mem = s.mem := by simp [State.writeReg32]
@[local simp] private theorem hb_mem_setPState (s : State) (p : PState) : (s.setPState p).mem = s.mem := rfl
@[local simp] private theorem hb_mem_advancePC (s : State) : s.advancePC.mem = s.mem := rfl
@[local simp] private theorem hb_mem_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := rfl
@[local simp] private theorem hb_mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl
@[local simp] private theorem hb_tlsFields_rfl (s : State) : StdTlsFieldsPreserved s s := .rfl s
@[local simp] private theorem hb_tlsFields_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) : StdTlsFieldsPreserved s0 (s.writeReg64 r v) ↔ StdTlsFieldsPreserved s0 s := by cases r <;> simp [State.writeReg64, StdTlsFieldsPreserved]
@[local simp] private theorem hb_tlsFields_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) : StdTlsFieldsPreserved s0 (s.writeReg32 r v) ↔ StdTlsFieldsPreserved s0 s := by simp [State.writeReg32]
@[local simp] private theorem hb_tlsFields_setPState (s0 s : State) (p : PState) : StdTlsFieldsPreserved s0 (s.setPState p) ↔ StdTlsFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem hb_tlsFields_advancePC (s0 s : State) : StdTlsFieldsPreserved s0 s.advancePC ↔ StdTlsFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem hb_tlsFields_setPC (s0 s : State) (pc : BitVec 64) : StdTlsFieldsPreserved s0 (s.setPC pc) ↔ StdTlsFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem hb_tlsFields_setMem {s0 s : State} {m : Memory} (hp : m.perm = s.mem.perm) : StdTlsFieldsPreserved s0 (s.setMem m) ↔ StdTlsFieldsPreserved s0 s := by simp [State.setMem, StdTlsFieldsPreserved, hp]
@[local simp] private theorem hb_stdPres_rfl (s : State) : StdStatePreserved s s := .rfl s
@[local simp] private theorem hb_stdPres_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) : StdStatePreserved s0 (s.writeReg64 r v) ↔ StdStatePreserved s0 s := by cases r <;> simp [State.writeReg64, StdStatePreserved]
@[local simp] private theorem hb_stdPres_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) : StdStatePreserved s0 (s.writeReg32 r v) ↔ StdStatePreserved s0 s := by simp [State.writeReg32]
@[local simp] private theorem hb_stdPres_setPState (s0 s : State) (p : PState) : StdStatePreserved s0 (s.setPState p) ↔ StdStatePreserved s0 s := Iff.rfl
@[local simp] private theorem hb_stdPres_advancePC (s0 s : State) : StdStatePreserved s0 s.advancePC ↔ StdStatePreserved s0 s := Iff.rfl
@[local simp] private theorem hb_stdPres_setPC (s0 s : State) (pc : BitVec 64) : StdStatePreserved s0 (s.setPC pc) ↔ StdStatePreserved s0 s := Iff.rfl
@[local simp] private theorem hb_stdPres_setMem {s0 s : State} {m : Memory} (hp : m.perm = s.mem.perm) : StdStatePreserved s0 (s.setMem m) ↔ StdStatePreserved s0 s := by simp [State.setMem, StdStatePreserved, hp]

private theorem hb_decode_nop : decodeWord 0xd503201f#32 = .nop := rfl
private theorem hb_decode_movz_x2_0 : decodeWord 0xd2800002#32 = .moveWide .W64 .MOVZ .x2 0#16 0 := rfl

local elab "hb_have_fetches " hc:ident lo:num hi:num : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let hcExpr ← Lean.Elab.Tactic.elabTerm hc none; let hcTy ← Lean.instantiateMVars (← Lean.Meta.inferType hcExpr)
    let instrsExpr := hcTy.getArg! 2; let mut cur ← Lean.Meta.whnfD instrsExpr; let mut elems : Array Lean.Expr := #[]
    while cur.isAppOfArity ``List.cons 3 do elems := elems.push (cur.getArg! 1); cur ← Lean.Meta.whnfD (cur.getArg! 2)
    for i in [lo.getNat : hi.getNat + 1] do
      let some instExpr := elems[i]? | throwError "hb_have_fetches: index {i} out of range ({elems.size})"
      let lenE ← Lean.Meta.mkAppM ``List.length #[instrsExpr]; let hiTy ← Lean.Meta.mkAppM ``LT.lt #[Lean.mkNatLit i, lenE]
      let hiGoal ← Lean.Meta.mkFreshExprMVar hiTy; let saved ← Lean.Elab.Tactic.getGoals; Lean.Elab.Tactic.setGoals [hiGoal.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| (simp only [initTpInstrs_length, copyTlsInstrs_length, staticInitTlsInstrs_length, hbStaticInitTlsInstrs_length, hbLibcStartMainInstrs_length, hbInitLibcPreInstrs_length, List.length_cons, List.length_nil, List.length_append, List.length_take, List.length_drop, decodeWords]; omega))); Lean.Elab.Tactic.setGoals saved
      let prf ← if i == 0 then Lean.Meta.mkAppM ``hb_hasInstrs_fetch_at0 #[hcExpr, instExpr, hiGoal, ← Lean.Meta.mkEqRefl instExpr]
        else let offE ← Lean.Meta.mkAppM ``BitVec.ofNat #[Lean.mkNatLit 64, Lean.mkNatLit (4 * i)]
             Lean.Meta.mkAppM ``hb_hasInstrs_fetch_at #[hcExpr, Lean.mkNatLit i, offE, instExpr, hiGoal, ← Lean.Meta.mkEqRefl offE, ← Lean.Meta.mkEqRefl instExpr]
      let hName := Lean.Name.mkSimple s!"_hf_{i}"
      let g ← Lean.Elab.Tactic.getMainGoal; let (_, g') ← (← g.assert hName (← Lean.Meta.inferType prf) prf).intro1P; Lean.Elab.Tactic.replaceMainGoal [g']
      let hId := Lean.mkIdent hName
      Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [hb_decode_nop, hb_decode_movz_x2_0] at $hId:ident))

local elab "hb_clear_fetches " lo:num hi:num : tactic => do
  for i in [lo.getNat : hi.getNat + 1] do
    let hId := Lean.mkIdent (Lean.Name.mkSimple s!"_hf_{i}")
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear $hId))

local elab (priority := high) "have_instrs" h:ident startIdx:num count:num : tactic => do
  for k in [0:count.getNat] do
    let i := startIdx.getNat + k; let fnId := Lean.Name.mkSimple s!"hf_{i}"; let fnName := Lean.mkIdent fnId
    let iStx := Lean.Syntax.mkNumLit (toString i); let offStx := Lean.Syntax.mkNumLit (toString (4 * i))
    if i == 0 then Lean.Elab.Tactic.evalTactic (← `(tactic| have $fnName := ProofLib.StdStartup.hasInstrs.fetch_at_zero $h))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| have $fnName := ProofLib.StdStartup.hasInstrs.fetch_at $h $iStx (off := BitVec.ofNat 64 $offStx)))
    Lean.Elab.Tactic.liftMetaTactic1 fun mvarId => mvarId.withContext do
      let some decl := (← Lean.MonadLCtx.getLCtx).findFromUserName? fnId | return mvarId
      let ty ← Lean.instantiateMVars decl.type
      if ty.isAppOfArity ``Eq 3 && ty.appArg!.isAppOfArity ``Option.some 2 && ty.appArg!.appArg!.isAppOfArity ``ProofLib.StdStartup.decodeWord 1 then
        let instRaw ← Lean.Meta.reduce ty.appArg!.appArg! (explicitOnly := false) (skipTypes := true) (skipProofs := true)
        let instClean ← Lean.Meta.transform instRaw (pre := fun sub => do
          if sub.isAppOfArity ``BitVec.ofFin 2 && (sub.getArg! 1).isAppOfArity ``Fin.mk 3 then
            return .done (Lean.mkApp2 (Lean.mkConst ``BitVec.ofNat) (sub.getArg! 0) ((sub.getArg! 1).getArg! 1))
          return .continue)
        let newTy ← Lean.Meta.mkEq (ty.getArg! 1) (Lean.mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``Instr) instClean)
        let (_, mvarId') ← (← mvarId.assert fnId newTy decl.toExpr).intro1P; return ← mvarId'.tryClear decl.fvarId
      return mvarId
    if i != 0 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv at $fnName:ident => lhs; try simp (config := { ground := true }) only [BitVec.add_assoc]))

private theorem hb_step_str8_perm {prog : Program} {target_pc : BitVec 64} {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : (s.readReg32 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P') (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s') (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; have htrunc : (s.readReg64 rt).truncate 8 = val := bitvec_truncate8_truncate32 _ ▸ hval
  let m' := s.mem.write8 ea val; have hm' : m' ⊨ P' ∗ R := hstore.store hm; have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write8 s.mem ea val); unfold SepWP at hn; exact hn R hm'

private theorem hb_step_str32_perm {prog : Program} {target_pc : BitVec 64} {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hfetch : prog.fetch pc = some (.str .W32 rt addr)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P') (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s') (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val; have hm' : m' ⊨ P' ∗ R := hstore.store hm; have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write32 s.mem ea val); unfold SepWP at hn; exact hn R hm'

private theorem hb_step_str64_perm {prog : Program} {target_pc : BitVec 64} {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P') (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s') (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m' := s.mem.write64 ea val; have hm' : m' ⊨ P' ∗ R := hstore.store hm; have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write64 s.mem ea val); unfold SepWP at hn; exact hn R hm'

private theorem hb_step_stp64_perm {prog : Program} {target_pc : BitVec 64} {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc ea ea2 : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2) (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s') (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) : SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2; have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm; have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1; rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]; have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)); unfold SepWP at hn; exact hn R hm2

private theorem hb_hasInstrs_of_hasWords {P : Program} {addr : BitVec 64} {ws : List (BitVec 32)}
    (hw : P.hasWords addr ws) (hdec : ws.all (fun w => (Arm64.decode w).isSome) = true := by decide) :
    hasInstrs P addr (decodeWords ws) := by
  intro i hi; simp only [decodeWords, List.length_map] at hi
  obtain ⟨inst, hinst⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hdec ws[i] (List.getElem_mem hi))
  simp [Program.fetch_of_hasWords hw i hi, decodeWords, decodeWord, hinst]

private theorem hb_spAligned_of_mod16 {sp : BitVec 64} (h : sp.toNat % 16 = 0) :
    (sp &&& 15#64 == 0#64) = true := by
  rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]
  change sp.toNat &&& (2 ^ 4 - 1) = 0; rw [Nat.and_two_pow_sub_one_eq_mod]; exact h

private theorem hb_spAligned_sub {sp0 : BitVec 64} (h : sp0.toNat % 16 = 0) (off : BitVec 64)
    (hoff : off.toNat % 16 = 0 := by decide) : ((sp0 - off) &&& 15#64 == 0#64) = true :=
  hb_spAligned_of_mod16 (by rw [BitVec.toNat_sub]; omega)

local elab "hb_wp_steps_p " n:num : tactic => do
  for _ in [0 : n.getNat] do
    Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal; let gTy := (← Lean.instantiateMVars (← g.getType)).consumeMData; let mut handled := false
      if gTy.isAppOfArity ``SepWP 6 then
        let sExpr := gTy.getArg! 2
        for decl in (← Lean.MonadLCtx.getLCtx) do
          if !handled && (decl.userName.toString.startsWith "_hf_" || decl.userName.toString.startsWith "hf_") then
            let ty := (← Lean.instantiateMVars decl.type).consumeMData
            if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Program.fetch 2 && (ty.getArg! 2).isAppOfArity ``Option.some 2 then
              let pcExpr := (ty.getArg! 1).getArg! 1; let inst := (ty.getArg! 2).getArg! 1
              let isStr := inst.isAppOfArity ``Instr.str 3 && ((inst.getArg! 0).isConstOf ``MemWidth.B8 || (inst.getArg! 0).isConstOf ``MemWidth.W32 || (inst.getArg! 0).isConstOf ``MemWidth.X64)
              let isStp := inst.isAppOfArity ``Instr.stp 4 && (inst.getArg! 0).isConstOf ``RegWidth.W64
              if isStr || isStp then
                let pcEqTy ← Lean.Meta.mkEq (Lean.mkApp (Lean.mkConst ``State.pc) sExpr) pcExpr
                let sv ← Lean.Elab.Tactic.saveState; let msgCnt := (← Lean.Core.getMessageLog).toList.length
                let pcOk ← try
                  let m ← Lean.Meta.mkFreshExprMVar pcEqTy; let savedG ← Lean.Elab.Tactic.getGoals; Lean.Elab.Tactic.setGoals [m.mvarId!]
                  Lean.Elab.Tactic.evalTactic (← `(tactic| (simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)))
                  let rem ← Lean.Elab.Tactic.getGoals; Lean.Elab.Tactic.setGoals savedG; pure (rem.isEmpty && (← Lean.Core.getMessageLog).toList.length == msgCnt)
                catch _ => pure false
                sv.restore
                if pcOk then
                  let hfId := Lean.mkIdent decl.userName; handled := true
                  if isStr then
                    let rId := if (inst.getArg! 0).isConstOf ``MemWidth.B8 then Lean.mkCIdent ``hb_step_str8_perm else if (inst.getArg! 0).isConstOf ``MemWidth.W32 then Lean.mkCIdent ``hb_step_str32_perm else Lean.mkCIdent ``hb_step_str64_perm
                    Lean.Elab.Tactic.evalTactic (← `(tactic| (apply $rId; (wp_focus_close (exact $hfId)); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs); intro _ _hp; try simp only [hb_mem_writeReg64, hb_mem_writeReg32, hb_mem_setPState, hb_mem_advancePC, hb_mem_setPC, hb_mem_setMem] at _hp)))
                  else
                    let stpId := Lean.mkCIdent ``hb_step_stp64_perm
                    Lean.Elab.Tactic.evalTactic (← `(tactic| (apply $stpId; (wp_focus_close (exact $hfId)); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs); intro _ _hp; try simp only [hb_mem_writeReg64, hb_mem_writeReg32, hb_mem_setPState, hb_mem_advancePC, hb_mem_setPC, hb_mem_setMem] at _hp)))
      if !handled then Lean.Elab.Tactic.evalTactic (← `(tactic| wp_step))

private theorem hb_align8_and_seven {a : BitVec 64} (h : a.toNat % 8 = 0) : a &&& 7#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]
  change a.toNat &&& (2 ^ 3 - 1) = 0; rw [Nat.and_two_pow_sub_one_eq_mod]; exact h

private theorem hb_copyTls_align_zero {a : BitVec 64} (h : a.toNat % 8 = 0) :
    7#64 &&& (0xffffffffffffff38#64 - a) = 0#64 := by
  have := hb_align8_and_seven h; bv_bits

private def hbCopyTlsSpec (L : StdBinaryLayout) : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = L.builtinTlsAddr⌝ ∗
    (memRegion (s0.sp - 0x50#64) 0x50 ∗ HbDtvZero L.builtinTlsAddr ∗
      ((L.builtinTlsAddr + 0xd8#64) ↦ₛ List.replicate 0x30 0#8) ∗
      (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ HbMainTlsInit L ∗ HbLibcTlsInit L)
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = L.builtinTlsAddr ∧ StdStatePreserved s0 sf⌝ ∗
    (memRegion (sf.sp - 0x50#64) 0x50 ∗ HbDtvInit L.builtinTlsAddr ∗
      ((L.builtinTlsAddr + 0xd8#64) ↦ₛ hbTdataBytes) ∗
      (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ HbMainTlsInit L ∗ HbLibcTlsInit L)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

section
arm64_proof_prelude

private theorem hbCopyTls_ok {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.copyTlsAddr (copyTlsInstrs L)) (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (halign : L.builtinTlsAddr.toNat % 8 = 0) (hmain_nz : L.mainTlsAddr ≠ 0#64) :
    subroutine_ok P L.copyTlsAddr (hbCopyTlsSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbCopyTlsSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hx0, hpre⟩; rw [sepConj_assoc] at hpre
  obtain ⟨ws, hws_len, hpre⟩ := hb_satisfies_memRegion_words64 10 (by decide) hpre
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ | ⟨w9, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hws_len)
  simp only [pointsToWords64_cons, pointsToWords64_nil, HbDtvZero, HbMainTlsInit, HbLibcTlsInit, sepConj_emp, sepConj_assoc] at hpre
  have ha1 : s0.sp - 0x50#64 + 8#64 = s0.sp - 0x48#64 := by bv_lin
  have ha2 : s0.sp - 0x48#64 + 8#64 = s0.sp - 0x40#64 := by bv_lin
  have ha3 : s0.sp - 0x40#64 + 8#64 = s0.sp - 0x38#64 := by bv_lin
  have ha4 : s0.sp - 0x38#64 + 8#64 = s0.sp - 0x30#64 := by bv_lin
  have ha5 : s0.sp - 0x30#64 + 8#64 = s0.sp - 0x28#64 := by bv_lin
  have ha6 : s0.sp - 0x28#64 + 8#64 = s0.sp - 0x20#64 := by bv_lin
  have ha7 : s0.sp - 0x20#64 + 8#64 = s0.sp - 0x18#64 := by bv_lin
  have ha8 : s0.sp - 0x18#64 + 8#64 = s0.sp - 0x10#64 := by bv_lin
  have ha9 : s0.sp - 0x10#64 + 8#64 = s0.sp - 0x08#64 := by bv_lin
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at hpre
  refine ⟨((s0.sp - 0x50#64) ↦₆₄ w0) ∗ ((s0.sp - 0x48#64) ↦₆₄ w1) ∗ ((s0.sp - 0x40#64) ↦₆₄ w2) ∗ ((s0.sp - 0x38#64) ↦₆₄ w3) ∗
    ((s0.sp - 0x30#64) ↦₆₄ w4) ∗ ((s0.sp - 0x28#64) ↦₆₄ w5) ∗ ((s0.sp - 0x20#64) ↦₆₄ w6) ∗ ((s0.sp - 0x18#64) ↦₆₄ w7) ∗
    ((s0.sp - 0x10#64) ↦₆₄ w8) ∗ ((s0.sp - 0x08#64) ↦₆₄ w9) ∗ ((L.builtinTlsAddr + 0xc0#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x130#64) ↦₆₄ 0#64) ∗
    ((L.builtinTlsAddr + 0x138#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0xd8#64) ↦ₛ List.replicate 0x30 0#8) ∗ (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗
    (L.mainTlsAddr ↦₆₄ 0#64) ∗ ((L.mainTlsAddr + 0x08#64) ↦₆₄ L.tlsImageAddr) ∗ ((L.mainTlsAddr + 0x10#64) ↦₆₄ 0x30#64) ∗
    ((L.mainTlsAddr + 0x18#64) ↦₆₄ 0x50#64) ∗ ((L.mainTlsAddr + 0x20#64) ↦₆₄ 8#64) ∗ ((L.mainTlsAddr + 0x28#64) ↦₆₄ 0x10#64) ∗
    ((L.libcAddr + 0x10#64) ↦₆₄ L.mainTlsAddr) ∗ ((L.libcAddr + 0x18#64) ↦₆₄ 0x140#64) ∗ ((L.libcAddr + 0x20#64) ↦₆₄ 8#64) ∗ ((L.libcAddr + 0x28#64) ↦₆₄ 1#64),
    by simpa only [sepConj_assoc] using hpre, ?_⟩
  have halign0 : 7#64 &&& (0xffffffffffffff38#64 - L.builtinTlsAddr) = 0#64 := hb_copyTls_align_zero halign
  hb_have_fetches hc 0 21; hb_wp_steps_p 16; (try simp only [halign0, BitVec.add_zero]); hb_wp_steps_p 6
  hb_clear_fetches 0 21; hb_have_fetches hc 22 29; wp_step; wp_if hcbz1
  · exact absurd (by simpa [wp_norm, arm64_norm] using hcbz1) hmain_nz
  · hb_wp_steps_p 7
    have hdst_mr : ((L.builtinTlsAddr + 0xd8#64) ↦ₛ List.replicate 0x30 0#8) ⊢ memRegion (L.builtinTlsAddr + 0xd8#64) hbTdataBytes.length :=
      pointsToBytes_entails_memRegion_of_length (by rw [hbTdataBytes_length]; rfl)
    refine ops.call_memcpy_ro (ret_pc := L.copyTlsAddr + 0x78#64) (dst := L.builtinTlsAddr + 0xd8#64) (src := L.tlsImageAddr) (bs := hbTdataBytes)
      (F := ?F_mc) (fun _ hm => Satisfies.mono (sepConj_mono_left (sepConj_mono_left hdst_mr)) (Satisfies.mono (by sep_frame) hm))
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (hx2 := by rw [hbTdataBytes_length]; simp [wp_norm, arm64_norm])
      (hlen := by rw [hbTdataBytes_length]; decide)
    have hstd01 : StdStatePreserved s0 sf1 := StdStatePreserved.trans (by simp [*]) hstd1
    obtain ⟨hc19, _, _, hc22, hc23, hc24, hc25, hc26, hc27, hc28, _, hcv⟩ := hcs1
    simp only [wp_norm, arm64_norm] at hc19 hc22 hc23 hc24 hc25 hc26 hc27 hc28 hcv
    have hsp1_eq : sf1.sp = s0.sp - 0x50#64 := by rw [hsp1]; simp [wp_norm, arm64_norm]
    have hsp1_align : sf1.spAligned = true := by simp only [State.spAligned, hsp1_eq, beq_iff_eq] at hsp_align ⊢; bv_bits
    hb_clear_fetches 22 29; hb_have_fetches hc 30 31; hb_have_fetches hc 22 22; hb_have_fetches hc 32 42; hb_wp_steps_p 14
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, hc27, hc28, hcv]⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *]⟩, ?_⟩
    simp only [wp_norm, arm64_norm] at hm ⊢
    simpa only [List.length_cons, List.length_nil, sepConj_assoc] using hb_satisfies_words64_memRegion (base := s0.sp - 0x50#64)
      [s0.readReg64 .x29, s0.readReg64 .x30, s0.readReg64 .x19, s0.readReg64 .x20, s0.readReg64 .x21,
       s0.readReg64 .x22, s0.readReg64 .x23, s0.readReg64 .x24, s0.readReg64 .x25, s0.readReg64 .x26]
      (Rest := HbDtvInit L.builtinTlsAddr ∗ ((L.builtinTlsAddr + 0xd8#64) ↦ₛ hbTdataBytes) ∗ (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ HbMainTlsInit L ∗ HbLibcTlsInit L ∗ R)
      (by simp) (by simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, HbDtvInit, HbMainTlsInit, HbLibcTlsInit, arm64_norm] at hm ⊢; ac_nf at hm ⊢)

end

private theorem hb_bitvec_ofNat_or (w x y : Nat) :
    BitVec.ofNat w (x ||| y) = BitVec.ofNat w x ||| BitVec.ofNat w y := by ext i hi; simp
private theorem hb_bitvec_ofNat_u8 (w : Nat) (b : BitVec 8) :
    BitVec.ofNat w b.toNat = b.zeroExtend w := by ext i hi; simp
private theorem hb_bitvec_ofNat_u8_shl (w : Nat) (b : BitVec 8) (k : Nat) :
    BitVec.ofNat w (b.toNat <<< k) = (b.zeroExtend w) <<< k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.testBit_toNat, hi, decide_true, Bool.true_and]
  by_cases hk : k ≤ i
  · simp [hk, show ¬(i < k) by omega, show i - k < w by omega]
  · simp [hk, show i < k by omega]

private theorem hb_u32_pack (b0 b1 b2 b3 : BitVec 8) :
    BitVec.ofNat 32 (b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24)) =
      b3 ++ b2 ++ b1 ++ b0 := by
  rw [hb_bitvec_ofNat_or, hb_bitvec_ofNat_or, hb_bitvec_ofNat_or, hb_bitvec_ofNat_u8,
      hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, Nat.sub_sub, hi, decide_true, Bool.true_and]; repeat' split
  all_goals simp (discharger := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false]

private theorem hb_listReadU32LE_lt {bs : List (BitVec 8)} {off : Nat} (hle : off + 4 ≤ bs.length) :
    listReadU32LE bs off < 2 ^ 32 := by
  have hlen : 4 ≤ (bs.drop off).length := by simp; omega
  rcases hd : bs.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;> try (rw [hd] at hlen; simp at hlen)
  unfold listReadU32LE; rw [hd]
  have h0 : b0.toNat < 2 ^ 32 := by have := b0.isLt; omega
  have h1 : b1.toNat <<< 8 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; have := b1.isLt; omega
  have h2 : b2.toNat <<< 16 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; have := b2.isLt; omega
  have h3 : b3.toNat <<< 24 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; have := b3.isLt; omega
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h0 h1) h2) h3

private theorem hb_phdr_dup_u32 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat) (hle : off + 4 ≤ bs.length) :
    ((base ↦ᵣ bs) ∗ ((base + BitVec.ofNat 64 off) ↦₃₂ᵣ BitVec.ofNat 32 (listReadU32LE bs off))) = (base ↦ᵣ bs) := by
  have hlen : 4 ≤ (bs.drop off).length := by simp; omega
  rcases hd : bs.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;> try (rw [hd] at hlen; simp at hlen)
  have hdup := pointsToBytesRO_dup_slice base bs off 4 hle; rw [hd] at hdup
  simp only [List.take] at hdup; rw [pointsToBytesRO4_eq_pointsTo32RO] at hdup
  have hv : BitVec.ofNat 32 (listReadU32LE bs off) = b3 ++ b2 ++ b1 ++ b0 := by
    unfold listReadU32LE; rw [hd]; exact hb_u32_pack b0 b1 b2 b3
  rwa [hv]

private theorem hb_phdr_dup_u64 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat) (hle : off + 8 ≤ bs.length) :
    ((base ↦ᵣ bs) ∗ ((base + BitVec.ofNat 64 off) ↦₆₄ᵣ BitVec.ofNat 64 (listReadU64LE bs off))) = (base ↦ᵣ bs) := by
  have hlen : 8 ≤ (bs.drop off).length := by simp; omega
  rcases hd : bs.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [hd] at hlen; simp at hlen)
  have hdup := pointsToBytesRO_dup_slice base bs off 8 hle; rw [hd] at hdup
  simp only [List.take] at hdup; rw [pointsToBytesRO8_eq_pointsTo64RO] at hdup
  have hv : BitVec.ofNat 64 (listReadU64LE bs off) = b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
    unfold listReadU64LE
    rw [hd, hb_bitvec_ofNat_or, hb_bitvec_ofNat_or, hb_bitvec_ofNat_or, hb_bitvec_ofNat_or,
        hb_bitvec_ofNat_or, hb_bitvec_ofNat_or, hb_bitvec_ofNat_or, hb_bitvec_ofNat_u8,
        hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl,
        hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl, hb_bitvec_ofNat_u8_shl]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_append, Nat.sub_sub, hi, decide_true, Bool.true_and]; repeat' split
    all_goals simp (discharger := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false]
  rwa [hv]

private theorem hb_ofNat32_eq_iff {n c : Nat} (hn : n < 2 ^ 32) (hc : c < 2 ^ 32) :
    BitVec.ofNat 32 n = BitVec.ofNat 32 c ↔ n = c :=
  ⟨fun h => by have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hc] using this,
   fun h => h ▸ rfl⟩

section
arm64_proof_prelude

private theorem hbStaticInitTls_phdr_loop {P : Program} {C : HbCliLayout}
    (hc : hasInstrs P C.std.staticInitTlsAddr (hbStaticInitTlsInstrs C.std))
    (hphdr : checkHbPhdrTable C = true) (hphdr_end : C.std.phdrAddr.toNat + C.std.phnum * 56 < 2 ^ 64)
    (auxPtr : BitVec 64) :
    ∀ (rem idx : Nat), 1 ≤ idx → idx + rem = C.std.phnum →
      ∀ {target_pc : BitVec 64} (s : State) (F : SepProp) {post : State → SepProp → Prop} {oom : State → SepProp},
      s.pc = C.std.staticInitTlsAddr + 0x54#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x0 = auxPtr → s.readReg64 .x1 = C.std.phdrAddr + BitVec.ofNat 64 ((idx - 1) * 56) →
      s.readReg64 .x3 = 0#64 → s.readReg64 .x4 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x6 = (if C.std.tlsPhdrIdx < idx then C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56) else 0#64) →
      s.readReg64 .x7 = C.std.defaultStacksizeAddr → s.readReg64 .x9 = C.std.phdrAddr → s.readReg64 .x10 = 0x6474e551#64 →
      (∀ sf : State, sf.pc = C.std.staticInitTlsAddr + 0xb0#64 → sf.status = .Running → sf.sp = s.sp →
        CalleeSavedPreserved s sf → sf.mem = s.mem → StdStatePreserved s sf → sf.readReg64 .x3 = 0#64 →
        sf.readReg64 .x6 = C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56) →
        SepWP P target_pc sf (((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F) post oom) →
      SepWP P target_pc s (((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F) post oom := by
  obtain ⟨_, _, hplen, _, htls_lt, _, _, _⟩ := hbCheckPhdrTable_hdr hphdr
  intro rem; induction rem with
  | zero =>
    intro idx hidx1 hsum target_pc s F post oom hpc hrun hsp hx0 hx1 hx3 hx4 hx6 hx7 hx9 hx10 hnext
    have hidx_eq : idx = C.std.phnum := by omega
    hb_have_fetches hc 21 24; hb_wp_steps_p 4
    exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm]) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [*]) (by simp [wp_norm, arm64_norm, hx3])
      (by simp [wp_norm, arm64_norm, hx6, hidx_eq, htls_lt])
  | succ rem' ih =>
    intro idx hidx1 hsum target_pc s F post oom hpc hrun hsp hx0 hx1 hx3 hx4 hx6 hx7 hx9 hx10 hnext
    have hidx_lt : idx < C.std.phnum := by omega
    have hent := hbCheckPhdrTable_entry hphdr hidx_lt
    have hx4_sub : BitVec.ofNat 64 (rem' + 1 + 1) - 1#64 = BitVec.ofNat 64 (rem' + 1) := by
      rw [show BitVec.ofNat 64 (rem' + 1 + 1) = BitVec.ofNat 64 (rem' + 1) + 1#64 by simp [BitVec.ofNat_add]]; bv_lin
    have hx4_nz : BitVec.ofNat 64 (rem' + 1) ≠ 0#64 := by
      intro hz; have := congrArg BitVec.toNat hz; simp [Nat.mod_eq_of_lt (by omega : rem' + 1 < 2 ^ 64)] at this
    have hx1_next : C.std.phdrAddr + BitVec.ofNat 64 ((idx - 1) * 56) + 56#64 = C.std.phdrAddr + BitVec.ofNat 64 (idx * 56) := by
      rw [BitVec.add_assoc, show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, ← BitVec.ofNat_add, show (idx - 1) * 56 + 56 = idx * 56 by omega]
    have hx6_of_ne (hne : idx ≠ C.std.tlsPhdrIdx) :
        (if C.std.tlsPhdrIdx < idx then C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56) else 0#64) =
        (if C.std.tlsPhdrIdx < idx + 1 then C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56) else 0#64) := by
      by_cases hlt : C.std.tlsPhdrIdx < idx <;> simp [hlt, show C.std.tlsPhdrIdx < idx + 1 ↔ C.std.tlsPhdrIdx < idx by omega]
    hb_have_fetches hc 15 29; hb_have_fetches hc 34 39; hb_wp_steps_p 3; wp_step; wp_if hcbz
    · exact absurd (by simpa [wp_norm, arm64_norm, hx4_sub] using hcbz) hx4_nz
    · have hdup_pt := hb_phdr_dup_u32 C.std.phdrAddr C.std.phdrBytes (idx * 56) (by omega)
      have hpt_lt := hb_listReadU32LE_lt (bs := C.std.phdrBytes) (off := idx * 56) (by omega)
      (wp_conv_pre => rw [← hdup_pt]); hb_wp_steps_p 2; wp_step; (wp_conv_pre => rw [hdup_pt]); wp_if heq6
      · have hpt6 : listReadU32LE C.std.phdrBytes (idx * 56) = 6 := by
          (try simp only [wp_norm, arm64_norm, hx1_next] at heq6); exact (hb_ofNat32_eq_iff hpt_lt (by decide)).mp heq6
        have hdup_pv := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes (idx * 56 + 16) (by omega)
        rw [hent.2.1 hpt6, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add] at hdup_pv
        (wp_conv_pre => rw [← hdup_pv]); hb_wp_steps_p 3; (wp_conv_pre => rw [hdup_pv])
        have hx6_next := hx6_of_ne (fun heq => by have := (hent.2.2.2.1 heq).1; omega)
        refine ih (idx + 1) (by omega) (by omega) _ F (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp) (by simp [wp_norm, arm64_norm, hx0]) (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx6, hx6_next]) (by simp [wp_norm, arm64_norm, hx7])
          (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
            hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f) (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
              (by simpa only [wp_norm, arm64_norm] using hmem_f) (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
      · hb_wp_steps_p 1; wp_step; wp_if hne2
        · hb_wp_steps_p 1; wp_step; wp_if hne7
          · have hpt_ne7 : listReadU32LE C.std.phdrBytes (idx * 56) ≠ 7 := fun h7 => hne7 (by simp [wp_norm, arm64_norm, h7])
            have hx6_next := hx6_of_ne (fun heq => hpt_ne7 (hent.2.2.2.1 heq).1); hb_wp_steps_p 1; wp_step; wp_if hne_st
            · refine ih (idx + 1) (by omega) (by omega) _ F (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
                (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp) (by simp [wp_norm, arm64_norm, hx0]) (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm, hx3]) (by simp only [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx6, hx6_next]) (by simp [wp_norm, arm64_norm, hx7])
                (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
                  hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f) (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
                    (by simpa only [wp_norm, arm64_norm] using hmem_f) (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
            · have hpt_st : listReadU32LE C.std.phdrBytes (idx * 56) = 0x6474e551 := by
                (try simp only [wp_norm, arm64_norm, Classical.not_not] at hne_st); exact (hb_ofNat32_eq_iff hpt_lt (by decide)).mp hne_st
              have hdup_msz := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes (idx * 56 + 40) (by omega); rw [hent.2.2.1 hpt_st, BitVec.ofNat_add] at hdup_msz
              (wp_conv_pre => rw [← hdup_msz]); hb_wp_steps_p 4; (wp_conv_pre => rw [hdup_msz])
              refine ih (idx + 1) (by omega) (by omega) _ F (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
                (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp) (by simp [wp_norm, arm64_norm, hx0]) (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm, hx3]) (by simp only [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx6, hx6_next]) (by simp [wp_norm, arm64_norm, hx7])
                (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
                  hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f) (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
                    (by simpa only [wp_norm, arm64_norm] using hmem_f) (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
          · have hpt7 : listReadU32LE C.std.phdrBytes (idx * 56) = 7 := by
              (try simp only [wp_norm, arm64_norm, Classical.not_not] at hne7); exact (hb_ofNat32_eq_iff hpt_lt (by decide)).mp hne7
            hb_wp_steps_p 1; have hidx_tls : idx = C.std.tlsPhdrIdx := Classical.byContradiction fun hne => hent.2.2.2.2 hne hpt7
            refine ih (idx + 1) (by omega) (by omega) _ F (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
              (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp) (by simp [wp_norm, arm64_norm, hx0]) (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hx3]) (by simp only [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hidx_tls]) (by simp [wp_norm, arm64_norm, hx7])
              (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10]) fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
                hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f) (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
                  (by simpa only [wp_norm, arm64_norm] using hmem_f) (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
        · exfalso; apply hent.1; (try simp only [wp_norm, arm64_norm, Classical.not_not] at hne2); exact (hb_ofNat32_eq_iff hpt_lt (by decide)).mp hne2

private theorem hbStaticInitTls_setup {P : Program} {C : HbCliLayout}
    (hc : hasInstrs P C.std.staticInitTlsAddr (hbStaticInitTlsInstrs C.std))
    (hphdr : checkHbPhdrTable C = true) (hphdr_end : C.std.phdrAddr.toNat + C.std.phnum * 56 < 2 ^ 64)
    {target_pc : BitVec 64} (s : State) (F : SepProp) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = C.std.staticInitTlsAddr + 0xb0#64) (hrun : s.status = .Running)
    (hx3 : s.readReg64 .x3 = 0#64) (hx6 : s.readReg64 .x6 = C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56))
    (hnext : ∀ sf : State, sf.pc = C.std.staticInitTlsAddr + 0x190#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → StdStatePreserved s sf → sf.readReg64 .x0 = C.std.builtinTlsAddr →
      SepWP P target_pc sf ((C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ HbMainTlsInit C.std ∗ HbLibcTlsInit C.std ∗ F) post oom) :
    SepWP P target_pc s ((C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ StdMainTlsZero C.std ∗ StdLibcTlsZero C.std ∗ F) post oom := by
  obtain ⟨_, _, hplen, _, htls_lt, hti_al, _, _⟩ := hbCheckPhdrTable_hdr hphdr
  obtain ⟨_, hpv, hfsz, hmsz, haln⟩ := (hbCheckPhdrTable_entry hphdr htls_lt).2.2.2.1 rfl
  have hx6_nz : C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56) ≠ 0#64 := by
    intro hz; have htn := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : C.std.tlsPhdrIdx * 56 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : C.std.phdrAddr.toNat + C.std.tlsPhdrIdx * 56 < 2 ^ 64)] at htn; omega
  have hal1a : (-(0x50#64 + C.std.tlsImageAddr)) &&& 7#64 = 0#64 := by have := hb_align8_and_seven hti_al; bv_bits
  have hal1b : (0#64 - (0x50#64 + C.std.tlsImageAddr)) &&& 7#64 = 0#64 := by have := hb_align8_and_seven hti_al; bv_bits
  have hal2 : (C.std.tlsImageAddr - 0x10#64) &&& 7#64 = 0#64 := by have := hb_align8_and_seven hti_al; bv_bits
  have hdup16 := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes (C.std.tlsPhdrIdx * 56 + 16) (by omega)
  rw [hpv, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup16
  have hdup32 := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes (C.std.tlsPhdrIdx * 56 + 32) (by omega)
  rw [hfsz, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup32
  have hdup40 := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes (C.std.tlsPhdrIdx * 56 + 40) (by omega)
  rw [hmsz, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup40
  have hdup48 := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes (C.std.tlsPhdrIdx * 56 + 48) (by omega)
  rw [haln, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup48
  (wp_conv_pre => simp only [StdMainTlsZero, StdLibcTlsZero, sepConj_assoc])
  hb_have_fetches hc 44 79; hb_have_fetches hc 98 99; hb_wp_steps_p 1; wp_step; wp_if hcbz
  · exact absurd (by simpa [wp_norm, arm64_norm, hx6] using hcbz) hx6_nz
  · (wp_conv_pre => rw [← hdup16]); hb_wp_steps_p 6; (wp_conv_pre => rw [hdup16, ← hdup32]); hb_wp_steps_p 2
    (wp_conv_pre => rw [hdup32, ← hdup48]); hb_wp_steps_p 3; (wp_conv_pre => rw [hdup48, ← hdup40]); hb_wp_steps_p 1
    (wp_conv_pre => rw [hdup40]); hb_wp_steps_p 8; (try simp only [hal1a, hal1b, hal2, BitVec.zero_add]); hb_wp_steps_p 16
    exact SepWP.weaken_pre (P' := (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ HbMainTlsInit C.std ∗ HbLibcTlsInit C.std ∗ F)
      (by dsimp only [HbMainTlsInit, HbLibcTlsInit]; sep_entail)
      (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
        (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by simp [*]) (by simp [wp_norm, arm64_norm]; bv_lin))

end

private theorem hb_aux_words_split (p a0 a1 a2 a3 a4 a5 : BitVec 64) (tl : List (BitVec 64)) :
    (p ↦₆₄* (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: tl)) =
      (p ↦₆₄ a0) ∗ ((p + 0x08#64) ↦₆₄ a1) ∗ ((p + 0x10#64) ↦₆₄ a2) ∗
      ((p + 0x18#64) ↦₆₄ a3) ∗ ((p + 0x20#64) ↦₆₄ a4) ∗ ((p + 0x28#64) ↦₆₄ a5) ∗
      ((p + 0x30#64) ↦₆₄* tl) := by simp only [pointsToWords64_cons, BitVec.add_assoc]; rfl

private theorem hb_stdTlsGlobals_split (L : StdBinaryLayout) :
    StdTlsGlobals L =
      StdTdZero L.builtinTlsAddr ∗ HbDtvZero L.builtinTlsAddr ∗
      ((L.builtinTlsAddr + 0x24#64) ↦₃₂ 0#32) ∗
      ((L.builtinTlsAddr + 0xd8#64) ↦ₛ List.replicate 0x30 0#8) ∗
      ((L.builtinTlsAddr + 0x120#64) ↦₆₄ 0#64) ∗
      HbBuiltinTlsPad L.builtinTlsAddr ∗ StdMainTlsZero L := by
  simp only [StdTlsGlobals, StdBinaryLayout.tlsAtoms, rwAtomListSep, RwAtom.toSepProp,
    hbBuiltinTls_zero_split, StdMainTlsZero, sepConj_assoc]

private def hbStaticInitTlsSpec (L : StdBinaryLayout) : Spec (BitVec 64 × List (BitVec 64) × BitVec 8 × BitVec 64) where
  pre := fun (auxPtr, aux, canDo0, sysinfoVal) s0 =>
    ⌜s0.readReg64 .x0 = auxPtr ∧ aux[3]? = some L.phdrAddr ∧ aux[4]? = some 56#64 ∧ aux[5]? = some (BitVec.ofNat 64 L.phnum)⌝ ∗
    (memRegion (s0.sp - 0x60#64) 0x60 ∗ (auxPtr ↦₆₄* aux) ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
      (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗ (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗
      (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ StdTlsGlobals L ∗ (L.libcAddr ↦₈ canDo0) ∗ StdLibcTlsZero L)
  post := fun (auxPtr, aux, _, sysinfoVal) s0 sf =>
    ⌜sf.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 ∧ StdTlsFieldsPreserved s0 sf⌝ ∗
    (((sf.tpidrEl0 - 0xa4#64) ↦₃₂ 0#32) ∗ ((sf.tpidrEl0 + 0x58#64) ↦₆₄ 0#64) ∗
      (L.libcAddr ↦₈ 1#8) ∗ memRegion (sf.sp - 0x60#64) 0x60 ∗ (auxPtr ↦₆₄* aux) ∗
      (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
      (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ HbTlsState L sysinfoVal)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

section
arm64_proof_prelude

private theorem hbStaticInitTls_prologue {P : Program} {C : HbCliLayout}
    (hc : hasInstrs P C.std.staticInitTlsAddr (hbStaticInitTlsInstrs C.std))
    (hphdr : checkHbPhdrTable C = true) (hphdr_end : C.std.phdrAddr.toNat + C.std.phnum * 56 < 2 ^ 64)
    {target_pc : BitVec 64} (s0 : State) (auxPtr w0 w1 : BitVec 64) (F : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = C.std.staticInitTlsAddr) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true) (hx0 : s0.readReg64 .x0 = auxPtr)
    (hnext : ∀ sf1 : State, sf1.pc = C.std.staticInitTlsAddr + 0xb0#64 → sf1.status = .Running →
      sf1.sp = s0.sp - 0x10#64 → CalleeSavedPreserved (s0.writeReg64 .x29 (s0.sp - 0x10#64)) sf1 →
      StdStatePreserved s0 sf1 → sf1.readReg64 .x3 = 0#64 →
      sf1.readReg64 .x6 = C.std.phdrAddr + BitVec.ofNat 64 (C.std.tlsPhdrIdx * 56) →
      SepWP P target_pc sf1 (((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((auxPtr + 0x18#64) ↦₆₄ C.std.phdrAddr) ∗
        ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 C.std.phnum) ∗
        (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.gotAddr ↦₆₄ 0#64) ∗
        (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F) post oom) :
    SepWP P target_pc s0 (((s0.sp - 0x10#64) ↦₆₄ w0) ∗ ((s0.sp - 0x08#64) ↦₆₄ w1) ∗
      ((auxPtr + 0x18#64) ↦₆₄ C.std.phdrAddr) ∗ ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗
      ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 C.std.phnum) ∗
      (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.gotAddr ↦₆₄ 0#64) ∗
      (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F) post oom := by
  obtain ⟨hph_pos, _, hplen, htls_pos, _, _, hp0_t, hp0_v⟩ := hbCheckPhdrTable_hdr hphdr
  have hph_nz : BitVec.ofNat 64 C.std.phnum ≠ 0#64 := by
    intro hz; have := congrArg BitVec.toNat hz; simp [Nat.mod_eq_of_lt (by omega : C.std.phnum < 2 ^ 64)] at this; omega
  have hdup0_pt := hb_phdr_dup_u32 C.std.phdrAddr C.std.phdrBytes 0 (by omega); simp only [hp0_t, BitVec.add_zero] at hdup0_pt
  have hdup0_pv := hb_phdr_dup_u64 C.std.phdrAddr C.std.phdrBytes 16 (by omega); simp only [hp0_v, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hdup0_pv
  hb_have_fetches hc 0 17; hb_have_fetches hc 24 27; hb_wp_steps_p 15; wp_step; wp_if hcbz0
  · exact absurd (by simpa [wp_norm, arm64_norm] using hcbz0) hph_nz
  · (wp_conv_pre => rw [← hdup0_pt]); hb_wp_steps_p 3; (wp_conv_pre => rw [hdup0_pt, ← hdup0_pv]); hb_wp_steps_p 3; (wp_conv_pre => rw [hdup0_pv])
    have hsp_sub10_al : (s0.sp - 0x10#64) &&& 15#64 = 0#64 := by simp only [State.spAligned, beq_iff_eq] at hsp_align; bv_bits
    refine SepWP.weaken_pre (P' := ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ ?F_loop) (by sep_frame) ?_
    refine hbStaticInitTls_phdr_loop hc hphdr hphdr_end auxPtr (C.std.phnum - 1) 1 (by omega) (by omega) _ _
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [State.spAligned, wp_norm, arm64_norm, hsp_sub10_al])
      (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, Nat.sub_add_cancel hph_pos]) (by simp [wp_norm, arm64_norm, show ¬(C.std.tlsPhdrIdx < 1) by omega])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      fun sf1 hpc1 hrun1 hsp1 hcs1 _ hstd1 hx3_1 hx6_1 => ?_
    refine SepWP.weaken_pre (P' := ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((auxPtr + 0x18#64) ↦₆₄ C.std.phdrAddr) ∗
      ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 C.std.phnum) ∗
      (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.gotAddr ↦₆₄ 0#64) ∗ (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F) (by sep_entail)
      (hnext sf1 hpc1 hrun1 (by simpa [wp_norm, arm64_norm] using hsp1)
        (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs1)
        (StdStatePreserved.trans (by simp [*]) hstd1) hx3_1 hx6_1)

private def tidOnlySvc : State → State := Syscall.dispatch [(96#64, execSetTidAddress)]

private theorem svcKeepsFrozen_tidOnlySvc : SvcKeepsFrozen tidOnlySvc := by
  intro s; dsimp [tidOnlySvc, Syscall.dispatch, List.find?]
  by_cases h : (96#64 == s.readReg64 Reg.x8) = true
  · rw [h]; cases s; exact ⟨Memory.KeepsFrozenCells.refl _, rfl, rfl⟩
  · rw [Bool.eq_false_iff.mpr h]; cases s; exact ⟨Memory.KeepsFrozenCells.refl _, rfl, rfl⟩

private theorem tidOnlySvc_set_tid_address (s : State) (h : s.readReg64 .x8 = 96#64) :
    tidOnlySvc s = execSetTidAddress s := by
  dsimp [tidOnlySvc, Syscall.dispatch, List.find?]; rw [h]; rfl

private theorem hbInitTp_tidOnly_ok {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initTpAddr (initTpInstrs L))
    (hset : subroutine_ok P L.setThreadAreaAddr stdSetThreadAreaSpec)
    (hsvc : P.svc = tidOnlySvc) : subroutine_ok P L.initTpAddr (stdInitTpSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨canDo0, sysinfoVal⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [stdInitTpSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩; rw [sepConj_assoc] at hpre
  obtain ⟨ws, hws_len, hpre⟩ := hb_satisfies_memRegion_words64 4 (by decide) hpre
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | _⟩⟩⟩⟩ <;> try (simp at hws_len)
  simp only [pointsToWords64_cons, pointsToWords64_nil, StdTdZero, sepConj_emp, sepConj_assoc] at hpre
  have ha1 : s0.sp - 0x20#64 + 8#64 = s0.sp - 0x18#64 := by bv_lin
  have ha2 : s0.sp - 0x18#64 + 8#64 = s0.sp - 0x10#64 := by bv_lin
  have ha3 : s0.sp - 0x10#64 + 8#64 = s0.sp - 0x08#64 := by bv_lin
  rw [ha1, ha2, ha3] at hpre
  refine ⟨((s0.sp - 0x20#64) ↦₆₄ w0) ∗ ((s0.sp - 0x18#64) ↦₆₄ w1) ∗ ((s0.sp - 0x10#64) ↦₆₄ w2) ∗
    ((s0.sp - 0x08#64) ↦₆₄ w3) ∗ (L.builtinTlsAddr ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x08#64) ↦₆₄ 0#64) ∗
    ((L.builtinTlsAddr + 0x10#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x18#64) ↦₆₄ 0#64) ∗
    ((L.builtinTlsAddr + 0x20#64) ↦₃₂ 0#32) ∗ ((L.builtinTlsAddr + 0x28#64) ↦₃₂ 0#32) ∗
    ((L.builtinTlsAddr + 0x78#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x98#64) ↦₆₄ 0#64) ∗
    (L.libcAddr ↦₈ canDo0) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal), by simpa only [sepConj_assoc] using hpre, ?_⟩
  hb_have_fetches hc 0 6; hb_wp_steps_p 7
  refine SepWP.call_subroutine_frame (ret_pc := L.initTpAddr + 0x1c#64) hset (x := L.builtinTlsAddr + 0xc8#64) (F := ?_)
    (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, beq_iff_eq] at hsp_align ⊢; bv_bits)
    (by simp [wp_norm, arm64_norm]; try bv_lin) (by dsimp only [stdSetThreadAreaSpec]; simp only [wp_norm, arm64_norm]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_
  dsimp only [stdSetThreadAreaSpec]; apply SepWP.pure_elim; rintro ⟨htp1, hx0_1, htls1⟩
  have htls01 : StdTlsFieldsPreserved s0 sf1 := StdTlsFieldsPreserved.trans (by simp [*]) htls1
  have hx19_1 : sf1.readReg64 .x19 = L.builtinTlsAddr := by rw [hcs1.1]; simp [wp_norm, arm64_norm]
  have hsp1_eq : sf1.sp = s0.sp - 0x20#64 := by rw [hsp1]; simp [wp_norm, arm64_norm]
  have hsp1_align : sf1.spAligned = true := by simp only [State.spAligned, hsp1_eq, beq_iff_eq] at hsp_align ⊢; bv_bits
  hb_clear_fetches 0 6; hb_have_fetches hc 7 18; hb_wp_steps_p 11
  refine SepWP.step_svc_set_tid_address (pc := L.initTpAddr + 0x48#64)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) _hf_18
    (by simp [wp_norm, arm64_norm]) rfl ?_
    (by rw [evalInst_eq_execInstWithSvc (hsvc ▸ svcKeepsFrozen_tidOnlySvc), execInstWithSvc_svc0, hsvc]
        exact tidOnlySvc_set_tid_address _ (by simp [wp_norm, arm64_norm]))
  hb_clear_fetches 7 18; hb_have_fetches hc 19 33; hb_wp_steps_p 15
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, htp1], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *]⟩, ?_⟩
    simp only [wp_norm, arm64_norm, SIM_TID] at hm ⊢
    simpa only [List.length_cons, List.length_nil, sepConj_assoc] using
      hb_satisfies_words64_memRegion (base := s0.sp - 0x20#64) [s0.readReg64 .x29, s0.readReg64 .x30, s0.readReg64 .x19, w3]
        (Rest := StdTdInit L sysinfoVal ∗ (L.libcAddr ↦₈ 1#8) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ R) (by simp)
        (by simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, ha1, ha2, ha3, StdTdInit, arm64_norm] at hm ⊢; ac_nf at hm ⊢)
  · obtain ⟨_, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, _, hcv⟩ := hcs1
    simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv]

private theorem hbStaticInitTls_ok {P : Program} {C : HbCliLayout}
    (hc_static : hasInstrs P C.std.staticInitTlsAddr (hbStaticInitTlsInstrs C.std))
    (hc_copy : hasInstrs P C.std.copyTlsAddr (copyTlsInstrs C.std))
    (hc_init : hasInstrs P C.std.initTpAddr (initTpInstrs C.std))
    (hc_set : P.hasCode C.std.setThreadAreaAddr setThreadAreaWords)
    (ops : StdMemOps P C.std.memcpyAddr C.std.memsetAddr) (hsvc : P.svc = tidOnlySvc)
    (hphdr : checkHbPhdrTable C = true) (hphdr_end : C.std.phdrAddr.toNat + C.std.phnum * 56 < 2 ^ 64)
    (halign : C.std.builtinTlsAddr.toNat % 8 = 0) (hmain_nz : C.std.mainTlsAddr ≠ 0#64) :
    subroutine_ok P C.std.staticInitTlsAddr (hbStaticInitTlsSpec C.std) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨auxPtr, aux, canDo0, sysinfoVal⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbStaticInitTlsSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, haux3, haux4, haux5⟩, hpre⟩
  rcases aux with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, auxTl⟩⟩⟩⟩⟩⟩ <;> try (simp at haux3 haux4 haux5)
  subst haux3 haux4 haux5
  have hsp50 : s0.sp - 0x60#64 + 0x50#64 = s0.sp - 0x10#64 := by bv_lin
  have hsp30 : s0.sp - 0x60#64 + 0x30#64 = s0.sp - 0x30#64 := by bv_lin
  have hsp10_8 : s0.sp - 0x10#64 + 8#64 = s0.sp - 0x08#64 := by bv_lin
  have hmr60 : memRegion (s0.sp - 0x60#64) 0x60 = memRegion (s0.sp - 0x60#64) 0x50 ∗ memRegion (s0.sp - 0x10#64) 0x10 := by
    simpa only [hsp50] using memRegion_split_le (s0.sp - 0x60#64) 0x50 0x60 (by decide) (by decide)
  have hmr50 : memRegion (s0.sp - 0x60#64) 0x50 = memRegion (s0.sp - 0x60#64) 0x30 ∗ memRegion (s0.sp - 0x30#64) 0x20 := by
    simpa only [hsp30] using memRegion_split_le (s0.sp - 0x60#64) 0x30 0x50 (by decide) (by decide)
  simp only [hmr60, sepConj_assoc] at hpre; rw [sepConj_left_comm (memRegion (s0.sp - 0x60#64) 0x50)] at hpre
  obtain ⟨ws, hws_len, hpre⟩ := hb_satisfies_memRegion_words64 2 (by decide) hpre
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩ <;> try (simp at hws_len)
  rw [hb_aux_words_split, hb_stdTlsGlobals_split] at hpre
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, hsp10_8, sepConj_assoc] at hpre
  refine ⟨((s0.sp - 0x10#64) ↦₆₄ w0) ∗ ((s0.sp - 0x08#64) ↦₆₄ w1) ∗ ((auxPtr + 0x18#64) ↦₆₄ C.std.phdrAddr) ∗
    ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 C.std.phnum) ∗
    (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ (C.std.gotAddr ↦₆₄ 0#64) ∗ (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗
    memRegion (s0.sp - 0x60#64) 0x50 ∗ (auxPtr ↦₆₄ a0) ∗ ((auxPtr + 0x08#64) ↦₆₄ a1) ∗ ((auxPtr + 0x10#64) ↦₆₄ a2) ∗
    ((auxPtr + 0x30#64) ↦₆₄* auxTl) ∗ (C.std.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ (C.std.sysinfoAddr ↦₆₄ sysinfoVal) ∗
    StdTdZero C.std.builtinTlsAddr ∗ HbDtvZero C.std.builtinTlsAddr ∗ ((C.std.builtinTlsAddr + 0x24#64) ↦₃₂ 0#32) ∗
    ((C.std.builtinTlsAddr + 0xd8#64) ↦ₛ List.replicate 0x30 0#8) ∗ ((C.std.builtinTlsAddr + 0x120#64) ↦₆₄ 0#64) ∗
    HbBuiltinTlsPad C.std.builtinTlsAddr ∗ StdMainTlsZero C.std ∗ (C.std.libcAddr ↦₈ canDo0) ∗ StdLibcTlsZero C.std,
    by dsimp only [StdMainTlsZero, StdLibcTlsZero] at hpre ⊢; ac_nf at hpre ⊢, ?_⟩
  have hsp_sub10_al : (s0.sp - 0x10#64) &&& 15#64 = 0#64 := by simp only [State.spAligned, beq_iff_eq] at hsp_align; bv_bits
  refine hbStaticInitTls_prologue hc_static hphdr hphdr_end s0 auxPtr w0 w1 _ hpc hrun hsp_align hx0
    fun sf1 hpc1 hrun1 hsp1_eq hcs01 hstd01 hx3_1 hx6_1 => ?_
  refine SepWP.weaken_pre (P' := (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗ StdMainTlsZero C.std ∗ StdLibcTlsZero C.std ∗ ?F_setup)
    (by dsimp only [StdMainTlsZero, StdLibcTlsZero]; sep_frame) ?_
  refine hbStaticInitTls_setup hc_static hphdr hphdr_end sf1 _ hpc1 hrun1 hx3_1 hx6_1
    fun sf2 hpc2 hrun2 hsp2 hcs2 hstd2 hx0_2 => ?_
  have hstd02 : StdStatePreserved s0 sf2 := StdStatePreserved.trans hstd01 hstd2
  have hsp2_eq : sf2.sp = s0.sp - 0x10#64 := hsp2.trans hsp1_eq
  have hsp2_50 : sf2.sp - 0x50#64 = s0.sp - 0x60#64 := by rw [hsp2_eq]; bv_lin
  hb_have_fetches hc_static 100 104; hb_wp_steps_p 1
  refine SepWP.call_subroutine_frame (ret_pc := C.std.staticInitTlsAddr + 0x194#64)
    (hbCopyTls_ok hc_copy ops halign hmain_nz) (x := ()) (F := ?F_copy)
    (by simp [wp_norm, arm64_norm]; bv_lin) (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp2_eq, hsp_sub10_al]) (by simp [wp_norm, arm64_norm])
    (by dsimp only [hbCopyTlsSpec, HbDtvZero, HbMainTlsInit, HbLibcTlsInit]; simp only [wp_norm, arm64_norm, hx0_2, hsp2_50]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf3 hpc3 hrun3 hsp3 hcs3 => ?_
  dsimp only [hbCopyTlsSpec]; (wp_conv_pre => rw [sepConj_assoc]); apply SepWP.pure_elim; rintro ⟨hx0_3, hstd3⟩
  have hstd03 : StdStatePreserved s0 sf3 := StdStatePreserved.trans (StdStatePreserved.trans hstd02 (by simp [*])) hstd3
  have hsp3_eq : sf3.sp = s0.sp - 0x10#64 := by simpa [wp_norm, arm64_norm, hsp2_eq] using hsp3
  have hsp3_50 : sf3.sp - 0x50#64 = s0.sp - 0x60#64 := by rw [hsp3_eq]; bv_lin
  have hsp3_20 : sf3.sp - 0x20#64 = s0.sp - 0x30#64 := by rw [hsp3_eq]; bv_lin
  (wp_conv_pre => simp only [hsp3_50, hmr50, sepConj_assoc]); hb_wp_steps_p 1
  refine SepWP.call_subroutine_frame (ret_pc := C.std.staticInitTlsAddr + 0x198#64)
    (hbInitTp_tidOnly_ok hc_init (setThreadArea_ok hc_set) hsvc) (x := (canDo0, sysinfoVal)) (F := ?F_init)
    (by simp [wp_norm, arm64_norm]; bv_lin) (by simp [wp_norm, arm64_norm, hrun3])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp3_eq, hsp_sub10_al]) (by simp [wp_norm, arm64_norm])
    (by dsimp only [stdInitTpSpec, StdTdZero]; simp only [wp_norm, arm64_norm, hx0_3, hsp3_20]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf4 hpc4 hrun4 hsp4 hcs4 => ?_
  dsimp only [stdInitTpSpec]; (wp_conv_pre => rw [sepConj_assoc]); apply SepWP.pure_elim; rintro ⟨htp4, hx0_4, htls4⟩
  simp only [arm64_norm] at hx0_4
  have htls04 : StdTlsFieldsPreserved s0 sf4 := StdTlsFieldsPreserved.trans (StdStatePreserved.toTlsFields (StdStatePreserved.trans hstd03 (by simp [*]))) htls4
  have hsp4_eq : sf4.sp = s0.sp - 0x10#64 := by simpa [wp_norm, arm64_norm, hsp3_eq] using hsp4
  have hsp4_al : sf4.spAligned = true := by simp [State.spAligned, hsp4_eq, hsp_sub10_al]
  have hsp4_20 : sf4.sp - 0x20#64 = s0.sp - 0x30#64 := by rw [hsp4_eq]; bv_lin
  (wp_conv_pre => simp only [hsp4_20]); hb_wp_steps_p 3
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, htp4], by simp [wp_norm, arm64_norm, *]⟩, ?_⟩
    have herr_addr : C.std.builtinTlsAddr + 0xc8#64 - 0xa4#64 = C.std.builtinTlsAddr + 0x24#64 := by bv_lin
    have htid_addr : C.std.builtinTlsAddr + 0xc8#64 + 0x58#64 = C.std.builtinTlsAddr + 0x120#64 := by bv_lin
    have hpack10 : (((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5))) ⊢ memRegion (s0.sp - 0x10#64) 0x10 := by
      simpa only [pointsToWords64_cons, pointsToWords64_nil, List.length_cons, List.length_nil, sepConj_emp, hsp10_8] using
        pointsToWords64_entails_memRegion [s0.readReg64 (.gpr 29#5), s0.readReg64 (.gpr 30#5)] (s0.sp - 0x10#64) (by simp)
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [wp_norm, arm64_norm, htp4, herr_addr, htid_addr, hmr60, hmr50, hb_aux_words_split, HbTlsState]
    refine Entails.trans (Q := (((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5))) ∗ ?F_pack)
      (by sep_frame) (Entails.trans (sepConj_mono_left hpack10) (by sep_entail))
  · obtain ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩ :=
      CalleeSavedPreserved.trans (CalleeSavedPreserved.trans (CalleeSavedPreserved.trans (CalleeSavedPreserved.trans (CalleeSavedPreserved.trans hcs01 hcs2)
        (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])) hcs3) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])) hcs4
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

end

/-! ## Stage 1 (`_start` to `libc_start_main_stage2`) -/

def HbStage1Got (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  let L := C.std
  (L.gotAddr ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x08#64) ↦₆₄ L.finiFnAddr) ∗
  ((L.gotAddr + 0x10#64) ↦₆₄ L.initFnAddr) ∗ ((L.gotAddr + 0x18#64) ↦₆₄ L.cMainAddr) ∗
  (S.gotEnvironAddr ↦₆₄ L.environAddr) ∗ (S.gotPrognameFullAddr ↦₆₄ L.prognameFullAddr) ∗
  (S.gotPrognameAddr ↦₆₄ L.prognameAddr)

private theorem hb_ofNat_shl3 {k : Nat} (hk : 8 * k < 2 ^ 64) :
    (BitVec.ofNat 64 k) <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]; omega

private theorem hb_replicate_zero_eq_unpackL : ∀ n : Nat, List.replicate (8 * n) 0#8 = unpackL (List.replicate n 0#64)
  | 0 => rfl
  | n + 1 => by rw [Nat.mul_succ, Nat.add_comm, List.replicate_add, hb_replicate_zero_eq_unpackL n]; rfl

local elab "hb_clear_hf " lo:num hi:num : tactic => do
  for i in [lo.getNat : hi.getNat + 1] do
    let hId := Lean.mkIdent (Lean.Name.mkSimple s!"hf_{i}")
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear $hId))

section
open Stage1Internal
arm64_proof_prelude

private theorem hb_envp_scan_loop {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S))
    (rem : List (BitVec 64)) (base : BitVec 64) (k : Nat) {s : State} (F : SepProp)
    (hno0 : ∀ p ∈ rem, p ≠ 0#64) (hbnd : 8 * (k + rem.length + 1) < 2 ^ 64)
    (hpc : s.pc = C.std.initLibcAddr + 0x40#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = base) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 k) :
    SepWP P (C.std.initLibcAddr + 0x4c#64) s (((base + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)
      (fun sf Q => sf.pc = C.std.initLibcAddr + 0x4c#64 ∧ sf.status = .Running ∧ sf.sp = s.sp ∧
        sf.readReg64 .x2 = BitVec.ofNat 64 (k + rem.length + 1) ∧ sf.readReg64 .x4 = s.readReg64 .x4 ∧
        sf.readReg64 .x19 = base ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        StdStatePreserved s sf ∧ Q = (((base + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (rem ++ [0#64])) ∗ F)) := by
  have_instrs hc 16 3
  induction rem generalizing k s F with
  | nil =>
    have hsh := hb_ofNat_shl3 (k := k) (by simp at hbnd; omega)
    rw [List.nil_append, pointsToWords64RO_cons, pointsToWords64RO_nil]; hb_wp_steps_p 3
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    have hk1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 0 + 1) := by rw [Nat.add_zero, BitVec.ofNat_add]
    refine ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
      by simp only [wp_norm, arm64_norm], by simp only [List.length_nil, wp_norm, arm64_norm, hk1],
      by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx19],
      by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], by simp [*], ?_⟩
    rw [← pointsToWords64RO_nil (base + BitVec.ofNat 64 (8 * k) + 8#64), ← pointsToWords64RO_cons]
  | cons p ps ih =>
    have hsh := hb_ofNat_shl3 (k := k) (by simp at hbnd; omega)
    have hp0 : (p == 0#64) = false := beq_eq_false_iff_ne.mpr (hno0 p (List.mem_cons_self ..))
    have hnext_addr : base + BitVec.ofNat 64 (8 * k) + 8#64 = base + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
    rw [List.cons_append, pointsToWords64RO_cons, hnext_addr, sepConj_assoc]
    apply SepWP.cut (mid := C.std.initLibcAddr + 0x48#64); hb_wp_steps_p 2
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    hb_wp_steps_p 1; rw [← sepConj_assoc, sepConj_comm ((base + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ p), sepConj_assoc]
    have hk1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [BitVec.ofNat_add]
    refine SepWP.mono (ih (k + 1) _ (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) (by simp at hbnd ⊢; omega)
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hk1])) ?_ (fun _ _ _ ho => ho)
    rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx2_f, hx4_f, hx19_f, hx20_f, hx29_f, hstd_f, rfl⟩
    refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f,
      by simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx2_f,
      by simpa [wp_norm, arm64_norm] using hx4_f, hx19_f, by simpa [wp_norm, arm64_norm] using hx20_f,
      by simpa [wp_norm, arm64_norm] using hx29_f, StdStatePreserved.trans (by simp [*]) hstd_f, by ac_rfl⟩

private theorem hb_auxv_scan_loop {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S))
    (entries : List (BitVec 64 × BitVec 64)) (curPtr auxPtr : BitVec 64) (acc : List (BitVec 64)) {s : State} (F : SepProp)
    (hno0 : ∀ p ∈ entries, p.1 ≠ 0#64) (hlen : acc.length = 38)
    (hpc : s.pc = C.std.initLibcAddr + 0x68#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = curPtr) (hx4 : s.readReg64 .x4 = auxPtr) :
    SepWP P (C.std.initLibcAddr + 0x84#64) s
      (((curPtr ↦₆₄* ((entries ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗ (auxPtr ↦₆₄* acc)) ∗ F)
      (fun sf Q => sf.pc = C.std.initLibcAddr + 0x84#64 ∧ sf.status = .Running ∧ sf.sp = s.sp ∧
        sf.readReg64 .x4 = auxPtr ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧ StdStatePreserved s sf ∧
        Q = (((curPtr ↦₆₄* ((entries ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
              (auxPtr ↦₆₄* entries.foldl (fun a (t, v) => if t.toNat < 38 then a.set t.toNat v else a) acc)) ∗ F)) := by
  have_instrs hc 25 8
  induction entries generalizing curPtr acc s F with
  | nil =>
    simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.foldl_nil]
    rw [pointsToWords64_cons, pointsToWords64_cons, pointsToWords64_nil]; hb_wp_steps_p 2
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
      by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx4], by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], by simp [*], rfl⟩
  | cons p ps ih =>
    rcases p with ⟨t, v⟩
    have ht0 : (t == 0#64) = false := beq_eq_false_iff_ne.mpr (hno0 (t, v) (List.mem_cons_self ..))
    have hcur16 : curPtr + 8#64 + 8#64 = curPtr + 16#64 := by bv_lin
    conv => arg 4; simp only [List.cons_append, List.flatMap_cons, List.nil_append]
    rw [pointsToWords64_cons, pointsToWords64_cons, hcur16]
    apply SepWP.cut (mid := C.std.initLibcAddr + 0x74#64); hb_wp_steps_p 3
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    by_cases hlt : t.toNat < 38
    · have hult : (37#64).ult t = false := by simp [BitVec.ult]; omega
      have hsh_t : t <<< 3 = BitVec.ofNat 64 (8 * t.toNat) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      apply SepWP.cut (mid := C.std.initLibcAddr + 0x68#64)
      rw [pointsToWords64_focus auxPtr acc t.toNat (by omega)]; hb_wp_steps_p 5
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      have hupd : ((auxPtr + BitVec.ofNat 64 (8 * t.toNat)) ↦₆₄ v) ∗
          (pointsToArray 8 (· ↦₆₄ ·) auxPtr (acc.take t.toNat) ∗
           pointsToArray 8 (· ↦₆₄ ·) (auxPtr + BitVec.ofNat 64 (8 * (t.toNat + 1))) (acc.drop (t.toNat + 1))) =
          (auxPtr ↦₆₄* acc.set t.toNat v) := by
        rw [pointsToArray_update 8 (· ↦₆₄ ·) auxPtr acc t.toNat v (by omega), ← pointsToWords64_eq_pointsToArray]
      refine SepWP.weaken_pre (P' := (((curPtr + 16#64) ↦₆₄* ((ps ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        (auxPtr ↦₆₄* acc.set t.toNat v)) ∗ ?F_lt) (by rw [← hupd]; sep_frame) ?_
      refine SepWP.mono (ih (curPtr + 16#64) (acc.set t.toNat v) ?F_lt (fun q hq => hno0 q (List.mem_cons_of_mem _ hq))
        (by simp [hlen]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx4])) ?_ (fun _ _ _ ho => ho)
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hx20_f, hx21_f, hx29_f, hstd_f, rfl⟩
      refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f, hx4_f,
        by simpa [wp_norm, arm64_norm] using hx20_f, by simpa [wp_norm, arm64_norm] using hx21_f,
        by simpa [wp_norm, arm64_norm] using hx29_f, StdStatePreserved.trans (by simp [*]) hstd_f, ?_⟩
      simp only [List.cons_append, List.flatMap_cons, List.nil_append, List.foldl_cons, hlt, ↓reduceIte]
      rw [pointsToWords64_cons, pointsToWords64_cons, hcur16]; ac_rfl
    · have hult : (37#64).ult t = true := by simp [BitVec.ult]; omega
      apply SepWP.cut (mid := C.std.initLibcAddr + 0x68#64); hb_wp_steps_p 2
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre (P' := (((curPtr + 16#64) ↦₆₄* ((ps ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
        (auxPtr ↦₆₄* acc)) ∗ ?F_hi) (by sep_frame) ?_
      refine SepWP.mono (ih (curPtr + 16#64) acc ?F_hi (fun q hq => hno0 q (List.mem_cons_of_mem _ hq)) hlen
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx4])) ?_ (fun _ _ _ ho => ho)
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hx20_f, hx21_f, hx29_f, hstd_f, rfl⟩
      refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f, hx4_f,
        by simpa [wp_norm, arm64_norm] using hx20_f, by simpa [wp_norm, arm64_norm] using hx21_f,
        by simpa [wp_norm, arm64_norm] using hx29_f, StdStatePreserved.trans (by simp [*]) hstd_f, ?_⟩
      simp only [List.cons_append, List.flatMap_cons, List.nil_append, List.foldl_cons, hlt, ↓reduceIte]
      rw [pointsToWords64_cons, pointsToWords64_cons, hcur16]; ac_rfl

private theorem hb_progname_scan_loop {P : Program} {L : StdBinaryLayout}
    (hc58 : hasInstrs P (L.initLibcAddr + 0xe8#64) (((initLibcInstrs L).drop 58).take 14))
    (bs : List (BitVec 8)) (curPtr best : BitVec 64) {s : State} (F : SepProp) (hno0 : 0#8 ∉ bs)
    (hpc : s.pc = L.initLibcAddr + 0xec#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = curPtr + 1#64) (hx2 : s.readReg64 .x2 = L.prognameAddr) :
    SepWP P (L.initLibcAddr + 0x104#64) s (((curPtr ↦ᵣ (bs ++ [0#8])) ∗ (L.prognameAddr ↦₆₄ best)) ∗ F)
      (fun sf Q => sf.pc = L.initLibcAddr + 0x104#64 ∧ sf.status = .Running ∧ sf.sp = s.sp ∧
        sf.readReg64 .x4 = s.readReg64 .x4 ∧ StdStatePreserved s sf ∧
        Q = (((curPtr ↦ᵣ (bs ++ [0#8])) ∗ (L.prognameAddr ↦₆₄ scanSlashPtr curPtr best bs)) ∗ F)) := by
  have_instrs hc58 0 7
  induction bs generalizing curPtr best s F with
  | nil =>
    have hcur_m1 : curPtr + 1#64 + (-1#64 : BitVec 64) = curPtr := by bv_lin
    conv => arg 4; rw [List.nil_append, pointsToBytesRO_cons, pointsToBytesRO_nil]
    hb_wp_steps_p 2; refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
      by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], by simp [*], ?_⟩
    simp only [scanSlashPtr, List.nil_append, pointsToBytesRO_cons, pointsToBytesRO_nil]
  | cons b rest ih =>
    have hcur_m1 : curPtr + 1#64 + (-1#64 : BitVec 64) = curPtr := by bv_lin
    have hb0 : b ≠ 0#8 := fun h => hno0 (h ▸ List.mem_cons_self ..)
    have hb32 : (b.zeroExtend 32 == 0#32) = false := beq_eq_false_iff_ne.mpr fun h => hb0 (by simpa using congrArg (BitVec.truncate 8) h)
    have hb64 : (b.zeroExtend 64 == 0#64) = false := beq_eq_false_iff_ne.mpr fun h => hb0 (by simpa using congrArg (BitVec.truncate 8) h)
    conv => arg 4; rw [List.cons_append, pointsToBytesRO_cons]
    by_cases hslash : (b == 0x2f#8) = true
    · obtain rfl := beq_iff_eq.mp hslash
      apply SepWP.cut (mid := L.initLibcAddr + 0xec#64); hb_wp_steps_p 7
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre (P' := ((((curPtr + 1#64) ↦ᵣ (rest ++ [0#8])) ∗ (L.prognameAddr ↦₆₄ (curPtr + 1#64))) ∗ ?F_sl)) (by sep_frame) ?_
      refine SepWP.mono (ih (curPtr + 1#64) (curPtr + 1#64) ?F_sl (fun hm => hno0 (List.mem_cons_of_mem _ hm))
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx2])) ?_ (fun _ _ _ ho => ho)
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hstd_f, rfl⟩
      refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f, by simpa [wp_norm, arm64_norm] using hx4_f,
        StdStatePreserved.trans (by simp [*]) hstd_f, ?_⟩
      simp only [scanSlashPtr, ↓reduceIte, beq_self_eq_true, List.cons_append, pointsToBytesRO_cons]; ac_rfl
    · have hslash_f : (b == 0x2f#8) = false := Bool.eq_false_iff.mpr hslash
      have hne32 : (b.zeroExtend 32 == 0x2f#32) = false := beq_eq_false_iff_ne.mpr fun h =>
        (beq_eq_false_iff_ne.mp hslash_f) (by simpa using congrArg (BitVec.truncate 8) h)
      apply SepWP.cut (mid := L.initLibcAddr + 0xec#64); hb_wp_steps_p 5
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
      refine SepWP.weaken_pre (P' := ((((curPtr + 1#64) ↦ᵣ (rest ++ [0#8])) ∗ (L.prognameAddr ↦₆₄ best)) ∗ ?F_ns)) (by sep_frame) ?_
      refine SepWP.mono (ih (curPtr + 1#64) best ?F_ns (fun hm => hno0 (List.mem_cons_of_mem _ hm))
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx2])) ?_ (fun _ _ _ ho => ho)
      rintro sf Q hpc_f hrun_f ⟨_, _, hsp_f, hx4_f, hstd_f, rfl⟩
      refine ⟨hpc_f, hrun_f, by simpa [wp_norm, arm64_norm] using hsp_f, by simpa [wp_norm, arm64_norm] using hx4_f,
        StdStatePreserved.trans (by simp [*]) hstd_f, ?_⟩
      simp only [scanSlashPtr, hslash_f, Bool.false_eq_true, ↓reduceIte, List.cons_append, pointsToBytesRO_cons]; ac_rfl

private theorem hbStart_to_initLibc {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s0 : State} {F : SepProp}
    (hc_start : hasInstrs P C.std.startAddr (startInstrs C.std))
    (hc_startC : hasInstrs P C.std.startCAddr (startCInstrs C.std))
    (hc_lsm : hasInstrs P C.std.libcStartMainAddr (hbLibcStartMainInstrs C.std))
    (hc_init : hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S))
    (hsp0 : s0.sp = sl.sp0) (hpc0 : s0.pc = C.std.startAddr) (hrun0 : s0.status = .Running)
    (hal16 : sl.sp0.toNat % 16 = 0) (hargc_lo : 1 ≤ inputs.argv.length) (hargc_hi : inputs.argv.length < 2 ^ 31)
    (hargv_len : sl.argvAddrs.length = inputs.argv.length)
    (henvp_eq : sl.envpTableAddr = sl.sp0 + BitVec.ofNat 64 (8 * (inputs.argv.length + 2)))
    (hargv_eq : sl.argvTableAddr = sl.sp0 + 8#64) :
    SepWP P C.std.initLibcAddr s0
      (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        HbStage1Got C S ∗ memRegion (sl.sp0 - 0x30#64) 0x30) ∗ F)
      (fun s1 Q => s1.pc = C.std.initLibcAddr ∧ s1.status = .Running ∧ s1.sp = sl.sp0 - 0x30#64 ∧
        s1.readReg64 .lr = C.std.libcStartMainAddr + 0x2c#64 ∧ s1.readReg64 .x0 = sl.envpTableAddr ∧
        s1.readReg64 .x1 = sl.argvAddrs.getD 0 0#64 ∧ s1.readReg64 .x19 = sl.argvTableAddr ∧
        s1.readReg32 .x20 = BitVec.ofNat 32 inputs.argv.length ∧ s1.readReg64 .x21 = C.std.cMainAddr ∧
        StdStatePreserved s0 s1 ∧ Q = (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
          (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ HbStage1Got C S ∗ LsmSavedFrame sl.sp0 s0) ∗ F)) := by
  have hsp_al0 : s0.spAligned = true := by simp only [State.spAligned, hsp0, beq_iff_eq]; exact align16_and_15 hal16
  have hsp_al_lsm : ((sl.sp0 - 0x30#64) &&& 15#64 == 0#64) = true := by
    have := align16_and_15 hal16; simp only [beq_iff_eq]; bv_bits
  have hmask : sl.sp0 &&& 0xfffffffffffffff0#64 = sl.sp0 := align16_and_mask hal16
  have _hne1 := pc_ne_of_fetch_ne (fetch_at 6 0x18#64 hc_start) (fetch_at0 hc_startC)
  have _hne2 := pc_ne_of_fetch_ne (fetch_at 9 0x24#64 hc_startC) (fetch_at0 hc_lsm)
  have _hne3 := pc_ne_of_fetch_ne (fetch_at 10 0x28#64 hc_lsm) (fetch_at0 hc_init)
  have_instrs hc_start 0 7
  apply SepWP.cut (mid := C.std.startAddr + 0x18#64); hb_wp_steps_p 6
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  apply SepWP.cut (mid := C.std.startCAddr); hb_wp_steps_p 1; rw [add_sub_pc]; hb_clear_hf 0 6
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  have_instrs hc_startC 0 10
  apply SepWP.cut (mid := C.std.startCAddr + 0x24#64); conv => arg 4; dsimp only [HbStage1Got]
  hb_wp_steps_p 9
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  change SepWP P C.std.initLibcAddr _ (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
    (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ HbStage1Got C S ∗ memRegion (sl.sp0 - 0x30#64) 0x30) ∗ F) _ _
  apply SepWP.cut (mid := C.std.libcStartMainAddr); hb_wp_steps_p 1; rw [add_sub_pc]; hb_clear_hf 0 9
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  obtain ⟨argv0, argvRest, ha_cons⟩ : ∃ a as, sl.argvAddrs = a :: as := by
    cases h : sl.argvAddrs with | nil => simp [h] at hargv_len; omega | cons a as => exact ⟨a, as, rfl⟩
  rw [memRegion_uncons (sl.sp0 - 0x30#64) (by decide) (by decide), show (0x30 - 8 : Nat) = 40 from rfl, show sl.sp0 - 0x30#64 + 8#64 = sl.sp0 - 0x28#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x28#64) (by decide) (by decide), show (40 - 8 : Nat) = 32 from rfl, show sl.sp0 - 0x28#64 + 8#64 = sl.sp0 - 0x20#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x20#64) (by decide) (by decide), show (32 - 8 : Nat) = 24 from rfl, show sl.sp0 - 0x20#64 + 8#64 = sl.sp0 - 0x18#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x18#64) (by decide) (by decide), show (24 - 8 : Nat) = 16 from rfl, show sl.sp0 - 0x18#64 + 8#64 = sl.sp0 - 0x10#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x10#64) (by decide) (by decide), show (16 - 8 : Nat) = 8 from rfl, show sl.sp0 - 0x10#64 + 8#64 = sl.sp0 - 0x08#64 by bv_lin]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_left fun w0 => SepWP.exists_left fun w1 => SepWP.exists_left fun w2 =>
    SepWP.exists_left fun w3 => SepWP.exists_left fun w4 => ?_
  rw [ha_cons, List.cons_append, pointsToWords64RO_cons, hargv_eq]
  have_instrs hc_lsm 0 11
  apply SepWP.cut (mid := C.std.libcStartMainAddr + 0x28#64); hb_wp_steps_p 10
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  hb_wp_steps_p 1; rw [add_sub_pc]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun0]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun0],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm, sxtw3_argc_eq hargc_hi, henvp_eq, envpTableAddr_calc],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm]; rfl,
    by simp (config := { decide := true }) only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm]; apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : inputs.argv.length < 2 ^ 32)],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm], by simp [*], by dsimp only [HbStage1Got, LsmSavedFrame]⟩

private theorem hbInitLibc_prologue_envp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s1 : State} {F : SepProp}
    (hc : hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S))
    (ops : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (hpc1 : s1.pc = C.std.initLibcAddr) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = sl.sp0 - 0x30#64)
    (hx0 : s1.readReg64 .x0 = sl.envpTableAddr) (hx1 : s1.readReg64 .x1 = sl.argvAddrs.getD 0 0#64)
    (hal16 : sl.sp0.toNat % 16 = 0) (henvp_len : sl.envpAddrs.length = inputs.envp.length)
    (henvp_hi : inputs.envp.length < 2 ^ 31) (henvp_no0 : ∀ p ∈ sl.envpAddrs, p ≠ 0#64)
    (hauxv_eq : sl.auxvTableAddr = sl.envpTableAddr + BitVec.ofNat 64 (8 * (inputs.envp.length + 1)))
    (_hne_memset : C.std.initLibcAddr + 0x28#64 ≠ C.std.memsetAddr) :
    SepWP P (C.std.initLibcAddr + 0x68#64) s1
      ((memRegion (sl.sp0 - 0x1c0#64) 0x190 ∗ HbStage1Got C S ∗ (C.std.environAddr ↦₆₄ 0#64) ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ 0#64) ∗ (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64]))) ∗ F)
      (fun s2 Q => s2.pc = C.std.initLibcAddr + 0x68#64 ∧ s2.status = .Running ∧ s2.sp = sl.sp0 - 0x1c0#64 ∧
        s2.readReg64 .x0 = sl.auxvTableAddr ∧ s2.readReg64 .x4 = sl.sp0 - 0x160#64 ∧
        s2.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 ∧ s2.readReg64 .x21 = C.std.libcAddr &&& 0xfffffffffffff000#64 ∧
        s2.readReg64 .x29 = sl.sp0 - 0x1c0#64 ∧ StdStatePreserved s1 s2 ∧
        Q = ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64) ∗
          HbStage1Got C S ∗ (C.std.environAddr ↦₆₄ sl.envpTableAddr) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
          (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64]))) ∗ F)) := by
  have_instrs hc 0 16; have_instrs hc 19 6
  have hsp0_al : (sl.sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr (align16_and_15 hal16)
  have hsp_sub : sl.sp0 - 0x30#64 + (-0x190#64 : BitVec 64) = sl.sp0 - 0x1c0#64 := by bv_lin
  have hgot_env := page_add_lo12_eq S.gotEnvironAddr; have hlibc_pg := page_add_trunc12_eq C.std.libcAddr
  rw [memRegion_split_le (sl.sp0 - 0x1c0#64) 0x60 0x190 (by decide) (by decide), show (0x190 - 0x60 : Nat) = 304 from rfl, show sl.sp0 - 0x1c0#64 + BitVec.ofNat 64 0x60 = sl.sp0 - 0x160#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1c0#64) (by decide) (by decide), show (0x60 - 8 : Nat) = 88 from rfl, show sl.sp0 - 0x1c0#64 + 8#64 = sl.sp0 - 0x1b8#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1b8#64) (by decide) (by decide), show (88 - 8 : Nat) = 80 from rfl, show sl.sp0 - 0x1b8#64 + 8#64 = sl.sp0 - 0x1b0#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1b0#64) (by decide) (by decide), show (80 - 8 : Nat) = 72 from rfl, show sl.sp0 - 0x1b0#64 + 8#64 = sl.sp0 - 0x1a8#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1a8#64) (by decide) (by decide), show (72 - 8 : Nat) = 64 from rfl, show sl.sp0 - 0x1a8#64 + 8#64 = sl.sp0 - 0x1a0#64 by bv_lin]
  rw [memRegion_uncons (sl.sp0 - 0x1a0#64) (by decide) (by decide), show (64 - 8 : Nat) = 0x38 from rfl, show sl.sp0 - 0x1a0#64 + 8#64 = sl.sp0 - 0x198#64 by bv_lin]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_left fun u0 => SepWP.exists_left fun u1 => SepWP.exists_left fun u2 =>
    SepWP.exists_left fun u3 => SepWP.exists_left fun u4 => ?_
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x28#64); hb_wp_steps_p 10
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1]) ?_
  apply SepWP.cut (mid := C.std.memsetAddr); hb_wp_steps_p 1; rw [add_sub_pc]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1]) ?_
  refine ops.call_memset (dst := sl.sp0 - 0x160#64) (byteVal := 0#8) (len := 304)
    (ret_pc := C.std.initLibcAddr + 0x2c#64) (F := ?F_ms) (by sep_frame) ?_
    (hsp_align := by simp only [State.spAligned, wp_norm, arm64_norm, hsp0_al]) (hx1 := by simp only [wp_norm, arm64_norm])
  intro sm hpc_m hrun_m hsp_m hcs_m hx0_m hstd_m
  have hpres_m : StdStatePreserved s1 sm := StdStatePreserved.trans (by simp [*]) hstd_m
  have hsp_m' : sm.sp = sl.sp0 - 0x1c0#64 := by simpa [wp_norm, arm64_norm, hsp_sub] using hsp_m
  have hx19_m : sm.readReg64 .x19 = sl.envpTableAddr := by simpa [wp_norm, arm64_norm, hx0] using hcs_m.readReg64_x19
  have hx20_m : sm.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 := by simpa [wp_norm, arm64_norm, hx1] using hcs_m.readReg64_x20
  have hx29_m : sm.readReg64 .x29 = sl.sp0 - 0x1c0#64 := by simpa [wp_norm, arm64_norm, hsp_sub] using hcs_m.readReg64_x29
  rw [show (304 : Nat) = 8 * 38 from rfl, hb_replicate_zero_eq_unpackL 38, ← pointsToWords64_eq_pointsToBytes]
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x40#64); conv => arg 4; dsimp only [HbStage1Got]
  hb_wp_steps_p 5
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_m]) ?_
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x4c#64)
  refine SepWP.weaken_pre (P' := ((sl.envpTableAddr + BitVec.ofNat 64 (8 * 0)) ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ ?F_ev)
    (by simp only [Nat.mul_zero, BitVec.add_zero]; sep_frame) ?_
  refine SepWP.mono (hb_envp_scan_loop hc sl.envpAddrs sl.envpTableAddr 0 ?F_ev henvp_no0 (by rw [henvp_len]; omega)
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_m])
    (by simp only [wp_norm, arm64_norm, hx19_m]) (by simp only [wp_norm, arm64_norm])) ?_ (fun _ _ _ ho => ho)
  rintro se Q hpc_e hrun_e ⟨_, _, hsp_e, hx2_e, hx4_e, hx19_e, hx20_e, hx29_e, hstd_e, rfl⟩
  simp only [Nat.zero_add, Nat.mul_zero, BitVec.add_zero] at hx2_e ⊢
  have hpres_e : StdStatePreserved s1 se := hpres_m.trans (StdStatePreserved.trans (by simp [*]) hstd_e)
  have hsh_ev := hb_ofNat_shl3 (k := inputs.envp.length + 1) (by omega)
  have hx2_ev : se.readReg64 .x2 = BitVec.ofNat 64 (inputs.envp.length + 1) := by simpa [henvp_len] using hx2_e
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x60#64); hb_wp_steps_p 5
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_e]) ?_
  hb_wp_steps_p 1; refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_e]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_e],
    by simpa [wp_norm, arm64_norm, hsp_m'] using hsp_e, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hauxv_eq],
    by simpa [wp_norm, arm64_norm, hx0_m] using hx4_e, by simpa [wp_norm, arm64_norm, hx20_m] using hx20_e,
    by simp (config := { decide := true }) only [wp_norm, arm64_norm], by simpa [wp_norm, arm64_norm, hx29_m] using hx29_e,
    hpres_e.trans (by simp [*]), ?_⟩
  rw [← hauxv_eq]; dsimp only [InitSavedFrame, HbStage1Got]; ac_rfl

private theorem hbInitLibc_auxv_scan {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s2 : State} {F : SepProp}
    (hc : hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S))
    (hpc2 : s2.pc = C.std.initLibcAddr + 0x68#64) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = sl.sp0 - 0x1c0#64)
    (hx0 : s2.readReg64 .x0 = sl.auxvTableAddr) (hx4 : s2.readReg64 .x4 = sl.sp0 - 0x160#64)
    (hx20 : s2.readReg64 .x20 = sl.argvAddrs.getD 0 0#64) (hx21 : s2.readReg64 .x21 = C.std.libcAddr &&& 0xfffffffffffff000#64)
    (hal16 : sl.sp0.toNat % 16 = 0) (hauxv_no0 : ∀ p ∈ sl.auxvEntries, p.1 ≠ 0#64)
    (hauxv_hwcap : (auxvScan38 sl.auxvEntries).getD 16 0#64 = inputs.init.auxv.hwcap)
    (hauxv_pagesz : (auxvScan38 sl.auxvEntries).getD 6 0#64 = 4096#64) :
    SepWP P (C.std.initLibcAddr + 0xac#64) s2
      ((((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (C.std.hwcapAddr ↦₆₄ 0#64) ∗ (C.std.sysinfoAddr ↦₆₄ 0#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 0#64)) ∗ F)
      (fun s3 Q => s3.pc = C.std.initLibcAddr + 0xac#64 ∧ s3.status = .Running ∧ s3.sp = sl.sp0 - 0x1c0#64 ∧
        s3.readReg64 .x4 = sl.sp0 - 0x160#64 ∧ s3.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 ∧ StdStatePreserved s2 s3 ∧
        Q = ((((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
          (C.std.hwcapAddr ↦₆₄ inputs.init.auxv.hwcap) ∗ (C.std.sysinfoAddr ↦₆₄ (auxvScan38 sl.auxvEntries).getD 32 0#64) ∗
          ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ F)) := by
  have_instrs hc 33 10
  have hsp0_al : (sl.sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr (align16_and_15 hal16)
  have hhw_pg := page_add_lo12_eq C.std.hwcapAddr; have hsys_pg := page_add_lo12_eq C.std.sysinfoAddr
  have hlibc_pg := page_add_trunc12_eq C.std.libcAddr; have haux_len := auxvScan38_length sl.auxvEntries
  have ha32 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 32) = sl.sp0 - 0x1c0#64 + 0x160#64 := by bv_lin
  have ha16 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 16) = sl.sp0 - 0x1c0#64 + 0xe0#64 := by bv_lin
  have ha6 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 6) = sl.sp0 - 0x1c0#64 + 0x90#64 := by bv_lin
  conv => arg 4; rw [encodeAuxvBytes_eq_flatMap_bytesLE, ← pointsToWords64_eq_pointsToBytesLE]
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x84#64)
  refine SepWP.weaken_pre (P' := (((sl.auxvTableAddr ↦₆₄* ((sl.auxvEntries ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
    ((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64)) ∗ ?F_ax)) (by sep_frame) ?_
  refine SepWP.mono (hb_auxv_scan_loop hc sl.auxvEntries sl.auxvTableAddr (sl.sp0 - 0x160#64) (List.replicate 38 0#64)
    ?F_ax hauxv_no0 (by simp) hpc2 hrun2 hx0 hx4) ?_ (fun _ _ _ ho => ho)
  rintro sa Q _ hrun_a ⟨hpc_a, _, hsp_a, hx4_a, hx20_a, hx21_a, _, hstd_a, rfl⟩
  have hsp_a' : sa.sp = sl.sp0 - 0x1c0#64 := hsp_a.trans hsp2
  have hx20_a' : sa.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 := hx20_a.trans hx20
  have hx21_a' : sa.readReg64 .x21 = C.std.libcAddr &&& 0xfffffffffffff000#64 := hx21_a.trans hx21
  change SepWP P (C.std.initLibcAddr + 0xac#64) sa
    (((sl.auxvTableAddr ↦₆₄* ((sl.auxvEntries ++ [(AuxvTag.null, 0#64)]).flatMap fun (t, v) => [t, v])) ∗
      ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries)) ∗ _) _
  rw [pointsToWords64_eq_pointsToBytesLE, ← encodeAuxvBytes_eq_flatMap_bytesLE]
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x94#64)
  rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 32 (by omega), ha32]; hb_wp_steps_p 2
  rw [← ha32, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 32 (by omega)]
  rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 16 (by omega), ha16]; hb_wp_steps_p 1
  rw [← ha16, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 16 (by omega)]; hb_wp_steps_p 1
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_a]) ?_
  apply SepWP.cut (mid := C.std.initLibcAddr + 0xa0#64)
  refine SepWP.mono (post := fun sb Qb => sb.pc = C.std.initLibcAddr + 0xa0#64 ∧ sb.status = .Running ∧
    sb.sp = sl.sp0 - 0x1c0#64 ∧ sb.readReg64 .x4 = sl.sp0 - 0x160#64 ∧ sb.readReg64 .x20 = sl.argvAddrs.getD 0 0#64 ∧
    sb.readReg64 .x21 = C.std.libcAddr &&& 0xfffffffffffff000#64 ∧ StdStatePreserved s2 sb ∧
    Qb = (((sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗
      (C.std.hwcapAddr ↦₆₄ inputs.init.auxv.hwcap) ∗ (C.std.sysinfoAddr ↦₆₄ (auxvScan38 sl.auxvEntries).getD 32 0#64) ∗
      ((C.std.libcAddr + 0x30#64) ↦₆₄ 0#64)) ∗ F)) ?_ ?_
  · by_cases hsys : (auxvScan38 sl.auxvEntries).getD 32 0#64 = 0#64
    · rw [hsys]; hb_wp_steps_p 1
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_a]) ?_
      exact ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_a],
        by simp only [wp_norm, arm64_norm, hsp_a'], by simp only [wp_norm, arm64_norm, hx4_a],
        by simp only [wp_norm, arm64_norm, hx20_a'], by simp only [wp_norm, arm64_norm, hx21_a'], hstd_a.trans (by simp [*]), by ac_rfl⟩
    · have hsys_f : ((auxvScan38 sl.auxvEntries).getD 32 0#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hsys
      hb_wp_steps_p 3
      refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_a]) ?_
      exact ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_a],
        by simp only [wp_norm, arm64_norm, hsp_a'], by simp only [wp_norm, arm64_norm, hx4_a],
        by simp only [wp_norm, arm64_norm, hx20_a'], by simp only [wp_norm, arm64_norm, hx21_a'], hstd_a.trans (by simp [*]), by ac_rfl⟩
  · rintro sb Qb _ _ ⟨hpc_b, hrun_b, hsp_b, hx4_b, hx20_b, hx21_b, hstd_b, rfl⟩
    rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 6 (by omega), ha6]; hb_wp_steps_p 2
    rw [← ha6, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 6 (by omega)]; hb_wp_steps_p 1
    refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_b]) ?_
    exact ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_b],
      by simp only [wp_norm, arm64_norm, hsp_b], by simp only [wp_norm, arm64_norm, hx4_b],
      by simp only [wp_norm, arm64_norm, hx20_b], hstd_b.trans (by simp [*]), by ac_rfl⟩

private theorem hbInitLibc_progname_to_tls {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s3 : State} {F : SepProp}
    (hc : hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S))
    (hc58 : hasInstrs P (C.std.initLibcAddr + 0xe8#64) (((initLibcInstrs C.std).drop 58).take 14))
    (hpc3 : s3.pc = C.std.initLibcAddr + 0xac#64) (hrun3 : s3.status = .Running) (hsp3 : s3.sp = sl.sp0 - 0x1c0#64)
    (hx4 : s3.readReg64 .x4 = sl.sp0 - 0x160#64) (hx20 : s3.readReg64 .x20 = sl.argvAddrs.getD 0 0#64)
    (hargv0_ne0 : sl.argvAddrs.getD 0 0#64 ≠ 0#64) (hargv0_no0 : 0#8 ∉ inputs.argv.getD 0 [])
    (hargv0_dup : ∃ pad : List (BitVec 8), ((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗
      ((sl.argvAddrs.getD 0 0#64) ↦ᵣ (inputs.argv.getD 0 [] ++ [0#8] ++ pad))) = (sl.argvBase ↦ᵣ sl.upperStrBytes))
    (_hne_tls : C.std.initLibcAddr + 0x108#64 ≠ C.std.staticInitTlsAddr) :
    SepWP P C.std.staticInitTlsAddr s3
      (((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbStage1Got C S ∗ (C.std.prognameFullAddr ↦₆₄ 0#64) ∗ (C.std.prognameAddr ↦₆₄ 0#64)) ∗ F)
      (fun st Q =>
        let a0 := sl.argvAddrs.getD 0 0#64
        st.pc = C.std.staticInitTlsAddr ∧ st.status = .Running ∧ st.sp = sl.sp0 - 0x1c0#64 ∧
        st.readReg64 .x0 = sl.sp0 - 0x160#64 ∧ st.readReg64 .lr = C.std.initLibcAddr + 0x10c#64 ∧ StdStatePreserved s3 st ∧
        Q = (((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbStage1Got C S ∗
          (C.std.prognameFullAddr ↦₆₄ a0) ∗ (C.std.prognameAddr ↦₆₄ scanSlashPtr a0 a0 (inputs.argv.getD 0 []))) ∗ F)) := by
  have_instrs hc 43 10
  have ha0_f : (sl.argvAddrs.getD 0 0#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hargv0_ne0
  have hgot_pf := page_add_lo12_eq S.gotPrognameFullAddr; have hgot_p := page_add_lo12_eq S.gotPrognameAddr
  obtain ⟨pad, hdup⟩ := hargv0_dup
  apply SepWP.cut (mid := C.std.initLibcAddr + 0xec#64); conv => arg 4; dsimp only [HbStage1Got]
  hb_wp_steps_p 10; hb_clear_hf 43 52
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3]) ?_
  conv => arg 4; rw [← hdup, pointsToBytesRO_append]
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x104#64)
  refine SepWP.weaken_pre (P' := ((((sl.argvAddrs.getD 0 0#64) ↦ᵣ (inputs.argv.getD 0 [] ++ [0#8])) ∗
    (C.std.prognameAddr ↦₆₄ sl.argvAddrs.getD 0 0#64)) ∗ ?F_pg)) (by sep_frame) ?_
  refine SepWP.mono (hb_progname_scan_loop hc58 (inputs.argv.getD 0 []) (sl.argvAddrs.getD 0 0#64)
    (sl.argvAddrs.getD 0 0#64) ?F_pg hargv0_no0 (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun3]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])) ?_ (fun _ _ _ ho => ho)
  rintro spg Q _ hrun_p ⟨hpc_p, _, hsp_p, hx4_p, hstd_p, rfl⟩
  have hpres_p : StdStatePreserved s3 spg := StdStatePreserved.trans (by simp [*]) hstd_p
  have_instrs hc58 7 2
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x108#64); hb_wp_steps_p 1
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_p]) ?_
  hb_wp_steps_p 1; rw [add_sub_pc]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun_p]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun_p],
    by simpa [wp_norm, arm64_norm, hsp3] using hsp_p, by simp only [wp_norm, arm64_norm],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm], hpres_p.trans (by simp [*]), ?_⟩
  conv => rhs; rw [← hdup, pointsToBytesRO_append]
  dsimp only [HbStage1Got]; ac_rfl

private theorem hbInitLibc_post_tls_to_stage2 {P : Program} {C : HbCliLayout}
    {inputs : ProcessInputs} {sl : StackLayout} {s0 s1 st' : State} {F : SepProp}
    (hc58 : hasInstrs P (C.std.initLibcAddr + 0xe8#64) (((initLibcInstrs C.std).drop 58).take 14))
    (hc91 : hasInstrs P (C.std.initLibcAddr + 0x16c#64) (((initLibcInstrs C.std).drop 91).take 6))
    (hc114 : hasInstrs P (C.std.initLibcAddr + 0x1c8#64) ((initLibcInstrs C.std).drop 114))
    (hc_lsm : hasInstrs P C.std.libcStartMainAddr (hbLibcStartMainInstrs C.std))
    (hdummy1 : P.hasWords C.std.dummy1Addr dummy1Words)
    (hpc : st'.pc = C.std.initLibcAddr + 0x10c#64) (hrun : st'.status = .Running) (hsp : st'.sp = sl.sp0 - 0x1c0#64)
    (hal16 : sl.sp0.toNat % 16 = 0) (hlr_1 : s1.readReg64 .lr = C.std.libcStartMainAddr + 0x2c#64)
    (hx19_1 : s1.readReg64 .x19 = sl.argvTableAddr) (hx20_1 : s1.readReg32 .x20 = BitVec.ofNat 32 inputs.argv.length)
    (hx21_1 : s1.readReg64 .x21 = C.std.cMainAddr)
    (huid : (auxvScan38 sl.auxvEntries).getD 11 0#64 = (auxvScan38 sl.auxvEntries).getD 12 0#64)
    (hgid : (auxvScan38 sl.auxvEntries).getD 13 0#64 = (auxvScan38 sl.auxvEntries).getD 14 0#64)
    (hsec : (auxvScan38 sl.auxvEntries).getD 23 0#64 = 0#64)
    (_hne_stage2 : C.std.libcStartMainAddr + 0x50#64 ≠ C.std.libcStartMainStage2Addr) :
    SepWP P C.std.libcStartMainStage2Addr st'
      ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ LsmSavedFrame sl.sp0 s0) ∗ F)
      (fun sf Q => sf.pc = C.std.libcStartMainStage2Addr ∧ sf.status = .Running ∧ sf.sp = sl.sp0 ∧
        sf.readReg64 .x0 = C.std.cMainAddr ∧ sf.readReg32 .x1 = BitVec.ofNat 32 inputs.argv.length ∧
        sf.readReg64 .x2 = sl.argvTableAddr ∧ StdStatePreserved st' sf ∧
        Q = ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ LsmSavedFrame sl.sp0 s0) ∗ F)) := by
  have hsp0_al : (sl.sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr (align16_and_15 hal16)
  have haux_len := auxvScan38_length sl.auxvEntries
  have ha25 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 25) = sl.sp0 - 0x1c0#64 + 0x128#64 := by bv_lin
  have ha11 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 11) = sl.sp0 - 0x1c0#64 + 0xb8#64 := by bv_lin
  have ha13 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 13) = sl.sp0 - 0x1c0#64 + 0xc8#64 := by bv_lin
  have ha23 : sl.sp0 - 0x160#64 + BitVec.ofNat 64 (8 * 23) = sl.sp0 - 0x1c0#64 + 0x118#64 := by bv_lin
  have hstg2_adr := add_sub_pc (C.std.libcStartMainAddr + 0x3c#64) C.std.libcStartMainStage2Addr
  have_instrs hc58 9 5; have hfi68 := hf_10; have hfi69 := hf_11; have hfd0 := fetch_dummy1 hdummy1
  have _hne_d1 : C.std.initLibcAddr + 0x110#64 ≠ C.std.dummy1Addr := pc_ne_of_fetch_ne hfi68 hfd0
  have _hne_d2 : C.std.dummy1Addr ≠ C.std.initLibcAddr + 0x114#64 := pc_ne_of_fetch_ne hfd0 hfi69
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x110#64)
  rw [pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 25 (by omega), ha25]; hb_wp_steps_p 1
  rw [← ha25, ← pointsToWords64_focus (sl.sp0 - 0x160#64) (auxvScan38 sl.auxvEntries) 25 (by omega)]
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  apply SepWP.cut (mid := C.std.dummy1Addr); hb_wp_steps_p 1; rw [add_sub_pc]; hb_clear_hf 9 10
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  have hf_0 := hfd0; apply SepWP.cut (mid := C.std.initLibcAddr + 0x114#64); hb_wp_steps_p 1; hb_clear_hf 0 0
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
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x16c#64); (conv => arg 4; rw [hf11]); hb_wp_steps_p 3; (conv => arg 4; rw [← hf11]); hb_clear_hf 11 13
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  have_instrs hc91 0 6
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x1c8#64); (conv => arg 4; rw [hf13]); hb_wp_steps_p 3; (conv => arg 4; rw [← hf13, hf23]); hb_wp_steps_p 3; (conv => arg 4; rw [← hf23]); hb_clear_hf 0 5
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  have_instrs hc114 0 4; have hfi117 := hf_3; have hfl11 := fetch_at 11 0x2c#64 hc_lsm
  have _hne_ret : C.std.initLibcAddr + 0x1d4#64 ≠ C.std.libcStartMainAddr + 0x2c#64 := pc_ne_of_fetch_ne hfi117 hfl11
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x1d4#64); (conv => arg 4; dsimp only [InitSavedFrame, LsmSavedFrame]); hb_wp_steps_p 3
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  apply SepWP.cut (mid := C.std.libcStartMainAddr + 0x2c#64); hb_wp_steps_p 1; hb_clear_hf 0 3
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  have_instrs hc_lsm 11 10
  apply SepWP.cut (mid := C.std.libcStartMainAddr + 0x50#64); hb_wp_steps_p 9
  refine SepWP.done (by simp (config := { decide := true }) only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  hb_wp_steps_p 1; refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hrun],
    by simp (config := { decide := true }) only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simpa [wp_norm, arm64_norm, State.readReg32] using hx20_1, by simp only [wp_norm, arm64_norm],
    by simp [*], by dsimp only [InitSavedFrame, LsmSavedFrame]⟩

def HbPreTlsSep (L : StdBinaryLayout) (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 0x220#64) 0x60 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗
  (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ StdTlsGlobals L ∗ (L.libcAddr ↦₈ 0#8) ∗ StdLibcTlsZero L

def HbPostTlsSep (L : StdBinaryLayout) (sp0 sysinfoVal : BitVec 64) : SepProp :=
  (((L.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ 0#32) ∗ (((L.builtinTlsAddr + 0xc8#64) + 0x58#64) ↦₆₄ 0#64) ∗
  (L.libcAddr ↦₈ 1#8) ∗ memRegion (sp0 - 0x220#64) 0x60 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
  (L.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ HbTlsState L sysinfoVal

private theorem hbStage1_to_stage2 {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {img : ElfImage} {inputs : ProcessInputs} {s0 : State} {F : SepProp}
    (hS : S.Valid C) (hm : HbMatchesImage C S img = true) (hvalid : inputs.Valid)
    (hinfo : InitialStackInfo img inputs s0)
    (hstage1 : CodeChunks P (hbStage1Chunks C S)) (hmemOps : HbMemOpsCode P C)
    (hsvc : P.svc = tidOnlySvc)
    (hne_m : C.std.initLibcAddr + 0x28#64 ≠ C.std.memsetAddr)
    (hne_t : C.std.initLibcAddr + 0x108#64 ≠ C.std.staticInitTlsAddr)
    (hne_s : C.std.libcStartMainAddr + 0x50#64 ≠ C.std.libcStartMainStage2Addr) :
    let sl := StackLayout.of img inputs
    SepWP P C.std.libcStartMainStage2Addr s0
      ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPre C.std ∗ HbStage1Got C S ∗
        (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbPreTlsSep C.std sl.sp0) ∗ F)
      (sepPost
        (fun sf => sf.sp = sl.sp0 ∧ sf.readReg64 .x0 = C.std.cMainAddr ∧
          sf.readReg32 .x1 = BitVec.ofNat 32 inputs.argv.length ∧ sf.readReg64 .x2 = sl.argvTableAddr ∧
          sf.tpidrEl0 = C.std.builtinTlsAddr + 0xc8#64 ∧ StdTlsFieldsPreserved s0 sf)
        ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPost C.std inputs sl ∗ HbStage1Got C S ∗
          (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
          (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
          (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbPostTlsSep C.std sl.sp0 ((auxvScan38 sl.auxvEntries).getD 32 0#64)) ∗ F)) := by
  dsimp only; let sl := StackLayout.of img inputs
  obtain ⟨hwf, hentry_eq, hphdr_eq, hphnum_eq, _, _, hphdrC, _⟩ := HbMatchesImage.unpack hm
  have hphent_eq := (wellFormed_segments_bounds hwf).1
  obtain ⟨hc_start, hc_startC, hc_lsm, hc_init, hc58, hc91, hc114, hdummy1, hc_stls, hc_ctls, hc_itp, hset_tp⟩ :=
    (by simpa [hbStage1Chunks, CodeChunks, CodeChunk.holds] using hstage1 :
      hasInstrs P C.std.startAddr (startInstrs C.std) ∧ hasInstrs P C.std.startCAddr (startCInstrs C.std) ∧
      hasInstrs P C.std.libcStartMainAddr (hbLibcStartMainInstrs C.std) ∧ hasInstrs P C.std.initLibcAddr (hbInitLibcPreInstrs C S) ∧
      hasInstrs P (C.std.initLibcAddr + 0xe8#64) (((initLibcInstrs C.std).drop 58).take 14) ∧
      hasInstrs P (C.std.initLibcAddr + 0x16c#64) (((initLibcInstrs C.std).drop 91).take 6) ∧
      hasInstrs P (C.std.initLibcAddr + 0x1c8#64) ((initLibcInstrs C.std).drop 114) ∧
      P.hasWords C.std.dummy1Addr dummy1Words ∧ hasInstrs P C.std.staticInitTlsAddr (hbStaticInitTlsInstrs C.std) ∧
      hasInstrs P C.std.copyTlsAddr (copyTlsInstrs C.std) ∧ hasInstrs P C.std.initTpAddr (initTpInstrs C.std) ∧
      P.hasWords C.std.setThreadAreaAddr setThreadAreaWords)
  have ops := hbStdMemOps hmemOps
  have hbtls8 : C.std.builtinTlsAddr.toNat % 8 = 0 := by have := hS.builtinTls_align; omega
  have hTlsSpec := hbStaticInitTls_ok hc_stls hc_ctls hc_itp hset_tp ops hsvc hphdrC (hbMatchesImage_phdr_end hm) hbtls8 hS.mainTls_nz
  have ⟨hargc_lo, hargc_hi, henvp_hi⟩ := hinfo.argc_bounds
  have hargv_len : sl.argvAddrs.length = inputs.argv.length := hinfo.argvAddrs_length
  have henvp_len : sl.envpAddrs.length = inputs.envp.length := hinfo.envpAddrs_length
  have henvp_eq : sl.envpTableAddr = sl.sp0 + BitVec.ofNat 64 (8 * (inputs.argv.length + 2)) := by
    simp only [StackLayout.envpTableAddr, StackLayout.argc, hargv_len]
  have hauxv_eq : sl.auxvTableAddr = sl.envpTableAddr + BitVec.ofNat 64 (8 * (inputs.envp.length + 1)) := by
    simp only [StackLayout.auxvTableAddr, StackLayout.envpTableAddr, StackLayout.argc, StackLayout.envc, hargv_len, henvp_len, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have henvp_no0 : ∀ p ∈ sl.envpAddrs, p ≠ 0#64 := fun p hp => by obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp; exact hinfo.envpAddr_ne_zero (henvp_len ▸ hi)
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr; rw [← hinfo.auxvEntries_eq] at hwf_aux
  have hscan := auxvScan38_mkAuxvEntries img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr; rw [← hinfo.auxvEntries_eq] at hscan
  rcases hscan with ⟨haux_len, hs3, hs4, hs5, hs6, _, hs11, hs12, hs13, hs14, _, hs16, hs23, _, _, _⟩
  have gd : ∀ {xs : List (BitVec 64)} {k : Nat} {v : BitVec 64}, xs[k]? = some v → xs.getD k 0#64 = v := fun h => by rw [List.getD, h]; rfl
  have h0_lt : 0 < inputs.argv.length := by omega
  have h0_lt' : 0 < sl.argvAddrs.length := by omega
  have ha0_eq : sl.argvAddrs.getD 0 0#64 = sl.argvAddrs[0]'h0_lt' := by simp [List.getD, getElem?_pos, h0_lt']
  have hv0_eq : inputs.argv.getD 0 [] = inputs.argv[0]'h0_lt := by simp [List.getD, getElem?_pos, h0_lt]
  obtain ⟨pad, hargv0_no0', _, _, _, hdup'⟩ := hinfo.dup_argv_cstr_padded hvalid.1 h0_lt
  conv => arg 4; rw [memRegion_split_le (sl.sp0 - 0x1c0#64) 0x190 0x1c0 (by decide) (by decide), show (0x1c0 - 0x190 : Nat) = 0x30 from rfl, show sl.sp0 - 0x1c0#64 + BitVec.ofNat 64 0x190 = sl.sp0 - 0x30#64 by bv_lin]
  conv => arg 4; dsimp only [Stage1GlobalsPre]
  apply SepWP.cut (mid := C.std.initLibcAddr); refine SepWP.weaken_pre (P' := (((sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ HbStage1Got C S ∗ memRegion (sl.sp0 - 0x30#64) 0x30) ∗ ?F1)) (by sep_frame) ?_
  refine SepWP.mono (hbStart_to_initLibc (inputs := inputs) hc_start hc_startC hc_lsm hc_init hinfo.s0_sp (hinfo.s0_pc.trans hentry_eq) hinfo.s0_status hinfo.sp0_align16 hargc_lo hargc_hi hargv_len henvp_eq rfl) ?_ (fun _ _ _ ho => ho)
  rintro s1 _ _ _ ⟨hpc1, hrun1, hsp1, hlr1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hstd01, rfl⟩
  apply SepWP.cut (mid := C.std.initLibcAddr + 0x68#64); refine SepWP.weaken_pre (P' := ((memRegion (sl.sp0 - 0x1c0#64) 0x190 ∗ HbStage1Got C S ∗ (C.std.environAddr ↦₆₄ 0#64) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ 0#64) ∗ (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64]))) ∗ ?F2)) (by sep_frame) ?_
  refine SepWP.mono (hbInitLibc_prologue_envp (inputs := inputs) hc_init ops hpc1 hrun1 hsp1 hx0_1 hx1_1 hinfo.sp0_align16 henvp_len henvp_hi henvp_no0 hauxv_eq hne_m) ?_ (fun _ _ _ ho => ho)
  rintro s2 _ _ _ ⟨hpc2, hrun2, hsp2, hx0_2, hx4_2, hx20_2, hx21_2, _, hstd12, rfl⟩
  apply SepWP.cut (mid := C.std.initLibcAddr + 0xac#64); refine SepWP.weaken_pre (P' := ((((sl.sp0 - 0x160#64) ↦₆₄* List.replicate 38 0#64) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗ (C.std.hwcapAddr ↦₆₄ 0#64) ∗ (C.std.sysinfoAddr ↦₆₄ 0#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 0#64)) ∗ ?F3)) (by sep_frame) ?_
  refine SepWP.mono (hbInitLibc_auxv_scan (inputs := inputs) hc_init hpc2 hrun2 hsp2 hx0_2 hx4_2 hx20_2 hx21_2 hinfo.sp0_align16 (fun p hp => (hwf_aux.2.2 p.1 p.2 hp).1) (gd hs16) (gd hs6)) ?_ (fun _ _ _ ho => ho)
  rintro s3 _ _ _ ⟨hpc3, hrun3, hsp3, hx4_3, hx20_3, hstd23, rfl⟩
  apply SepWP.cut (mid := C.std.staticInitTlsAddr); refine SepWP.weaken_pre (P' := (((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbStage1Got C S ∗ (C.std.prognameFullAddr ↦₆₄ 0#64) ∗ (C.std.prognameAddr ↦₆₄ 0#64)) ∗ ?F4)) (by sep_frame) ?_
  refine SepWP.mono (hbInitLibc_progname_to_tls (inputs := inputs) hc_init hc58 hpc3 hrun3 hsp3 hx4_3 hx20_3 (ha0_eq ▸ hinfo.argvAddr_ne_zero h0_lt) (hv0_eq ▸ hargv0_no0') ⟨pad, by rwa [ha0_eq, hv0_eq]⟩ hne_t) ?_ (fun _ _ _ ho => ho)
  rintro st _ _ _ ⟨hpct, hrunt, hspt, hx0_t, hlr_t, hstd3t, rfl⟩
  have hstd0t : StdStatePreserved s0 st := hstd01.trans (hstd12.trans (hstd23.trans hstd3t))
  have hsp_al_t : st.spAligned = true := by
    simp only [State.spAligned, hspt]; exact hb_spAligned_sub hinfo.sp0_align16 0x1c0#64
  have hsp_60 : st.sp - 0x60#64 = sl.sp0 - 0x220#64 := by rw [hspt]; bv_lin
  conv => arg 4; dsimp only [HbStage1Got, HbPreTlsSep]
  refine SepWP.call_subroutine_frame (ret_pc := C.std.initLibcAddr + 0x10c#64) hTlsSpec
    (x := (sl.sp0 - 0x160#64, auxvScan38 sl.auxvEntries, 0#8, (auxvScan38 sl.auxvEntries).getD 32 0#64)) (F := ?FTls)
    hpct hrunt hsp_al_t hlr_t
    (by dsimp only [hbStaticInitTlsSpec]; rw [hsp_60, pure_sepConj_of_true ⟨hx0_t, hphdr_eq ▸ hs3, hphent_eq ▸ hs4, hphnum_eq ▸ hs5⟩]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun st' hpct' hrunt' hspt' _ => ?_
  dsimp only [hbStaticInitTlsSpec]; (wp_conv_pre => rw [sepConj_assoc]); apply SepWP.pure_elim; rintro ⟨htp', htlst⟩
  have hspt'' : st'.sp = sl.sp0 - 0x1c0#64 := hspt'.trans hspt
  have hsp'_60 : st'.sp - 0x60#64 = sl.sp0 - 0x220#64 := by rw [hspt'']; bv_lin
  (wp_conv_pre => rw [htp', hsp'_60])
  refine SepWP.weaken_pre (P' := ((InitSavedFrame sl.sp0 s1 ∗ ((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ LsmSavedFrame sl.sp0 s0) ∗ ?F6)) (by sep_frame) ?_
  refine SepWP.mono (hbInitLibc_post_tls_to_stage2 (inputs := inputs) hc58 hc91 hc114 hc_lsm hdummy1 hpct' hrunt' hspt'' hinfo.sp0_align16 hlr1 hx19_1 hx20_1 hx21_1 ((gd hs11).trans (gd hs12).symm) ((gd hs13).trans (gd hs14).symm) (gd hs23) hne_s) ?_ (fun _ _ _ ho => ho)
  rintro sf _ _ _ ⟨_, _, hspf, hx0f, hx1f, hx2f, hstdtf, rfl⟩
  refine ⟨⟨hspf, hx0f, hx1f, hx2f, hstdtf.2.2.1.trans htp', (hstd0t.toTlsFields.trans htlst).trans hstdtf.toTlsFields⟩, ?_⟩
  refine Entails.trans (sepConj_mono_left (stage1_stack_entails_memRegion sl.sp0 s0 s1 (auxvScan38 sl.auxvEntries) haux_len)) ?_
  dsimp only [Stage1GlobalsPost, HbStage1Got, HbPostTlsSep]; sep_frame

end

/-! ## Stage 2 (`libc_start_main_stage2` to `c_main`) and `_start` to `c_main` Composition -/

private def hbInitLseSpec (L : StdBinaryLayout) : Spec (BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, auxvAddr, entries) s0 =>
    ⌜(∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == 16#64) = some (16#64, hwcap)⌝ ∗
    ((L.haveLseAtomicsAddr ↦₈ 0#8) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x30)
  post := fun (hwcap, auxvAddr, entries) s0 sf =>
    ⌜StdStatePreserved s0 sf⌝ ∗
    ((L.haveLseAtomicsAddr ↦₈ (if hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x30)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

private def hbCpuCtorSpec (S : HbStartupLayout) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (ptr, hwcap2, oldVal) s0 =>
    ⌜(s0.readReg64 (.gpr 0#5)).getLsbD 62 = true ∧ s0.readReg64 (.gpr 1#5) = ptr⌝ ∗
    ((S.cpuFeaturesGlobalAddr ↦₆₄ oldVal) ∗ (ptr ↦₆₄ hwcap2) ∗ stackFrameAt s0.sp 0x40)
  post := fun (ptr, hwcap2, _) s0 sf =>
    ⌜StdStatePreserved s0 sf⌝ ∗
    ((∃∗ v : BitVec 64, S.cpuFeaturesGlobalAddr ↦₆₄ v) ∗ (ptr ↦₆₄ hwcap2) ∗ stackFrameAt s0.sp 0x40)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

private def hbInitCpuFeaturesSpec (C : HbCliLayout) (S : HbStartupLayout) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, hwcap2, auxvAddr, entries) s0 =>
    ⌜(∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == 16#64) = some (16#64, hwcap) ∧
      entries.find? (·.1 == 26#64) = some (26#64, hwcap2)⌝ ∗
    ((S.cpuFeaturesGlobalAddr ↦₆₄ 0#64) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x70)
  post := fun (_, _, auxvAddr, entries) s0 sf =>
    ⌜StdStatePreserved s0 sf⌝ ∗
    ((∃∗ v : BitVec 64, S.cpuFeaturesGlobalAddr ↦₆₄ v) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x70)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

private def HbCtorTailRel (s0 sf : State) : Prop :=
  sf.sp = s0.sp - 64#64 ∧ sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  sf.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StdStatePreserved s0 sf

private theorem HbCtorTailRel.step {s0 s1 s2 : State} (h1 : HbCtorTailRel s0 s1)
    (hsp : s2.sp = s1.sp) (h26 : s2.readReg64 (.gpr 26#5) = s1.readReg64 (.gpr 26#5))
    (h27 : s2.readReg64 (.gpr 27#5) = s1.readReg64 (.gpr 27#5))
    (h28 : s2.readReg64 (.gpr 28#5) = s1.readReg64 (.gpr 28#5))
    (h29 : s2.readReg64 (.gpr 29#5) = s1.readReg64 (.gpr 29#5))
    (hv : calleeSavedVRegs s2 = calleeSavedVRegs s1) (hstd : StdStatePreserved s1 s2) : HbCtorTailRel s0 s2 :=
  ⟨hsp.trans h1.1, h26.trans h1.2.1, h27.trans h1.2.2.1, h28.trans h1.2.2.2.1,
   h29.trans h1.2.2.2.2.1, hv.trans h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.trans hstd⟩

section
arm64_proof_prelude
set_option Elab.async false
set_option maxRecDepth 200000

private theorem hbDoInit_ok {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.doInitAddr [ .adr true .x1 (adrpOff L.doInitAddr L.initializedAddr),
      .ldr .W32 .B8 false .x0 (.Offset .x1 (pageLo12 L.initializedAddr)), decodeWord 0x35000160#32,
      .adr true .x0 (adrpOff (L.doInitAddr + 0x0c#64) (L.gotAddr + 0x30#64)), decodeWord 0x52800022#32,
      .str .B8 .x2 (.Offset .x1 (pageLo12 L.initializedAddr)),
      .ldr .W64 .X64 false .x0 (.Offset .x0 (pageLo12 (L.gotAddr + 0x30#64))), decodeWord 0xb40000c0#32 ])
    (hw34 : P.hasWords (L.doInitAddr + 0x34#64) [0xd65f03c0#32]) :
    subroutine_ok P L.doInitAddr (stdDoInitSpec L) := by
  apply subroutine_ok_of_sepWP_init; intro initVal R s0 hpc hrun hpre _
  dsimp only [stdDoInitSpec] at hpre ⊢; refine ⟨(L.initializedAddr ↦₈ initVal) ∗ ((L.gotAddr + 0x30#64) ↦₆₄ 0#64), hpre, ?_⟩
  have hc34 := hb_hasInstrs_of_hasWords hw34; have_instrs hc 0 8
  have hf_ret : P.fetch (L.doInitAddr + 0x34#64) = some (.ret .lr) := by
    simpa [decodeWord] using hasInstrs.fetch_at_zero hc34
  wp_step; wp_step; by_cases hzero : initVal == 0#8
  · have hiz : initVal = 0#8 := of_decide_eq_true hzero; subst hiz; hb_wp_steps_p 7
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]⟩
    simp only [beq_self_eq_true, ↓reduceIte]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [wp_norm, arm64_norm, *], hm⟩
  · have hne8 : initVal ≠ 0#8 := fun h => hzero (by subst h; rfl)
    have hnz : (initVal.zeroExtend 32 != 0#32) = true := by rw [bne_iff_ne]; intro h; exact hne8 (by simpa using congrArg (BitVec.truncate 8) h)
    have hnz64 : (initVal.zeroExtend 64).truncate 32 ≠ 0#32 := fun h => hne8 (by simpa using congrArg (BitVec.truncate 8) h)
    wp_step; wp_step; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]⟩
    simp only [hzero, Bool.false_eq_true, ↓reduceIte]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨ProcessFieldsPreserved.refl s0, hm⟩

private theorem hb_ubfx_bit8 (src : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 src) >>> 8 &&& 1#64) =
      if src.getLsbD 8 then 1#8 else 0#8 := by
  rw [BitVec.getLsbD_eq_getElem (by decide)]; ext i hi
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (cases h8 : src[8] <;> simp (config := { decide := true }) [h8])

private theorem hb_let_sp {P : Program} {t sp' : BitVec 64} {s : State} {Pre : SepProp} {post oom}
    (hsp : s.sp = sp') (h : (s.sp = sp') → SepWP P t s Pre post oom) : SepWP P t s Pre post oom := h hsp

private theorem hb_let_x0 {P : Program} {t v : BitVec 64} {s : State} {Pre : SepProp} {post oom}
    (hx0 : s.readReg64 (.gpr 0#5) = v) (h : (s.readReg64 (.gpr 0#5) = v) → SepWP P t s Pre post oom) :
    SepWP P t s Pre post oom := h hx0

private theorem hbInitLse_ok {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initLseAddr (decodeWords [0xf81f0ffe#32, 0xd2800200#32] ++
      [ .bl (L.getauxvalAddr - (L.initLseAddr + 0x08#64)), decodeWord 0x53082000#32,
        .adr true .x1 (adrpOff (L.initLseAddr + 0x10#64) L.haveLseAtomicsAddr), decodeWord 0xf84107fe#32,
        .str .B8 .x0 (.Offset .x1 (pageLo12 L.haveLseAtomicsAddr)), decodeWord 0xd65f03c0#32 ]))
    (hGetauxval : subroutine_ok P L.getauxvalAddr (stdGetauxvalSpec L)) :
    subroutine_ok P L.initLseAddr (hbInitLseSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbInitLseSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hnonull, hfind16⟩, hpre⟩
  refine ⟨(L.haveLseAtomicsAddr ↦₈ 0#8) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x30, hpre, ?_⟩
  have hsf10 : stackFrameAt s0.sp 0x10 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1)) := by simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackFrameAt_split s0.sp 0x10 0x20, hsf10]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  have_instrs hc 0 8; clear hc; have hsp0 := sp_and_15_of_spAligned hsp
  hb_wp_steps_p 3
  refine hb_let_sp (sp' := s0.sp - 16#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) fun hsp_bl => ?_
  refine hb_let_x0 (v := 16#64) (by simp [wp_norm, arm64_norm]) fun hx0_bl => ?_
  have htag17 : (16#64 : BitVec 64) ≠ 0x17#64 := by decide
  refine SepWP.call_subroutine_frame_auto hGetauxval (x := (16#64, hwcap, auxvAddr, entries)) (ret_pc := L.initLseAddr + 0x0c#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    (by dsimp only [stdGetauxvalSpec]; rw [hsp_bl]; sep_frame (disch := assumption))
  dsimp only [stdGetauxvalSpec]; (wp_conv_pre => rw [hsp_bl, sepConj_assoc]); apply SepWP.pure_elim; rintro ⟨hx0_1, hstd1⟩
  have hsp1' : sf1.sp = s0.sp - 16#64 := hsp1.trans hsp_bl
  wp_steps 2
  refine SepWP.step_ldr64 (ea := s0.sp - 16#64) (wb := some (.sp, s0.sp))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1]) hf_5
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp1', hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp1', bv_lin_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
  hb_wp_steps_p 2
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨(StdStatePreserved.trans (by simp [wp_norm, arm64_norm, *]) hstd1).trans (by simp [wp_norm, arm64_norm, *]),
      Satisfies.mono (sepConj_mono_left ?_) hm⟩
    rw [hb_ubfx_bit8, stackFrameAt_split s0.sp 0x10 0x20, hsf10]; sep_frame
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, gv⟩
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 gv
    rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, gv]

set_option maxHeartbeats 400000 in
private theorem hbCpuCtor_chunk0b {P : Program} {ctorAddr ptr hwcap2 : BitVec 64} {s0 s1 : State}
    {target_pc : BitVec 64} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw0 : P.hasWords ctorAddr hbCpuCtorWords0)
    (hpc1 : s1.pc = ctorAddr + 20#64) (hrun1 : s1.status = .Running)
    (hx1_1 : s1.readReg64 (.gpr 1#5) = ptr) (hrel1 : HbCtorTailRel s0 s1)
    (hnext : ∀ sf : State, sf.pc = ctorAddr + 0x8c#64 → sf.status = .Running → HbCtorTailRel s0 sf →
      SepWP P target_pc sf ((((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        (ptr ↦₆₄ hwcap2)) ∗ F) post oom) :
    SepWP P target_pc s1 ((((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
      (ptr ↦₆₄ hwcap2)) ∗ F) post oom := by
  have hc0 := hb_hasInstrs_of_hasWords hw0; have_instrs hc0 5 30; clear hc0 hw0
  wp_steps 27; wp_if htbz7
  · wp_step
    exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (hrel1.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s1))
  · wp_steps 3
    exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (hrel1.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s1))

private theorem hbCpuCtor_chunk0 {P : Program} {ctorAddr ptr hwcap2 : BitVec 64} {s0 : State}
    {target_pc : BitVec 64} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw0 : P.hasWords ctorAddr hbCpuCtorWords0)
    (hpc : s0.pc = ctorAddr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hbit62 : (s0.readReg64 (.gpr 0#5)).getLsbD 62 = true) (hx1 : s0.readReg64 (.gpr 1#5) = ptr)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (hnext : ∀ sf : State, sf.pc = ctorAddr + 0x8c#64 → sf.status = .Running → HbCtorTailRel s0 sf →
      SepWP P target_pc sf ((((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        (ptr ↦₆₄ hwcap2)) ∗ F) post oom) :
    SepWP P target_pc s0 ((((s0.sp - 64#64) ↦₆₄ w0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗
      ((s0.sp - 48#64) ↦₆₄ w2) ∗ ((s0.sp - 40#64) ↦₆₄ w3) ∗ ((s0.sp - 32#64) ↦₆₄ w4) ∗
      ((s0.sp - 24#64) ↦₆₄ w5) ∗ ((s0.sp - 16#64) ↦₆₄ w6) ∗ ((s0.sp - 8#64) ↦₆₄ w7) ∗
      (ptr ↦₆₄ hwcap2)) ∗ F) post oom := by
  have hc0 := hb_hasInstrs_of_hasWords hw0; have_instrs hc0 0 5; clear hc0
  have hsp0 := sp_and_15_of_spAligned hsp
  hb_wp_steps_p 4; wp_step
  refine hbCpuCtor_chunk0b (s0 := s0) hw0 ?_ ?_ ?_ ?_ hnext
  · simp [wp_norm, arm64_norm, bv_lin_norm]
  · simp [wp_norm, arm64_norm, hrun]
  · simp [wp_norm, arm64_norm, hx1]
  · clear hw0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [wp_norm, arm64_norm, bv_lin_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp only [calleeSavedVRegs_writeReg64, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]
    · simp [*]

private theorem hbCpuCtor_mid {P : Program} {S : HbStartupLayout} {s0 s : State}
    {target_pc : BitVec 64} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (S.initCpuFeaturesCtorAddr + 0x8c#64)
      ([.adr true .x3 (adrpOff (S.initCpuFeaturesCtorAddr + 0x8c#64) S.cpuFeaturesGlobalAddr)] ++
       decodeWords [0x9a851021#32, 0xf265001f#32, 0xb27f0025#32] ++
       [.addSubImm .W64 .ADD .x3 .x3 (S.cpuFeaturesGlobalAddr.truncate 12) false]))
    (hpc : s.pc = S.initCpuFeaturesCtorAddr + 0x8c#64) (hrun : s.status = .Running) (hrel : HbCtorTailRel s0 s)
    (hnext : ∀ sf : State, sf.pc = S.initCpuFeaturesCtorAddr + 0xa0#64 → sf.status = .Running →
      sf.readReg64 (.gpr 3#5) = S.cpuFeaturesGlobalAddr → HbCtorTailRel s0 sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 5; clear hc; wp_steps 5
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm])
    (hrel.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s))

private theorem hbCpuCtor_chunk1 {P : Program} {ctorAddr addr3 : BitVec 64} {s0 s : State}
    {target_pc : BitVec 64} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw1 : P.hasWords ctorAddr hbCpuCtorWords1)
    (hpc : s.pc = ctorAddr) (hrun : s.status = .Running) (hx3 : s.readReg64 (.gpr 3#5) = addr3) (hrel : HbCtorTailRel s0 s)
    (hnext : ∀ sf : State, sf.pc = ctorAddr + 0xac#64 → sf.status = .Running → sf.readReg64 (.gpr 3#5) = addr3 →
      HbCtorTailRel s0 sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have hc1 := hb_hasInstrs_of_hasWords hw1; have_instrs hc1 0 43; clear hc1 hw1; wp_steps 43
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx3])
    (hrel.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s))

private theorem hbCpuCtor_chunk2 {P : Program} {ctorAddr addr3 : BitVec 64} {s0 s : State}
    {target_pc : BitVec 64} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw2 : P.hasWords ctorAddr hbCpuCtorWords2)
    (hpc : s.pc = ctorAddr) (hrun : s.status = .Running) (hx3 : s.readReg64 (.gpr 3#5) = addr3) (hrel : HbCtorTailRel s0 s)
    (hnext : ∀ sf : State, sf.pc = ctorAddr + 0xac#64 → sf.status = .Running → sf.readReg64 (.gpr 3#5) = addr3 →
      HbCtorTailRel s0 sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have hc2 := hb_hasInstrs_of_hasWords hw2; have_instrs hc2 0 43; clear hc2 hw2; wp_steps 43
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx3])
    (hrel.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s))

private theorem hbCpuCtor_chunk3a {P : Program} {ctorAddr addr3 : BitVec 64} {s0 s : State}
    {target_pc : BitVec 64} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw3 : P.hasWords ctorAddr hbCpuCtorWords3)
    (hpc : s.pc = ctorAddr) (hrun : s.status = .Running) (hx3 : s.readReg64 (.gpr 3#5) = addr3) (hrel : HbCtorTailRel s0 s)
    (hnext : ∀ sf : State, sf.pc = ctorAddr + 0x94#64 → sf.status = .Running → sf.readReg64 (.gpr 3#5) = addr3 →
      HbCtorTailRel s0 sf → SepWP P target_pc sf Pre post oom) : SepWP P target_pc s Pre post oom := by
  have hc3 := hb_hasInstrs_of_hasWords hw3; have_instrs hc3 0 37; clear hc3 hw3; wp_steps 37
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx3])
    (hrel.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (ProcessFieldsPreserved.refl s))

private theorem hbCpuCtor_chunk3b {P : Program} {ctorAddr addr3 oldVal : BitVec 64} {s0 s : State}
    {target_pc : BitVec 64} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw3 : P.hasWords ctorAddr hbCpuCtorWords3) (hsp : s0.spAligned = true)
    (hpc : s.pc = ctorAddr + 0x94#64) (hrun : s.status = .Running) (hx3 : s.readReg64 (.gpr 3#5) = addr3) (hrel : HbCtorTailRel s0 s)
    (hnext : ∀ sf : State, sf.pc = s0.readReg64 (.gpr 30#5) → sf.status = .Running → sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf → StdStatePreserved s0 sf →
      SepWP P target_pc sf (((∃∗ v : BitVec 64, addr3 ↦₆₄ v) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5))) ∗ F) post oom) :
    SepWP P target_pc s (((addr3 ↦₆₄ oldVal) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5))) ∗ F) post oom := by
  have hc3 := hb_hasInstrs_of_hasWords hw3; have_instrs hc3 37 6; clear hc3 hw3
  rcases hrel with ⟨hsp_s, h26, h27, h28, h29, hv, hstd0⟩
  have hsp0 := sp_and_15_of_spAligned hsp
  hb_wp_steps_p 1
  refine SepWP.step_ldp64 (ea := s0.sp - 48#64) (ea2 := s0.sp - 40#64) (wb := none)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_38
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_s, hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_s, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  refine SepWP.step_ldp64 (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := none)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_39
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_s, hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_s, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_40
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_s, hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_s, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  refine SepWP.step_ldp64 (ea := s0.sp - 64#64) (ea2 := s0.sp - 56#64) (wb := some (.sp, s0.sp))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_41
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp_s, hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp_s, bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step
  refine SepWP.weaken_pre (by sep_frame) (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm])
    (by rw [CalleeSavedPreserved.iff_regs]; refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, h26], by simp [wp_norm, arm64_norm, h27], by simp [wp_norm, arm64_norm, h28], by simp [wp_norm, arm64_norm, h29], by simp only [calleeSavedVRegs_writeReg64, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, hv]⟩)
    (hstd0.trans (by simp [wp_norm, arm64_norm, *])))

private theorem hbCpuFeaturesCtor_ok {P : Program} {S : HbStartupLayout}
    (hw0 : P.hasWords S.initCpuFeaturesCtorAddr hbCpuCtorWords0)
    (hc_mid : hasInstrs P (S.initCpuFeaturesCtorAddr + 0x8c#64)
      ([.adr true .x3 (adrpOff (S.initCpuFeaturesCtorAddr + 0x8c#64) S.cpuFeaturesGlobalAddr)] ++
       decodeWords [0x9a851021#32, 0xf265001f#32, 0xb27f0025#32] ++
       [.addSubImm .W64 .ADD .x3 .x3 (S.cpuFeaturesGlobalAddr.truncate 12) false]))
    (hw1 : P.hasWords (S.initCpuFeaturesCtorAddr + 0xa0#64) hbCpuCtorWords1)
    (hw2 : P.hasWords (S.initCpuFeaturesCtorAddr + 0x14c#64) hbCpuCtorWords2)
    (hw3 : P.hasWords (S.initCpuFeaturesCtorAddr + 0x1f8#64) hbCpuCtorWords3) :
    subroutine_ok P S.initCpuFeaturesCtorAddr (hbCpuCtorSpec S) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨ptr, hwcap2, oldVal⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbCpuCtorSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hbit62, hx1⟩, hpre⟩
  refine ⟨(S.cpuFeaturesGlobalAddr ↦₆₄ oldVal) ∗ (ptr ↦₆₄ hwcap2) ∗ stackFrameAt s0.sp 0x40, hpre, ?_⟩
  have hsf40 : stackFrameAt s0.sp 0x40 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ((s0.sp - 64#64) ↦₆₄ w0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗ ((s0.sp - 48#64) ↦₆₄ w2) ∗ ((s0.sp - 40#64) ↦₆₄ w3) ∗
    ((s0.sp - 32#64) ↦₆₄ w4) ∗ ((s0.sp - 24#64) ↦₆₄ w5) ∗ ((s0.sp - 16#64) ↦₆₄ w6) ∗ ((s0.sp - 8#64) ↦₆₄ w7)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [hsf40]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  refine SepWP.weaken_pre (by sep_frame) (hbCpuCtor_chunk0 hw0 hpc hrun hsp hbit62 hx1 w0 w1 w2 w3 w4 w5 w6 w7 fun s1 hpc1 hrun1 hrel1 => ?_)
  refine hbCpuCtor_mid hc_mid hpc1 hrun1 hrel1 fun s2 hpc2 hrun2 hx3_2 hrel2 => ?_
  refine hbCpuCtor_chunk1 hw1 hpc2 hrun2 hx3_2 hrel2 fun s3 hpc3 hrun3 hx3_3 hrel3 => ?_
  have hpc3' : s3.pc = S.initCpuFeaturesCtorAddr + 0x14c#64 := by rw [hpc3]; bv_lin
  refine hbCpuCtor_chunk2 hw2 hpc3' hrun3 hx3_3 hrel3 fun s4 hpc4 hrun4 hx3_4 hrel4 => ?_
  have hpc4' : s4.pc = S.initCpuFeaturesCtorAddr + 0x1f8#64 := by rw [hpc4]; bv_lin
  refine hbCpuCtor_chunk3a hw3 hpc4' hrun4 hx3_4 hrel4 fun s5 hpc5 hrun5 hx3_5 hrel5 => ?_
  refine SepWP.weaken_pre (by sep_frame) (hbCpuCtor_chunk3b hw3 hsp hpc5 hrun5 hx3_5 hrel5 fun sf hpcf hrunf hspf hcsf hstdf => ?_)
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_cpu
  apply SepWP.done hpcf hrunf; refine ⟨fun hm => ?_, hspf, hcsf⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hstdf, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  rw [hsf40]; sep_frame

private theorem hb_let_ctor_args {P : Program} {t ptr : BitVec 64} {s : State} {Pre : SepProp} {post oom}
    (hb : (s.readReg64 (.gpr 0#5)).getLsbD 62 = true) (hx1 : s.readReg64 (.gpr 1#5) = ptr)
    (h : (s.readReg64 (.gpr 0#5)).getLsbD 62 = true → s.readReg64 (.gpr 1#5) = ptr → SepWP P t s Pre post oom) :
    SepWP P t s Pre post oom := h hb hx1

private def HbInitCpuMidRel (s0 sf : State) : Prop :=
  sf.sp = s0.sp - 48#64 ∧
  sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) ∧ sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧ sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧ sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧ sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧ sf.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StdStatePreserved s0 sf

private abbrev hbInitCpuFeaturesInstrs (C : HbCliLayout) (S : HbStartupLayout) : List Instr :=
  [decodeWord 0xd503201f#32, .adr false .x0 (S.cpuFeaturesGlobalAddr - (S.initCpuFeaturesAddr + 0x04#64))] ++
  decodeWords [0xf9400000#32, 0xb4000040#32, 0xd65f03c0#32, 0xa9bd7bf3#32, 0xd2800200#32] ++
  [.bl (C.std.getauxvalAddr - (S.initCpuFeaturesAddr + 0x1c#64))] ++
  decodeWords [0xaa0003f3#32, 0xd2800340#32] ++
  [.bl (C.std.getauxvalAddr - (S.initCpuFeaturesAddr + 0x28#64))] ++
  decodeWords [0xaa0003e2#32, 0xd2800303#32, 0xb2420260#32, 0x9100a3e1#32, 0xa901cfe3#32, 0xf90017e2#32] ++
  [.bl (S.initCpuFeaturesCtorAddr - (S.initCpuFeaturesAddr + 0x44#64))] ++
  decodeWords [0xa8c37bf3#32, 0xd65f03c0#32]

private theorem hbInitCpuFeatures_tail {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {hwcap hwcap2 auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)}
    {R : SepProp} {s0 sf2 : State} {w2 w3 w4 w5 : BitVec 64}
    (hc : hasInstrs P S.initCpuFeaturesAddr (hbInitCpuFeaturesInstrs C S))
    (hCtor : subroutine_ok P S.initCpuFeaturesCtorAddr (hbCpuCtorSpec S))
    (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hsf30 : stackFrameAt s0.sp 0x30 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
      ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)))
    (hpc2 : sf2.pc = S.initCpuFeaturesAddr + 0x2c#64) (hrun2 : sf2.status = .Running)
    (hx19_2 : sf2.readReg64 (.gpr 19#5) = hwcap) (hx0_2 : sf2.readReg64 (.gpr 0#5) = hwcap2)
    (hrel2 : HbInitCpuMidRel s0 sf2) :
    SepWP P (s0.readReg64 .x30) sf2
      ((((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        stackFrameAt (s0.sp - 48#64) 0x20) ∗
       (S.cpuFeaturesGlobalAddr ↦₆₄ 0#64) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ w2) ∗ ((s0.sp - 24#64) ↦₆₄ w3) ∗
       ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5) ∗
       stackFrameAt (s0.sp - 48#64 - 32#64) 0x20)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (hbInitCpuFeaturesSpec C S).post (hwcap, hwcap2, auxvAddr, entries) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rcases hrel2 with ⟨hsp2', b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv, hstd02⟩
  have_instrs hc 11 9; clear hc
  wp_steps 4; hb_wp_steps_p 3
  refine hb_let_sp (sp' := s0.sp - 48#64) (by simp [wp_norm, arm64_norm, hsp2']) fun hsp_bl3 => ?_
  refine hb_let_ctor_args (ptr := s0.sp - 8#64) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) fun hbit62_bl3 hx1_bl3 => ?_
  refine SepWP.call_subroutine_frame_auto hCtor (x := (s0.sp - 8#64, hwcap2, 0#64)) (ret_pc := S.initCpuFeaturesAddr + 0x48#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp2', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 => ?_)
    (by dsimp only [hbCpuCtorSpec]; rw [hsp_bl3, stackFrameAt_split (s0.sp - 48#64) 0x20 0x20]; sep_frame (disch := assumption))
  dsimp only [hbCpuCtorSpec]; (wp_conv_pre => rw [hsp_bl3, sepConj_assoc]); apply SepWP.pure_elim; intro hstd3
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_cpu
  have hsp3' : sf3.sp = s0.sp - 48#64 := hsp3.trans hsp_bl3
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs3 with ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩
  simp only [wp_norm, arm64_norm, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 cv
  refine SepWP.step_ldp64 (ea := s0.sp - 48#64) (ea2 := s0.sp - 40#64) (wb := some (.sp, s0.sp))
    hpc3 hrun3 hf_18
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp3', hsp0])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp3', bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · dsimp only [hbInitCpuFeaturesSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    have hstd23 : StdStatePreserved sf2 sf3 := StdStatePreserved.trans (by simp [*]) hstd3
    refine ⟨(hstd02.trans hstd23).trans (by simp [*]),
      Satisfies.mono (sepConj_mono_left ?_) hm⟩
    rw [stackFrameAt_split s0.sp 0x30 0x40, hsf30]; sep_frame
  · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv]

private theorem hbInitCpuFeatures_ok {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : hasInstrs P S.initCpuFeaturesAddr (hbInitCpuFeaturesInstrs C S))
    (hGetauxval : subroutine_ok P C.std.getauxvalAddr (stdGetauxvalSpec C.std))
    (hCtor : subroutine_ok P S.initCpuFeaturesCtorAddr (hbCpuCtorSpec S)) :
    subroutine_ok P S.initCpuFeaturesAddr (hbInitCpuFeaturesSpec C S) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨hwcap, hwcap2, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbInitCpuFeaturesSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hnonull, hfind16, hfind26⟩, hpre⟩
  refine ⟨(S.cpuFeaturesGlobalAddr ↦₆₄ 0#64) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
    (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x70, hpre, ?_⟩
  have hsf30 : stackFrameAt s0.sp 0x30 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
    ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackFrameAt_split s0.sp 0x30 0x40, stackFrameAt_split (s0.sp - 48#64) 0x20 0x20, hsf30]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  have_instrs hc 0 11; have hsp0 := sp_and_15_of_spAligned hsp
  wp_steps 2
  refine SepWP.step_ldr64 (ea := S.cpuFeaturesGlobalAddr) (wb := none)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_2 rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step; hb_wp_steps_p 3
  refine hb_let_sp (sp' := s0.sp - 48#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) fun hsp_bl1 => ?_
  refine hb_let_x0 (v := 16#64) (by simp [wp_norm, arm64_norm]) fun hx0_bl1 => ?_
  have htag16 : (16#64 : BitVec 64) ≠ 0x17#64 := by decide
  refine SepWP.call_subroutine_frame_auto hGetauxval (x := (16#64, hwcap, auxvAddr, entries)) (ret_pc := S.initCpuFeaturesAddr + 0x20#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    (by dsimp only [stdGetauxvalSpec]; rw [hsp_bl1]; sep_frame (disch := assumption))
  dsimp only [stdGetauxvalSpec]; (wp_conv_pre => rw [hsp_bl1, sepConj_assoc]); apply SepWP.pure_elim; rintro ⟨hx0_1, hstd1⟩
  have hsp1' : sf1.sp = s0.sp - 48#64 := hsp1.trans hsp_bl1
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av⟩
  simp only [wp_norm, arm64_norm] at a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 av
  wp_steps 3
  refine hb_let_sp (sp' := s0.sp - 48#64) (by simp [wp_norm, arm64_norm, hsp1']) fun hsp_bl2 => ?_
  refine hb_let_x0 (v := 26#64) (by simp [wp_norm, arm64_norm]) fun hx0_bl2 => ?_
  have htag26 : (26#64 : BitVec 64) ≠ 0x17#64 := by decide
  refine SepWP.call_subroutine_frame_auto hGetauxval (x := (26#64, hwcap2, auxvAddr, entries)) (ret_pc := S.initCpuFeaturesAddr + 0x2c#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp1', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_)
    (by dsimp only [stdGetauxvalSpec]; rw [hsp_bl2]; sep_frame (disch := assumption))
  dsimp only [stdGetauxvalSpec]; (wp_conv_pre => rw [hsp_bl2, sepConj_assoc]); apply SepWP.pure_elim; rintro ⟨hx0_2, hstd2⟩
  have hsp2' : sf2.sp = s0.sp - 48#64 := hsp2.trans hsp_bl2
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨hx19_2, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv⟩
  simp only [wp_norm, arm64_norm, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av] at hx19_2 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 bv
  have hstd01 : StdStatePreserved s0 sf1 := StdStatePreserved.trans (by simp [*]) hstd1
  have hstd12 : StdStatePreserved sf1 sf2 := StdStatePreserved.trans (by simp [*]) hstd2
  exact hbInitCpuFeatures_tail hc hCtor hsp0 hsf30 hpc2 hrun2 hx19_2 hx0_2
    ⟨hsp2', b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv, hstd01.trans hstd12⟩

private abbrev hbInitGlobalsPre (C : HbCliLayout) (S : HbStartupLayout)
    (auxvAddr : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) : SepProp :=
  let L := C.std
  (S.gotInitArrayStartAddr ↦₆₄ L.initArrayAddr) ∗ (S.gotInitArrayEndAddr ↦₆₄ (L.initArrayAddr + 0x18#64)) ∗
  (L.initArrayAddr ↦₆₄ L.initLseAddr) ∗ ((L.initArrayAddr + 0x08#64) ↦₆₄ L.doInitAddr) ∗
  ((L.initArrayAddr + 0x10#64) ↦₆₄ S.initCpuFeaturesAddr) ∗ (L.initializedAddr ↦₈ 0#8) ∗
  ((L.gotAddr + 0x30#64) ↦₆₄ 0#64) ∗ (L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (S.cpuFeaturesGlobalAddr ↦₆₄ 0#64) ∗
  ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries)

private abbrev hbInitGlobalsPost (C : HbCliLayout) (S : HbStartupLayout)
    (hwcap auxvAddr : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) : SepProp :=
  let L := C.std
  (S.gotInitArrayStartAddr ↦₆₄ L.initArrayAddr) ∗ (S.gotInitArrayEndAddr ↦₆₄ (L.initArrayAddr + 0x18#64)) ∗
  (L.initArrayAddr ↦₆₄ L.initLseAddr) ∗ ((L.initArrayAddr + 0x08#64) ↦₆₄ L.doInitAddr) ∗
  ((L.initArrayAddr + 0x10#64) ↦₆₄ S.initCpuFeaturesAddr) ∗ (L.initializedAddr ↦₈ 1#8) ∗
  ((L.gotAddr + 0x30#64) ↦₆₄ 0#64) ∗ (L.haveLseAtomicsAddr ↦₈ (if hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
  (∃∗ v : BitVec 64, S.cpuFeaturesGlobalAddr ↦₆₄ v) ∗
  ((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries)

private def hbLibcStartInitSpec (C : HbCliLayout) (S : HbStartupLayout) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, hwcap2, auxvAddr, entries) s0 =>
    ⌜(∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧ entries.find? (·.1 == 16#64) = some (16#64, hwcap) ∧
      entries.find? (·.1 == 26#64) = some (26#64, hwcap2) ∧ C.std.initArrayAddr.toNat + 24 < 2 ^ 64⌝ ∗
    (hbInitGlobalsPre C S auxvAddr entries ∗ stackFrameAt s0.sp 0x90)
  post := fun (hwcap, _, auxvAddr, entries) s0 sf =>
    ⌜StdStatePreserved s0 sf⌝ ∗
    (hbInitGlobalsPost C S hwcap auxvAddr entries ∗ stackFrameAt s0.sp 0x90)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

private theorem hbLibcStartInit_ok {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : hasInstrs P C.std.libcStartInitAddr (decodeWords [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32] ++
      [ .adr true .x19 (adrpOff (C.std.libcStartInitAddr + 0x0c#64) S.gotInitArrayStartAddr),
        .adr true .x20 (adrpOff (C.std.libcStartInitAddr + 0x10#64) S.gotInitArrayEndAddr),
        .bl (C.std.initFnAddr - (C.std.libcStartInitAddr + 0x14#64)),
        .ldr .W64 .X64 false .x19 (.Offset .x19 (pageLo12 S.gotInitArrayStartAddr)),
        .ldr .W64 .X64 false .x20 (.Offset .x20 (pageLo12 S.gotInitArrayEndAddr)) ] ++
      decodeWords [0xeb14027f#32, 0x54000082#32, 0xf8408660#32, 0xd63f0000#32,
                   0x17fffffc#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32]))
    (hInitFn : subroutine_ok P C.std.initFnAddr stdInitFnSpec)
    (hInitLse : subroutine_ok P C.std.initLseAddr (hbInitLseSpec C.std))
    (hDoInit : subroutine_ok P C.std.doInitAddr (stdDoInitSpec C.std))
    (hInitCpu : subroutine_ok P S.initCpuFeaturesAddr (hbInitCpuFeaturesSpec C S)) :
    subroutine_ok P C.std.libcStartInitAddr (hbLibcStartInitSpec C S) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨hwcap, hwcap2, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbLibcStartInitSpec, hbInitGlobalsPre, hbInitGlobalsPost] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hnonull, hfind16, hfind26, hbound⟩, hpre⟩
  refine ⟨hbInitGlobalsPre C S auxvAddr entries ∗ stackFrameAt s0.sp 0x90, hpre, ?_⟩; dsimp only [hbInitGlobalsPre]
  have hsf20 : stackFrameAt s0.sp 0x20 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗ ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackFrameAt_split s0.sp 0x20 0x70, stackFrameAt_split (s0.sp - 32#64) 0x10 0x60, stackFrameAt_split (s0.sp - 32#64 - 16#64) 0x20 0x40, show s0.sp - 32#64 - 16#64 - 32#64 = s0.sp - 32#64 - 48#64 by bv_lin, hsf20]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  have_instrs hc 0 16; clear hc; have hsp0 := sp_and_15_of_spAligned hsp
  hb_wp_steps_p 6
  refine hb_let_sp (sp' := s0.sp - 32#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) fun hsp_bl1 => ?_
  refine SepWP.call_subroutine_frame_auto hInitFn (x := ()) (ret_pc := C.std.libcStartInitAddr + 0x18#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_) (by dsimp only [stdInitFnSpec]; rw [hsp_bl1]; sep_frame)
  dsimp only [stdInitFnSpec]; (wp_conv_pre => rw [hsp_bl1, sepConj_assoc]); apply SepWP.pure_elim; intro hstd1
  have hsp1' : sf1.sp = s0.sp - 32#64 := hsp1.trans hsp_bl1
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨hx19_1, hx20_1, a21, a22, a23, a24, a25, a26, a27, a28, _, av⟩
  simp only [wp_norm, arm64_norm] at hx19_1 hx20_1 a21 a22 a23 a24 a25 a26 a27 a28 av
  refine SepWP.step_ldr64 (ea := S.gotInitArrayStartAddr) (wb := none) hpc1 hrun1 hf_6 rfl (by simp [evalAddrMode, hx19_1]) (by wp_sep_access) (by wp_norm_lhs) ?_
  refine SepWP.step_ldr64 (ea := S.gotInitArrayEndAddr) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1]) hf_7 rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx20_1]) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_steps 2; wp_if hbhs1
  · have hbad : BitVec.ule (C.std.initArrayAddr + 24#64) C.std.initArrayAddr = true := by simpa [wp_norm, arm64_norm] using hbhs1
    simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hbad; omega
  · refine SepWP.step_ldr64 (ea := C.std.initArrayAddr) (wb := some (.gpr 19#5, C.std.initArrayAddr + 8#64)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1]) hf_10 rfl (by simp [evalAddrMode, wp_norm, arm64_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
    wp_step; refine hb_let_sp (sp' := s0.sp - 32#64) (by simp [wp_norm, arm64_norm, hsp1']) fun hsp_bl2 => ?_
    refine SepWP.call_subroutine_frame_auto hInitLse (x := (hwcap, auxvAddr, entries)) (ret_pc := C.std.libcStartInitAddr + 0x30#64)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp1', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_)
      (by dsimp only [hbInitLseSpec]; rw [hsp_bl2, stackFrameAt_split (s0.sp - 32#64) 0x10 0x20]; sep_frame (disch := assumption))
    dsimp only [hbInitLseSpec]; (wp_conv_pre => rw [hsp_bl2, sepConj_assoc]); apply SepWP.pure_elim; intro hstd2
    have hsp2' : sf2.sp = s0.sp - 32#64 := hsp2.trans hsp_bl2
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨hx19_2, hx20_2, b21, b22, b23, b24, b25, b26, b27, b28, _, bv⟩
    simp only [wp_norm, arm64_norm, a21, a22, a23, a24, a25, a26, a27, a28, av] at hx19_2 hx20_2 b21 b22 b23 b24 b25 b26 b27 b28 bv
    wp_steps 3; wp_if hbhs2
    · have hbad : BitVec.ule (C.std.initArrayAddr + 24#64) (C.std.initArrayAddr + 8#64) = true := by simpa [wp_norm, arm64_norm, hx19_2, hx20_2] using hbhs2
      simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hbad; omega
    · refine SepWP.step_ldr64 (ea := C.std.initArrayAddr + 8#64) (wb := some (.gpr 19#5, C.std.initArrayAddr + 16#64)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2]) hf_10 rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx19_2, bv_lin_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
      wp_step
      refine SepWP.call_subroutine_frame_auto hDoInit (x := 0#8) (ret_pc := C.std.libcStartInitAddr + 0x30#64)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
        (by simp [State.spAligned, wp_norm, arm64_norm, hsp2', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (fun sf3 hpc3 hrun3 hsp3 hcs3 => ?_) (by dsimp only [stdDoInitSpec]; sep_frame)
      dsimp only [stdDoInitSpec]; (wp_conv_pre => simp only [beq_self_eq_true, ↓reduceIte, sepConj_assoc]); apply SepWP.pure_elim; intro hstd3
      have hstd3' : StdStatePreserved _ sf3 := StdStatePreserved.of_processFields hstd3
      have hsp3' : sf3.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm, hsp2'] using hsp3
      rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs3 with ⟨hx19_3, hx20_3, c21, c22, c23, c24, c25, c26, c27, c28, _, cv⟩
      simp only [wp_norm, arm64_norm, hx20_2, b21, b22, b23, b24, b25, b26, b27, b28, bv] at hx19_3 hx20_3 c21 c22 c23 c24 c25 c26 c27 c28 cv
      wp_steps 3; wp_if hbhs3
      · have hbad : BitVec.ule (C.std.initArrayAddr + 24#64) (C.std.initArrayAddr + 16#64) = true := by simpa [wp_norm, arm64_norm, hx19_3, hx20_3] using hbhs3
        simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hbad; omega
      · refine SepWP.step_ldr64 (ea := C.std.initArrayAddr + 16#64) (wb := some (.gpr 19#5, C.std.initArrayAddr + 24#64)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun3]) hf_10 rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx19_3, bv_lin_norm]) (by wp_sep_access) (by wp_norm_lhs) ?_
        wp_step; refine hb_let_sp (sp' := s0.sp - 32#64) (by simp [wp_norm, arm64_norm, hsp3']) fun hsp_bl4 => ?_
        refine SepWP.call_subroutine_frame_auto hInitCpu (x := (hwcap, hwcap2, auxvAddr, entries)) (ret_pc := C.std.libcStartInitAddr + 0x30#64)
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
          (by simp [State.spAligned, wp_norm, arm64_norm, hsp3', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
          (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
          (fun sf4 hpc4 hrun4 hsp4 hcs4 => ?_)
          (by dsimp only [hbInitCpuFeaturesSpec]; rw [hsp_bl4, stackFrameAt_split (s0.sp - 32#64) 0x30 0x40]; sep_frame (disch := assumption))
        dsimp only [hbInitCpuFeaturesSpec]; (wp_conv_pre => rw [hsp_bl4, sepConj_assoc]); apply SepWP.pure_elim; intro hstd4
        wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_cpu
        have hsp4' : sf4.sp = s0.sp - 32#64 := hsp4.trans hsp_bl4
        rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs4 with ⟨hx19_4, hx20_4, d21, d22, d23, d24, d25, d26, d27, d28, _, dv⟩
        simp only [wp_norm, arm64_norm, hx20_3, c21, c22, c23, c24, c25, c26, c27, c28, cv] at hx19_4 hx20_4 d21 d22 d23 d24 d25 d26 d27 d28 dv
        wp_steps 3
        refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun4]) hf_13
          (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp4', hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp4', bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
        refine SepWP.step_ldp64 (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := some (.sp, s0.sp)) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun4]) hf_14
          (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp4', hsp0]) (by simp [evalAddrMode, wp_norm, arm64_norm, hsp4', bv_lin_norm]) (by bv_lin) (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
        wp_step; apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4]); refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
        · rw [sepConj_assoc, satisfies_pure_sepConj]
          have hstd01 : StdStatePreserved s0 sf1 := StdStatePreserved.trans (by simp [wp_norm, arm64_norm, *]) hstd1
          have hstd12 : StdStatePreserved sf1 sf2 := StdStatePreserved.trans (by simp [wp_norm, arm64_norm, *]) hstd2
          have hstd23 : StdStatePreserved sf2 sf3 := StdStatePreserved.trans (by simp [wp_norm, arm64_norm, *]) hstd3'
          have hstd34 : StdStatePreserved sf3 sf4 := StdStatePreserved.trans (by simp [wp_norm, arm64_norm, *]) hstd4
          refine ⟨(((hstd01.trans hstd12).trans hstd23).trans hstd34).trans (by simp [wp_norm, arm64_norm, *]),
            Satisfies.mono (sepConj_mono_left ?_) hm⟩
          rw [stackFrameAt_split s0.sp 0x20 0x70, hsf20]; sep_frame
        · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, d21, d22, d23, d24, d25, d26, d27, d28, dv]

private theorem hb_sxtw_shl3_add8_eq {argc : Nat} (hargc : argc < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 argc) <<< 3 + 8#64 = BitVec.ofNat 64 (8 * (argc + 1)) := by
  let v := BitVec.ofNat 64 argc
  have hv_lt : v.ult 0x80000000#64 = true := by simp only [v, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  have hv_tr : v.truncate 32 = BitVec.ofNat 32 argc := by apply BitVec.eq_of_toNat_eq; simp [v]
  have hv_se : BitVec.signExtend 64 (v.truncate 32) = v := by revert hv_lt; bv_bits
  rw [← hv_tr, hv_se]; apply BitVec.eq_of_toNat_eq; simp [v, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem hbStage2_to_cMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : hasInstrs P C.std.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs C.std))
    (hLibcStartInit : subroutine_ok P C.std.libcStartInitAddr (hbLibcStartInitSpec C S))
    {target_pc sp0 argvTableAddr hwcap hwcap2 auxvAddr : BitVec 64} {argc : Nat} {entries : List (BitVec 64 × BitVec 64)}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = C.std.libcStartMainStage2Addr) (hrun : s0.status = .Running) (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = C.std.cMainAddr) (hx1 : s0.readReg32 .x1 = BitVec.ofNat 32 argc) (hx2 : s0.readReg64 .x2 = argvTableAddr) (hargc : argc < 2 ^ 31)
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hfind16 : entries.find? (·.1 == 16#64) = some (16#64, hwcap)) (hfind26 : entries.find? (·.1 == 26#64) = some (26#64, hwcap2)) (hbound : C.std.initArrayAddr.toNat + 24 < 2 ^ 64)
    (hnext : ∀ sf : State, sf.pc = C.std.cMainAddr → sf.status = .Running → sf.sp = sp0 - 0x30#64 → sf.spAligned = true →
      sf.readReg64 .x30 = C.std.libcStartMainStage2Addr + 0x38#64 → sf.readReg64 .x0 = BitVec.ofNat 64 argc → sf.readReg64 .x1 = argvTableAddr →
      sf.readReg64 .x2 = argvTableAddr + BitVec.ofNat 64 (8 * (argc + 1)) → StdStatePreserved s0 sf →
      SepWP P target_pc sf ((hbInitGlobalsPost C S hwcap auxvAddr entries ∗ stackFrameAt sp0 0x30 ∗ stackFrameAt (sp0 - 0x30#64) 0x90) ∗ F) post oom) :
    SepWP P target_pc s0 ((hbInitGlobalsPre C S auxvAddr entries ∗ stackFrameAt sp0 0xc0) ∗ F) post oom := by
  subst hsp
  have hsp0 : s0.sp &&& 15#64 = 0#64 := sp_and_15_of_spAligned hsp_align
  have hx0' : s0.readReg64 (.gpr 0#5) = C.std.cMainAddr := hx0
  have hx2' : s0.readReg64 (.gpr 2#5) = argvTableAddr := hx2
  have hx1' : (s0.readReg64 (.gpr 1#5)).truncate 32 = BitVec.ofNat 32 argc := hx1
  have hsf30 : stackFrameAt s0.sp 0x30 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗ ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => dsimp only [hbInitGlobalsPre]; rw [stackFrameAt_split s0.sp 0x30 0x90, hsf30]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  have_instrs hc 0 14; clear hc
  hb_wp_steps_p 10
  refine hb_let_sp (sp' := s0.sp - 48#64) (by simp [wp_norm, arm64_norm, bv_lin_norm]) fun hsp_bl => ?_
  refine SepWP.call_subroutine_frame_auto hLibcStartInit (x := (hwcap, hwcap2, auxvAddr, entries)) (ret_pc := C.std.libcStartMainStage2Addr + 0x28#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    (by dsimp only [hbLibcStartInitSpec, hbInitGlobalsPre]; rw [hsp_bl]; sep_frame (disch := assumption))
  dsimp only [hbLibcStartInitSpec, hbInitGlobalsPost]; (wp_conv_pre => rw [hsp_bl, sepConj_assoc]); apply SepWP.pure_elim; intro hstd1
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_cpu
  have hsp1' : sf1.sp = s0.sp - 48#64 := hsp1.trans hsp_bl
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨g19, g20, g21, g22, _⟩
  simp only [wp_norm, arm64_norm] at g19 g20 g21 g22
  have hstd01 : StdStatePreserved s0 sf1 := StdStatePreserved.trans (by simp [wp_norm, arm64_norm, *]) hstd1
  wp_steps 4
  refine SepWP.weaken_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1'])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp1', hsp0]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by apply BitVec.eq_of_toNat_eq; simp [wp_norm, arm64_norm]; omega)
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, BitVec.add_assoc, hb_sxtw_shl3_add8_eq hargc])
    (hstd01.trans (by simp [wp_norm, arm64_norm, *])))
  dsimp only [hbInitGlobalsPost]; rw [hsf30]; sep_frame

end

def HbStage2GlobalsPre (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  let L := C.std
  (S.gotInitArrayStartAddr ↦₆₄ L.initArrayAddr) ∗ (S.gotInitArrayEndAddr ↦₆₄ (L.initArrayAddr + 0x18#64)) ∗
  (L.initArrayAddr ↦₆₄ L.initLseAddr) ∗ ((L.initArrayAddr + 0x08#64) ↦₆₄ L.doInitAddr) ∗
  ((L.initArrayAddr + 0x10#64) ↦₆₄ S.initCpuFeaturesAddr) ∗ (L.initializedAddr ↦₈ 0#8) ∗
  ((L.gotAddr + 0x30#64) ↦₆₄ 0#64) ∗ (L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (S.cpuFeaturesGlobalAddr ↦₆₄ 0#64)

def HbStage2GlobalsPost (C : HbCliLayout) (S : HbStartupLayout) (hwcap : BitVec 64) : SepProp :=
  let L := C.std
  (S.gotInitArrayStartAddr ↦₆₄ L.initArrayAddr) ∗ (S.gotInitArrayEndAddr ↦₆₄ (L.initArrayAddr + 0x18#64)) ∗
  (L.initArrayAddr ↦₆₄ L.initLseAddr) ∗ ((L.initArrayAddr + 0x08#64) ↦₆₄ L.doInitAddr) ∗
  ((L.initArrayAddr + 0x10#64) ↦₆₄ S.initCpuFeaturesAddr) ∗ (L.initializedAddr ↦₈ 1#8) ∗
  ((L.gotAddr + 0x30#64) ↦₆₄ 0#64) ∗ (L.haveLseAtomicsAddr ↦₈ (if hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
  (∃∗ v : BitVec 64, S.cpuFeaturesGlobalAddr ↦₆₄ v)

private theorem Steps.of_tidOnly_running {prog : Program} {s sf : State}
    (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    (hsteps : Steps (prog.withSvc tidOnlySvc) s sf) (hrun_f : sf.status = .Running) :
    Steps prog s sf ∧ sf.sigAltStack = s.sigAltStack := by
  induction hsteps with
  | refl => exact ⟨.refl _, rfl⟩
  | @step s1 s2 s3 h1 hrest ih =>
    have hr2 : s2.status = .Running := by cases hrest with | refl => exact hrun_f | step h2 _ => cases h2 <;> assumption
    rcases ih hrun_f with ⟨hsteps_rest, hsas_rest⟩
    have hf_eq : (prog.withSvc tidOnlySvc).fetchMem s1.mem s1.pc = prog.fetchMem s1.mem s1.pc := rfl
    cases h1 with
    | @exec inst hr1 hfe =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0; rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hr_svc : (tidOnlySvc s1).status = .Running := by
          rw [evalInst_eq_execInstWithSvc svcKeepsFrozen_tidOnlySvc, execInstWithSvc_svc0] at hr2
          exact hr2
        by_cases hx8 : s1.readReg64 Reg.x8 = 96#64
        · have hs_tid : tidOnlySvc s1 = execSetTidAddress s1 := tidOnlySvc_set_tid_address s1 hx8
          have hs_std : prog.svc s1 = execSetTidAddress s1 := by
            rw [hsvc]; dsimp [Syscall.standard, Syscall.dispatch]; rw [hx8]; rfl
          have hev_eq : (prog.withSvc tidOnlySvc).evalInst (.system false 0#16) s1 =
              prog.evalInst (.system false 0#16) s1 := by
            rw [evalInst_eq_execInstWithSvc svcKeepsFrozen_tidOnlySvc,
                evalInst_eq_execInstWithSvc (hsvc ▸ svcKeepsFrozen_standard),
                execInstWithSvc_svc0, execInstWithSvc_svc0, Program.withSvc_svc, hs_tid, hs_std]
          have hsas1 : ((prog.withSvc tidOnlySvc).evalInst (.system false 0#16) s1).sigAltStack = s1.sigAltStack := by
            rw [evalInst_eq_execInstWithSvc svcKeepsFrozen_tidOnlySvc, execInstWithSvc_svc0, Program.withSvc_svc, hs_tid]
            rfl
          rw [hev_eq] at hsteps_rest hsas_rest hsas1
          exact ⟨.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest, hsas_rest.trans hsas1⟩
        · have hne : (96#64 == s1.readReg64 Reg.x8) = false := beq_eq_false_iff_ne.mpr (Ne.symm hx8)
          dsimp [tidOnlySvc, Syscall.dispatch, List.find?] at hr_svc; rw [hne] at hr_svc
          cases s1; cases hr_svc
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev1 := evalInst_eq_execInst_of_not_isSvc0 (prog.withSvc tidOnlySvc) hnsvc0 s1
        have hev2 := evalInst_eq_execInst_of_not_isSvc0 prog hnsvc0 s1
        rw [hev1] at hsteps_rest hsas_rest
        exact ⟨.step (hev2 ▸ Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest,
          hsas_rest.trans (execInst_sigAltStack_of_not_isSvc0 hnsvc0 s1)⟩
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern _ he _ _ => rw [Program.withSvc_externAt?, hext] at he; cases he
    | extern_fault _ he _ => rw [Program.withSvc_externAt?, hext] at he; cases he

private theorem SepWP.of_tidOnlySvc {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc tidOnlySvc) target s P (fun sf Pf => sf.sigAltStack = s.sigAltStack → post sf Pf)) :
    SepWP prog target s P post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  rcases SepWP.to_reaches_pc h hm ((Program.withSvc_codeLoaded ..).mpr hL) with
    ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hp⟩ | ⟨_, hoom⟩⟩
  · rcases Steps.of_tidOnly_running hext hsvc hsteps hrun with ⟨hstepsP, hsas⟩
    exact ⟨sf, hstepsP, Or.inl ⟨hpc, hrun, Pf, hmf, hp hsas⟩⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

private theorem hbStageCodeChunk_withSvc {P : Program} {svc : State → State} :
    ∀ {c : CodeChunk}, c.holds P → c.holds (P.withSvc svc)
  | .words _ _, h => by cases P; exact h
  | .instrs0 _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi
  | .instrs _ _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi

private theorem hbStageCodeChunks_withSvc {P : Program} {svc : State → State} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → CodeChunks (P.withSvc svc) cs
  | [], _ => trivial
  | [_], h => hbStageCodeChunk_withSvc h
  | _ :: _ :: _, ⟨h, hs⟩ => ⟨hbStageCodeChunk_withSvc h, hbStageCodeChunks_withSvc hs⟩

theorem hbStage12_to_cMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {img : ElfImage} {inputs : ProcessInputs} {s0 : State} {F : SepProp}
    (hS : S.Valid C) (hm : HbMatchesImage C S img = true) (hvalid : inputs.Valid)
    (hinfo : InitialStackInfo img inputs s0) (hc : HbPreMainCode P C S) :
    let sl := StackLayout.of img inputs
    SepWP P C.std.cMainAddr s0
      ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPre C.std ∗ HbStage1Got C S ∗
        HbStage2GlobalsPre C S ∗
        (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbPreTlsSep C.std sl.sp0) ∗ F)
      (sepPost
        (fun sf => sf.sp = sl.sp0 - 0x30#64 ∧ sf.spAligned = true ∧
          sf.readReg64 .x30 = C.std.libcStartMainStage2Addr + 0x38#64 ∧
          sf.readReg64 .x0 = BitVec.ofNat 64 inputs.argv.length ∧
          sf.readReg64 .x1 = sl.argvTableAddr ∧ sf.readReg64 .x2 = sl.envpTableAddr ∧
          sf.tpidrEl0 = C.std.builtinTlsAddr + 0xc8#64 ∧
          sf.sigAltStack = s0.sigAltStack ∧ StdTlsFieldsPreserved s0 sf)
        ((stackAt sl.sp0 48 ∗ memRegion (sl.sp0 - 0x220#64) 0x1f0 ∗
          Stage1GlobalsPost C.std inputs sl ∗ HbStage1Got C S ∗
          HbStage2GlobalsPost C S inputs.init.auxv.hwcap ∗
          (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
          (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
          (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗
          (((C.std.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ 0#32) ∗
          (((C.std.builtinTlsAddr + 0xc8#64) + 0x58#64) ↦₆₄ 0#64) ∗
          (C.std.libcAddr ↦₈ 1#8) ∗ (C.std.phdrAddr ↦ᵣ C.std.phdrBytes) ∗
          (C.std.tlsImageAddr ↦ᵣ hbTdataBytes) ∗ (C.std.defaultStacksizeAddr ↦₃₂ 131072#32) ∗
          HbTlsState C.std ((auxvScan38 sl.auxvEntries).getD 32 0#64)) ∗ F)) := by
  dsimp only; let sl := StackLayout.of img inputs
  refine SepWP.of_tidOnlySvc hc.no_hooks hc.svc_eq ?_
  let P' := P.withSvc tidOnlySvc
  obtain ⟨hc_st2, hc_lsi, hw_initFn, hc_doInit, hw_doInit34, hc_getaux, _, hc_ilse, hc_icpu,
    hw_ctor0, hc_ctorMid, hw_ctor1, hw_ctor2, hw_ctor3⟩ :=
    (by simpa [hbStage2Chunks, CodeChunks, CodeChunk.holds] using hbStageCodeChunks_withSvc hc.stage2 :
      hasInstrs P' C.std.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs C.std) ∧
      hasInstrs P' C.std.libcStartInitAddr (decodeWords [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32] ++
        [ .adr true .x19 (adrpOff (C.std.libcStartInitAddr + 0x0c#64) S.gotInitArrayStartAddr),
          .adr true .x20 (adrpOff (C.std.libcStartInitAddr + 0x10#64) S.gotInitArrayEndAddr),
          .bl (C.std.initFnAddr - (C.std.libcStartInitAddr + 0x14#64)),
          .ldr .W64 .X64 false .x19 (.Offset .x19 (pageLo12 S.gotInitArrayStartAddr)),
          .ldr .W64 .X64 false .x20 (.Offset .x20 (pageLo12 S.gotInitArrayEndAddr)) ] ++
        decodeWords [0xeb14027f#32, 0x54000082#32, 0xf8408660#32, 0xd63f0000#32,
                     0x17fffffc#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32]) ∧
      P'.hasWords C.std.initFnAddr initFnWords ∧
      hasInstrs P' C.std.doInitAddr [ .adr true .x1 (adrpOff C.std.doInitAddr C.std.initializedAddr),
        .ldr .W32 .B8 false .x0 (.Offset .x1 (pageLo12 C.std.initializedAddr)), decodeWord 0x35000160#32,
        .adr true .x0 (adrpOff (C.std.doInitAddr + 0x0c#64) (C.std.gotAddr + 0x30#64)), decodeWord 0x52800022#32,
        .str .B8 .x2 (.Offset .x1 (pageLo12 C.std.initializedAddr)),
        .ldr .W64 .X64 false .x0 (.Offset .x0 (pageLo12 (C.std.gotAddr + 0x30#64))), decodeWord 0xb40000c0#32 ] ∧
      P'.hasWords (C.std.doInitAddr + 0x34#64) [0xd65f03c0#32] ∧
      hasInstrs P' C.std.getauxvalAddr (getauxvalInstrs C.std) ∧
      P'.hasWords C.std.errnoLocationAddr [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32] ∧
      hasInstrs P' C.std.initLseAddr (decodeWords [0xf81f0ffe#32, 0xd2800200#32] ++
        [ .bl (C.std.getauxvalAddr - (C.std.initLseAddr + 0x08#64)), decodeWord 0x53082000#32,
          .adr true .x1 (adrpOff (C.std.initLseAddr + 0x10#64) C.std.haveLseAtomicsAddr), decodeWord 0xf84107fe#32,
          .str .B8 .x0 (.Offset .x1 (pageLo12 C.std.haveLseAtomicsAddr)), decodeWord 0xd65f03c0#32 ]) ∧
      hasInstrs P' S.initCpuFeaturesAddr ([decodeWord 0xd503201f#32,
        .adr false .x0 (S.cpuFeaturesGlobalAddr - (S.initCpuFeaturesAddr + 0x04#64))] ++
        decodeWords [0xf9400000#32, 0xb4000040#32, 0xd65f03c0#32, 0xa9bd7bf3#32, 0xd2800200#32] ++
        [.bl (C.std.getauxvalAddr - (S.initCpuFeaturesAddr + 0x1c#64))] ++
        decodeWords [0xaa0003f3#32, 0xd2800340#32] ++
        [.bl (C.std.getauxvalAddr - (S.initCpuFeaturesAddr + 0x28#64))] ++
        decodeWords [0xaa0003e2#32, 0xd2800303#32, 0xb2420260#32, 0x9100a3e1#32,
                     0xa901cfe3#32, 0xf90017e2#32] ++
        [.bl (S.initCpuFeaturesCtorAddr - (S.initCpuFeaturesAddr + 0x44#64))] ++
        decodeWords [0xa8c37bf3#32, 0xd65f03c0#32]) ∧
      P'.hasWords S.initCpuFeaturesCtorAddr hbCpuCtorWords0 ∧
      hasInstrs P' (S.initCpuFeaturesCtorAddr + 0x8c#64)
        ([.adr true .x3 (adrpOff (S.initCpuFeaturesCtorAddr + 0x8c#64) S.cpuFeaturesGlobalAddr)] ++
         decodeWords [0x9a851021#32, 0xf265001f#32, 0xb27f0025#32] ++
         [.addSubImm .W64 .ADD .x3 .x3 (S.cpuFeaturesGlobalAddr.truncate 12) false]) ∧
      P'.hasWords (S.initCpuFeaturesCtorAddr + 0xa0#64) hbCpuCtorWords1 ∧
      P'.hasWords (S.initCpuFeaturesCtorAddr + 0x14c#64) hbCpuCtorWords2 ∧
      P'.hasWords (S.initCpuFeaturesCtorAddr + 0x1f8#64) hbCpuCtorWords3)
  have hGetaux := getauxval_found_ok P' C.std hc_getaux
  have hLsi := hbLibcStartInit_ok hc_lsi (initFn_ok P' C.std.initFnAddr hw_initFn)
    (hbInitLse_ok hc_ilse hGetaux) (hbDoInit_ok hc_doInit hw_doInit34)
    (hbInitCpuFeatures_ok hc_icpu hGetaux (hbCpuFeaturesCtor_ok hw_ctor0 hc_ctorMid hw_ctor1 hw_ctor2 hw_ctor3))
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo.auxvEntries_eq] at hwf_aux
  have hfind_aux := mkAuxvEntries_find? img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr []
  rw [List.append_nil, ← hinfo.auxvEntries_eq] at hfind_aux
  have hbound : C.std.initArrayAddr.toNat + 24 < 2 ^ 64 := by have := hS.initArray_noWrap; omega
  have hargv_len : sl.argvAddrs.length = inputs.argv.length := hinfo.argvAddrs_length
  have henvp_eq : sl.argvTableAddr + BitVec.ofNat 64 (8 * (inputs.argv.length + 1)) = sl.envpTableAddr := by
    simp only [StackLayout.envpTableAddr, StackLayout.argvTableAddr, StackLayout.argc,
      BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hmr_split : memRegion (sl.sp0 - 0x1c0#64) 0x1c0 =
      memRegion (sl.sp0 - 0x1c0#64) 0x100 ∗ stackFrameAt sl.sp0 0xc0 := by
    have s1 := memRegion_split_le (sl.sp0 - 0x1c0#64) 0x100 0x1c0 (by decide) (by decide)
    rw [show sl.sp0 - 0x1c0#64 + BitVec.ofNat 64 0x100 = sl.sp0 - 0xc0#64 by bv_lin,
        show (0x1c0 - 0x100 : Nat) = 0xc0 from rfl] at s1
    rw [s1, ← stackAt_eq_stackFrameAt sl.sp0 0xc0]
  have hmr_recomb : memRegion (sl.sp0 - 0x220#64) 0x60 ∗ memRegion (sl.sp0 - 0x1c0#64) 0x100 ∗
      stackFrameAt (sl.sp0 - 0x30#64) 0x90 = memRegion (sl.sp0 - 0x220#64) 0x1f0 := by
    rw [← stackAt_eq_stackFrameAt (sl.sp0 - 0x30#64) 0x90]
    dsimp only [stackAt]
    rw [show (sl.sp0 - 0x30#64) - BitVec.ofNat 64 0x90 = sl.sp0 - 0xc0#64 by bv_lin]
    have s1 := memRegion_split_le (sl.sp0 - 0x1c0#64) 0x100 0x190 (by decide) (by decide)
    rw [show sl.sp0 - 0x1c0#64 + BitVec.ofNat 64 0x100 = sl.sp0 - 0xc0#64 by bv_lin,
        show (0x190 - 0x100 : Nat) = 0x90 from rfl] at s1
    have s2 := memRegion_split_le (sl.sp0 - 0x220#64) 0x60 0x1f0 (by decide) (by decide)
    rw [show sl.sp0 - 0x220#64 + BitVec.ofNat 64 0x60 = sl.sp0 - 0x1c0#64 by bv_lin,
        show (0x1f0 - 0x60 : Nat) = 0x190 from rfl] at s2
    rw [← s1, ← s2]
  apply SepWP.cut (mid := C.std.libcStartMainStage2Addr)
  refine SepWP.weaken_pre (P' := ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPre C.std ∗ HbStage1Got C S ∗
    (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
    (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
    (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbPreTlsSep C.std sl.sp0) ∗ (HbStage2GlobalsPre C S ∗ F))) (by sep_frame) ?_
  refine SepWP.mono (hbStage1_to_stage2 hS hm hvalid hinfo (hbStageCodeChunks_withSvc hc.stage1) (hc.memOps.withSvc tidOnlySvc) rfl hc.ne_memset hc.ne_tls hc.ne_stage2) ?_ (fun _ _ _ ho => ho)
  rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hx0_1, hx1_1, hx2_1, htp1, htls1⟩, hent1⟩
  apply SepWP.weaken_pre hent1
  have hsp_al1 : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]; exact hb_spAligned_of_mod16 hinfo.sp0_align16
  refine SepWP.weaken_pre (P' := ((hbInitGlobalsPre C S sl.auxvTableAddr sl.auxvEntries ∗ stackFrameAt sl.sp0 0xc0) ∗ ?F_st2))
    (by rw [hmr_split]; dsimp only [Stage1GlobalsPost, HbStage2GlobalsPre, hbInitGlobalsPre, HbPostTlsSep]; sep_frame) ?_
  refine hbStage2_to_cMain hc_st2 hLsi hpc1 hrun1 hsp1 hsp_al1 hx0_1 hx1_1 hx2_1 hinfo.argc_bounds.2.1
    (fun t v h => (hwf_aux.2.2 t v h).1) hfind_aux.2.2.2.2.2.2.2.2.2.2.1 hfind_aux.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hbound
    fun sf hpcf hrunf hspf hsp_alf hlrf hx0f hx1f hx2f hstdf => ?_
  wp_conv_pre => dsimp only [hbInitGlobalsPost]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_cpu
  apply SepWP.done hpcf hrunf; intro hsas_f
  refine ⟨⟨hspf, hsp_alf, hlrf, hx0f, hx1f, hx2f.trans henvp_eq, hstdf.2.2.1.trans htp1, hsas_f, htls1.trans hstdf.toTlsFields⟩, ?_⟩
  rw [← stackAt_eq_stackFrameAt sl.sp0 0x30]
  refine Entails.trans (Q := (memRegion (sl.sp0 - 0x220#64) 0x60 ∗ memRegion (sl.sp0 - 0x1c0#64) 0x100 ∗ stackFrameAt (sl.sp0 - 0x30#64) 0x90) ∗ _)
    (by sep_frame) ?_
  rw [hmr_recomb]
  dsimp only [Stage1GlobalsPost, HbStage2GlobalsPost]
  sep_frame

end CaseStudies.Hashbrown.Proofs.StdCli
