/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.ProgramReflection.Variant

/-!
# Simp-Set Delta-Unfold Linter and Tests

Defines `#assert_simp_set_no_delta_unfold <simp_attr>+ [allow [<decl>,*]]`, which fails if any
declaration in a simp extension's `SimpTheorems.toUnfold` (`declsToUnfold`) set is not on the
explicit allowlist, or if any allowlist entry is unknown or stale. Passing a non-recursive
definition by name to a simp attribute registers it in `toUnfold` without smart unfolding; during
pre-pass `dsimp`, delta-unfolding `toUnfold` entries emits `proof? := none` and can leave unreduced
internal `match` expressions whose reflexivity check stalls kernel `isDefEq`.
-/

@[expose] public section

namespace Testing.SimpSetUnfoldLint

open Lean Meta Elab Command

/-- Format an array of equation lemma names concisely for diagnostics. -/
public meta def formatEqnsList (eqns? : Option (Array Name)) : String :=
  match eqns? with
  | none => "none"
  | some eqns =>
    if eqns.isEmpty then "none"
    else if eqns.size ≤ 4 then
      String.intercalate ", " (eqns.toList.map toString)
    else
      let prefix4 := String.intercalate ", " ((eqns.extract 0 4).toList.map toString)
      s!"{prefix4}, … ({eqns.size} total)"

/-- Inspect each `SimpExtension` in `attrNames` and throw an error if:
    1. any declaration in its `toUnfold` (`declsToUnfold`) set is not in `allowEntries`, or
    2. any entry in `allowEntries` does not exist in the environment or is stale (not present in
       `toUnfold` of any inspected simp extension). -/
public meta def checkSimpSetsNoDeltaUnfold (attrNames : Array Name)
    (allowEntries : Array (String × Option Name)) : TermElabM Unit := do
  let env ← getEnv
  let mut allowSet : NameSet := {}
  for (_, resolved?) in allowEntries do
    if let some nm := resolved? then
      allowSet := allowSet.insert nm
  let mut allToUnfold : NameSet := {}
  let mut badMsgs : Array String := #[]
  for attrName in attrNames do
    let some ext ← getSimpExtension? attrName
      | throwError "unknown simp extension `{attrName}`"
    let thms ← ext.getTheorems
    let decls := thms.toUnfold.toList.toArray.qsort (fun a b => a.toString < b.toString)
    for declName in decls do
      allToUnfold := allToUnfold.insert declName
      if allowSet.contains declName then
        continue
      let hasSunfold := hasSmartUnfoldingDecl env declName ||
        env.contains (Name.mkStr declName "_sunfold")
      let eqns? ← try getEqnsFor? declName catch _ => pure none
      let eqnsStr := formatEqnsList eqns?
      let eq1Name := match eqns? with
        | some eqns =>
          if h : 0 < eqns.size then toString eqns[0] else s!"{declName}.eq_1"
        | none => s!"{declName}.eq_1"
      badMsgs := badMsgs.push
        s!"  [{attrName}] {declName} (smartUnfolding/_sunfold: {hasSunfold}, eqns: {eqnsStr}) — \
           register `{eq1Name}`/`@[simp] theorem` instead, or add to the allowlist with a justification"
  let attrsStr := String.intercalate ", " (attrNames.toList.map toString)
  let mut badAllowMsgs : Array String := #[]
  for (rawLabel, resolved?) in allowEntries do
    match resolved? with
    | none =>
      badAllowMsgs := badAllowMsgs.push
        s!"  {rawLabel} — declaration does not exist in the environment (remove from allowlist)"
    | some nm =>
      if !allToUnfold.contains nm then
        badAllowMsgs := badAllowMsgs.push
          s!"  {nm} — stale allowlist entry (not in `toUnfold` of [{attrsStr}]; remove from allowlist)"
  let mut sections : Array String := #[]
  if !badMsgs.isEmpty then
    let body := String.intercalate "\n" badMsgs.toList
    sections := sections.push
      s!"Found declarations in simp set `toUnfold` (`declsToUnfold`) that are not on the allowlist \
        (delta-unfolding in `dsimp`/`simp` emits `proof? := none` and can leave unreduced `match` terms \
        that hang the kernel; register `Foo.eq_1`/`@[simp] theorem` instead, or add to the allowlist \
        with a justification):\n{body}"
  if !badAllowMsgs.isEmpty then
    let allowBody := String.intercalate "\n" badAllowMsgs.toList
    sections := sections.push
      s!"Found invalid or stale entries in `#assert_simp_set_no_delta_unfold` allowlist:\n{allowBody}"
  if !sections.isEmpty then
    throwError "{String.intercalate "\n\n" sections.toList}"

/-- Entry in the `allow [...]` clause of `#assert_simp_set_no_delta_unfold`: either an identifier
    or a string literal (for deprecated `ProofLib` symbols barred as raw identifiers in diffs by
    `deprecated-prooflib`). -/
syntax simpUnfoldAllowItem := ident <|> str

/-- Assert that the given `register_simp_attr` sets contain no delta-unfold (`toUnfold`)
    declarations other than those explicitly listed in `allow [...]`, and that every allowlisted
    name resolves and is actively present in `toUnfold`. -/
syntax "#assert_simp_set_no_delta_unfold" (ppSpace ident)+ (" allow " "[" simpUnfoldAllowItem,* "]")? : command

elab_rules : command
  | `(#assert_simp_set_no_delta_unfold $attrs:ident* $[allow [$allowItems:simpUnfoldAllowItem,*]]?) => do
    Command.liftTermElabM do
      let env ← getEnv
      let attrNames := attrs.map (·.getId)
      let mut allowEntries : Array (String × Option Name) := #[]
      if let some items := allowItems then
        for item in items.getElems do
          if let some s := item.raw[0].isStrLit? then
            let nm := s.toName
            let resolved? := if env.contains nm then some nm else none
            allowEntries := allowEntries.push (s, resolved?)
          else
            let id : TSyntax `ident := ⟨item.raw[0]⟩
            let rawId := id.getId
            let resolved? ←
              try
                let r ← realizeGlobalConstNoOverload id
                pure (some r)
              catch _ =>
                pure (if env.contains rawId then some rawId else none)
            let label := match resolved? with
              | some r => toString r
              | none => toString rawId
            allowEntries := allowEntries.push (label, resolved?)
      checkSimpSetsNoDeltaUnfold attrNames allowEntries

/-! ## Simp Sets Without Delta-Unfolded Definitions -/

#assert_simp_set_no_delta_unfold
  wp_proj_guard
  callee_saved_split
  wp_unfold
  ctype_simp
  byteslice
  bv_arith_norm
  bv_bits_nat
  addr_norm
  wp_branch
  width_norm
  bv_lin_norm

/-! ## Global Check Across Custom Simp Sets -/

#assert_simp_set_no_delta_unfold
  arm64_norm wp_norm wp_proj_guard
  callee_saved_split wp_unfold ctype_simp byteslice
  bv_arith_norm bv_bits_nat addr_norm wp_branch width_norm bv_lin_norm
  allow [
    -- Named GPR constants (`Arm64/Trusted/ISA/Syntax.lean`): 0-arity `.gpr i#5` abbreviations.
    Arm64.Reg.x0, Arm64.Reg.x1, Arm64.Reg.x2, Arm64.Reg.x3,
    Arm64.Reg.x4, Arm64.Reg.x5, Arm64.Reg.x6, Arm64.Reg.x7,
    Arm64.Reg.x8, Arm64.Reg.x9, Arm64.Reg.x10, Arm64.Reg.x11,
    Arm64.Reg.x12, Arm64.Reg.x13, Arm64.Reg.x14, Arm64.Reg.x15,
    Arm64.Reg.x16, Arm64.Reg.x17, Arm64.Reg.x18, Arm64.Reg.x19,
    Arm64.Reg.x20, Arm64.Reg.x21, Arm64.Reg.x22, Arm64.Reg.x23,
    Arm64.Reg.x24, Arm64.Reg.x25, Arm64.Reg.x26, Arm64.Reg.x27,
    Arm64.Reg.x28, Arm64.Reg.x29, Arm64.Reg.x30,
    Arm64.Reg.fp, Arm64.Reg.lr,

    -- Register index & operand syntax projections (`Arm64/Trusted/ISA/Syntax.lean`):
    -- unfold ground decoded instruction operands to canonical `Reg` / `AddrMode` / `BitVec` values.
    Arm64.Reg.fromSPBits, Arm64.Reg.fromZRBits,
    Arm64.CondCode.ofBits, Arm64.ShiftType.ofBits, Arm64.ExtendType.ofBits,
    Arm64.AddrMode.baseReg,
    Arm64.MemWidth.isAligned,

    -- PState flag pack/unpack & syscall trace wrappers (`Arm64/Trusted/ISA/State.lean`).
    Arm64.PState.zero, Arm64.PState.ofBits4, Arm64.PState.toBits4,
    Arm64.OutputStream.ofFd,
    Arm64.TraceEvent.ofBytes, Arm64.TraceEvent.stdout, Arm64.TraceEvent.stderr,

    -- Callee-saved SIMD helpers & memory width-dispatch wrappers
    -- (`ProofLib/CoreLemmas.lean`, `Arm64/Trusted/ISA/Memory.lean`).
    -- Note: all `Arm64.State.*` wrappers (`State.writeReg`, `State.readReg`, `State.readReg32`,
    -- `State.writeReg32`, `State.spAligned`, `State.readVReg32`, `State.readVReg64`,
    -- `State.writeVReg32`, `State.writeVReg64`) are registered via equation/simp theorems and must
    -- never appear in `toUnfold`.
    Arm64.isCalleeSavedVReg, Arm64.updateCalleeSavedVRegs,
    Arm64.Memory.read128, Arm64.Memory.write128,
    Arm64.Memory.readSized, Arm64.Memory.writeSized,
    Arm64.Memory.readSimdSized, Arm64.Memory.writeSimdSized,

    -- Pure ALU, bitfield, shift, address, and SIMD lane helpers (`Arm64/Trusted/ISA/Eval.lean`,
    -- `ProofLib/Lemmas.lean`): unfolded on ground decoded instruction operands.
    Arm64.shiftVal, Arm64.shift32, Arm64.shift64, Arm64.extendVal,
    Arm64.evalLogical, Arm64.evalBitfield, Arm64.evalAddrMode,
    Arm64.checkRegSPAligned, Arm64.checkAddrSPAligned,
    Arm64.getSimdLane, Arm64.applySimdSatResult,
    ProofLib.applyWriteback, ProofLib.mapLanes, ProofLib.zipLanes,

    -- Single-instruction & per-class evaluators (`Arm64/Trusted/ISA/Eval.lean`,
    -- `ProofLib/Lemmas.lean`, `ProofLib/SepLogic/WP/StateNorm.lean`): unfolded when applied to a
    -- concrete decoded instruction constructor.
    Arm64.Program.evalInst, Arm64.execInst, Arm64.execInstWithSvc,
    Arm64.execAddSubImm, Arm64.execAddSubExt,
    Arm64.execAddSubShift, Arm64.execAddSubCarry,
    Arm64.execLogicalImm, Arm64.execLogicalShift,
    Arm64.execMoveWide, Arm64.execBitfield,
    Arm64.execCondSelect, Arm64.execCondCompare,
    Arm64.execDataProc1, Arm64.execDataProc2, Arm64.execDataProc3,
    Arm64.execLdr, Arm64.execLdrLit, Arm64.execStr, Arm64.execLdp, Arm64.execStp,

    -- Linux syscall evaluators & flag/errno constants (`Arm64/Trusted/Syscalls/`).
    Arm64.SYS_READ, Arm64.SYS_WRITE, Arm64.SYS_READV, Arm64.SYS_WRITEV, Arm64.SYS_EXIT,
    Arm64.SYS_EXIT_GROUP,
    Arm64.SYS_FCNTL, Arm64.SYS_IOCTL, Arm64.SYS_OPENAT, Arm64.SYS_CLOSE,
    Arm64.SYS_LSEEK, Arm64.SYS_PREAD64, Arm64.SYS_FSTAT, Arm64.SYS_PPOLL,
    Arm64.SYS_BRK, Arm64.SYS_MUNMAP, Arm64.SYS_MREMAP, Arm64.SYS_MMAP,
    Arm64.SYS_MPROTECT, Arm64.SYS_MADVISE,
    Arm64.SYS_TKILL, Arm64.SYS_TGKILL, Arm64.SYS_SIGALTSTACK, Arm64.SYS_RT_SIGACTION,
    Arm64.SYS_RT_SIGPROCMASK,
    Arm64.SYS_CLOCK_GETTIME, Arm64.SYS_GETRANDOM,
    Arm64.SYS_SET_TID_ADDRESS, Arm64.SYS_SCHED_GETAFFINITY, Arm64.SYS_GETPID, Arm64.SYS_GETTID,
    Arm64.execMmap, Arm64.execBrk, Arm64.execMunmap, Arm64.execMprotect, Arm64.execMadvise,
    Arm64.MMAP_PROT_NONE, Arm64.MMAP_PROT_RW, Arm64.MMAP_FLAGS_PRIVATE_ANON,
    Arm64.MMAP_FLAGS_PRIVATE_ANON_STACK, Arm64.MMAP_FLAGS_PRIVATE_ANON_FIXED, Arm64.MMAP_MIN_ADDR,
    Arm64.MADV_NORMAL, Arm64.MADV_RANDOM, Arm64.MADV_SEQUENTIAL, Arm64.MADV_WILLNEED,
    Arm64.MADV_DONTNEED, Arm64.MADV_FREE, Arm64.MADV_HUGEPAGE, Arm64.MADV_NOHUGEPAGE,
    Arm64.MADV_DONTDUMP, Arm64.MADV_DODUMP,
    Arm64.GRND_NONBLOCK, Arm64.GRND_RANDOM, Arm64.GRND_INSECURE, Arm64.GRND_KNOWN_MASK,
    Arm64.MAX_RW_COUNT,
    Arm64.EINVAL, Arm64.ENOMEM,

    -- ABI `Spec` combinators & tuple/byte-matching predicates (`ProofLib/Abi/{Aapcs,Rust}.lean`,
    -- `ProofLib/SepLogic/Frame.lean`): non-recursive contract wrappers unfolded at proof entry,
    -- plus structural-recursion `MemMatchesBytes` (has `_sunfold`).
    Arm64.Spec.split, Arm64.Spec.fn1, Arm64.Spec.fn2, Arm64.Spec.fn3,
    Arm64.Spec.withStack, Arm64.Spec.withStack16, Arm64.Spec.withStack32,
    Arm64.Spec.withGuard, Arm64.Spec.withPanicWhen, Arm64.Spec.withPreserves,
    Arm64.Spec.rustSliceFn1, Arm64.Spec.rustPair,
    Arm64.Spec.rustOption8, Arm64.Spec.rustOption64,
    Arm64.Spec.rustNiche64, Arm64.Spec.rustResult64, Arm64.Spec.rustSret,
    ProofLib.MemMatchesBytes,

    -- Standard library list/option helpers in `arm64_norm` (`ProofLib/Lemmas.lean`).
    List.map, Option.isSome
  ]

/-! ## Positive Test: Equation Lemmas -/

section EquationLemmasPass

/-- Non-recursive definition with an internal `match` (`hasSmartUnfolding = false`, `.eq_1` and
    `.eq_2` generated). -/
def sampleWithInternalMatch (flag : Bool) (x : BitVec 64) : BitVec 64 :=
  x + (match flag with | true => 1#64 | false => 2#64)

attribute [local width_norm] sampleWithInternalMatch.eq_1 sampleWithInternalMatch.eq_2

#assert_simp_set_no_delta_unfold width_norm

end EquationLemmasPass

/-! ## Negative Tests -/

section NegativeDeltaUnfoldInWpNorm

def badDeltaUnfoldDef (flag : Bool) (x : BitVec 64) : BitVec 64 :=
  x + (match flag with | true => 1#64 | false => 2#64)

attribute [local wp_norm ↓] badDeltaUnfoldDef

/--
error: Found declarations in simp set `toUnfold` (`declsToUnfold`) that are not on the allowlist (delta-unfolding in `dsimp`/`simp` emits `proof? := none` and can leave unreduced `match` terms that hang the kernel; register `Foo.eq_1`/`@[simp] theorem` instead, or add to the allowlist with a justification):
  [wp_norm] Testing.SimpSetUnfoldLint.badDeltaUnfoldDef (smartUnfolding/_sunfold: false, eqns: Testing.SimpSetUnfoldLint.badDeltaUnfoldDef.eq_1, Testing.SimpSetUnfoldLint.badDeltaUnfoldDef.eq_2) — register `Testing.SimpSetUnfoldLint.badDeltaUnfoldDef.eq_1`/`@[simp] theorem` instead, or add to the allowlist with a justification
-/
#guard_msgs in
#assert_simp_set_no_delta_unfold width_norm wp_norm allow [
  Arm64.Spec.fn1, Arm64.Spec.fn2, Arm64.Spec.fn3,
  Arm64.Spec.rustSliceFn1,
  Arm64.Spec.withGuard, Arm64.Spec.withPanicWhen, Arm64.Spec.withPreserves,
  Arm64.Spec.withStack, Arm64.Spec.withStack16, Arm64.Spec.withStack32,
  Arm64.applySimdSatResult, Arm64.evalAddrMode,
  Arm64.execAddSubCarry, Arm64.execAddSubImm, Arm64.execAddSubExt,
  Arm64.execAddSubShift, Arm64.execBitfield,
  Arm64.execCondCompare, Arm64.execCondSelect,
  Arm64.execDataProc1, Arm64.execDataProc2, Arm64.execDataProc3,
  Arm64.Program.evalInst, Arm64.execInst, Arm64.execInstWithSvc,
  Arm64.execLogicalImm, Arm64.execLogicalShift, Arm64.execMoveWide,
  Arm64.isCalleeSavedVReg, Arm64.updateCalleeSavedVRegs,
  ProofLib.applyWriteback
]

end NegativeDeltaUnfoldInWpNorm

section NegativeDeltaUnfoldInWidthNorm

@[local width_norm]
def badWidthNormDef (x : BitVec 64) : BitVec 64 := x + 1#64

/--
error: Found declarations in simp set `toUnfold` (`declsToUnfold`) that are not on the allowlist (delta-unfolding in `dsimp`/`simp` emits `proof? := none` and can leave unreduced `match` terms that hang the kernel; register `Foo.eq_1`/`@[simp] theorem` instead, or add to the allowlist with a justification):
  [width_norm] Testing.SimpSetUnfoldLint.badWidthNormDef (smartUnfolding/_sunfold: false, eqns: Testing.SimpSetUnfoldLint.badWidthNormDef.eq_1) — register `Testing.SimpSetUnfoldLint.badWidthNormDef.eq_1`/`@[simp] theorem` instead, or add to the allowlist with a justification
-/
#guard_msgs in
#assert_simp_set_no_delta_unfold width_norm

end NegativeDeltaUnfoldInWidthNorm

section NegativeStaleOrUnknownAllowlist

/--
error: Found invalid or stale entries in `#assert_simp_set_no_delta_unfold` allowlist:
  NonExistent.fakeDecl — declaration does not exist in the environment (remove from allowlist)
  Arm64.State.writeReg — stale allowlist entry (not in `toUnfold` of [width_norm]; remove from allowlist)
-/
#guard_msgs in
#assert_simp_set_no_delta_unfold width_norm allow [
  NonExistent.fakeDecl,
  Arm64.State.writeReg
]

end NegativeStaleOrUnknownAllowlist

/-! ## `Memory.KeepsFrozen.refl` Normalization -/

section KeepsFrozenReflNorm

example (m : Arm64.Memory) : m.KeepsFrozen m := by simp
example (m : Arm64.Memory) : m.KeepsFrozen m := by simp only [arm64_norm]
example (m : Arm64.Memory) : m.KeepsFrozen m := by simp only [wp_norm]

end KeepsFrozenReflNorm

end Testing.SimpSetUnfoldLint
