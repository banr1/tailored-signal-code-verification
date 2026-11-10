/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib

/-!
# Tests for `ProofLib.OpcodeExclusion` and `ProofLib.LiteralFetchLint`

Tests `prove_all_instrs` whole-code opcode exclusion, decoder characterisations and unhooked
zero-stub soundness (`CodeLoaded` and `Program.fetchMem_of_allInstrs`), and `linter.literalFetch` /
`#lint_literal_fetches!` diagnostics.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.OpcodeExclusion

open Arm64 ProofLib.ProgramReflection

/-! ## Fixture Programs -/

/-- Four non-privileged instructions (`NOP`, `ADD X0, X0, #1`, `MRS X1, TPIDR_EL0`, `RET`);
    reading `TPIDR_EL0` via `MRS` (`0xd53bd041`) is not an `MSR` write. -/
def safeFixtureCode : Program := {
  base := 0x0#64
  code :=
    -- 0x00: d503201f  nop
    [0x1f#8, 0x20#8, 0x03#8, 0xd5#8,
    -- 0x04: 91000400  add x0, x0, #1
     0x00#8, 0x04#8, 0x00#8, 0x91#8,
    -- 0x08: d53bd041  mrs x1, tpidr_el0
     0x41#8, 0xd0#8, 0x3b#8, 0xd5#8,
    -- 0x0c: d65f03c0  ret
     0xc0#8, 0x03#8, 0x5f#8, 0xd6#8]
}

def safeFixtureCode_tree : WordTree := word_tree_of% safeFixtureCode

theorem safeFixtureCode_code_eq : safeFixtureCode.code = safeFixtureCode_tree.toBytes := by
  rfl_kernel

theorem safeFixtureCode_tree_size : safeFixtureCode_tree.checkSize? = some 4 := by rfl_kernel

theorem safeFixtureCode_noStubBefore : noStubBefore 0x10 safeFixtureCode.stubs = true := by
  rfl_kernel

theorem safeFixtureCode_fetch_at {off : Nat} {inst : Instr}
    (h : safeFixtureCode_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64 := by decide) :
    safeFixtureCode.fetch (BitVec.ofNat 64 off) = some inst := by
  have h' := fetch_of_wordTree 4 safeFixtureCode_code_eq safeFixtureCode_tree_size h hoff
  rwa [show safeFixtureCode.base = 0#64 from rfl, BitVec.zero_add] at h'

theorem safeFixtureCode_fetch_rebase {b : BitVec 64} {X O : String → Option (State → State)}
    {off : Nat} {inst : Instr}
    (h : safeFixtureCode_tree.fetchDecodeAt off = some inst)
    (hhook : (safeFixtureCode.rebase b X O).hookAtOff? off = none)
    (hoff : off < 2 ^ 64 := by decide) :
    (safeFixtureCode.rebase b X O).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_eq_of_hookAtOff? rfl (fun _ => rfl) (fun _ => rfl) hoff hhook).trans
    (safeFixtureCode_fetch_at h hoff)

theorem safeFixtureCode_fetch_rebase_text {b : BitVec 64} {X : String → Option (State → State)}
    {off : Nat} {inst : Instr}
    (h : safeFixtureCode_tree.fetchDecodeAt off = some inst)
    (htext : off < 0x10 := by decide)
    (hoff : off < 2 ^ 64 := by decide) :
    (safeFixtureCode.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  safeFixtureCode_fetch_rebase h
    (hookAtOff?_eq_none_of_noStubBefore safeFixtureCode_noStubBefore (fun _ => rfl) htext) hoff

/-- Program containing `SVC #0` (`0xd4000001`) at offset `0x4`. -/
def svcFixtureCode : Program := {
  base := 0x2000#64
  code :=
    [0x1f#8, 0x20#8, 0x03#8, 0xd5#8,
     0x01#8, 0x00#8, 0x00#8, 0xd4#8]
}

/-- Program containing `MSR TPIDR_EL0, X0` (`0xd51bd040`) at offset `0x0`. -/
def msrTpidrFixtureCode : Program := {
  base := 0x3000#64
  code := [0x40#8, 0xd0#8, 0x1b#8, 0xd5#8]
}

/-! ## Positive `prove_all_instrs` Tests -/

theorem safe_allInstrs_no_svc : safeFixtureCode.allInstrs (!·.isSvc) = true := by
  prove_all_instrs

theorem safe_code_allInstrs_no_svc0 : Code.allInstrs (!·.isSvc0) safeFixtureCode = true := by
  prove_all_instrs

theorem safe_allInstrs_no_brk : safeFixtureCode.allInstrs (!·.isBrk) = true := by
  prove_all_instrs

theorem safe_allInstrs_no_msr : safeFixtureCode.allInstrs (!·.isMsr) = true := by
  prove_all_instrs

theorem safe_allInstrs_no_msr_tpidr_el0 :
    safeFixtureCode.allInstrs (!·.isMsrTpidrEl0) = true := by
  prove_all_instrs

theorem safe_allInstrs_no_msr_fpcr :
    safeFixtureCode.allInstrs (!·.isMsrSysreg 0x5a20#15) = true := by
  prove_all_instrs

theorem safe_fetch_no_svc (addr : BitVec 64) (i : Instr) :
    safeFixtureCode.fetch addr = some i → ¬ i.isSvc := by
  prove_all_instrs

theorem safe_rebase_fetch_no_svc (b : BitVec 64) (X : String → Option (State → State))
    (addr : BitVec 64) (i : Instr) :
    (safeFixtureCode.rebase b X).fetch addr = some i → ¬ i.isSvc := by
  prove_all_instrs

theorem safe_rebase_fetch_no_msr_tpidr_el0 (b : BitVec 64) (X : String → Option (State → State))
    (addr : BitVec 64) (i : Instr) :
    (safeFixtureCode.rebase b X).fetch addr = some i → i.isMsrTpidrEl0 = false := by
  prove_all_instrs

/-- Inline `Program` literal without a pre-declared `<prog>_code_eq` theorem. -/
theorem inline_prog_no_svc :
    ({ base := 0x0#64, code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] } : Program).allInstrs
      (!·.isSvc) = true := by
  prove_all_instrs

/-! ## Negative `#guard_msgs` Tests for `prove_all_instrs` -/

/--
error: (kernel) application type mismatch
-/
#guard_msgs (substring := true) in
example : svcFixtureCode.allInstrs (!·.isSvc) = true := by
  prove_all_instrs

/--
error: (kernel) application type mismatch
-/
#guard_msgs (substring := true) in
example : msrTpidrFixtureCode.allInstrs (!·.isMsrTpidrEl0) = true := by
  prove_all_instrs

/-! ## Decoder Characterisations and Unhooked Zero-Stub Soundness -/

theorem check_decode_svc0_iff :
    ∀ w : BitVec 32, (∃ i, decode w = some i ∧ i.isSvc0 = true) ↔ w = 0xd4000001#32 := by
  intro w
  simpa [isSvc0Word, beq_iff_eq] using @decode_isSvc0_iff w

theorem check_decode_msr_tpidr_iff (w : BitVec 32) :
    (∃ i, decode w = some i ∧ i.isMsrTpidrEl0 = true) ↔
      (w &&& 0xffffffe0#32) == 0xd51bd040#32 :=
  @decode_isMsrTpidrEl0_iff w

def zeroStubProg : Program := {
  base := 0x0#64
  code := [0x00#8, 0x00#8, 0x00#8, 0x00#8]
  stubs := [("ext_fn", 0)]
  externs := fun _ => none
}

def svcStubMemProg : Program := {
  base := 0x0#64
  code := [0x01#8, 0x00#8, 0x00#8, 0xd4#8]
}

/-- Strict `Program.CodeLoaded` rejects unhooked zero-stub programs when memory at the stub offset
    holds a different instruction (`SVC #0`), and `Program.fetchMem_of_allInstrs` lifts whole-code
    exclusion directly from `CodeLoaded` + `ExecOnlyIn` even with `externs := fun _ => none`. -/
theorem strict_codeLoaded_rejects_unhooked_svc_stub :
    let mRx : Memory := svcStubMemProg.loadCode Memory.empty
    ¬ zeroStubProg.CodeLoaded mRx := by
  intro mRx hL
  have hb0 := hL.byte_eq 0 (by decide)
  have hm0 : mRx.read8 (zeroStubProg.base + BitVec.ofNat 64 0) = 0x01#8 :=
    (Program.holdsBytes_loadCode svcStubMemProg Memory.empty (by decide) 0 (by decide)).1
  have h00 : zeroStubProg.code[0] = 0x00#8 := rfl
  rw [hm0, h00] at hb0
  contradiction

theorem unhooked_zero_stub_fetchMem_no_svc (m : Memory)
    (hL : zeroStubProg.CodeLoaded m) (hexec : zeroStubProg.ExecOnlyIn m)
    (pc : BitVec 64) (i : Instr) (hf : zeroStubProg.fetchMem m pc = some i) :
    (!i.isSvc) = true :=
  Program.fetchMem_of_allInstrs (p := (!·.isSvc)) (by prove_all_instrs) hL hexec pc i hf

/-! ## `linter.literalFetch` and `#lint_literal_fetches!` Regression Tests -/

gen_fetches safeFixtureCode safeGen 0x10 [0x0, 0x4, 0x8, 0xc]

@[nolint_literal_fetch]
theorem check_gen_fetches_base_corollary (b : BitVec 64) (X : String → Option (State → State)) :
    (safeFixtureCode.rebase b X).fetch b = some .nop :=
  safeGen_rebase_fetch_base b X

theorem symbolic_fetch_hypothesis_ok (addr : BitVec 64) (inst : Instr)
    (h : safeFixtureCode.fetch addr = some inst) :
    safeFixtureCode.fetch addr = some inst :=
  h

set_option warningAsError false in
/--
warning: declaration `Examples.Testing.ProofLib.OpcodeExclusion.bad_handwritten_fetch_0x0` states a literal ISA AST constructor (`Arm64.Instr.ret`) in a fetch/decode conclusion; generate fetch/decode lemmas with `gen_fetches` or `gen_decodes` (`ProofLib.GenDecodes`) instead of writing literal instruction syntax by hand

Note: This linter can be disabled with `set_option linter.literalFetch false`
-/
#guard_msgs in
theorem bad_handwritten_fetch_0x0 :
    safeFixtureCode.fetch 0x0c#64 = some (.ret .x30) := by
  decide

/--
error: declaration `Examples.Testing.ProofLib.OpcodeExclusion.bad_handwritten_fetch_0x0` states a literal ISA AST constructor (`Arm64.Instr.ret`) in a fetch/decode conclusion; generate fetch/decode lemmas with `gen_fetches` or `gen_decodes` (`ProofLib.GenDecodes`) instead of writing literal instruction syntax by hand
-/
#guard_msgs in
#lint_literal_fetches!

-- `set_option linter.literalFetch false` suppresses the per-declaration linter;
-- `@[nolint_literal_fetch]` suppresses both the linter and `#lint_literal_fetches!`.
set_option linter.literalFetch false in
theorem section_opted_out_fetch_0x0 :
    safeFixtureCode.fetch 0x0c#64 = some (.ret .x30) := by
  decide

@[nolint_literal_fetch]
theorem intentional_reloc_fixture_fetch_0x0 :
    safeFixtureCode.fetch 0x0c#64 = some (.ret .x30) := by
  decide

#guard_msgs in
#lint_literal_fetches! ProofLib

end Examples.Testing.ProofLib.OpcodeExclusion
