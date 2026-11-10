/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process.Assumptions

/-!
# Linux `ProcessInputs.Valid` Conformance Tests

Positive and negative regression tests for `ProcessInputs.Valid`, `ProcessInputs.check`, and the
clauses of `ArgsValid`, `AuxvValid`, `StackValid`, `ProcessInit.Valid`, and `FsValid`.
-/

@[expose] public section

namespace Testing.ProcessAssumptions

open Arm64 Arm64.Process

set_option maxRecDepth 600000

/-! ## Positive Witnesses -/

theorem default_inputs_valid : ({} : ProcessInputs).Valid := by
  decide +kernel

theorem default_inputs_check : ({} : ProcessInputs).check = true := by
  decide +kernel

theorem default_init_valid : ({} : ProcessInit).Valid := by
  decide +kernel

theorem default_init_check : ({} : ProcessInit).check = true := by
  decide +kernel

theorem max_stack_size_inputs_valid :
    ({ init := { stackSize := STACK_SIZE_MAX } } : ProcessInputs).Valid := by
  decide +kernel

theorem lse_hwcap_inputs_valid :
    ({ init := { auxv := { hwcap := 0x103#64 } } } : ProcessInputs).Valid := by
  decide +kernel

def populatedInputs : ProcessInputs :=
  { argv := [bytesOfString "prog", bytesOfString "sub/in.bin", bytesOfString "out.bin"]
    envp := [bytesOfString "PATH=/usr/bin:/bin", bytesOfString "LC_ALL=C"]
    execfn := bytesOfString "bin/prog"
    init :=
      { auxv :=
          { uid := 1000#64
            euid := 1000#64
            gid := 1000#64
            egid := 1000#64
            hwcap := 0xff#64
            hwcap2 := 0x1#64
            secure := 0#64
            extra := [(51#64, 0x40020#64), (99#64, 42#64)] } }
    stdin := [0xde#8, 0xad#8, 0xbe#8, 0xef#8]
    dirs := ["sub", "empty_dir/nested"]
    files := [("sub/in.bin", [1#8, 2#8, 3#8]), ("README", bytesOfString "hello\n")] }

theorem populated_inputs_valid : populatedInputs.Valid := by
  decide +kernel

/-! ## Negative Tests: `ArgsValid` (`A1`-`A5`) -/

theorem reject_empty_argv : ¬ ({ argv := [] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_argv_embedded_nul : ¬ ({ argv := [[0x61#8, 0x00#8, 0x62#8]] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_envp_embedded_nul : ¬ ({ envp := [[0x41#8, 0x3d#8, 0x00#8]] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_execfn_embedded_nul : ¬ ({ execfn := [0x61#8, 0x00#8] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_argv_over_max_arg_strlen :
    ¬ ({ argv := [List.replicate MAX_ARG_STRLEN 0x41#8] } : ProcessInputs).Valid := by
  intro h
  have hlen := h.1.strlen (List.replicate MAX_ARG_STRLEN 0x41#8) (by simp)
  rw [List.length_replicate] at hlen
  unfold MAX_ARG_STRLEN Obj.pageSize at hlen
  omega

theorem reject_execfn_at_path_max :
    ¬ ({ execfn := List.replicate PATH_MAX 0x61#8 } : ProcessInputs).Valid := by
  intro h
  have hlen := h.1.execfn_len
  simp [PATH_MAX] at hlen

/-- `A5`: Total `argBytes > argLimit stackSize` (`17 * 130000 > 2 MiB` with each entry `< MAX_ARG_STRLEN`). -/
theorem reject_arg_bytes_over_limit :
    ¬ ({ envp := List.replicate 17 (List.replicate 130000 0x41#8) } : ProcessInputs).Valid := by
  intro h
  have htot := h.1.total
  unfold argBytes argLimit defaultStackSize Obj.pageSize ARG_MAX STK_LIM at htot
  generalize hs : List.replicate 130000 0x41#8 = s at htot
  have hslen : s.length = 130000 := by rw [← hs, List.length_replicate]
  simp only [List.foldl_cons, List.foldl_nil,
    List.length_cons, List.length_nil, List.replicate_succ, List.replicate_zero, hslen] at htot
  omega

/-! ## Negative Tests: `AuxvValid` (`X1`-`X5`) -/

theorem reject_auxv_random15 :
    ¬ ({ init := { auxv := { randomBytes := List.replicate 15 0#8 } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_secure_nonzero :
    ¬ ({ init := { auxv := { secure := 1#64 } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_uid_ne_euid :
    ¬ ({ init := { auxv := { uid := 1000#64, euid := 0#64 } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_gid_ne_egid :
    ¬ ({ init := { auxv := { gid := 1000#64, egid := 0#64 } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_seven_extras :
    ¬ ({ init := { auxv := { extra :=
          [(34#64, 0#64), (35#64, 0#64), (36#64, 0#64), (37#64, 0#64),
           (38#64, 0#64), (51#64, 5120#64), (52#64, 0#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_extra_shadow_secure :
    ¬ ({ init := { auxv := { extra := [(23#64, 1#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_extra_fixed_phdr :
    ¬ ({ init := { auxv := { extra := [(3#64, 0x400040#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_extra_at_null :
    ¬ ({ init := { auxv := { extra := [(0#64, 0#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_extra_duplicate_tags :
    ¬ ({ init := { auxv := { extra := [(34#64, 0#64), (34#64, 1#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

/-- `X3c`: `AT_SYSINFO_EHDR` (`33`) in `auxv.extra` is rejected because no `[vdso]` is mapped. -/
theorem reject_auxv_extra_sysinfo_ehdr :
    ¬ ({ init := { auxv := { extra := [(33#64, 0x7fff0000#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_hwcap_zero :
    ¬ ({ init := { auxv := { hwcap := 0x0#64 } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_hwcap_missing_fp :
    ¬ ({ init := { auxv := { hwcap := 0x2#64 } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_hwcap_missing_asimd :
    ¬ ({ init := { auxv := { hwcap := 0x101#64 } } } : ProcessInputs).Valid := by
  decide +kernel

/-- `X5`: `AT_MINSIGSTKSZ` (`51`) accepts values up to `524288` (`512 KiB`) and rejects larger values. -/
theorem accept_auxv_minsigstksz_values :
    ({ init := { auxv := { extra := [(51#64, 0#64)] } } } : ProcessInputs).Valid ∧
    ({ init := { auxv := { extra := [(51#64, 4720#64)] } } } : ProcessInputs).Valid ∧
    ({ init := { auxv := { extra := [(51#64, 5120#64)] } } } : ProcessInputs).Valid ∧
    ({ init := { auxv := { extra := [(51#64, 524288#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_auxv_minsigstksz_above_512k :
    ¬ ({ init := { auxv := { extra := [(51#64, 524289#64)] } } } : ProcessInputs).Valid := by
  decide +kernel

/-! ## Negative Tests: `StackValid` (`S1`-`S5`) -/

theorem reject_stack_top_unaligned :
    ¬ ({ init := { stackTop := 0x7fffffff0008#64 } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_stack_top_above_task_size :
    ¬ ({ init := { stackTop := 0x1000000001000#64 } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_stack_size_unaligned :
    ¬ ({ init := { stackSize := 0x800008 } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_stack_size_below_8m :
    ¬ ({ init := { stackSize := 32 * Obj.pageSize } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_stack_size_one_page_below_8m :
    ¬ ({ init := { stackSize := STK_LIM - Obj.pageSize } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_stack_size_above_128m :
    ¬ ({ init := { stackSize := STACK_SIZE_MAX + Obj.pageSize } } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_stack_base_below_min :
    ¬ ({ init := { stackTop := 0x1000000#64, stackSize := 0x800000 } } : ProcessInputs).Valid := by
  decide +kernel

/-! ## Negative Tests: `FsValid` (`F1`-`F6`) -/

theorem reject_fs_leading_slash :
    ¬ ({ files := [("/etc/passwd", [])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_dot_segment :
    ¬ ({ files := [("./foo", [])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_dotdot_segment :
    ¬ ({ dirs := ["a/../b"] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_double_slash_segment :
    ¬ ({ files := [("a//b", [])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_empty_path :
    ¬ ({ files := [("", [])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_over_name_max :
    ¬ ({ files := [(String.ofList (List.replicate 256 'a'), [])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_non_byte_char :
    ¬ ({ files := [(String.ofList [Char.ofNat 256], [])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_duplicate_files :
    ¬ ({ files := [("a/x", [1#8]), ("a/x", [2#8])] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_file_dir_equal :
    ¬ ({ files := [("sub", [1#8])], dirs := ["sub"] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_file_prefix_of_dir :
    ¬ ({ files := [("sub", [1#8])], dirs := ["sub/nested"] } : ProcessInputs).Valid := by
  decide +kernel

theorem reject_fs_nested_files :
    ¬ ({ files := [("sub", [1#8]), ("sub/child", [2#8])] } : ProcessInputs).Valid := by
  decide +kernel

end Testing.ProcessAssumptions
