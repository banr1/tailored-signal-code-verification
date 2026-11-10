/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Proofs.EncoderDecoder.Common
public import Arm64.Testing.Proofs.EncoderDecoder.Part1
public import Arm64.Testing.Proofs.EncoderDecoder.Part2
public import Arm64.Testing.Proofs.EncoderDecoder.Part3
public import Arm64.Testing.Proofs.EncoderDecoder.Part4
public import Arm64.Testing.Proofs.EncoderDecoder.Part5

/-!
# Formal Round-Trip Proof for the ARM64 ISA Decoder & Encoder (`Arm64.Testing.Proofs.EncoderDecoder`)

- **Layer / Role**: Core ISA conformance proof suite (`Role::Proof` in `Arm64/Testing/`).
- **Purpose & Key Exports**: Proves formally that the 32-bit AArch64 machine-code decoder
  (`Arm64.decode`) and AST-to-binary encoder (`Arm64.encode`) round-trip across all instruction
  groups (`encode_of_decode : decode bs = some p → encode p = some bs`), covering bitmask
  immediates, data processing, branches, loads/stores, and SIMD/FP/AES operations.
  Splits the per-instruction-class proofs across `Arm64.Testing.Proofs.EncoderDecoder.Common` and
  `Part1`..`Part5`.
- **When to build / read**: Run `timeout 600 lake build --no-ansi Arm64.Testing.Proofs.EncoderDecoder`
  after modifying `Arm64/Trusted/ISA/Syntax.lean`, `Arm64/Trusted/ISA/Decode.lean`, or `Arm64/Testing/Harness/Encode.lean`.
-/

@[expose] public section

namespace Arm64

/-!
## Main Decoder Soundness Theorems (`encode_of_decode`, `encodeInst_of_decode`, `encodeProg_of_decodeProg`)
-/

/-- **Main Theorem (Decoder Soundness)**:
    For every 32-bit instruction word `bs` and AST instruction `p`,
    if the trusted decoder accepts `bs` and returns `some p` (`decode bs = some p`),
    then the encoder `encode p` returns `some bs`. -/
theorem encode_of_decode (bs : BitVec 32) (p : Instr) (h : decode bs = some p) :
    encode p = some bs := by
  dsimp only [decode] at h
  apply ite_some_imp (branch_nop_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_svc_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_brk_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_hint_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_udf_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_dcZva_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_adr_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_addSubImm_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_logicalImm_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_moveWide_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_bitfield_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_extr_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_b_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cbz_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_tbz_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_bCond_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_br_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_logicalReg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_addSubReg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_addSubExt_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_addSubCarry_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_condCompare_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_condSelect_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_dataProc1_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_crc32_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_dataProc2_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_dataProc3_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ldnp_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_loadStorePair_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_prfmImm_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_prfum_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_prfmReg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_lse_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_rcpc_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_loadStoreUImm_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_loadStore24_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ldrLit_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ldrSimdLit_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ldarStlr_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ldxr_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_stxr_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ldxp_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_stxp_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cas_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_casp_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_sysReg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_barrier_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdNp_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdLoadStorePair_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdLoadStoreUImm_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdLoadStore24_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ld1Multi_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_ld1r_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_st1SinglePost_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdLdSt1Single_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_aes_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fmovGprVec_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdImmShift_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdTbl_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdAddpScalar_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdDupScalar_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdInsDup_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdThreeSame_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdTwoRegMisc_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdAcrossLanes_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdPermute_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdExt_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdPmull_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_simdThreeDiff_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cryptoSha2Reg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cryptoSha3Reg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cryptoSha512Reg2_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cryptoSha512Reg3_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cryptoSha3FourReg_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_cryptoXar_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpDataProc1_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpDataProc2_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpCompare_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpImm_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpCondCompare_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpCondSelect_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpDataProc3_sound bs p) _ h; intro _ h
  apply ite_some_imp (branch_fpFixedConv_sound bs p) _ h; intro _ h
  cases h

/-- Corollary for the total encoder `encodeInst`:
    If `decode bs = some p`, then `encodeInst p = bs`. -/
theorem encodeInst_of_decode (bs : BitVec 32) (p : Instr) (h : decode bs = some p) :
    encodeInst p = bs := by
  have henc := encode_of_decode bs p h
  simp [encodeInst, henc]

/-- Corollary for hex-string encoding (`encodeHex`):
    If `decode bs = some p`, then `encodeHex p = some (hex32 bs)`. -/
theorem encodeHex_of_decode (bs : BitVec 32) (p : Instr) (h : decode bs = some p) :
    encodeHex p = some (hex32 bs) := by
  have henc := encode_of_decode bs p h
  simp [encodeHex, henc]

/-- Program-level soundness theorem:
    If `decodeProg bs = some p`, then `encodeProg p = some bs`. -/
theorem encodeProg_of_decodeProg :
    ∀ (bs : List (BitVec 32)) (p : List Instr),
      decodeProg bs = some p → encodeProg p = some bs
  | [], [], _ => rfl
  | [], _ :: _, h => by
    simp [decodeProg, List.mapM_nil] at h
  | w :: ws, p, h => by
    dsimp [decodeProg] at h
    rw [List.mapM_cons] at h
    cases hd : decode w with
    | none => simp [hd] at h
    | some inst =>
      simp [hd] at h
      cases htl : ws.mapM decode with
      | none => simp [htl] at h
      | some insts =>
        simp [htl] at h
        subst h
        dsimp [encodeProg]
        rw [List.mapM_cons]
        have henc := encode_of_decode w inst hd
        have hrest := encodeProg_of_decodeProg ws insts htl
        dsimp [encodeProg] at hrest
        simp [henc, hrest]

end Arm64
