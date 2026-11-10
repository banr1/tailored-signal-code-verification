/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.Placed.Bridge
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection

/-!
# Return-Address Disjointness from Hole-2 Keep Regions

**Checked by Lean.**

Ports the concrete `cliElfBytes` disjointness bridges for `LibsignalBinary.Proofs.Placed.ElfLsRetAddr`
(`lsLen`, `LsRetAddr`, `LsRetAddr624`) onto the stock `ld.lld` layout (where block
`623` begins at `0x4686a0` with length `132`):
- `h2lr_lsLen_eq_code_length`: kernel-verified equality `lsLen j = libsignalSessionLib.blocks[j].code.length`
  across all `624` blocks (`rfl_kernel`).
- `lsRetAddr_keep_false` / `h2lr_lsRetAddr_keep_false`: under `[LibsignalPlacement]` with
  `libsignalSessionLib.LinkedAt cliElfBytes lsmpl`, `LsRetAddr lr → hole2_keep lr = false ∧ hole2_keepSub lr = false`
  (`0` byte slack at `j = 622`: `0x4685ec + 180 = 0x4686a0`).
- `h2lr_lsRetAddr624_keepSub_false`: under `[LibsignalPlacement]` with
  `libsignalSessionLib.LinkedAt cliElfBytes lsmpl`, `LsRetAddr624 lr → hole2_keepSub lr = false`
  (covering blocks `0 .. 623`, including `j = 623` at `[0x4686a0, 0x468724)` disjoint from `:text_b`
  `[0x469000, 0x46f000)`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfBlockBases cliElfMultiPlacement cliElf_externs_nodup_of_linkedAt
   cliElf_libsignal_placed cliElf_linkedAt cliElf_linkedAt_unique)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup hole2_keep hole2_keepSub)

section KernelBounds
set_option maxRecDepth 400000

/-- Boolean kernel check on the stock `ld.lld` layout verifying across all 624 blocks that
`lsLen j` equals block `j`'s code length and blocks `0..622` end at or below `0x4686a0` (tight at `j = 622`, `0x4685ec + 180 = 0x4686a0`). -/
noncomputable def h2lr_checkLsRetAddrDisjointHole2B : Bool :=
  Nat.beq libsignalSessionLib.blocks.length 624 &&
  Nat.beq cliElfBlockBases.length 624 &&
  (List.range 624).all (fun j =>
    Nat.beq (lsLen j) (libsignalSessionLib.blocks.getD j { code := [] }).code.length) &&
  (List.range 623).all (fun j =>
    Nat.ble ((cliElfBlockBases.getD j 0#64).toNat + lsLen j) 0x4686a0) &&
  Nat.beq (cliElfBlockBases.getD 622 0#64).toNat 0x4685ec &&
  Nat.beq ((cliElfBlockBases.getD 622 0#64).toNat + lsLen 622) 0x4686a0 &&
  Nat.beq (cliElfBlockBases.getD 623 0#64).toNat 0x4686a0

theorem h2lr_checkLsRetAddrDisjointHole2_ok : h2lr_checkLsRetAddrDisjointHole2B = true := by
  rfl_kernel

end KernelBounds

theorem h2lr_blocks_length_eq_624 : libsignalSessionLib.blocks.length = 624 := by
  have hok := h2lr_checkLsRetAddrDisjointHole2_ok
  unfold h2lr_checkLsRetAddrDisjointHole2B at hok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  exact hok.1.1.1.1.1.1

/-- `lsLen j` equals `libsignalSessionLib.blocks[j].code.length` for all `j < 624`. -/
theorem h2lr_lsLen_eq_code_length (j : Nat) (hj : j < libsignalSessionLib.blocks.length) :
    lsLen j = libsignalSessionLib.blocks[j].code.length := by
  have hj624 : j < 624 := h2lr_blocks_length_eq_624 ▸ hj
  have hok := h2lr_checkLsRetAddrDisjointHole2_ok
  unfold h2lr_checkLsRetAddrDisjointHole2B at hok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  have hall := List.all_eq_true.mp hok.1.1.1.1.2 j (List.mem_range.mpr hj624)
  rw [Nat.beq_eq] at hall
  simpa [List.getD, List.getElem?_eq_getElem hj] using hall

private theorem h2lr_cliElfMultiPlacement_base_eq (j : Nat) :
    cliElfMultiPlacement.base j = cliElfBlockBases.getD j 0#64 :=
  rfl

theorem h2lr_cliElf_base_add_lsLen_le_blk623 {j : Nat} (hj : j < 623) :
    (cliElfMultiPlacement.base j).toNat + lsLen j ≤ 0x4686a0 := by
  have hok := h2lr_checkLsRetAddrDisjointHole2_ok
  unfold h2lr_checkLsRetAddrDisjointHole2B at hok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  have hall := List.all_eq_true.mp hok.1.1.1.2 j (List.mem_range.mpr hj)
  rw [Nat.ble_eq] at hall
  rwa [h2lr_cliElfMultiPlacement_base_eq]

theorem h2lr_cliElf_base_add_lsLen_le_488498 {j : Nat} (hj : j < 623) :
    (cliElfMultiPlacement.base j).toNat + lsLen j ≤ 0x488498 := by
  have h := h2lr_cliElf_base_add_lsLen_le_blk623 hj
  omega

private theorem h2lr_toNat_add_ofNat_of_lt64 {b : BitVec 64} {o : Nat}
    (h : b.toNat + o < 18446744073709551616) :
    (b + BitVec.ofNat 64 o).toNat = b.toNat + o := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have ho : (BitVec.ofNat 64 o).toNat = o := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, ho, Nat.mod_eq_of_lt (hpow ▸ h)]

/-- Under `LinkedAt cliElfBytes lsmpl`, any `LsRetAddr lr` lies outside both `hole2_keep` and `hole2_keepSub`. -/
theorem lsRetAddr_keep_false [LibsignalPlacement]
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr lr) :
    hole2_keep lr = false ∧ hole2_keepSub lr = false := by
  rcases hlr with ⟨j, hj, o, ho, rfl⟩
  have hj624 : j < libsignalSessionLib.blocks.length := by
    rw [h2lr_blocks_length_eq_624]; omega
  have hbase_eq : lsmpl.base j = cliElfMultiPlacement.base j :=
    (cliElf_linkedAt_unique hlink).1 j hj624
  have hbnd : (cliElfMultiPlacement.base j).toNat + lsLen j ≤ 0x4686a0 :=
    h2lr_cliElf_base_add_lsLen_le_blk623 hj
  rw [hbase_eq]
  have hlt : (cliElfMultiPlacement.base j + BitVec.ofNat 64 o).toNat < 0x4686a0 := by
    rw [h2lr_toNat_add_ofNat_of_lt64 (by omega)]
    omega
  constructor
  · unfold hole2_keep
    rw [decide_eq_false_iff_not]
    omega
  · unfold hole2_keepSub
    rw [decide_eq_false_iff_not]
    omega

theorem h2lr_lsRetAddr_keep_false [LibsignalPlacement]
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr lr) :
    hole2_keep lr = false ∧ hole2_keepSub lr = false :=
  lsRetAddr_keep_false hlink hlr

theorem h2lr_lsRetAddr_keep_false_seam
    (mpl : MultiPlacement) (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {lr : BitVec 64}
    (hlr : @LsRetAddr (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) lr) :
    hole2_keep lr = false ∧ hole2_keepSub lr = false :=
  @lsRetAddr_keep_false
    (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
    hLs lr hlr

/-- Under `LinkedAt cliElfBytes lsmpl`, any `LsRetAddr624 lr` lies outside `hole2_keepSub`. -/
theorem h2lr_lsRetAddr624_keepSub_false [LibsignalPlacement]
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    hole2_keepSub lr = false := by
  rcases hlr with ⟨j, hj, o, ho, rfl⟩
  by_cases hj623 : j < 623
  · exact (lsRetAddr_keep_false hlink ⟨j, hj623, o, ho, rfl⟩).2
  · have hj_eq : j = 623 := by omega
    subst hj_eq
    have hjlen : (623 : Nat) < libsignalSessionLib.blocks.length := by
      rw [h2lr_blocks_length_eq_624]; decide
    have hbase_eq : lsmpl.base 623 = cliElfMultiPlacement.base 623 :=
      (cliElf_linkedAt_unique hlink).1 623 hjlen
    have hdef : cliElfMultiPlacement.base 623 = cliElfBlockBases.getD 623 0#64 :=
      h2lr_cliElfMultiPlacement_base_eq 623
    have hok := h2lr_checkLsRetAddrDisjointHole2_ok
    unfold h2lr_checkLsRetAddrDisjointHole2B at hok
    simp only [Bool.and_eq_true, Nat.beq_eq] at hok
    have hb623 : (cliElfBlockBases.getD 623 0#64).toNat = 0x4686a0 := hok.2
    have hlen623 : lsLen 623 = 132 := rfl
    rw [hlen623] at ho
    rw [hbase_eq, hdef]
    have hadd : (cliElfBlockBases.getD 623 0#64 + BitVec.ofNat 64 o).toNat = 0x4686a0 + o := by
      rw [h2lr_toNat_add_ofNat_of_lt64 (by omega), hb623]
    unfold hole2_keepSub
    rw [hadd, decide_eq_false_iff_not]
    omega

theorem lsRetAddr624_keepSub_false [LibsignalPlacement]
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    hole2_keepSub lr = false :=
  h2lr_lsRetAddr624_keepSub_false hlink hlr

theorem h2lr_lsRetAddr624_keepSub_false_seam
    (mpl : MultiPlacement) (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {lr : BitVec 64}
    (hlr : @LsRetAddr624 (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) lr) :
    hole2_keepSub lr = false :=
  @h2lr_lsRetAddr624_keepSub_false
    (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
    hLs lr hlr

/-- `LibsignalPlacement` instance at the canonical `cliElfMultiPlacement`. -/
@[instance_reducible]
noncomputable def h2lr_f3CliLibsignalPlacement : LibsignalPlacement :=
  (LibsignalFullPlacement.ofPlaceable cliElfMultiPlacement
    cliElf_libsignal_placed.1
    (cliElf_externs_nodup_of_linkedAt cliElf_linkedAt)).toLibsignalPlacement

theorem h2lr_lsRetAddr_keep_false_f3LsMpl {lr : BitVec 64}
    (hlr : @LsRetAddr h2lr_f3CliLibsignalPlacement lr) :
    hole2_keep lr = false ∧ hole2_keepSub lr = false :=
  @lsRetAddr_keep_false h2lr_f3CliLibsignalPlacement cliElf_linkedAt lr hlr

theorem h2lr_lsRetAddr624_keepSub_false_f3LsMpl {lr : BitVec 64}
    (hlr : @LsRetAddr624 h2lr_f3CliLibsignalPlacement lr) :
    hole2_keepSub lr = false :=
  @h2lr_lsRetAddr624_keepSub_false h2lr_f3CliLibsignalPlacement cliElf_linkedAt lr hlr

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
