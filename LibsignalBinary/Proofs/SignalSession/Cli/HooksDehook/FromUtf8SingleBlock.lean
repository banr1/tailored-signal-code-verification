/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8
public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8RO
public import ProofLib.Placed.Multi
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection

/-!
# Single-Block Placement-Generic Proofs & Trap-Safety for `core::str::converts::from_utf8` (`HooksDehook.FromUtf8SingleBlock`)

Establishes single-block (`156` words = `624` B) identity with engine `coreMultiLib` block `1`
(musl sysroot `core`; identity with the stock CLI bytes and table is R1-a2), trap-safety /
opcode-exclusion, and `pureWordsProg` `subroutine_ok` for `core::str::converts::from_utf8`
(`fuLib1` / `fuTree1`) without requiring `coreMultiLib.blocks[0]` (`core::fmt::write`, which stays
hooked on the stock ELF) or `coreMultiLib.blocks[2]` (`memrchr`) in `s0.mem`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock

open Arm64 Arm64.Obj Arm64.Process ProofLib
open ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open VerifiedLibraries.RustStd (coreMultiLib coreUtf8CharWidthSym coreFromUtf8Sym
  fuTree1 fu1_code_eq fu1_tree_size isUtf8ContByte signExtend32_and_ff64
  utf8CharWidth_zeroExtend32_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)

/-! ## 1. `fromUtf8Block` Patched Word List, `pureWordsProg` Byte Equality, & Concrete `hasWords` -/

/-- The single `624`-byte (`156`-word) relocatable `CodeBlock` of `core::str::converts::from_utf8`
    (`coreMultiLib` block `1`). -/
abbrev fromUtf8Block : CodeBlock := (coreMultiLib.blockLib 1).text

/-- Canonical single-block `Placement` of `fromUtf8Block` at code address `entry` with the
    `256`-byte `UTF8_CHAR_WIDTH` `.rodata` table (`coreUtf8CharWidthSym`) at `tbl` and optional
    linker `ADRP+ADD → NOP+ADR` relaxation predicate `relax1`. -/
@[expose] def fromUtf8Placement (entry tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) : Placement where
  base := entry
  ρ := fun sym => if sym == coreUtf8CharWidthSym then tbl else entry + BitVec.ofNat 64 4096
  relax := relax1

/-- The `156` relocated `32`-bit instruction words of `core::str::converts::from_utf8` under any
    single-block placement `pl : Placement`. -/
@[expose] def fromUtf8PatchedWords (pl : Placement) : List (BitVec 32) :=
  (List.range 156).map fun j => fromUtf8Block.patchedWord pl (4 * j)

/-- Convenience specialization of `fromUtf8PatchedWords` to `(entry, tbl, relax1)`. -/
abbrev fromUtf8WordsAt (entry tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) : List (BitVec 32) :=
  fromUtf8PatchedWords (fromUtf8Placement entry tbl relax1)

theorem fromUtf8Block_code_length : fromUtf8Block.code.length = 624 := by
  decide +kernel

theorem fromUtf8PatchedWords_length (pl : Placement) :
    (fromUtf8PatchedWords pl).length = 156 := by
  simp [fromUtf8PatchedWords]

theorem fromUtf8PatchedWords_ne_nil (pl : Placement) :
    fromUtf8PatchedWords pl ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp [fromUtf8PatchedWords_length] at hlen

/-- `(pureWordsProg pl.base (fromUtf8PatchedWords pl)).code` is byte-identical to
    `fromUtf8Block.patched pl`. -/
theorem pureWordsProg_fromUtf8_code_eq (pl : Placement) :
    (pureWordsProg pl.base (fromUtf8PatchedWords pl)).code = fromUtf8Block.patched pl := by
  change (fromUtf8PatchedWords pl).flatMap Program.wordToBytesLE = fromUtf8Block.patched pl
  unfold fromUtf8PatchedWords CodeBlock.patched
  have hdiv : fromUtf8Block.code.length / 4 = 156 := by
    rw [fromUtf8Block_code_length]
  rw [hdiv, List.flatMap_map]
  rfl

/-- Concrete `hasWords` witness: `pureWordsProg pl.base (fromUtf8PatchedWords pl)` contains the
    `156` relocated words `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem pureWordsProg_fromUtf8_hasWords (pl : Placement) :
    (pureWordsProg pl.base (fromUtf8PatchedWords pl)).hasWords pl.base (fromUtf8PatchedWords pl) := by
  unfold Program.hasWords Program.hasWordsOff
  have hsub : (pl.base - (pureWordsProg pl.base (fromUtf8PatchedWords pl)).base).toNat = 0 := by
    change (pl.base - pl.base).toNat = 0
    simp
  rw [hsub]
  have hlen : (fromUtf8PatchedWords pl).length = 156 := fromUtf8PatchedWords_length pl
  refine ⟨by omega, fun i hi => ?_, rfl, rfl⟩
  rw [Nat.zero_add, Program.readWordOff_eq_some_iff _ _ _ (by omega)]
  have h (r : Nat) (hr : r < 4) :=
    Program.getElem?_flatMap_wordToBytesLE (fromUtf8PatchedWords pl) i r hi hr
  refine ⟨?_, h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at h0
  exact h0

/-! ## 2. Placement-Independent Opcode Exclusion & S2 Trap-Safety Checks (`decide +kernel`) -/

/-- Word pattern matching any `SVC #imm16` (`11010100_000_imm16_00001`). -/
@[expose] def svcAnyPat : WordPat := { mask := 0xffe0001f#32, value := 0xd4000001#32 }

/-- Word pattern matching `BR Xn` (`1101011_0000_11111_000000_rn_00000`). -/
@[expose] def brPat : WordPat := { mask := 0xfffffc1f#32, value := 0xd61f0000#32 }

/-- Word pattern matching `BLR Xn` (`1101011_0001_11111_000000_rn_00000`). -/
@[expose] def blrPat : WordPat := { mask := 0xfffffc1f#32, value := 0xd63f0000#32 }

/-- Word pattern matching `BL #imm26` (`100101_imm26`). -/
@[expose] def blPat : WordPat := { mask := 0xfc000000#32, value := 0x94000000#32 }

theorem svcAnyPat_matches (w : BitVec 32) : svcAnyPat.matches w = isSvcWord w := rfl

theorem fromUtf8Block_patchSafe_svc0 : fromUtf8Block.patchSafe svc0Pat = true := by
  decide +kernel

theorem fromUtf8Block_patchSafe_svcAny : fromUtf8Block.patchSafe svcAnyPat = true := by
  decide +kernel

theorem fromUtf8Block_patchSafe_msrTpidrEl0 : fromUtf8Block.patchSafe msrTpidrEl0Pat = true := by
  decide +kernel

theorem fromUtf8Block_patchSafe_br : fromUtf8Block.patchSafe brPat = true := by
  decide +kernel

theorem fromUtf8Block_patchSafe_blr : fromUtf8Block.patchSafe blrPat = true := by
  decide +kernel

theorem fromUtf8Block_patchSafe_bl : fromUtf8Block.patchSafe blPat = true := by
  decide +kernel

/-- Across every placement `pl`, none of the `156` patched words of `from_utf8` matches `SVC #imm16`,
    `MSR TPIDR_EL0`, `BR Xn`, `BLR Xn`, or `BL #imm26` (S2 `lr`-trap safety input). -/
theorem fromUtf8PatchedWords_no_svc_msr_br_blr_bl (pl : Placement) :
    ∀ w ∈ fromUtf8PatchedWords pl,
      svcAnyPat.matches w = false ∧
      msrTpidrEl0Pat.matches w = false ∧
      brPat.matches w = false ∧
      blrPat.matches w = false ∧
      blPat.matches w = false := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨j, hj, rfl⟩
  rw [List.mem_range] at hj
  have hj' : 4 * j + 4 ≤ fromUtf8Block.code.length := by
    rw [fromUtf8Block_code_length]; omega
  exact ⟨CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_svcAny pl hj',
    CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_msrTpidrEl0 pl hj',
    CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_br pl hj',
    CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_blr pl hj',
    CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_bl pl hj'⟩

/-- For every placement `pl`, `pureWordsProg pl.base (fromUtf8PatchedWords pl)` contains no `SVC`
    instruction and no `MSR TPIDR_EL0` instruction (`allInstrs` witness for
    `subroutine_ok_lift_pureWords_process`). -/
theorem pureWordsProg_fromUtf8_noSvcMsr (pl : Placement) :
    (pureWordsProg pl.base (fromUtf8PatchedWords pl)).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true := by
  have hcode : (pureWordsProg pl.base (fromUtf8PatchedWords pl)).code = fromUtf8Block.patched pl :=
    pureWordsProg_fromUtf8_code_eq pl
  have hall_words :
      Program.allWords (fun w => !(svcAnyPat.matches w || msrTpidrEl0Pat.matches w))
        (pureWordsProg pl.base (fromUtf8PatchedWords pl)) = true := by
    unfold Program.allWords
    rw [hcode]
    unfold CodeBlock.patched
    rw [bytesAllWords_flatMap_bytesOfWordLE
      (fun w => !(svcAnyPat.matches w || msrTpidrEl0Pat.matches w))
      (fun j => fromUtf8Block.patchedWord pl (4 * j))]
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    have hj' : 4 * j + 4 ≤ fromUtf8Block.code.length := by
      rw [fromUtf8Block_code_length] at hj ⊢; omega
    have hs := CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_svcAny pl hj'
    have hm := CodeBlock.patchedWord_not_matches fromUtf8Block_patchSafe_msrTpidrEl0 pl hj'
    simp [Function.comp, hs, hm]
  have himp :
      ∀ w (i : Instr), decode w = some i →
        (svcAnyPat.matches w || msrTpidrEl0Pat.matches w) = false →
        (i.isSvc || i.isMsrTpidrEl0) = false := by
    intro w i hd hfm
    rw [Bool.or_eq_false_iff] at hfm ⊢
    have hs : isSvcWord w = false := by rw [← svcAnyPat_matches]; exact hfm.1
    have hm : isMsrTpidrEl0Word w = false := by rw [← msrTpidrEl0Pat_matches]; exact hfm.2
    exact ⟨decode_not_isSvc hd hs, decode_not_isMsrTpidrEl0 hd hm⟩
  have hres := Program.allInstrs_of_allWords
    (pw := fun w => svcAnyPat.matches w || msrTpidrEl0Pat.matches w)
    (p := fun i => i.isSvc || i.isMsrTpidrEl0) himp hall_words
  have hfn : (fun i : Instr => !(i.isSvc || i.isMsrTpidrEl0)) =
      (fun i : Instr => !i.isSvc && !i.isMsrTpidrEl0) := by
    funext i; cases i.isSvc <;> cases i.isMsrTpidrEl0 <;> rfl
  rwa [hfn] at hres

/-! ## 3. Single-Block `PlacedLib` Fetch Generation (`0x0 → 0x26c`, Zero Other Blocks) -/

/-- Single-block `PlacedLib` wrapping `fromUtf8Block` (`coreMultiLib` block `1`) with `data = []`
    so `fuSingleLib.Placeable pl` depends ONLY on `fromUtf8Block.Placeable pl`. -/
@[expose] def fuSingleLib : PlacedLib :=
  { name := coreMultiLib.name
    text := fromUtf8Block
    data := []
    exports := [coreFromUtf8Sym] }

theorem fuSingleLib_placeable_of_block {pl : Placement}
    (hblk : fromUtf8Block.Placeable pl) : fuSingleLib.Placeable pl :=
  { text := hblk
    data_nodup := by decide
    data_ok := fun _ hd => nomatch hd
    data_relocs_ok := fun _ hd _ _ => nomatch hd }

class SingleFromUtf8Pl where
  pl : Placement
  placeable : fromUtf8Block.Placeable pl

abbrev sfuPl [SingleFromUtf8Pl] : Placement := SingleFromUtf8Pl.pl

theorem sfuPlaceable [SingleFromUtf8Pl] : fuSingleLib.Placeable sfuPl :=
  fuSingleLib_placeable_of_block SingleFromUtf8Pl.placeable

@[expose] def sfuPC [SingleFromUtf8Pl] : Program := fuSingleLib.program sfuPl

theorem sfu_code_eq : fuSingleLib.text.code = fuTree1.toBytes := fu1_code_eq

section
set_option linter.literalFetch false
gen_placed_fetches sfuPC fuSingleLib fuTree1 sfu_code_eq fu1_tree_size
  via_placement sfuPl sfuPlaceable [0x0 → 0x26c]
end

/-- Transfer `subroutine_ok` from `sfuPC.rebase sfuPl.base (fun _ => none)` directly to
    `pureWordsProg sfuPl.base (fromUtf8PatchedWords sfuPl)` (identical `.base`, `.code`,
    `.externAt? = none`, and `.svc = Syscall.standard`). -/
theorem subroutine_ok_pureWords_of_sfuRebase [SingleFromUtf8Pl] {α : Type}
    {spec : Spec α}
    (hsub : subroutine_ok (sfuPC.rebase sfuPl.base (fun _ => none)) sfuPl.base spec) :
    subroutine_ok (pureWordsProg sfuPl.base (fromUtf8PatchedWords sfuPl)) sfuPl.base spec := by
  have hcode : (sfuPC.rebase sfuPl.base (fun _ => none)).code =
      (pureWordsProg sfuPl.base (fromUtf8PatchedWords sfuPl)).code :=
    (pureWordsProg_fromUtf8_code_eq sfuPl).symm
  have hext1 : ∀ pc, (sfuPC.rebase sfuPl.base (fun _ => none)).externAt? pc = none :=
    fun pc => PlacedLib.externAt?_program_rebase_none fuSingleLib sfuPl sfuPl.base pc
  have hext2 : ∀ pc, (pureWordsProg sfuPl.base (fromUtf8PatchedWords sfuPl)).externAt? pc = none :=
    pureWordsProg_externAt_none sfuPl.base (fromUtf8PatchedWords sfuPl)
  exact subroutine_ok_of_codeLoaded_imp hsub hext1 hext2 rfl
    (fun _ hL => hL.of_base_code rfl hcode)

/-! ## 4. Shared Condition-Code, UTF-8 Byte-Range, & Length-Bound Helpers -/

theorem fu_cmn41_le (b : BitVec 8) :
    ConditionHolds .LE (addsPState32 (b.signExtend 32) 0x41#32) = isUtf8ContByte b := by
  unfold addsPState32; revert b; decide

theorem fu_cmn41_gt (b : BitVec 8) :
    ConditionHolds .GT (addsPState32 (b.signExtend 32) 0x41#32) = !isUtf8ContByte b := by
  unfold addsPState32; revert b; decide

theorem fu_cmn40_lt (b : BitVec 8) :
    ConditionHolds .LT (addsPState32 (b.signExtend 32) 0x40#32) = isUtf8ContByte b := by
  unfold addsPState32; revert b; decide

theorem fu_cmn40_ge (b : BitVec 8) :
    ConditionHolds .GE (addsPState32 (b.signExtend 32) 0x40#32) = !isUtf8ContByte b := by
  unfold addsPState32; revert b; decide

theorem fu_cmn61_le (b1 : BitVec 8) :
    ConditionHolds .LE (addsPState32 (b1.signExtend 32) 0x61#32) = (0x80#8 ≤ b1 && b1 ≤ 0x9f#8) := by
  unfold addsPState32; revert b1; decide

theorem fu_cmn71_le (b1 : BitVec 8) :
    ConditionHolds .LE (addsPState32 (b1.signExtend 32) 0x71#32) = (0x80#8 ≤ b1 && b1 ≤ 0x8f#8) := by
  unfold addsPState32; revert b1; decide

theorem fu_byte32_beq (b : BitVec 8) (k : BitVec 32) (hk : k.toNat < 256) :
    (BitVec.setWidth 32 b == k) = (b == BitVec.setWidth 8 k) :=
  utf8CharWidth_zeroExtend32_eq b k hk

theorem fu_byte32_bne (b : BitVec 8) (k : BitVec 32) (hk : k.toNat < 256) :
    (BitVec.setWidth 32 b != k) = !(b == BitVec.ofNat 8 k.toNat) := by
  unfold bne; rw [utf8CharWidth_zeroExtend32_eq b k hk]; rfl

theorem fu_e0_mask_eq (b1 : BitVec 8) :
    ((BitVec.setWidth 32 b1 &&& 0xe0#32) == 0xa0#32) = (0xa0#8 ≤ b1 && b1 ≤ 0xbf#8) := by
  revert b1; decide

theorem fu_f0_sub_ult (b1 : BitVec 8) :
    BitVec.ult (BitVec.setWidth 32 b1 - 0x90#32) 0x30#32 = (0x90#8 ≤ b1 && b1 ≤ 0xbf#8) := by
  revert b1; decide

theorem fu_e_ee_ef_ne_false (b0 : BitVec 8) (hw3 : (0xe0#8 ≤ b0 && b0 ≤ 0xef#8) = true)
    (hne0 : (b0 == 0xe0#8) = false) (hned : (b0 == 0xed#8) = false)
    (hcs : BitVec.ule 0x0c#32 (BitVec.setWidth 32 b0 - 0xe1#32) = true) :
    ((BitVec.setWidth 32 b0 &&& 0xfe#32) != 0xee#32) = false := by
  revert b0; decide

theorem fu_f_f1_f3_hi_false (b0 : BitVec 8) (hw4 : (0xf0#8 ≤ b0 && b0 ≤ 0xf4#8) = true)
    (hne0 : (b0 == 0xf0#8) = false) (hne4 : (b0 == 0xf4#8) = false) :
    BitVec.ult 0x02#32 (BitVec.setWidth 32 b0 - 0xf1#32) = false := by
  revert b0; decide

theorem fu_multibyte_and64 (b0 : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.signExtend 64 b0)) &&& 255#64 =
      BitVec.ofNat 64 b0.toNat := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.signExtend 64 b0)) &&& 255#64 =
      b0.zeroExtend 64 := by revert b0; decide
  rw [h1, (signExtend32_and_ff64 b0).2]

theorem fu_tbnz31_64 (b0 : BitVec 8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0))).getLsbD 31 =
      !(decide (b0 < 0x80#8)) := by
  revert b0; decide

theorem fu_tbnz31_32 (b0 : BitVec 8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0)))).getLsbD 31 =
      !(decide (b0 < 0x80#8)) := by
  revert b0; decide

theorem fu_tbnz31_se (b0 : BitVec 8) :
    (b0.signExtend 32).getLsbD 31 = !(decide (b0 < 0x80#8)) := by
  revert b0; decide

theorem fu_bne_len {k n : Nat} (hle : k ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != BitVec.ofNat 64 k) = decide (k < n) := by
  by_cases hlt : k < n
  · have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 k := fun heq => by
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at htn
      omega
    simp [bne_iff_ne, hne, hlt]
  · obtain rfl : k = n := by omega
    simp

theorem fu_ule_sub15 {idx n : Nat} (hle : idx ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - 15)).ule (BitVec.ofNat 64 idx) = decide (¬ (idx + 16 ≤ n)) := by
  rw [BitVec.ule, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n - 15 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega)]
  by_cases h16 : idx + 16 ≤ n
  · have h1 : ¬ (n - 15 ≤ idx) := by omega
    simp [h16, h1]
  · have h1 : n - 15 ≤ idx := by omega
    simp [h16, h1]

theorem fu_sub15_csel {n : Nat} (hn : n < 2 ^ 64) :
    (if (BitVec.ofNat 64 n).ult 15#64 = true then 0#64
     else BitVec.ofNat 64 n - 15#64) = BitVec.ofNat 64 (n - 15) := by
  by_cases h15 : n < 15
  · have hult : (BitVec.ofNat 64 n).ult 15#64 = true := by
      rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      exact decide_eq_true h15
    simp [hult, show n - 15 = 0 by omega]
  · have hult : (BitVec.ofNat 64 n).ult 15#64 = false := by
      rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      exact decide_eq_false h15
    simp only [hult, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock
