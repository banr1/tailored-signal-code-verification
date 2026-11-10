# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Deterministic stock-ELF regeneration and verification package for Variant 1C (`ld.lld`).

Modules:
  - elf_loader: Bit-exact mirror of Arm64/Trusted/Process/Loader.lean (`ElfImage.parse`),
    raw ELF PHDR/section/symtab parsers, and MultiPlacedLib / ExtractedObj / InternedMultiLib loaders.
  - uniqueness_steps: Generator & bit-exact Python verifier for `ConeCert.PinStep` (`checkPinCertB`,
    including `.relaxedNopAdr`) and unrelaxed `Obj.Interned.InvStep` (`checkRelocInvStepsB`).
  - elf_placed_witness: Solver & bit-exact verifier for `cliElfBlockBases`, `cliElfSymAddrTable`,
    `cliElfRelaxLists`, `checkMulti*` fast boolean checkers, GK Row 120a C2 `.symtab` tie check,
    `rangesSorted` vs `checkBlocksDisjoint` block-order check, and M3 `LabelsFromObjects` + MF3.
  - step2_constants: Extractor, verifier, and Lean generator for Step-2 constants (`MuslA1.lean`,
    `ElfMuslSlices.lean`, `CliElfProof.lean`, `ElfStaticsSlices.lean`, `MuslElf` PHDR helpers,
    and Hop/Harness offsets).
  - rekey_log_filter: Extractor, verifier, and Lean generator for `logFilterAddr` re-keying
    (Option (a) stock offset re-key and Option (b) `logAddr` parameterization / M3 retirement).
  - alpha_checks: Fail-closed Option-α `displaced_weak`, S1/S2 (`GK` rows 373 & 374 / A-LINK v0.3.2),
    and D1 `externData` linker/ELF verifiers.
"""

from . import alpha_checks
from .elf_loader import (
    ElfImage,
    ElfRegion,
    InternedMultiLib,
    MultiPlacedLib,
    Perm,
    intern_multi_placed_lib,
    parse_elf_image,
    parse_extracted_objs,
    parse_multi_placed_lib,
    parse_raw_elf,
)
__all__ = [
    "alpha_checks",
    "ElfImage",
    "ElfRegion",
    "InternedMultiLib",
    "MultiPlacedLib",
    "Perm",
    "intern_multi_placed_lib",
    "parse_elf_image",
    "parse_extracted_objs",
    "parse_multi_placed_lib",
    "parse_raw_elf",
]
