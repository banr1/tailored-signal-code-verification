/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Heap.Fine.F3LayoutData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import ProofLib.Placed.Multi
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Stock `ld.lld` Direct-Resolve Lemmas for `"memset"` and `"memcpy"` (`ElfStockStubResolve`)

**Checked by Lean. Untrusted (`Role::Proof`, Card `W2-C9H`, statement GO: `H-REV` `rev_c10_c3a.md` Addendum `06:20Z` §4).**

Proves that on the pinned stock `ld.lld --no-relax` CLI ELF (`cliElfBytes`, 37-row hook table),
for any generic placements `mpl mmpl : MultiPlacement` satisfying
`hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl` and
`hMm : mallocngLib.LinkedAt cliElfBytes mmpl`:

1. `h2b2_stockResolve_memset_eq_base`: `libsignalSessionLib.resolve mpl "memset" = mmpl.base 21`
2. `h2b2_stockResolve_memcpy_eq_base`: `libsignalSessionLib.resolve mpl "memcpy" = mmpl.base 20`

Each theorem combines layout-generic external-symbol resolution (`Obj.lookupBlockSym = none`),
relocation-inversion uniqueness on `cliElfBytes` (`f3CliElf_libsignal_linkedAt_unique` and
`f3CliElf_mallocng_linkedAt_unique` from WP3 stock regeneration), and a zero-hex `rfl_kernel`
equality check between `f3LsMpl.ρ` and `f3MallocngMpl.base`.

## Scoped-G1 (`RUST_OBJ2LEAN_PERTURB_BYTES=4096`) Frontier Note

- **Target membership**: `ElfStockStubResolve` belongs to `CliElfLib` (transitively importing
  `LibsignalBinary.Specifications.SignalSession.CliElf`), which is outside the default `lake build`
  target and therefore outside S1's default-target perturbation build.
- **Link-specific nature**: Under `RUST_OBJ2LEAN_PERTURB_BYTES=4096` (which prepends `1024` `nop`
  words to extracted object blocks while `.GeneratedLean/cli-elf/libsignal-cli.elf` stays fixed),
  upstream `ElfCodeMatchesPlaced` already fails closed because `InElf` no longer matches the
  unperturbed ELF image; furthermore, direct equality `resolve mpl "memset" = mmpl.base 21`
  (with zero PLT or range-extension branch veneer) is a genuine link-specific property of the
  pinned stock `--no-relax` `cliElfBytes` image.
- **S2 static scan (`pr-audit-check --check-layout-independent`)**: `0` findings in this module
  (uses the `0`-hex `f3LsMpl.ρ = f3MallocngMpl.base` `rfl_kernel` route).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStockStubResolve

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Heap.Fine (f3MallocngMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (lsInternedMultiLib ls_idsOk ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_linkedAt_unique f3CliElf_mallocng_linkedAt_unique f3LsMpl)

private theorem stock_mem_lsNames_of_getD {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s) :
    s ∈ lsInternedMultiLib.names := by
  rw [← heq, Obj.Interned.getD_of_lt hlt]
  exact List.getElem_mem hlt

private theorem stock_lookupBlockSym_none_of_idx {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
  rw [← heq, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hlt]
  exact hid

private noncomputable def stockMemsetIdx : Nat :=
  lsInternedMultiLib.names.idxOf "memset"

private theorem stock_memset_pin_ok :
    (Nat.blt stockMemsetIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD stockMemsetIdx "" == "memset") &&
     (Obj.Interned.lookupBlockSymId stockMemsetIdx lsInternedMultiLib.blocks == none) &&
     Nat.blt 21 mallocngLib.blocks.length &&
     (f3LsMpl.ρ "memset" == f3MallocngMpl.base 21)) = true := by
  rfl_kernel

private noncomputable def stockMemcpyIdx : Nat :=
  lsInternedMultiLib.names.idxOf "memcpy"

private theorem stock_memcpy_pin_ok :
    (Nat.blt stockMemcpyIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD stockMemcpyIdx "" == "memcpy") &&
     (Obj.Interned.lookupBlockSymId stockMemcpyIdx lsInternedMultiLib.blocks == none) &&
     Nat.blt 20 mallocngLib.blocks.length &&
     (f3LsMpl.ρ "memcpy" == f3MallocngMpl.base 20)) = true := by
  rfl_kernel

/-- On the stock `ld.lld --no-relax` CLI ELF (`cliElfBytes`), `"memset"` is an external symbol of
    `libsignalSessionLib` whose relocated call target equals `mallocngLib` block `21`
    (`mmpl.base 21`, with zero PLT/veneer stub). -/
theorem h2b2_stockResolve_memset_eq_base
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    libsignalSessionLib.resolve mpl "memset" = mmpl.base 21 := by
  have hc := stock_memset_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨⟨hlt, hnm⟩, hid⟩, h21⟩, hval⟩
  have hnone : Obj.lookupBlockSym "memset" libsignalSessionLib.blocks = none :=
    stock_lookupBlockSym_none_of_idx hlt hnm hid
  have hres : libsignalSessionLib.resolve mpl "memset" = mpl.ρ "memset" := by
    unfold Obj.MultiPlacedLib.resolve
    rw [hnone]
  have hρ : mpl.ρ "memset" = f3LsMpl.ρ "memset" :=
    (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 "memset"
      (stock_mem_lsNames_of_getD hlt hnm) hnone
  have hb : mmpl.base 21 = f3MallocngMpl.base 21 :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 21 h21
  exact hres.trans (hρ.trans (hval.trans hb.symm))

/-- On the stock `ld.lld --no-relax` CLI ELF (`cliElfBytes`), `"memcpy"` is an external symbol of
    `libsignalSessionLib` whose relocated call target equals `mallocngLib` block `20`
    (`mmpl.base 20`, with zero PLT/veneer stub). -/
theorem h2b2_stockResolve_memcpy_eq_base
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    libsignalSessionLib.resolve mpl "memcpy" = mmpl.base 20 := by
  have hc := stock_memcpy_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨⟨hlt, hnm⟩, hid⟩, h20⟩, hval⟩
  have hnone : Obj.lookupBlockSym "memcpy" libsignalSessionLib.blocks = none :=
    stock_lookupBlockSym_none_of_idx hlt hnm hid
  have hres : libsignalSessionLib.resolve mpl "memcpy" = mpl.ρ "memcpy" := by
    unfold Obj.MultiPlacedLib.resolve
    rw [hnone]
  have hρ : mpl.ρ "memcpy" = f3LsMpl.ρ "memcpy" :=
    (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 "memcpy"
      (stock_mem_lsNames_of_getD hlt hnm) hnone
  have hb : mmpl.base 20 = f3MallocngMpl.base 20 :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 20 h20
  exact hres.trans (hρ.trans (hval.trans hb.symm))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStockStubResolve
