/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Multi

/-!
# Segment-Only ELF Placement Transfer

Transfers `MultiPlacedLib.CodeLoaded` and `dataInit` across `ElfImage` values sharing identical
`PT_LOAD` segments (`img'.segments = img.segments`), independent of `.symtab` exports.
-/

set_option autoImplicit false

@[expose] public section

namespace Arm64.Obj

open Arm64.Process ProofLib

/-- `ElfMaps` reads only the image's segments. -/
theorem ElfMaps.of_segments {img img' : ElfImage} (hseg : img'.segments = img.segments)
    {addr : BitVec 64} {bytes : List (BitVec 8)} {ok : Perm → Bool}
    (h : ElfMaps img' addr bytes ok) : ElfMaps img addr bytes ok := by
  unfold ElfMaps at h ⊢
  rw [← hseg]
  exact h

/-- `InElf` minus its export clause moves between images with the same segments. -/
theorem MultiPlacedLib.inElf_noExports_of_segments {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {img img' : ElfImage} (hseg : img'.segments = img.segments) (hin : lib.InElf img' mpl) :
    MultiPlacedLib.InElf img { lib with exports := [] } mpl :=
  ⟨fun i hi => (hin.blocks i hi).of_segments hseg,
    fun d hd => (hin.data d hd).of_segments hseg, fun _ h => nomatch h⟩

/-- `Placeable` does not read `exports`. -/
theorem MultiPlacedLib.placeable_noExports {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) : MultiPlacedLib.Placeable { lib with exports := [] } mpl :=
  ⟨hpl.blocks_ok, hpl.blocks_disjoint, hpl.symbols_nodup, hpl.data_nodup, hpl.data_ok,
    hpl.data_relocs_ok⟩

/-- Every block of `lib` is `CodeLoaded` in the initial memory of `img`, given `InElf` for any
    image `img'` with the same segments. -/
theorem MultiPlacedLib.codeLoaded_of_inElf_segments {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {img img' : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img' mpl) (hseg : img'.segments = img.segments)
    (hload : img.loadState inputs = .ok s) :
    lib.CodeLoaded mpl s.mem :=
  MultiPlacedLib.codeLoaded_of_inElf (lib := { lib with exports := [] }) (MultiPlacedLib.placeable_noExports hpl)
    (lib.inElf_noExports_of_segments hseg hin) hload

/-- `s.mem ⊨ lib.dataInit mpl` in the initial state of `img`, given `InElf` for any image `img'`
    with the same segments. -/
theorem MultiPlacedLib.satisfies_dataInit_of_inElf_segments {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {img img' : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img' mpl) (hseg : img'.segments = img.segments)
    (hload : img.loadState inputs = .ok s) (hne : 0 < lib.blocks.length)
    (hdisj : lib.DataDisjoint mpl) :
    s.mem ⊨ lib.dataInit mpl :=
  MultiPlacedLib.satisfies_dataInit_of_inElf (lib := { lib with exports := [] }) (MultiPlacedLib.placeable_noExports hpl)
    (lib.inElf_noExports_of_segments hseg hin) hload hne hdisj

end Arm64.Obj
