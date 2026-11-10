/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import Arm64.Legacy
import all Arm64.Legacy.Spec.Helpers
public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SimpAttrs
public import ProofLib.PrologueFrame
public import ProofLib.ProgramReflection
public import ProofLib.CoreLemmas
public import ProofLib.BV.Bits
import ProofLib.SepLogic.Model

/-!
# Relocatable ELF Image Loading and Base-Address Independence

Connects `Arm64.Obj.LinkedImage.load` to `Arm64.Program.rebase`, `.rodata` and GOT memory
invariants, and `Obj.Image.FrozenLoaded` without running a linker inside the Lean kernel.
Also provides `WordTree` and `EncSymTable` reflection for `Obj.Loads` (`sym_guard`), linear
relocation evaluation (`relocRun`, `relocChunks`), and canonical loaded-state witnesses.
-/

@[expose] public section

/-! ## `Obj.LinkedImage` / `Obj.ObjectInfo` Function Tables and `Obj.Image` Loading -/

namespace Arm64

/-- Offset where `.text` ends and extern stubs begin in `li.code`. -/
def Obj.LinkedImage.textEnd (li : Obj.LinkedImage) : Nat :=
  match li.stubs with
  | (_, o) :: rest => Obj.minStubOff o rest
  | [] => li.code.length

/-- Function symbol table of `li`: maps each `.text` symbol `name` in `li.symbols`
    (`off < li.textEnd`) to `(off, span)` in `li.code`, preserving `li.symbols` order ($O(N \log N)$
    integer comparisons only, zero `String` unpacking in the kernel). -/
def Obj.funcTable (li : Obj.LinkedImage) : List (String × (Nat × Nat)) :=
  let textEnd := li.textEnd
  let textSyms := Obj.tagWithIdx 0 (li.symbols.filter fun (_, off) => Nat.blt off textEnd)
  let byOff := Obj.sortList (fun a b => Nat.ble a.2.2 b.2.2) textSyms
  let withSpans := (Obj.assignSpans textEnd byOff).2.2
  (Obj.sortList (fun a b => Nat.ble a.1 b.1) withSpans).map (·.2)

/-- Size in bytes of function `name` in `li` (`0` if not found). -/
def Obj.fnSize (li : Obj.LinkedImage) (name : String) : Nat :=
  match (Obj.funcTable li).find? (fun p => p.1 == name) with
  | some (_, (off, span)) => trimTrailingZeroBytesLen ((li.code.drop off).take span)
  | none => 0

/-- Extract the prologue stack frame size for an `(off, span)` entry of `li`. -/
def Obj.fnFrameBytesAt? (li : Obj.LinkedImage) : (Nat × Nat) → Option Nat
  | (off, span) => inferPrologueFrameBytes? ((li.code.drop off).take span)

/-- Prologue stack frame size in bytes of function `name` in `li` (`none` if not found or
    if its prologue uses dynamic/non-standard `SP` adjustments). -/
def Obj.fnFrameBytes? (li : Obj.LinkedImage) (name : String) : Option Nat :=
  match (Obj.funcTable li).find? (fun p => p.1 == name) with
  | some (_, info) => Obj.fnFrameBytesAt? li info
  | none => none

/-- Prologue stack frame size in bytes of function `name` in `li` (`0` if unknown). -/
def Obj.fnFrameBytes (li : Obj.LinkedImage) (name : String) : Nat :=
  (Obj.fnFrameBytes? li name).getD 0

/-- Function table of `o : Obj.ObjectInfo`: maps each function in `o.fns` and `o.callFns`
    to its code bytes. -/
def Obj.ObjectInfo.funcTable (o : Obj.ObjectInfo) : List (String × List (BitVec 8)) :=
  o.fns ++ o.callFns.map (fun (n, bs, _) => (n, bs))

/-- Byte slice of function `name` in `o` (`fns` or `callFns`). -/
def Obj.ObjectInfo.fnBytes? (o : Obj.ObjectInfo) (name : String) : Option (List (BitVec 8)) :=
  ((o.funcTable).find? (·.1 == name)).map (·.2)

/-- Size in bytes of function `name` in `o` (`0` if not found). -/
def Obj.ObjectInfo.fnSize (o : Obj.ObjectInfo) (name : String) : Nat :=
  match o.fnBytes? name with
  | some bs => bs.length
  | none => 0

/-- Prologue stack frame size in bytes of function `name` in `o`. -/
def Obj.ObjectInfo.fnFrameBytes? (o : Obj.ObjectInfo) (name : String) : Option Nat :=
  (o.fnBytes? name).bind inferPrologueFrameBytes?

/-- Prologue stack frame size in bytes of function `name` in `o` (`0` if unknown). -/
def Obj.ObjectInfo.fnFrameBytes (o : Obj.ObjectInfo) (name : String) : Nat :=
  (o.fnFrameBytes? name).getD 0

instance : HasFnFrameBytes Obj.LinkedImage where
  frameBytes := Obj.fnFrameBytes

instance : HasFnFrameBytes Obj.ObjectInfo where
  frameBytes := Obj.ObjectInfo.fnFrameBytes

theorem Obj.Image.frozenLoaded_iff {img : Obj.Image} {s : State} :
    img.FrozenLoaded s ↔
      (Program.ofImage img).CodeLoaded s.mem ∧
      img.RoDataLoaded s.mem ∧
      Obj.HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro) := by
  unfold Obj.Image.FrozenLoaded
  exact ⟨fun ⟨hc, hr, hg⟩ => ⟨hc.of_base_code rfl rfl, hr, hg⟩,
         fun ⟨hc, hr, hg⟩ => ⟨hc.of_base_code rfl rfl, hr, hg⟩⟩

theorem Obj.Image.FrozenLoaded.codeLoaded {img : Obj.Image} {s : State} (h : img.FrozenLoaded s) :
    (Program.ofImage img).CodeLoaded s.mem := (Obj.Image.frozenLoaded_iff.1 h).1

theorem Obj.Image.FrozenLoaded.roData {img : Obj.Image} {s : State} (h : img.FrozenLoaded s) :
    img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.1 h).2.1

theorem Obj.Image.FrozenLoaded.got {img : Obj.Image} {s : State} (h : img.FrozenLoaded s) :
    Obj.HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro) :=
  (Obj.Image.frozenLoaded_iff.1 h).2.2

theorem Obj.Image.loaded_iff {img : Obj.Image} {s : State} :
    img.Loaded s ↔
      (Program.ofImage img).CodeLoaded s.mem ∧
      Obj.HoldsBytes s.mem img.dataAddr img.data img.dataPerm ∧
      Obj.HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro) ∧
      s.symtab = img.symtab ∧
      s.brkStart = img.brkStart ∧
      s.brk = img.brkStart := by
  unfold Obj.Image.Loaded
  exact ⟨fun ⟨hc, r⟩ => ⟨hc.of_base_code rfl rfl, r⟩,
         fun ⟨hc, r⟩ => ⟨hc.of_base_code rfl rfl, r⟩⟩

theorem Obj.Image.Loaded.codeLoaded {img : Obj.Image} {s : State} (h : img.Loaded s) :
    (Program.ofImage img).CodeLoaded s.mem := (Obj.Image.loaded_iff.1 h).1

theorem Obj.Image.Loaded.data {img : Obj.Image} {s : State} (h : img.Loaded s) :
    Obj.HoldsBytes s.mem img.dataAddr img.data img.dataPerm := (Obj.Image.loaded_iff.1 h).2.1

theorem Obj.Image.Loaded.got {img : Obj.Image} {s : State} (h : img.Loaded s) :
    Obj.HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro) :=
  (Obj.Image.loaded_iff.1 h).2.2.1

theorem Obj.Image.Loaded.symtab {img : Obj.Image} {s : State} (h : img.Loaded s) :
    s.symtab = img.symtab :=
  (Obj.Image.loaded_iff.1 h).2.2.2.1

theorem Obj.Image.Loaded.brkStart {img : Obj.Image} {s : State} (h : img.Loaded s) :
    s.brkStart = img.brkStart :=
  (Obj.Image.loaded_iff.1 h).2.2.2.2.1

theorem Obj.Image.Loaded.brk {img : Obj.Image} {s : State} (h : img.Loaded s) :
    s.brk = img.brkStart :=
  (Obj.Image.loaded_iff.1 h).2.2.2.2.2

theorem Obj.Image.Loaded.frozenLoaded {img : Obj.Image} {s : State} (h : img.Loaded s) :
    img.FrozenLoaded s := by
  refine Obj.Image.frozenLoaded_iff.2 ⟨h.codeLoaded, fun i hi hro => ?_, h.got⟩
  obtain ⟨hb, hp, hlf⟩ := h.data i hi
  exact ⟨hb, by simpa [Obj.Image.dataPerm, hro] using hp, hlf⟩

/-- Frozen parts of an image stay loaded under any `KeepsFrozen` change. -/
theorem Obj.Image.FrozenLoaded.of_keepsFrozen {img : Obj.Image} {s s' : State}
    (hF : img.FrozenLoaded s) (hk : s.mem.KeepsFrozen s'.mem) : img.FrozenLoaded s' := by
  obtain ⟨hc, hro, hgot⟩ := Obj.Image.frozenLoaded_iff.1 hF
  refine Obj.Image.frozenLoaded_iff.2 ⟨hc.of_keepsFrozen hk, fun i hi hro_i => ?_, fun i hi => ?_⟩
  · obtain ⟨hb, hp, hlf⟩ := hro i hi hro_i
    have hf : s.mem.Frozen (img.dataAddr + BitVec.ofNat 64 i) := by
      unfold Memory.Frozen; rw [hp]; rfl
    obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
    exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩
  · obtain ⟨hb, hp, hlf⟩ := hgot i hi
    have hf : s.mem.Frozen (img.gotAddr + BitVec.ofNat 64 i) := by
      unfold Memory.Frozen; rw [hp]; rfl
    obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
    exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

theorem Step.frozenLoaded {prog : Program} {img : Obj.Image} {s s' : State}
    (h : Step prog s s') (hF : img.FrozenLoaded s) : img.FrozenLoaded s' :=
  hF.of_keepsFrozen h.keepsFrozen

theorem Steps.frozenLoaded {prog : Program} {img : Obj.Image} {s s' : State}
    (h : Steps prog s s') (hF : img.FrozenLoaded s) : img.FrozenLoaded s' :=
  hF.of_keepsFrozen h.keepsFrozen

@[simp, arm64_norm]
theorem Program.svc_ofImage (img : Obj.Image)
    (X O : String → Option (State → State)) :
    (Program.ofImage img X O).svc = Syscall.standard := by
  funext s; cases s; rfl

@[simp, arm64_norm]
theorem Program.svc_ofImageWithSvc (svc : State → State) (img : Obj.Image)
    (X O : String → Option (State → State)) :
    (Program.ofImageWithSvc svc img X O).svc = svc := by
  funext s; cases s; rfl

end Arm64

namespace Arm64.Snapshot

/-- `FrozenLoaded` from byte-level facts: code `r-x` at `img.base`, every data byte `r--` at
    `img.dataAddr` (so in particular every rodata byte), and the GOT `r--`. -/
theorem frozenLoaded_of_holdsBytes {img : Obj.Image} {s : State}
    (h_al : img.base.toNat % 4 = 0) (h_len : img.base.toNat + img.code.length ≤ 2 ^ 64)
    (hcode : Obj.HoldsBytes s.mem img.base img.code (fun _ => Perm.rx))
    (hdata : Obj.HoldsBytes s.mem img.dataAddr img.data (fun _ => Perm.ro))
    (hgot : Obj.HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro)) :
    img.FrozenLoaded s :=
  Obj.Image.frozenLoaded_iff.2
    ⟨Program.CodeLoaded.intro h_al h_len hcode, fun i hi _ => hdata i hi, hgot⟩

/-- An image without GOT slots holds its (empty) GOT in every memory. -/
theorem holdsBytes_got_nil {img : Obj.Image} {m : Memory} (h : img.got = []) :
    Obj.HoldsBytes m img.gotAddr img.gotBytes (fun _ => Perm.ro) := by
  intro i hi
  simp [Obj.Image.gotBytes, h] at hi

end Arm64.Snapshot

/-! ## `Obj.LinkedImage` Function-Table Reflection -/

namespace ProofLib.ProgramReflection

open Arm64

/-- Soundness of `Obj.funcTable` reflection for `Obj.fnSize`. -/
theorem fnSize_of_allFresh (li : Obj.LinkedImage)
    (syms : List (List Char × (Nat × Nat)))
    (htbl : Obj.funcTable li = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (sz : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hsz : (syms[k]?.map (fun p => trimTrailingZeroBytesLen ((li.code.drop p.2.1).take p.2.2))) = some sz) :
    Obj.fnSize li name = sz := by
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, off, span⟩
    simp only [hget, Option.map_some, Option.some.injEq] at hk hsz
    subst hk
    subst hsz
    simp only [Obj.fnSize, htbl, findAssoc_of_allFresh syms hfresh k hget]

/-- Soundness of `Obj.funcTable` reflection for `fnFrameBytes` on `Obj.LinkedImage`. -/
theorem fnFrameBytes_of_allFresh (li : Obj.LinkedImage)
    (syms : List (List Char × (Nat × Nat)))
    (htbl : Obj.funcTable li = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (fb : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hfb : (syms[k]?.bind (fun p => Obj.fnFrameBytesAt? li p.2)) = some fb) :
    fnFrameBytes li name = fb := by
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, info⟩
    simp only [hget, Option.map_some, Option.some.injEq] at hk
    subst hk
    simp only [hget, Option.bind_some] at hfb
    simp only [fnFrameBytes, HasFnFrameBytes.frameBytes, Obj.fnFrameBytes, Obj.fnFrameBytes?,
      htbl, findAssoc_of_allFresh syms hfresh k hget, hfb, Option.getD_some]

/-- Soundness of `Obj.funcTable` + `WordTree` reflection for `Obj.fnSize`: slices `t : WordTree`
    in $O(\log N + \text{span})$ steps instead of running `List.drop` on `li.code`. -/
theorem fnSize_of_wordTree (li : Obj.LinkedImage)
    {t : WordTree} {n : Nat}
    (hcode : li.code = t.toBytes)
    (hwf : t.checkSize? = some n)
    (syms : List (List Char × (Nat × Nat)))
    (htbl : Obj.funcTable li = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (sz : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hsz : (syms[k]?.bind (fun p =>
      (WordTree.sliceBytesChecked t n p.2.1 p.2.2).map trimTrailingZeroBytesLen)) = some sz) :
    Obj.fnSize li name = sz := by
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, off, span⟩
    simp only [hget, Option.map_some, Option.bind_some, Option.some.injEq] at hk hsz
    subst hk
    cases hslice : WordTree.sliceBytesChecked t n off span with
    | none => simp [hslice] at hsz
    | some bs =>
      simp only [hslice, Option.map_some, Option.some.injEq] at hsz
      subst hsz
      simp only [Obj.fnSize, htbl, findAssoc_of_allFresh syms hfresh k hget,
        hcode, WordTree.sliceBytesChecked_eq hwf hslice]

/-- Soundness of `Obj.funcTable` + `WordTree` reflection for `fnFrameBytes` on `Obj.LinkedImage`. -/
theorem fnFrameBytes_of_wordTree (li : Obj.LinkedImage)
    {t : WordTree} {n : Nat}
    (hcode : li.code = t.toBytes)
    (hwf : t.checkSize? = some n)
    (syms : List (List Char × (Nat × Nat)))
    (htbl : Obj.funcTable li = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (fb : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hfb : (syms[k]?.bind (fun p =>
      (WordTree.sliceBytesChecked t n p.2.1 p.2.2).bind inferPrologueFrameBytes?)) = some fb) :
    fnFrameBytes li name = fb := by
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, off, span⟩
    simp only [hget, Option.map_some, Option.bind_some, Option.some.injEq] at hk hfb
    subst hk
    cases hslice : WordTree.sliceBytesChecked t n off span with
    | none => simp [hslice] at hfb
    | some bs =>
      simp only [hslice, Option.bind_some] at hfb
      simp only [fnFrameBytes, HasFnFrameBytes.frameBytes, Obj.fnFrameBytes, Obj.fnFrameBytes?,
        Obj.fnFrameBytesAt?, htbl, findAssoc_of_allFresh syms hfresh k hget,
        hcode, WordTree.sliceBytesChecked_eq hwf hslice, hfb, Option.getD_some]

private theorem drop_take_of_take {α : Type} (l : List α) {m off span : Nat}
    (hle : off + span ≤ m) :
    (l.drop off).take span = ((l.take m).drop off).take span := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Prefix-sliced counterpart of `fnSize_of_wordTree` when `t` reflects `li.code.take m` (`m = 4 * n`). -/
theorem fnSize_of_wordTree_take (li : Obj.LinkedImage)
    {t : WordTree} {m n : Nat}
    (hcode : li.code.take m = t.toBytes)
    (hwf : t.checkSize? = some n)
    (syms : List (List Char × (Nat × Nat)))
    (htbl : Obj.funcTable li = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (sz : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hsz : (syms[k]?.bind (fun p =>
      (WordTree.sliceBytesChecked t n p.2.1 p.2.2).map trimTrailingZeroBytesLen)) = some sz)
    (hm : 4 * n = m := by rfl) :
    Obj.fnSize li name = sz := by
  subst hm
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, off, span⟩
    simp only [hget, Option.map_some, Option.bind_some, Option.some.injEq] at hk hsz
    subst hk
    cases hslice : WordTree.sliceBytesChecked t n off span with
    | none => simp [hslice] at hsz
    | some bs =>
      simp only [hslice, Option.map_some, Option.some.injEq] at hsz
      subst hsz
      have hbounds := WordTree.sliceBytesChecked_bounds hslice
      simp only [Obj.fnSize, htbl, findAssoc_of_allFresh syms hfresh k hget,
        drop_take_of_take li.code hbounds.2.2, hcode, WordTree.sliceBytesChecked_eq hwf hslice]

/-- Prefix-sliced counterpart of `fnFrameBytes_of_wordTree` when `t` reflects `li.code.take m` (`m = 4 * n`). -/
theorem fnFrameBytes_of_wordTree_take (li : Obj.LinkedImage)
    {t : WordTree} {m n : Nat}
    (hcode : li.code.take m = t.toBytes)
    (hwf : t.checkSize? = some n)
    (syms : List (List Char × (Nat × Nat)))
    (htbl : Obj.funcTable li = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (fb : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hfb : (syms[k]?.bind (fun p =>
      (WordTree.sliceBytesChecked t n p.2.1 p.2.2).bind inferPrologueFrameBytes?)) = some fb)
    (hm : 4 * n = m := by rfl) :
    fnFrameBytes li name = fb := by
  subst hm
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, off, span⟩
    simp only [hget, Option.map_some, Option.bind_some, Option.some.injEq] at hk hfb
    subst hk
    cases hslice : WordTree.sliceBytesChecked t n off span with
    | none => simp [hslice] at hfb
    | some bs =>
      simp only [hslice, Option.bind_some] at hfb
      have hbounds := WordTree.sliceBytesChecked_bounds hslice
      simp only [fnFrameBytes, HasFnFrameBytes.frameBytes, Obj.fnFrameBytes, Obj.fnFrameBytes?,
        Obj.fnFrameBytesAt?, htbl, findAssoc_of_allFresh syms hfresh k hget,
        drop_take_of_take li.code hbounds.2.2, hcode, WordTree.sliceBytesChecked_eq hwf hslice,
        hfb, Option.getD_some]

/-- Soundness of `Obj.ObjectInfo.funcTable` reflection for `fnFrameBytes` on `Obj.ObjectInfo`. -/
theorem objectInfo_fnFrameBytes_of_allFresh (o : Obj.ObjectInfo)
    (syms : List (List Char × List (BitVec 8)))
    (htbl : o.funcTable = toStringAssoc syms)
    (hfresh : allFreshCharAssoc syms = true)
    (k : Nat) (fb : Nat) {name : String}
    (hk : (syms[k]?.map (fun p => String.ofList p.1)) = some name)
    (hfb : (syms[k]?.bind (fun p => inferPrologueFrameBytes? p.2)) = some fb) :
    fnFrameBytes o name = fb := by
  cases hget : syms[k]? with
  | none => simp [hget] at hk
  | some entry =>
    rcases entry with ⟨cs, bs⟩
    simp only [hget, Option.map_some, Option.some.injEq] at hk
    subst hk
    simp only [hget, Option.bind_some] at hfb
    simp only [fnFrameBytes, HasFnFrameBytes.frameBytes, Obj.ObjectInfo.fnFrameBytes,
      Obj.ObjectInfo.fnFrameBytes?, Obj.ObjectInfo.fnBytes?, htbl,
      findAssoc_of_allFresh syms hfresh k hget, Option.map_some, Option.bind_some,
      hfb, Option.getD_some]

end ProofLib.ProgramReflection

namespace Arm64.Obj

@[simp] theorem LinkedImage.toProgram_base (li : LinkedImage) : li.toProgram.base = 0 := rfl
@[simp] theorem LinkedImage.toProgram_code (li : LinkedImage) : li.toProgram.code = li.code := rfl
@[simp] theorem LinkedImage.toProgram_symbols (li : LinkedImage) :
    li.toProgram.symbols = li.symbols := rfl
@[simp] theorem LinkedImage.toProgram_stubs (li : LinkedImage) :
    li.toProgram.stubs = li.stubs := rfl
@[simp, arm64_norm] theorem LinkedImage.toProgram_svc (li : LinkedImage) :
    li.toProgram.svc = execSyscall := by cases li; rfl



theorem LinkedImage.fnAddr_eq_add_of_toProgram {li : LinkedImage} {P : Program}
    (hc : li.toProgram = P) (b : BitVec 64) (n : String) :
    li.fnAddr b n = b + BitVec.ofNat 64 (P.fnOff n) := by
  subst hc
  rfl

end Arm64.Obj

/-! ## `imageInitialDataBss` / `imageDataBss` Unfolding Lemmas -/

namespace ProofLib

open Arm64

theorem imageInitialDataBss_holds (obj : Obj.LinkedImage) (base : BitVec 64) (h : Heap) :
    (imageInitialDataBss obj base) h ↔
      (h.auth = (fun _ _ => none) ∧
       h.frag = (fun _ _ => none) ∧
       h.mapped = (fun _ => false) ∧
       ∃ img : Obj.Image,
         obj.load base = .ok img ∧
         ∀ a : BitVec 64,
           if hlt : (a - img.dataAddr).toNat < img.data.length then
             let b := img.data[(a - img.dataAddr).toNat]
             h.phys a = some (if img.isRoData a then HeapCell.ro b else HeapCell.rw b)
           else
             h.phys a = none) :=
  Iff.rfl

theorem imageDataBss_holds (obj : Obj.LinkedImage) (base : BitVec 64) (h : Heap) :
    (imageDataBss obj base) h ↔
      (h.auth = (fun _ _ => none) ∧
       h.frag = (fun _ _ => none) ∧
       h.mapped = (fun _ => false) ∧
       ∃ img : Obj.Image,
         obj.load base = .ok img ∧
         ∀ a : BitVec 64,
           if hlt : (a - img.dataAddr).toNat < img.data.length then
             let b := img.data[(a - img.dataAddr).toNat]
             if img.isRoData a then h.phys a = some (HeapCell.ro b)
             else ∃ b' : BitVec 8, h.phys a = some (HeapCell.rw b')
           else
             h.phys a = none) :=
  Iff.rfl

end ProofLib

namespace ProofLib.ObjectLoad

open Arm64.Obj

/-- A successful `load`, spelled out. -/
theorem load_eq_ok {li : LinkedImage} {b : BitVec 64} {img : Image}
    (h : li.load b = .ok img) :
    ∃ data, li.relocs.foldlM (DataReloc.apply b) (li.data ++ List.replicate li.bss 0) = .ok data ∧
      b.toNat % pageSize = 0 ∧ li.wellFormed = true ∧
      b.toNat + li.gotOff + 8 * li.got.length ≤ 2 ^ 64 ∧
      img = { base := b, code := li.code
              dataAddr := b + BitVec.ofNat 64 li.dataOff
              data
              roData := li.roData.map fun (o, n) => (b + BitVec.ofNat 64 o, n)
              externData := li.externData.map fun (x, o, n) => (x, b + BitVec.ofNat 64 o, n)
              gotAddr := b + BitVec.ofNat 64 li.gotOff
              got := li.got.map (GotEntry.value b)
              symbols := li.symbols
              objSymbols := li.objSymbols
              stubs := li.stubs } := by
  simp only [LinkedImage.load, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  rename_i hal
  split at h
  · contradiction
  rename_i hwrap
  split at h
  · contradiction
  rename_i hwf
  split at h
  · contradiction
  rename_i data hdata
  cases h
  refine ⟨data, hdata, by simpa [bne_iff_ne] using hal, by simpa using hwf, by omega, rfl⟩

theorem load_ok {li : LinkedImage} {b : BitVec 64} {img : Image}
    (h : li.load b = .ok img) :
    img.base = b ∧ img.code = li.code ∧ img.symbols = li.symbols ∧ img.stubs = li.stubs ∧
      img.objSymbols = li.objSymbols ∧ b.toNat % pageSize = 0 ∧ li.wellFormed = true := by
  obtain ⟨_, _, hal, hwf, _, rfl⟩ := load_eq_ok h
  exact ⟨rfl, rfl, rfl, rfl, rfl, hal, hwf⟩

theorem Loads.canonical {li : LinkedImage} {img : Image} (h : Arm64.Obj.Loads li img) :
    img.code = li.code ∧ img.symbols = li.symbols ∧ img.stubs = li.stubs :=
  ⟨(load_ok h).2.1, (load_ok h).2.2.1, (load_ok h).2.2.2.1⟩

theorem Loads.symbols_eq {li : LinkedImage} {img : Image} (h : Arm64.Obj.Loads li img) :
    img.symbols = li.symbols :=
  (load_ok h).2.2.1

theorem Loads.stubs_eq {li : LinkedImage} {img : Image} (h : Arm64.Obj.Loads li img) :
    img.stubs = li.stubs :=
  (load_ok h).2.2.2.1

theorem Loads.aligned {li : LinkedImage} {img : Image} (h : Arm64.Obj.Loads li img) :
    img.base.toNat % pageSize = 0 :=
  (load_ok h).2.2.2.2.2.1

theorem Loads.wellFormed {li : LinkedImage} {img : Image} (h : Arm64.Obj.Loads li img) :
    li.wellFormed = true :=
  (load_ok h).2.2.2.2.2.2

/-- Witness `∃ img, Obj.Loads li img ∧ img.base = b` from `(li.load b).toOption.isSome = true`. -/
theorem exists_loads_of_isSome {li : LinkedImage} {b : BitVec 64}
    (hok : (li.load b).toOption.isSome = true) : ∃ img, Arm64.Obj.Loads li img ∧ img.base = b := by
  generalize hL : li.load b = r at hok
  cases r with
  | error e => simp [Except.toOption] at hok
  | ok img =>
    have hb := (load_ok hL).1
    refine ⟨img, ?_, hb⟩
    unfold Arm64.Obj.Loads
    rw [hb]
    exact hL

/-- The load base of any loaded `Obj.Image` has low 12 bits equal to 0 (`img.base &&& 0xfff#64 = 0#64`). -/
theorem base_aligned_of_loads {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img) :
    img.base &&& 0xfff#64 = 0#64 := by
  have hal := Loads.aligned h
  simp only [pageSize] at hal
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change img.base.toNat &&& (2 ^ 12 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 12]
  exact hal

abbrev base_aligned_mask := @base_aligned_of_loads
abbrev page_align_of_loads := @base_aligned_of_loads

theorem adrp_page_base {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    b &&& 0xfffffffffffff000#64 = b := by
  bv_bits

theorem adrp_page_of_aligned {b off : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (b + off) &&& 0xfffffffffffff000#64 = b + (off &&& 0xfffffffffffff000#64) := by
  bv_bits

theorem adrp_page_add_zero {b off : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hp : (off &&& 0xfffffffffffff000#64 == 0#64) = true) :
    (b + off) &&& 0xfffffffffffff000#64 = b := by
  rw [adrp_page_of_aligned hb, eq_of_beq hp, BitVec.add_zero]

theorem adrp_page_add_eq {b off pageOff : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hp : (off &&& 0xfffffffffffff000#64 == pageOff) = true) :
    (b + off) &&& 0xfffffffffffff000#64 = b + pageOff := by
  rw [adrp_page_of_aligned hb, eq_of_beq hp]

end ProofLib.ObjectLoad

end

public meta section

namespace ProofLib.ObjectLoad

open Arm64.Obj

open Lean Meta in
private partial def evalNatLitObj? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.rawNatLit? then return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (e.getArg! 1).rawNatLit? then return some n
  if let some n ← getNatValue? e then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .default (whnf e)
  if let some n := e'.rawNatLit? then return some n
  getNatValue? e'

open Lean Meta in
private partial def evalBitVecLitObj? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some w := (e.getArg! 0).rawNatLit? <|>
        (if (e.getArg! 0).isAppOfArity ``OfNat.ofNat 3 then ((e.getArg! 0).getArg! 1).rawNatLit? else none) then
      if let some v := (e.getArg! 1).rawNatLit? <|>
          (if (e.getArg! 1).isAppOfArity ``OfNat.ofNat 3 then ((e.getArg! 1).getArg! 1).rawNatLit? else none) then
        return some (w, v % (1 <<< w))
  if e.hasFVar || e.hasMVar then return none
  let e' ← if e.isConst then withTransparency .default (whnf e) else pure e
  if e'.isAppOfArity ``BitVec.ofNat 2 then
    if let some w ← evalNatLitObj? (e'.getArg! 0) then
      if let some v ← evalNatLitObj? (e'.getArg! 1) then
        return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    if let some w ← evalNatLitObj? (e'.getArg! 0) then
      let finExpr ← whnf (e'.getArg! 1)
      if finExpr.isAppOfArity ``Fin.mk 3 then
        if let some v ← evalNatLitObj? (finExpr.getArg! 1) then
          return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``HAdd.hAdd 6 then
    if let some (w1, v1) ← evalBitVecLitObj? (e'.getArg! 4) then
      if let some (w2, v2) ← evalBitVecLitObj? (e'.getArg! 5) then
        if w1 == w2 then
          return some (w1, (v1 + v2) % (1 <<< w1))
  if e'.isAppOfArity ``Neg.neg 3 then
    let inner := e'.getArg! 2
    if let some (w, v) ← evalBitVecLitObj? inner then
      let m := 1 <<< w
      return some (w, (m - (v % m)) % m)
  return none

open Lean Meta in
/-- Find a hypothesis `hb : b &&& 0xfff#64 = 0#64` in the local context for base address `b`. -/
def findBaseAlignedProof? (b : Expr) : MetaM (Option Expr) := do
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty ← instantiateMVars decl.type
      if let some (_, lhs, rhs) := ty.eq? then
        if (← evalBitVecLitObj? rhs) == some (64, 0) &&
            lhs.isAppOfArity ``HAnd.hAnd 6 then
          if lhs.getArg! 4 == b &&
              (← evalBitVecLitObj? (lhs.getArg! 5)) == some (64, 0xfff) then
            return some decl.toExpr
  return none

open Lean Meta in
/-- Normalize `pc &&& 0xfffffffffffff000#64` (produced by `ADRP`) and ground `BitVec` bitwise-AND
    expressions `lit1 &&& lit2` (after `adrp_page_of_aligned` rewrites `(b + off) &&& mask` to
    `b + (off &&& mask)`). -/
simproc [arm64_norm] reduceAdrpPage (_ &&& _) := fun e => do
  if e.getAppNumArgs != 6 then return .continue
  let lhs := e.getArg! 4
  let rhs := e.getArg! 5
  if let some (w1, v1) ← evalBitVecLitObj? lhs then
    if let some (w2, v2) ← evalBitVecLitObj? rhs then
      if w1 == w2 then
        return .done { expr := toExpr (BitVec.ofNat w1 (v1 &&& v2)) }
  let some (64, 0xfffffffffffff000) ← evalBitVecLitObj? rhs | return .continue
  if lhs.isAppOfArity ``HAdd.hAdd 6 then
    let b := lhs.getArg! 4
    let offExpr := lhs.getArg! 5
    if let some (64, offVal) ← evalBitVecLitObj? offExpr then
      if let some hbPrf ← findBaseAlignedProof? b then
        let pageVal := offVal &&& 0xfffffffffffff000
        let rflTrue ← mkEqRefl (mkConst ``true)
        if pageVal == 0 then
          let prf := mkApp4 (mkConst ``adrp_page_add_zero) b offExpr hbPrf rflTrue
          return .done { expr := b, proof? := some prf }
        else
          let pageExpr := toExpr (BitVec.ofNat 64 pageVal)
          let newExpr ← mkAppM ``HAdd.hAdd #[b, pageExpr]
          let prf := mkApp5 (mkConst ``adrp_page_add_eq) b offExpr pageExpr hbPrf rflTrue
          return .done { expr := newExpr, proof? := some prf }
  else
    if let some hbPrf ← findBaseAlignedProof? lhs then
      let prf := mkApp2 (mkConst ``adrp_page_base) lhs hbPrf
      return .done { expr := lhs, proof? := some prf }
  return .continue

end ProofLib.ObjectLoad

end

@[expose] public section

namespace ProofLib.ObjectLoad

open Arm64.Obj

namespace RoDataFactsAux

theorem bytesLE_length (n : Nat) (v : BitVec 64) : (bytesLE n v).length = n := by
  simp [bytesLE]

theorem dataReloc_apply_length {base : BitVec 64} {d out : List (BitVec 8)}
    {r : DataReloc} (h : DataReloc.apply base d r = .ok out)
    (hb : r.off + r.width ≤ d.length) : out.length = d.length := by
  unfold DataReloc.apply at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  simp only [List.length_append, List.length_take, List.length_drop, bytesLE_length]
  omega

theorem foldlM_dataReloc_length {base : BitVec 64} {N : Nat} :
    ∀ (rs : List DataReloc) (d out : List (BitVec 8)),
      rs.foldlM (DataReloc.apply base) d = .ok out →
      rs.all (fun r => decide (r.off + r.width ≤ N)) = true →
      N ≤ d.length → out.length = d.length
  | [], d, out, h, _, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | r :: rs, d, out, h, hrs, hN => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hrs
    cases hr : DataReloc.apply base d r with
    | error e => rw [hr] at h; cases h
    | ok d' =>
      rw [hr] at h
      have hl := dataReloc_apply_length hr (by omega)
      rw [foldlM_dataReloc_length rs d' out h hrs.2 (by omega), hl]

theorem dataReloc_apply_getElem?_of_lt {base : BitVec 64} {d out : List (BitVec 8)}
    {r : DataReloc} (h : DataReloc.apply base d r = .ok out)
    {k : Nat} (hk : k < r.off) {x : BitVec 8} (hd : d[k]? = some x) :
    out[k]? = some x := by
  unfold DataReloc.apply at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  have hlen : k < d.length := (List.getElem?_eq_some_iff.mp hd).1
  have htk : k < (d.take r.off).length := by simp only [List.length_take]; omega
  rw [List.append_assoc, List.getElem?_append_left htk, List.getElem?_take_of_lt hk, hd]


theorem dataReloc_apply_getElem?_of_disjoint {base : BitVec 64} {d out : List (BitVec 8)}
    {r : DataReloc} (h : DataReloc.apply base d r = .ok out)
    {k : Nat} (hk : k < r.off ∨ r.off + r.width ≤ k)
    {x : BitVec 8} (hd : d[k]? = some x) :
    out[k]? = some x := by
  rcases hk with hk | hk
  · exact dataReloc_apply_getElem?_of_lt h hk hd
  · unfold DataReloc.apply at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    simp only [Except.ok.injEq] at h
    subst h
    have hlen : k < d.length := (List.getElem?_eq_some_iff.mp hd).1
    have hpre : (d.take r.off ++ bytesLE r.width (base + BitVec.ofNat 64 r.target)).length =
        r.off + r.width := by
      simp only [List.length_append, List.length_take, bytesLE_length]; omega
    rw [List.getElem?_append_right (by omega), hpre, List.getElem?_drop,
      Nat.add_sub_cancel' hk, hd]

theorem foldlM_dataReloc_getElem?_of_disjoint {base : BitVec 64} {lo hi : Nat} :
    ∀ (rs : List DataReloc) (d out : List (BitVec 8)),
      rs.foldlM (DataReloc.apply base) d = .ok out →
      rs.all (fun r => decide (r.off + r.width ≤ lo ∨ hi ≤ r.off)) = true →
      ∀ {k : Nat}, lo ≤ k → k < hi → ∀ {x : BitVec 8}, d[k]? = some x → out[k]? = some x
  | [], d, out, h, _, _, _, _, _, hd => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hd
  | r :: rs, d, out, h, hrs, k, hlo, hhi, x, hd => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hrs
    cases hr : DataReloc.apply base d r with
    | error e => rw [hr] at h; cases h
    | ok d' =>
      rw [hr] at h
      have hd' := dataReloc_apply_getElem?_of_disjoint hr (by omega) hd
      exact foldlM_dataReloc_getElem?_of_disjoint rs d' out h hrs.2 hlo hhi hd'

end RoDataFactsAux

open RoDataFactsAux

set_option maxRecDepth 100000 in
/-- Every byte of a `.rodata` section `(secOff, secLen)` of `li` is mapped read-only
    whenever `Obj.Loads li img` and `img.RoDataLoaded m`. Unlike `rodata_bytes_disjoint`, this
    only concerns permissions, so the section may contain relocated pointers. -/
theorem rodata_perm {li : LinkedImage} {img : Image} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff := by rfl)
    {secOff secLen : Nat} (hsec : (secOff, secLen) ∈ li.roData)
    (_hlen : secLen < 2 ^ 32 := by decide)
    (m : Arm64.Memory) (hro : img.RoDataLoaded m) :
    ∀ k, k < secLen →
      m.perm (img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k) = some .ro ∧
      m.isLazyFree (img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k) = false := by
  intro k hkl
  obtain ⟨data, hfold, -, hwf, hwrap, himg_eq⟩ := load_eq_ok himg
  simp only [LinkedImage.wellFormed, Bool.and_eq_true] at hwf
  have hroD_wf := List.all_eq_true.mp hwf.1.1.1.1.2
  have hrel_wf := List.all_eq_true.mp hwf.1.1.2
  have hde_le : li.dataEnd ≤ li.gotOff := by
    have := hwf.1.1.1.1.1.1.2
    simpa [decide_eq_true_eq] using this
  have hsec_wf := hroD_wf _ hsec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsec_wf
  have hrel' : li.relocs.all
      (fun r => decide (r.off + r.width ≤ li.data.length)) = true := by
    rw [List.all_eq_true]
    intro r hr
    have := hrel_wf r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simpa using this.2
  have hdlen := foldlM_dataReloc_length li.relocs _ data hfold hrel'
    (by simp only [List.length_append]; omega)
  simp only [List.length_append, List.length_replicate] at hdlen
  have hda : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff := by
    conv => lhs; rw [himg_eq]
  have hdata_eq : img.data = data := by
    conv => lhs; rw [himg_eq]
  have hroD : (img.base + BitVec.ofNat 64 secOff, secLen) ∈ img.roData := by
    rw [show img.roData = li.roData.map (fun (o, n) => (img.base + BitVec.ofNat 64 o, n)) by
      conv => lhs; rw [himg_eq]]
    exact List.mem_map.mpr ⟨(secOff, secLen), hsec, rfl⟩
  have hdataEnd : li.dataEnd = li.dataOff + li.data.length + li.bss := rfl
  have hi : secOff - dataOff + k < img.data.length := by
    rw [hdata_eq, hdlen]; omega
  have haddr : img.dataAddr + BitVec.ofNat 64 (secOff - dataOff + k) =
      img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k := by
    rw [hda, hdo]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hisro : img.isRoData (img.dataAddr + BitVec.ofNat 64 (secOff - dataOff + k)) = true := by
    unfold Image.isRoData
    rw [List.any_eq_true]
    refine ⟨_, hroD, ?_⟩
    have e : img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k -
        (img.base + BitVec.ofNat 64 secOff) = BitVec.ofNat 64 k := by bv_lin
    rw [haddr, e]
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; exact hkl
  obtain ⟨-, hperm, hlf⟩ := hro _ hi hisro
  rw [haddr] at hperm hlf
  exact ⟨hperm, hlf⟩

/-- A `.rodata` section `(secOff, secLen)` in `li` with `dataOff ≤ secOff` and
    `[secOff - dataOff, secOff - dataOff + secLen)` disjoint from all data relocations is present
    verbatim in memory, read-only, whenever `Obj.Loads li img` and `img.RoDataLoaded m`. -/
theorem rodata_bytes_disjoint {li : LinkedImage} {img : Image} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff)
    {secOff secLen : Nat} (hsec : (secOff, secLen) ∈ li.roData)
    (hoff : dataOff ≤ secOff) (_hlen : secLen < 2 ^ 32)
    (hdlen : secOff - dataOff + secLen ≤ li.data.length)
    (hrel : li.relocs.all
      (fun r => decide (r.off + r.width ≤ secOff - dataOff ∨ secOff - dataOff + secLen ≤ r.off)) = true)
    (m : Arm64.Memory) (hro : img.RoDataLoaded m) :
    ∀ k, k < secLen →
      some (m.read8 (img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k)) =
        li.data[secOff - dataOff + k]? ∧
      m.perm (img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k) = some .ro := by
  intro k hkl
  obtain ⟨data, hfold, -, hwf, hwrap, himg_eq⟩ := load_eq_ok himg
  simp only [LinkedImage.wellFormed, Bool.and_eq_true] at hwf
  have hroD_wf := List.all_eq_true.mp hwf.1.1.1.1.2
  have hde_le : li.dataEnd ≤ li.gotOff := by
    have := hwf.1.1.1.1.1.1.2
    simpa [decide_eq_true_eq] using this
  have hsec_wf := hroD_wf _ hsec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsec_wf
  have hdataEnd : li.dataEnd = li.dataOff + li.data.length + li.bss := rfl
  have hda : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff := by
    conv => lhs; rw [himg_eq]
  have hdata_eq : img.data = data := by
    conv => lhs; rw [himg_eq]
  have hroD : (img.base + BitVec.ofNat 64 secOff, secLen) ∈ img.roData := by
    rw [show img.roData = li.roData.map (fun (o, n) => (img.base + BitVec.ofNat 64 o, n)) by
      conv => lhs; rw [himg_eq]]
    exact List.mem_map.mpr ⟨(secOff, secLen), hsec, rfl⟩
  have hidx_lt : secOff - dataOff + k < li.data.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, li.data[secOff - dataOff + k]? = some x :=
    ⟨_, List.getElem?_eq_getElem hidx_lt⟩
  have hinit : (li.data ++ List.replicate li.bss 0)[secOff - dataOff + k]? = some x := by
    rw [List.getElem?_append_left hidx_lt, hx]
  have hout := foldlM_dataReloc_getElem?_of_disjoint li.relocs _ data hfold hrel
    (k := secOff - dataOff + k) (by omega) (by omega) hinit
  rw [← hdata_eq] at hout
  have hi : secOff - dataOff + k < img.data.length := (List.getElem?_eq_some_iff.mp hout).1
  have haddr : img.dataAddr + BitVec.ofNat 64 (secOff - dataOff + k) =
      img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k := by
    rw [hda, hdo]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hisro : img.isRoData (img.dataAddr + BitVec.ofNat 64 (secOff - dataOff + k)) = true := by
    unfold Image.isRoData
    rw [List.any_eq_true]
    refine ⟨_, hroD, ?_⟩
    have e : img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 k -
        (img.base + BitVec.ofNat 64 secOff) = BitVec.ofNat 64 k := by bv_lin
    rw [haddr, e]
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; exact hkl
  obtain ⟨h8, hperm, _⟩ := hro _ hi hisro
  rw [haddr] at h8 hperm
  refine ⟨?_, hperm⟩
  rw [h8, hx, ← List.getElem?_eq_getElem hi, hout]

theorem readBytes_getElem? (m : Arm64.Memory) (p : BitVec 64) (n : Nat) (k : Nat) (hk : k < n) :
    (m.readBytes p n)[k]? = some (m.read8 (p + BitVec.ofNat 64 k)) := by
  induction n generalizing p k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [Arm64.Memory.readBytes_succ]
    | succ k =>
      simp only [Arm64.Memory.readBytes_succ, List.getElem?_cons_succ]
      rw [ih (p + 1#64) k (by omega)]
      have hadd : p + 1#64 + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (k + 1) := by bv_arith
      rw [hadd]

/-- Every `.rodata` section `(secOff, secLen)` of `li` is mapped read-only
    (`m.RO (img.base + secOff) secLen`) whenever `Obj.Loads li img` and `img.RoDataLoaded m`. -/
theorem rodata_ro {li : LinkedImage} {img : Image} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff := by rfl)
    {secOff secLen : Nat} (hsec : (secOff, secLen) ∈ li.roData)
    (hlen : secLen < 2 ^ 32 := by decide)
    (m : Arm64.Memory) (hro : img.RoDataLoaded m) :
    m.RO (img.base + BitVec.ofNat 64 secOff) secLen := by
  intro a ha
  unfold Arm64.InRegion at ha
  have hk : (a - (img.base + BitVec.ofNat 64 secOff)).toNat < secLen := ha
  have hperm := rodata_perm himg hdo hsec hlen m hro _ hk
  have heq : img.base + BitVec.ofNat 64 secOff +
      BitVec.ofNat 64 (a - (img.base + BitVec.ofNat 64 secOff)).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_lin
  rwa [heq] at hperm

/-- Region-level bridge for a `.rodata` section `(secOff, secLen)` disjoint from data relocations:
    under `Obj.Loads li img` and `img.RoDataLoaded m`, the section is mapped read-only (`m.RO`) and
    `m.readBytes (img.base + secOff) secLen = (li.data.drop (secOff - dataOff)).take secLen`. -/
theorem rodata_readBytes_disjoint {li : LinkedImage} {img : Image} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff := by rfl)
    {secOff secLen : Nat} (hsec : (secOff, secLen) ∈ li.roData)
    (hoff : dataOff ≤ secOff := by decide) (hlen : secLen < 2 ^ 32 := by decide)
    (hdlen : secOff - dataOff + secLen ≤ li.data.length := by decide)
    (hrel : li.relocs.all
      (fun r => decide (r.off + r.width ≤ secOff - dataOff ∨ secOff - dataOff + secLen ≤ r.off)) = true := by decide)
    (m : Arm64.Memory) (hro : img.RoDataLoaded m) :
    m.RO (img.base + BitVec.ofNat 64 secOff) secLen ∧
    m.readBytes (img.base + BitVec.ofNat 64 secOff) secLen =
      (li.data.drop (secOff - dataOff)).take secLen := by
  refine ⟨rodata_ro himg hdo hsec hlen m hro, ?_⟩
  apply List.ext_getElem?
  intro k
  by_cases hk : k < secLen
  · rw [readBytes_getElem? _ _ _ _ hk, List.getElem?_take_of_lt hk, List.getElem?_drop]
    exact (rodata_bytes_disjoint himg hdo hsec hoff hlen hdlen hrel m hro k hk).1
  · have h1 : ¬ k < (m.readBytes (img.base + BitVec.ofNat 64 secOff) secLen).length := by
      rw [Arm64.Memory.readBytes_length]; exact hk
    have h2 : ¬ k < ((li.data.drop (secOff - dataOff)).take secLen).length := by
      rw [List.length_take, List.length_drop]; omega
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h1), List.getElem?_eq_none (Nat.le_of_not_lt h2)]

/-- Region-level bridge from `Obj.HoldsBytes m addr bytes (fun _ => Perm.ro)` to `m.RO` and `m.readBytes`. -/
theorem holdsBytes_ro {m : Arm64.Memory} {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bytes (fun _ => .ro)) :
    m.RO addr bytes.length ∧ m.readBytes addr bytes.length = bytes := by
  refine ⟨fun a ha => ?_, ?_⟩
  · unfold Arm64.InRegion at ha
    have hk : (a - addr).toNat < bytes.length := ha
    have hp := (h (a - addr).toNat hk).2
    have heq : addr + BitVec.ofNat 64 (a - addr).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_lin
    rwa [heq] at hp
  · apply List.ext_getElem?
    intro k
    by_cases hk : k < bytes.length
    · rw [readBytes_getElem? _ _ _ _ hk, List.getElem?_eq_getElem hk]
      exact congrArg some (h k hk).1
    · have h1 : ¬ k < (m.readBytes addr bytes.length).length := by
        rw [Arm64.Memory.readBytes_length]; exact hk
      rw [List.getElem?_eq_none (Nat.le_of_not_lt h1), List.getElem?_eq_none (Nat.le_of_not_lt hk)]

/-- No data relocation in `rs` overlaps the byte range `[k, k + n)` (and every relocation lies
    within `dataLen`). -/
def noRelocInRange (rs : List DataReloc) (dataLen k n : Nat) : Bool :=
  rs.all fun r => decide (r.off + r.width ≤ dataLen ∧ (r.off + r.width ≤ k ∨ k + n ≤ r.off))

theorem splice_length {d bs : List (BitVec 8)} {off : Nat} (h : off + bs.length ≤ d.length) :
    (d.take off ++ bs ++ d.drop (off + bs.length)).length = d.length := by
  simp [List.length_take, List.length_drop]
  omega

theorem splice_drop_take_eq {d bs : List (BitVec 8)} {off k n : Nat}
    (hb : off + bs.length ≤ d.length) (hdisj : off + bs.length ≤ k ∨ k + n ≤ off) :
    ((d.take off ++ bs ++ d.drop (off + bs.length)).drop k).take n = (d.drop k).take n := by
  rcases hdisj with hle | hge
  · have hlen1 : (d.take off ++ bs).length = off + bs.length := by
      simp [List.length_take]; omega
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlen1,
      List.drop_drop, show off + bs.length + (k - (off + bs.length)) = k by omega]
  · rw [List.append_assoc, List.drop_append, List.take_append]
    have hlen_take : (d.take off).length = off := by simp [List.length_take]; omega
    have hlen_drop : ((d.take off).drop k).length = off - k := by
      simp [List.length_drop, hlen_take]
    have hsub : n - (off - k) = 0 := by omega
    rw [hlen_drop, hsub, List.take_zero, List.append_nil, List.drop_take, List.take_take,
      Nat.min_eq_left (by omega)]

theorem dataReloc_apply_preserves_slice {base : BitVec 64} {d d' : List (BitVec 8)} {r : DataReloc}
    {dataLen k n : Nat} (hlen : d.length = dataLen)
    (hr : r.off + r.width ≤ dataLen ∧ (r.off + r.width ≤ k ∨ k + n ≤ r.off))
    (happ : DataReloc.apply base d r = .ok d') :
    d'.length = dataLen ∧ (d'.drop k).take n = (d.drop k).take n := by
  simp only [DataReloc.apply] at happ
  split at happ
  · contradiction
  · injection happ with hd'
    subst hd'
    have hbw : (bytesLE r.width (base + BitVec.ofNat 64 r.target)).length = r.width :=
      bytesLE_length _ _
    have hb : r.off + (bytesLE r.width (base + BitVec.ofNat 64 r.target)).length ≤ d.length := by
      omega
    have hdisj :
        r.off + (bytesLE r.width (base + BitVec.ofNat 64 r.target)).length ≤ k ∨
          k + n ≤ r.off := by
      rw [hbw]; exact hr.2
    have h1 := splice_length hb
    have h2 := splice_drop_take_eq (n := n) hb hdisj
    rw [hbw] at h1 h2
    exact ⟨h1.trans hlen, h2⟩

theorem foldlM_dataReloc_preserves_slice {base : BitVec 64} :
    ∀ (rs : List DataReloc) (d d' : List (BitVec 8)) (dataLen k n : Nat),
      d.length = dataLen →
      noRelocInRange rs dataLen k n = true →
      rs.foldlM (DataReloc.apply base) d = .ok d' →
      d'.length = dataLen ∧ (d'.drop k).take n = (d.drop k).take n
  | [], d, d', dataLen, _, _, hlen, _, hfold => by
    injection hfold with h; subst h; exact ⟨hlen, rfl⟩
  | r :: rs, d, d', dataLen, k, n, hlen, hno, hfold => by
    simp only [noRelocInRange, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hno
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · contradiction
    · rename_i d1 happ
      obtain ⟨hlen1, hslice1⟩ := dataReloc_apply_preserves_slice hlen hno.1 happ
      obtain ⟨hlen2, hslice2⟩ :=
        foldlM_dataReloc_preserves_slice rs d1 d' dataLen k n hlen1 hno.2 hfold
      exact ⟨hlen2, hslice2.trans hslice1⟩

/-- If `[k, k + n)` lies inside `li.data` and is disjoint from all `li.relocs`, then any loaded
    image `img` (`Obj.Loads li img`) has `img.dataAddr = img.base + li.dataOff` and the same bytes
    at `[k, k + n)` in `img.data` as `li.data`. -/
theorem loads_data_slice_eq {li : LinkedImage} {img : Image}
    (himg : Arm64.Obj.Loads li img) {k n : Nat}
    (hk : k + n ≤ li.data.length)
    (hno : noRelocInRange li.relocs (li.data.length + li.bss) k n = true) :
    img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff ∧
      (img.data.drop k).take n = (li.data.drop k).take n := by
  obtain ⟨data, hfold, _, _, _, himg_eq⟩ := load_eq_ok himg
  have haddr : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff :=
    congrArg Image.dataAddr himg_eq
  have hdata : img.data = data := congrArg Image.data himg_eq
  refine ⟨haddr, ?_⟩
  rw [hdata]
  have hlen0 : (li.data ++ List.replicate li.bss 0).length = li.data.length + li.bss := by
    simp
  obtain ⟨_, hslice⟩ :=
    foldlM_dataReloc_preserves_slice li.relocs (li.data ++ List.replicate li.bss 0) data
      (li.data.length + li.bss) k n hlen0 hno hfold
  rw [hslice, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp [List.length_drop]; omega)]

/-- `[off, off + len)` lies inside one of `li.roData`'s read-only ranges. -/
def inLiRoData (li : LinkedImage) (off len : Nat) : Bool :=
  li.roData.any fun r => decide (r.1 ≤ off ∧ off + len ≤ r.1 + r.2 ∧ r.1 + r.2 < 2 ^ 64)

theorem bv_add_sub_add_of_le (b : BitVec 64) {x y : Nat} (hle : y ≤ x) (hx : x < 2 ^ 64) :
    (b + BitVec.ofNat 64 x) - (b + BitVec.ofNat 64 y) = BitVec.ofNat 64 (x - y) := by
  have h1 : (b + BitVec.ofNat 64 x) - (b + BitVec.ofNat 64 y) =
      BitVec.ofNat 64 x - BitVec.ofNat 64 y := by bv_lin
  rw [h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Combining `Obj.Loads li img` and `img.FrozenLoaded s` (`FrozenLoaded.roData`) yields
    `Obj.HoldsBytes s.mem (img.base + off) bs (fun _ => Perm.ro)` for any relocation-free slice
    `[off, off + n)` (`bs.length = n`) inside `li.roData`. -/
theorem loads_rodata_holdsBytes {li : LinkedImage} {img : Image} {s : Arm64.State}
    (himg : Arm64.Obj.Loads li img) (hF : img.FrozenLoaded s) {off n : Nat} {bs : List (BitVec 8)}
    (hoff : li.dataOff ≤ off)
    (hk : (off - li.dataOff) + n ≤ li.data.length)
    (hno : noRelocInRange li.relocs (li.data.length + li.bss) (off - li.dataOff) n = true)
    (hro : inLiRoData li off n = true)
    (hn : bs.length = n)
    (hbs : (li.data.drop (off - li.dataOff)).take n = bs) :
    Arm64.Obj.HoldsBytes s.mem (img.base + BitVec.ofNat 64 off) bs (fun _ => .ro) := by
  subst hn
  obtain ⟨data, hfold, _, _, _, himg_eq⟩ := load_eq_ok himg
  have haddr : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff :=
    congrArg Image.dataAddr himg_eq
  have hdata : img.data = data := congrArg Image.data himg_eq
  have hro_map : img.roData = li.roData.map (fun (o, m) => (img.base + BitVec.ofNat 64 o, m)) :=
    congrArg Image.roData himg_eq
  have hlen0 : (li.data ++ List.replicate li.bss 0).length = li.data.length + li.bss := by simp
  obtain ⟨hd_len, hd_slice⟩ :=
    foldlM_dataReloc_preserves_slice li.relocs (li.data ++ List.replicate li.bss 0) data
      (li.data.length + li.bss) (off - li.dataOff) bs.length hlen0 hno hfold
  have hslice : (img.data.drop (off - li.dataOff)).take bs.length = bs := by
    rw [hdata, hd_slice, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp [List.length_drop]; omega), hbs]
  simp only [inLiRoData, List.any_eq_true, decide_eq_true_eq] at hro
  obtain ⟨⟨rOff, rLen⟩, hr_mem, hr_le1, hr_le2, hr_lt⟩ := hro
  intro j hj
  have hi : (off - li.dataOff) + j < img.data.length := by
    rw [hdata, hd_len]; omega
  have ha_eq : img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j) =
      img.base + BitVec.ofNat 64 off + BitVec.ofNat 64 j := by
    rw [haddr, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; omega
  have ha_eq' : img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j) =
      img.base + BitVec.ofNat 64 (off + j) := by
    rw [ha_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hisRo : img.isRoData (img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j)) = true := by
    simp only [Image.isRoData, hro_map, List.any_map, List.any_eq_true]
    refine ⟨(rOff, rLen), hr_mem, ?_⟩
    simp only [Function.comp_apply, decide_eq_true_eq, ha_eq']
    rw [bv_add_sub_add_of_le img.base (by omega) (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hread, hperm, hlf⟩ := hF.roData ((off - li.dataOff) + j) hi hisRo
  have hget : bs[j] = img.data[(off - li.dataOff) + j] := by
    have h1 : ((img.data.drop (off - li.dataOff)).take bs.length)[j]'(by
        rw [List.length_take, List.length_drop, hdata, hd_len]; omega) = bs[j] := by
      simp only [hslice]
    rw [← h1, List.getElem_take, List.getElem_drop]
  rw [← ha_eq, hget]
  exact ⟨hread, hperm, hlf⟩

theorem holdsBytes_ro_of_keepsFrozen {m m' : Arm64.Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bs (fun _ => .ro)) (hk : m.KeepsFrozen m') :
    Arm64.Obj.HoldsBytes m' addr bs (fun _ => .ro) := by
  intro i hi
  obtain ⟨hb, hp, hlf⟩ := h i hi
  have hf : m.Frozen (addr + BitVec.ofNat 64 i) := by
    unfold Arm64.Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

theorem holdsBytes_cons_iff {m : Arm64.Memory} {addr : BitVec 64} {b : BitVec 8} {bs : List (BitVec 8)}
    {p : BitVec 64 → Arm64.Perm} :
    Arm64.Obj.HoldsBytes m addr (b :: bs) p ↔
      (m.read8 addr = b ∧ m.perm addr = some (p addr) ∧ m.isLazyFree addr = false) ∧
        Arm64.Obj.HoldsBytes m (addr + 1#64) bs p := by
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · obtain ⟨hb, hp, hlf⟩ := h 0 (by simp)
      exact ⟨by simpa using hb, by simpa using hp, by simpa using hlf⟩
    · have h1 := h (i + 1) (by simp; omega)
      have ha : addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      simpa [ha] using h1
  · rintro ⟨h0, hs⟩ i hi
    rcases i with _ | i
    · simpa using h0
    · have h1 := hs i (by simp at hi; omega)
      have ha : addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      simpa [ha] using h1

theorem holdsBytes_append {m : Arm64.Memory} {addr : BitVec 64} {bs1 bs2 : List (BitVec 8)}
    {p : BitVec 64 → Arm64.Perm} (h : Arm64.Obj.HoldsBytes m addr (bs1 ++ bs2) p) :
    Arm64.Obj.HoldsBytes m addr bs1 p ∧
      Arm64.Obj.HoldsBytes m (addr + BitVec.ofNat 64 bs1.length) bs2 p := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := h i (by simp; omega)
    rwa [List.getElem_append_left hi] at h1
  · have h1 := h (bs1.length + i) (by simp; omega)
    rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
    have ha : addr + BitVec.ofNat 64 (bs1.length + i) =
        addr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simpa [ha] using h1

theorem memSlice_of_holdsBytes_ro {m : Arm64.Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : Arm64.Obj.HoldsBytes m addr bs (fun _ => .ro)) :
    m.canRead addr bs.length = true ∧ m.readBytes addr bs.length = bs := by
  induction bs generalizing addr with
  | nil => simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree]
  | cons b bs ih =>
    obtain ⟨⟨hb, hp, hlf⟩, hs⟩ := holdsBytes_cons_iff.1 h
    obtain ⟨hc, hr⟩ := ih hs
    refine ⟨?_, by simp [hb, hr]⟩
    simp only [List.length_cons, Arm64.Memory.canRead, Arm64.Memory.allPerm,
      Arm64.Memory.allNoLazyFree, Bool.and_eq_true] at hc ⊢
    rw [hp, hlf]
    exact ⟨⟨rfl, hc.1⟩, ⟨rfl, hc.2⟩⟩

theorem gotBytes_length (img : Image) : img.gotBytes.length = 8 * img.got.length := by
  unfold Image.gotBytes
  induction img.got with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, RoDataFactsAux.bytesLE_length,
      List.length_cons, ih]
    omega

/-! ## Reflected `WordTree` & `List Char` Verification of `Obj.Loads` -/

open ProofLib.ProgramReflection

/-- Whether `DataReloc.apply base _ r` succeeds (depends only on `r.width` and `r.target`, not on `data`). -/
def DataReloc.validAt (base : BitVec 64) (r : DataReloc) : Bool :=
  let v := base + BitVec.ofNat 64 r.target
  !(r.width == 4 && !(-(2 ^ 31 : Int) ≤ v.toInt && v.toInt < (2 ^ 32 : Int)))

theorem DataReloc.exists_apply_of_validAt {base : BitVec 64} {r : DataReloc}
    (d : List (BitVec 8)) (hv : DataReloc.validAt base r = true) :
    ∃ d', DataReloc.apply base d r = .ok d' := by
  simp only [DataReloc.validAt, Bool.not_eq_true'] at hv
  simp only [DataReloc.apply, hv, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
    Except.ok.injEq, exists_eq']

/-- If every relocation in `rs` satisfies `DataReloc.validAt base`, then `rs.foldlM (DataReloc.apply base) d`
    succeeds without evaluating list splices on `d`. -/
theorem exists_foldlM_dataReloc_of_all_validAt {base : BitVec 64} :
    ∀ (rs : List DataReloc) (d : List (BitVec 8)),
      rs.all (DataReloc.validAt base) = true →
      ∃ d', rs.foldlM (DataReloc.apply base) d = .ok d'
  | [], d, _ => ⟨d, rfl⟩
  | r :: rs, d, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨d₁, hd₁⟩ := DataReloc.exists_apply_of_validAt d h.1
    simp only [List.foldlM_cons, bind, Except.bind, hd₁]
    exact exists_foldlM_dataReloc_of_all_validAt rs d₁ h.2

/-- Layout portion of `LinkedImage.wellFormed` parameterized by precomputed `codeLen` and `dataLen`
    so `li.code.length` and `li.data.length` are not recomputed inside `List.all`. -/
def LinkedImage.wellFormedLayout (li : LinkedImage) (codeLen dataLen : Nat) : Bool :=
  let dataEnd := li.dataOff + dataLen + li.bss
  codeLen ≤ li.dataOff && li.dataOff % pageSize == 0 &&
  dataEnd ≤ li.gotOff && li.gotOff % 8 == 0 &&
  li.roData.all (fun (o, n) => li.dataOff ≤ o && o + n ≤ dataEnd) &&
  li.externData.all (fun (_, o, n) => dataEnd ≤ o && o + n ≤ li.gotOff) &&
  li.relocs.all (fun r => (r.width == 8 || r.width == 4) && r.off + r.width ≤ dataLen) &&
  li.stubs.all (fun (_, s) => s + 4 ≤ codeLen)

theorem LinkedImage.wellFormed_of_layout_and_honours {li : LinkedImage} {codeLen dataLen : Nat}
    (hc : li.code.length = codeLen) (hd : li.data.length = dataLen)
    (hl : LinkedImage.wellFormedLayout li codeLen dataLen = true)
    (hh : li.objects.all li.honours = true) :
    li.wellFormed = true := by
  subst hc; subst hd
  unfold LinkedImage.wellFormed LinkedImage.dataEnd
  unfold LinkedImage.wellFormedLayout at hl
  rw [hl, hh]; rfl

/-- Pre-encoded `(length, codepoints)` association list for fast kernel lookups via `natEntryBeq`. -/
abbrev EncSymTable (α : Type) := List ((Nat × List Nat) × α)

def prepareCharAssocVal {α : Type} : List (List Char × α) → EncSymTable α
  | [] => []
  | (cs, v) :: rest => (encodeCharKey cs, v) :: prepareCharAssocVal rest

def lookupEnc {α : Type} (k : Nat × List Nat) : EncSymTable α → Option α
  | [] => none
  | (e, v) :: rest => if natEntryBeq e k then some v else lookupEnc k rest

def filterEnc {α : Type} (k : Nat × List Nat) : EncSymTable α → List ((Nat × List Nat) × α)
  | [] => []
  | (e, v) :: rest => if natEntryBeq e k then (e, v) :: filterEnc k rest else filterEnc k rest

def lookupUniqueEnc {α : Type} (k : Nat × List Nat) (xs : EncSymTable α) : Option α :=
  match filterEnc k xs with
  | [(_, v)] => some v
  | _ => none

def anyEnc {α : Type} (k : Nat × List Nat) : EncSymTable α → Bool
  | [] => false
  | (e, _) :: rest => if natEntryBeq e k then true else anyEnc k rest

def resolveSymEnc (symbols stubs : EncSymTable Nat) (k : Nat × List Nat) : Option Nat :=
  (lookupEnc k symbols).orElse fun _ => lookupEnc k stubs

/-- `List Char`-reflected counterpart of `Obj.ObjectInfo` for `natEntryBeq` symbol resolution. -/
structure CharObjectInfo where
  name : List Char
  fns : List (List Char × List (BitVec 8)) := []
  callFns : List (List Char × List (BitVec 8) × List (Nat × List Char)) := []
  relocFns : List SymCodeInfo := []
  dataSyms : List SymDataInfo := []

def toStringCallList : List (Nat × List Char) → List (Nat × String)
  | [] => []
  | (roff, cs) :: rest => (roff, String.ofList cs) :: toStringCallList rest

def toStringCallFns :
    List (List Char × List (BitVec 8) × List (Nat × List Char)) →
      List (String × List (BitVec 8) × List (Nat × String))
  | [] => []
  | (cs, bs, calls) :: rest =>
    (String.ofList cs, bs, toStringCallList calls) :: toStringCallFns rest

def toStringObjectInfo (co : CharObjectInfo) : ObjectInfo :=
  { name := String.ofList co.name
    fns := toStringAssoc co.fns
    callFns := toStringCallFns co.callFns
    relocFns := co.relocFns
    dataSyms := co.dataSyms }

def toStringObjects : List CharObjectInfo → List ObjectInfo
  | [] => []
  | co :: rest => toStringObjectInfo co :: toStringObjects rest

def toStringObjSymbols :
    List (List Char × List (List Char × Nat)) → List (String × List (String × Nat))
  | [] => []
  | (cs, syms) :: rest => (String.ofList cs, toStringSymbols syms) :: toStringObjSymbols rest

def prepareObjSymbols :
    List (List Char × List (List Char × Nat)) → EncSymTable (EncSymTable Nat)
  | [] => []
  | (cs, syms) :: rest => (encodeCharKey cs, prepareCharAssocVal syms) :: prepareObjSymbols rest

/-- Linear 4-byte lockstep check that each instruction word of `fnSlice` matches `bs` with
    direct branch relocations in `resolvedCalls` patched. -/
def checkCallWordsResolved (fnOff : Nat) (resolvedCalls : List (Nat × Nat)) :
    Nat → Nat → List (BitVec 8) → List (BitVec 8) → Bool
  | _, 0, _, _ => true
  | roff, fuel + 1, b0 :: b1 :: b2 :: b3 :: bsRest, c0 :: c1 :: c2 :: c3 :: fnRest =>
    let w := [b0, b1, b2, b3]
    let actual := [c0, c1, c2, c3]
    let expected := match resolvedCalls.find? (·.1 == roff) with
      | some (_, target) => patchBranchBytes w (fnOff + roff) target
      | none => w
    (actual == expected) && checkCallWordsResolved fnOff resolvedCalls (roff + 4) fuel bsRest fnRest
  | _, _, _, _ => false

/-- Resolve every call target in `calls` once against `symbols` and `stubs`. -/
def resolveCallsEnc (symbols stubs : EncSymTable Nat) :
    List (Nat × List Char) → Option (List (Nat × Nat))
  | [] => some []
  | (roff, cs) :: rest =>
    match resolveSymEnc symbols stubs (encodeCharKey cs), resolveCallsEnc symbols stubs rest with
    | some t, some rs => some ((roff, t) :: rs)
    | _, _ => none

/-- Reflected `WordTree` + `natEntryBeq` check for `LinkedImage.honours`. -/
def honoursCharObj (encObjSyms : EncSymTable (EncSymTable Nat))
    (encSymbols encStubs : EncSymTable Nat) (stubChars : List (List Char × Nat))
    (t : WordTree) (n : Nat) (co : CharObjectInfo) : Bool :=
  match lookupEnc (encodeCharKey co.name) encObjSyms with
  | none => false
  | some encSyms =>
    (co.fns.all fun (f, bs) =>
      let fk := encodeCharKey f
      match lookupUniqueEnc fk encSyms with
      | none => false
      | some off =>
        lookupEnc fk encSymbols == some off &&
        off % 4 == 0 && WordTree.sliceBytesChecked t n off bs.length == some bs &&
          stubChars.all fun (_, s) => !(off ≤ s && s < off + bs.length)) &&
    (co.callFns.all fun (f, bs, calls) =>
      let fk := encodeCharKey f
      match lookupUniqueEnc fk encSyms with
      | none => false
      | some off =>
        match WordTree.sliceBytesChecked t n off bs.length, resolveCallsEnc encSymbols encStubs calls with
        | some fnSlice, some resolvedCalls =>
          lookupEnc fk encSymbols == some off &&
          off % 4 == 0 && bs.length % 4 == 0 &&
          (resolvedCalls.all fun (roff, target) => branchInRange (off + roff) target) &&
          checkCallWordsResolved off resolvedCalls 0 (bs.length / 4) bs fnSlice &&
          stubChars.all fun (_, s) => !(off ≤ s && s < off + bs.length)
        | _, _ => false) &&
    co.relocFns.isEmpty && co.dataSyms.isEmpty

/-- Check `honoursCharObj` across all reflected objects, pre-encoding symbol tables once. -/
def checkAllHonoursChar (objSymChars : List (List Char × List (List Char × Nat)))
    (symChars stubChars : List (List Char × Nat))
    (t : WordTree) (n : Nat) (objs : List CharObjectInfo) : Bool :=
  let encObjSyms := prepareObjSymbols objSymChars
  let encSymbols := prepareCharAssocVal symChars
  let encStubs := prepareCharAssocVal stubChars
  objs.all (honoursCharObj encObjSyms encSymbols encStubs stubChars t n)

theorem toStringSymbols_eq_toStringAssoc :
    ∀ (xs : List (List Char × Nat)), toStringSymbols xs = toStringAssoc xs
  | [] => rfl
  | (_, _) :: rest => congrArg _ (toStringSymbols_eq_toStringAssoc rest)

theorem lookupEnc_prepareCharAssocVal {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      lookupEnc (encodeCharKey cs) (prepareCharAssocVal xs) =
        Arm64.Obj.lookup (String.ofList cs) (toStringAssoc xs)
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, lookupEnc, toStringAssoc, Arm64.Obj.lookup, List.find?,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact lookupEnc_prepareCharAssocVal cs rest
    · rfl

theorem lookupEnc_prepareObjSymbols_some (cs : List Char) :
    ∀ (xs : List (List Char × List (List Char × Nat))) {encSyms : EncSymTable Nat},
      lookupEnc (encodeCharKey cs) (prepareObjSymbols xs) = some encSyms →
      ∃ rawSyms,
        encSyms = prepareCharAssocVal rawSyms ∧
        Arm64.Obj.lookup (String.ofList cs) (toStringObjSymbols xs) = some (toStringSymbols rawSyms)
  | [], _, h => nomatch h
  | (cs₀, syms₀) :: rest, _, h => by
    simp only [prepareObjSymbols, lookupEnc, toStringObjSymbols, Arm64.Obj.lookup, List.find?,
      string_beq_eq_natEntryBeq cs₀ cs] at h ⊢
    cases hb : natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · rw [hb] at h
      exact lookupEnc_prepareObjSymbols_some cs rest h
    · simp only [hb, ↓reduceIte, Option.some.injEq] at h
      exact ⟨syms₀, h.symm, rfl⟩

private theorem filterEnc_map_snd {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      (filterEnc (encodeCharKey cs) (prepareCharAssocVal xs)).map Prod.snd =
        ((toStringAssoc xs).filter (·.1 == String.ofList cs)).map Prod.snd
  | [] => rfl
  | (cs₀, v) :: rest => by
    simp only [prepareCharAssocVal, filterEnc, toStringAssoc, List.filter,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact filterEnc_map_snd cs rest
    · simp only [↓reduceIte, List.map_cons, filterEnc_map_snd cs rest]

private theorem lookupUniqueEnc_of_map_snd_eq {α : Type}
    (ys : List ((Nat × List Nat) × α)) (zs : List (String × α))
    (h : ys.map Prod.snd = zs.map Prod.snd) :
    lookupUniqueEnc.match_1 (fun _ => Option α) ys (fun _ v => some v) (fun _ => none) =
    Arm64.Obj.lookupUnique.match_1 (fun _ => Option α) zs (fun _ v => some v) (fun _ => none) := by
  rcases ys with _ | ⟨⟨_, v₁⟩, _ | _⟩ <;>
    rcases zs with _ | ⟨⟨_, v₂⟩, _ | _⟩ <;>
    simp_all <;> rfl

theorem lookupUniqueEnc_prepareCharAssocVal {α : Type} (cs : List Char)
    (xs : List (List Char × α)) :
    lookupUniqueEnc (encodeCharKey cs) (prepareCharAssocVal xs) =
      Arm64.Obj.lookupUnique (String.ofList cs) (toStringAssoc xs) :=
  lookupUniqueEnc_of_map_snd_eq _ _ (filterEnc_map_snd cs xs)

theorem filterEnc_length {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      ((toStringAssoc xs).filter (·.1 == String.ofList cs)).length =
        (filterEnc (encodeCharKey cs) (prepareCharAssocVal xs)).length
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, filterEnc, toStringAssoc, List.filter,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact filterEnc_length cs rest
    · simp only [↓reduceIte, List.length_cons, filterEnc_length cs rest]

theorem anyEnc_prepareCharAssocVal {α : Type} (cs : List Char) :
    ∀ (xs : List (List Char × α)),
      anyEnc (encodeCharKey cs) (prepareCharAssocVal xs) =
        (toStringAssoc xs).any (·.1 == String.ofList cs)
  | [] => rfl
  | (cs₀, _) :: rest => by
    simp only [prepareCharAssocVal, anyEnc, toStringAssoc, List.any_cons,
      string_beq_eq_natEntryBeq cs₀ cs]
    cases natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs)
    · exact anyEnc_prepareCharAssocVal cs rest
    · rfl

theorem lookup_eq_lookupEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookup name tbl = lookupEnc (encodeCharKey cs) enc := by
  rw [htbl, hname, ← lookupEnc_prepareCharAssocVal, heq]

theorem lookupSymbols_eq_lookupEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookup name tbl = lookupEnc (encodeCharKey cs) enc := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact lookup_eq_lookupEnc htbl heq hname

theorem lookupUnique_eq_lookupUniqueEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookupUnique name tbl = lookupUniqueEnc (encodeCharKey cs) enc := by
  rw [htbl, hname, ← lookupUniqueEnc_prepareCharAssocVal, heq]

theorem lookupUniqueSymbols_eq_lookupUniqueEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookupUnique name tbl = lookupUniqueEnc (encodeCharKey cs) enc := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact lookupUnique_eq_lookupUniqueEnc htbl heq hname

theorem filter_length_eq_filterEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    (tbl.filter (·.1 == name)).length = (filterEnc (encodeCharKey cs) enc).length := by
  rw [htbl, hname, filterEnc_length, heq]

theorem filterSymbols_length_eq_filterEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    (tbl.filter (·.1 == name)).length = (filterEnc (encodeCharKey cs) enc).length := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact filter_length_eq_filterEnc htbl heq hname

theorem any_eq_anyEnc {α : Type} {tbl : List (String × α)}
    {xs : List (List Char × α)} {enc : EncSymTable α}
    (htbl : tbl = toStringAssoc xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    tbl.any (·.1 == name) = anyEnc (encodeCharKey cs) enc := by
  rw [htbl, hname, ← anyEnc_prepareCharAssocVal, heq]

theorem anySymbols_eq_anyEnc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    tbl.any (·.1 == name) = anyEnc (encodeCharKey cs) enc := by
  rw [toStringSymbols_eq_toStringAssoc] at htbl
  exact any_eq_anyEnc htbl heq hname

theorem lookup_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookup name tbl = lookupEnc (encodeCharKey cs) (prepareCharAssocVal xs) := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, lookupEnc_prepareCharAssocVal]

theorem lookupUnique_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    Arm64.Obj.lookupUnique name tbl = lookupUniqueEnc (encodeCharKey cs) (prepareCharAssocVal xs) := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, lookupUniqueEnc_prepareCharAssocVal]

theorem filter_length_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    (tbl.filter (·.1 == name)).length = (filterEnc (encodeCharKey cs) (prepareCharAssocVal xs)).length := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, filterEnc_length]

theorem any_prepareCharSymbols {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)}
    (htbl : tbl = toStringSymbols xs)
    {name : String} {cs : List Char} (hname : name = String.ofList cs) :
    tbl.any (·.1 == name) = anyEnc (encodeCharKey cs) (prepareCharAssocVal xs) := by
  rw [htbl, toStringSymbols_eq_toStringAssoc, hname, anyEnc_prepareCharAssocVal]

theorem toStringSymbols_getElem?_of_some :
    ∀ (xs : List (List Char × Nat)) (k : Nat) {cs : List Char} {off : Nat},
      xs[k]? = some (cs, off) →
      (toStringSymbols xs)[k]? = some (String.ofList cs, off)
  | [], _, _, _, h => nomatch h
  | (_, _) :: _, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | _ :: rest, k + 1, _, _, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa only [toStringSymbols, List.getElem?_cons_succ] using
      toStringSymbols_getElem?_of_some rest k h

theorem fnOff_of_allFresh_chars (prog : Arm64.Program) (charSyms : List (List Char × Nat))
    (hsyms : prog.symbols = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    prog.fnOff name = off :=
  fnOff_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem fnOff_of_stub_chars (prog : Arm64.Program) (charSyms stubSyms : List (List Char × Nat))
    (hsyms : prog.symbols = toStringSymbols charSyms)
    (hstubs : prog.stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    prog.fnOff name = off :=
  fnOff_of_stub charSyms stubSyms hsyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem lookup_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookup name syms = some off :=
  lookup_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem lookupUnique_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookupUnique name syms = some off :=
  lookupUnique_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem filter_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    syms.filter (·.1 == name) = [(name, off)] :=
  filter_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem filter_length_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    (syms.filter (·.1 == name)).length = 1 :=
  filter_length_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem any_of_allFresh_chars {syms : List (String × Nat)}
    (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    syms.any (·.1 == name) = true :=
  any_of_allFresh charSyms hsyms hfresh k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem lookup_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookup name stubs = some off :=
  lookup_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem lookupUnique_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookupUnique name stubs = some off :=
  lookupUnique_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem filter_length_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    (stubs.filter (·.1 == name)).length = 1 :=
  filter_length_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem any_stub_of_wf_chars {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    stubs.any (·.1 == name) = true :=
  any_stub_of_wf charSyms stubSyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem lookup_symbols_none_of_stub_chars {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    Arm64.Obj.lookup name syms = none :=
  lookup_symbols_none_of_stub charSyms stubSyms hsyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem any_symbols_false_of_stub_chars {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : stubSyms[k]? = some (cs, off)) :
    syms.any (·.1 == name) = false :=
  any_symbols_false_of_stub charSyms stubSyms hsyms hstubs hwf k
    (by rw [hstubs, hname]; exact toStringSymbols_getElem?_of_some stubSyms k hk)

theorem any_stubs_false_of_symbol_chars {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hk : charSyms[k]? = some (cs, off)) :
    stubs.any (·.1 == name) = false :=
  any_stubs_false_of_symbol charSyms stubSyms hsyms hstubs hwf k
    (by rw [hsyms, hname]; exact toStringSymbols_getElem?_of_some charSyms k hk)

theorem resolveSymEnc_eq {li : LinkedImage} {symChars stubChars : List (List Char × Nat)}
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars)
    (cs : List Char) :
    resolveSymEnc (prepareCharAssocVal symChars) (prepareCharAssocVal stubChars) (encodeCharKey cs) =
      li.resolveSym (String.ofList cs) := by
  simp only [resolveSymEnc, LinkedImage.resolveSym, hsyms, hstubs,
    toStringSymbols_eq_toStringAssoc, lookupEnc_prepareCharAssocVal]

theorem all_toStringSymbols_snd (P : Nat → Bool) :
    ∀ (xs : List (List Char × Nat)),
      (toStringSymbols xs).all (fun (_, s) => P s) = xs.all (fun (_, s) => P s)
  | [] => rfl
  | (_, _) :: rest => by
    simp only [toStringSymbols, List.all_cons, all_toStringSymbols_snd P rest]

theorem bytesAt_of_sliceBytesChecked {li : LinkedImage} {t : WordTree} {n off : Nat} {bs : List (BitVec 8)}
    (hcode : li.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hs : (WordTree.sliceBytesChecked t n off bs.length == some bs) = true) :
    bytesAt li.code off bs = true := by
  have hs' : WordTree.sliceBytesChecked t n off bs.length = some bs := beq_iff_eq.mp hs
  have hbounds := WordTree.sliceBytesChecked_bounds hs'
  have hlen : t.toBytes.length = 4 * n := WordTree.length_toBytes_of_checkSize? hwf
  have heq := WordTree.sliceBytesChecked_eq hwf hs'
  unfold bytesAt
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hcode, heq]
  exact ⟨by omega, rfl⟩

theorem resolveCallsEnc_spec {li : LinkedImage} {symChars stubChars : List (List Char × Nat)}
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars) (off : Nat) :
    ∀ (calls : List (Nat × List Char)) {resolvedCalls : List (Nat × Nat)},
      resolveCallsEnc (prepareCharAssocVal symChars) (prepareCharAssocVal stubChars) calls =
        some resolvedCalls →
      ((resolvedCalls.all fun (roff, target) => branchInRange (off + roff) target) =
        ((toStringCallList calls).all fun (roff, sym) =>
          match li.resolveSym sym with
          | some t => branchInRange (off + roff) t
          | none => false)) ∧
      ∀ (w : List (BitVec 8)) (x : Nat),
        (match resolvedCalls.find? (·.1 == x) with
         | some (_, target) => patchBranchBytes w (off + x) target
         | none => w) =
        (match (toStringCallList calls).find? (·.1 == x) with
         | some (_, sym) => patchBranchBytes w (off + x) ((li.resolveSym sym).getD 0)
         | none => w)
  | [], _, hres => by
    simp only [resolveCallsEnc, Option.some.injEq] at hres
    subst hres
    exact ⟨rfl, fun _ _ => rfl⟩
  | (roff, cs) :: rest, _, hres => by
    simp only [resolveCallsEnc, resolveSymEnc_eq hsyms hstubs cs] at hres
    split at hres <;> try contradiction
    rename_i t rs ht hrest
    simp only [Option.some.injEq] at hres
    subst hres
    obtain ⟨ih_all, ih_find⟩ := resolveCallsEnc_spec hsyms hstubs off rest hrest
    refine ⟨?_, fun w x => ?_⟩
    · simp only [toStringCallList, List.all_cons, ht, ih_all]
    · simp only [toStringCallList, List.find?]
      cases roff == x
      · exact ih_find w x
      · simp only [ht, Option.getD_some]

private theorem drop_four_mul_succ {α : Type} (x0 x1 x2 x3 : α) (xs : List α) (j : Nat) :
    (x0 :: x1 :: x2 :: x3 :: xs).drop (4 * (j + 1)) = xs.drop (4 * j) := by
  have : 4 * (j + 1) = 4 + 4 * j := by omega
  rw [this, ← List.drop_drop]
  rfl

theorem checkCallWordsResolved_spec (fnOff : Nat) (resolvedCalls : List (Nat × Nat)) :
    ∀ (m roff : Nat) (bs fnSlice : List (BitVec 8)),
      checkCallWordsResolved fnOff resolvedCalls roff m bs fnSlice = true →
      ∀ (j : Nat), j < m →
        let w := (bs.drop (4 * j)).take 4
        let actual := (fnSlice.drop (4 * j)).take 4
        let expected := match resolvedCalls.find? (·.1 == roff + 4 * j) with
          | some (_, target) => patchBranchBytes w (fnOff + (roff + 4 * j)) target
          | none => w
        (actual == expected) = true
  | 0, _, _, _, _, j, hj => by omega
  | m + 1, roff, bs, fnSlice, h, j, hj => by
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bsRest⟩⟩⟩⟩ <;> try contradiction
    rcases fnSlice with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, fnRest⟩⟩⟩⟩ <;> try contradiction
    simp only [checkCallWordsResolved, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero, List.drop_zero, List.take] using h.1
    | succ j' =>
      have := checkCallWordsResolved_spec fnOff resolvedCalls m (roff + 4) bsRest fnRest h.2 j' (by omega)
      have hadd : roff + 4 * (j' + 1) = (roff + 4) + 4 * j' := by omega
      rw [drop_four_mul_succ b0 b1 b2 b3 bsRest j',
          drop_four_mul_succ c0 c1 c2 c3 fnRest j', hadd]
      exact this

private theorem drop_take_drop_take_four (xs : List (BitVec 8)) (off len j : Nat)
    (hj : 4 * j + 4 ≤ len) :
    (((xs.drop off).take len).drop (4 * j)).take 4 = (xs.drop (off + 4 * j)).take 4 := by
  rw [List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

private theorem all_toStringAssoc_fns {li : LinkedImage} {t : WordTree} {n : Nat}
    {rawSyms symChars stubChars : List (List Char × Nat)}
    (hcode : li.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars) :
    ∀ (fns : List (List Char × List (BitVec 8))),
      (fns.all fun (f, bs) =>
        let fk := encodeCharKey f
        match lookupUniqueEnc fk (prepareCharAssocVal rawSyms) with
        | none => false
        | some off =>
          lookupEnc fk (prepareCharAssocVal symChars) == some off &&
          off % 4 == 0 && WordTree.sliceBytesChecked t n off bs.length == some bs &&
            stubChars.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true →
      ((toStringAssoc fns).all fun (f, bs) =>
        match Arm64.Obj.lookupUnique f (toStringSymbols rawSyms) with
        | none => false
        | some off =>
          Arm64.Obj.lookup f li.symbols == some off &&
          off % 4 == 0 && bytesAt li.code off bs &&
            li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true
  | [], _ => rfl
  | (cs, bs) :: rest, h => by
    simp only [toStringAssoc, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, all_toStringAssoc_fns hcode hwf hsyms hstubs rest h.2⟩
    have h1 := h.1
    rw [lookupUniqueEnc_prepareCharAssocVal, ← toStringSymbols_eq_toStringAssoc] at h1
    cases hlu : Arm64.Obj.lookupUnique (String.ofList cs) (toStringSymbols rawSyms) with
    | none => rw [hlu] at h1; nomatch h1
    | some off =>
      rw [hlu] at h1
      dsimp only at h1
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1 ⊢
      rw [lookupEnc_prepareCharAssocVal, ← toStringSymbols_eq_toStringAssoc, ← hsyms] at h1
      rw [hstubs, all_toStringSymbols_snd (fun s => !(off ≤ s && s < off + bs.length)) stubChars]
      exact ⟨⟨⟨h1.1.1.1, h1.1.1.2⟩, bytesAt_of_sliceBytesChecked hcode hwf h1.1.2⟩, h1.2⟩

private theorem all_toStringCallFns {li : LinkedImage} {t : WordTree} {n : Nat}
    {rawSyms symChars stubChars : List (List Char × Nat)}
    (hcode : li.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars) :
    ∀ (callFns : List (List Char × List (BitVec 8) × List (Nat × List Char))),
      (callFns.all fun (f, bs, calls) =>
        let fk := encodeCharKey f
        match lookupUniqueEnc fk (prepareCharAssocVal rawSyms) with
        | none => false
        | some off =>
          match WordTree.sliceBytesChecked t n off bs.length,
                resolveCallsEnc (prepareCharAssocVal symChars) (prepareCharAssocVal stubChars) calls with
          | some fnSlice, some resolvedCalls =>
            lookupEnc fk (prepareCharAssocVal symChars) == some off &&
            off % 4 == 0 && bs.length % 4 == 0 &&
            (resolvedCalls.all fun (roff, target) => branchInRange (off + roff) target) &&
            checkCallWordsResolved off resolvedCalls 0 (bs.length / 4) bs fnSlice &&
            stubChars.all fun (_, s) => !(off ≤ s && s < off + bs.length)
          | _, _ => false) = true →
      ((toStringCallFns callFns).all fun (f, bs, calls) =>
        match Arm64.Obj.lookupUnique f (toStringSymbols rawSyms) with
        | none => false
        | some off =>
          Arm64.Obj.lookup f li.symbols == some off &&
          off % 4 == 0 && bs.length % 4 == 0 && off + bs.length ≤ li.code.length &&
          (calls.all fun (roff, sym) =>
            match li.resolveSym sym with
            | some t => branchInRange (off + roff) t
            | none => false) &&
          ((List.range (bs.length / 4)).all fun j =>
            let w := (bs.drop (4 * j)).take 4
            let expected := match calls.find? (·.1 == 4 * j) with
              | some (_, sym) => patchBranchBytes w (off + 4 * j) ((li.resolveSym sym).getD 0)
              | none => w
            (li.code.drop (off + 4 * j)).take 4 == expected) &&
          li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true
  | [], _ => rfl
  | (cs, bs, calls) :: rest, h => by
    simp only [toStringCallFns, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, all_toStringCallFns hcode hwf hsyms hstubs rest h.2⟩
    have h1 := h.1
    rw [lookupUniqueEnc_prepareCharAssocVal, ← toStringSymbols_eq_toStringAssoc] at h1
    cases hlu : Arm64.Obj.lookupUnique (String.ofList cs) (toStringSymbols rawSyms) with
    | none => rw [hlu] at h1; nomatch h1
    | some off =>
      rw [hlu] at h1
      dsimp only at h1
      cases hslice : WordTree.sliceBytesChecked t n off bs.length with
      | none => rw [hslice] at h1; nomatch h1
      | some fnSlice =>
        cases hres : resolveCallsEnc (prepareCharAssocVal symChars) (prepareCharAssocVal stubChars) calls with
        | none => rw [hslice, hres] at h1; nomatch h1
        | some resolvedCalls =>
          rw [hslice, hres] at h1
          dsimp only at h1
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at h1
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true]
          rw [lookupEnc_prepareCharAssocVal, ← toStringSymbols_eq_toStringAssoc, ← hsyms] at h1
          have hbounds := WordTree.sliceBytesChecked_bounds hslice
          have hcode_len : li.code.length = 4 * n := by
            rw [hcode, WordTree.length_toBytes_of_checkSize? hwf]
          have hslice_eq : (li.code.drop off).take bs.length = fnSlice := by
            rw [hcode, WordTree.sliceBytesChecked_eq hwf hslice]
          obtain ⟨hcalls_all, hcalls_find⟩ := resolveCallsEnc_spec hsyms hstubs off calls hres
          rw [hstubs, all_toStringSymbols_snd (fun s => !(off ≤ s && s < off + bs.length)) stubChars, ← hcalls_all]
          refine ⟨⟨⟨⟨⟨⟨h1.1.1.1.1.1, h1.1.1.1.1.2⟩, h1.1.1.1.2⟩,
            decide_eq_true (by omega)⟩, h1.1.1.2⟩, ?_⟩, h1.2⟩
          rw [List.all_eq_true]
          intro j hj
          have hj_lt : j < bs.length / 4 := List.mem_range.mp hj
          have hj_word := checkCallWordsResolved_spec off resolvedCalls (bs.length / 4) 0 bs fnSlice h1.1.2 j hj_lt
          simp only [Nat.zero_add] at hj_word
          rw [← hslice_eq, drop_take_drop_take_four li.code off bs.length j (by omega)] at hj_word
          rw [← hcalls_find ((bs.drop (4 * j)).take 4) (4 * j)]
          exact hj_word

theorem honoursCharObj_imp_honours {li : LinkedImage} {t : WordTree} {n : Nat}
    {objSymChars : List (List Char × List (List Char × Nat))}
    {symChars stubChars : List (List Char × Nat)}
    (hcode : li.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars)
    (hobjSyms : li.objSymbols = toStringObjSymbols objSymChars)
    (co : CharObjectInfo)
    (h : honoursCharObj (prepareObjSymbols objSymChars) (prepareCharAssocVal symChars)
      (prepareCharAssocVal stubChars) stubChars t n co = true) :
    li.honours (toStringObjectInfo co) = true := by
  unfold honoursCharObj at h
  cases hlu : lookupEnc (encodeCharKey co.name) (prepareObjSymbols objSymChars) with
  | none => rw [hlu] at h; nomatch h
  | some encSyms =>
    rw [hlu] at h
    obtain ⟨rawSyms, rfl, hobj_lu⟩ := lookupEnc_prepareObjSymbols_some co.name objSymChars hlu
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    rcases h with ⟨⟨⟨hfns, hcallFns⟩, hreloc⟩, hdata⟩
    unfold LinkedImage.honours toStringObjectInfo
    simp only [hobjSyms, hobj_lu, hreloc, hdata, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨all_toStringAssoc_fns hcode hwf hsyms hstubs co.fns hfns,
      all_toStringCallFns hcode hwf hsyms hstubs co.callFns hcallFns⟩

theorem checkAllHonoursChar_imp_all_honours {li : LinkedImage} {t : WordTree} {n : Nat}
    {objSymChars : List (List Char × List (List Char × Nat))}
    {symChars stubChars : List (List Char × Nat)}
    (hcode : li.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars)
    (hobjSyms : li.objSymbols = toStringObjSymbols objSymChars) :
    ∀ (charObjs : List CharObjectInfo),
      checkAllHonoursChar objSymChars symChars stubChars t n charObjs = true →
      (toStringObjects charObjs).all li.honours = true
  | [], _ => rfl
  | co :: rest, h => by
    simp only [checkAllHonoursChar, toStringObjects, List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨honoursCharObj_imp_honours hcode hwf hsyms hstubs hobjSyms co h.1,
      checkAllHonoursChar_imp_all_honours hcode hwf hsyms hstubs hobjSyms rest h.2⟩

/-- Prove `∃ img, Obj.Loads li img ∧ img.base = b` in the kernel via `WordTree` instruction slicing
    and `natEntryBeq` symbol reflection (avoiding `List.drop` on `li.code`, splices on `li.data`,
    and kernel `String == String` evaluations). -/
theorem exists_loads_of_tree {li : LinkedImage} {b : BitVec 64}
    {t : WordTree} {n codeLen dataLen : Nat}
    {symChars stubChars : List (List Char × Nat)}
    {objSymChars : List (List Char × List (List Char × Nat))}
    {charObjs : List CharObjectInfo}
    (hcode : li.code = t.toBytes)
    (htree : t.checkSize? = some n)
    (hcode_len : 4 * n = codeLen)
    (hdata_len : li.data.length = dataLen)
    (hsyms : li.symbols = toStringSymbols symChars)
    (hstubs : li.stubs = toStringSymbols stubChars)
    (hobjSyms : li.objSymbols = toStringObjSymbols objSymChars)
    (hobjs : li.objects = toStringObjects charObjs)
    (hal : decide (b.toNat % pageSize = 0) = true)
    (hwrap : decide (b.toNat + li.gotOff + 8 * li.got.length ≤ 2 ^ 64) = true)
    (hlayout : LinkedImage.wellFormedLayout li codeLen dataLen = true)
    (hhonours : checkAllHonoursChar objSymChars symChars stubChars t n charObjs = true)
    (hrelocs : li.relocs.all (DataReloc.validAt b) = true) :
    ∃ img, Arm64.Obj.Loads li img ∧ img.base = b := by
  have hc_len : li.code.length = codeLen := by
    rw [hcode, WordTree.length_toBytes_of_checkSize? htree, hcode_len]
  have hh_all : li.objects.all li.honours = true := by
    rw [hobjs]
    exact checkAllHonoursChar_imp_all_honours hcode htree hsyms hstubs hobjSyms charObjs hhonours
  have hwf : li.wellFormed = true :=
    LinkedImage.wellFormed_of_layout_and_honours hc_len hdata_len hlayout hh_all
  obtain ⟨data, hfold⟩ := exists_foldlM_dataReloc_of_all_validAt li.relocs
    (li.data ++ List.replicate li.bss 0) hrelocs
  have hal' : (b.toNat % pageSize != 0) = false := by
    rw [bne_eq_false_iff_eq]; exact of_decide_eq_true hal
  have hwrap' : ¬ (b.toNat + li.gotOff + 8 * li.got.length > 2 ^ 64) := by
    have := of_decide_eq_true hwrap; omega
  refine exists_loads_of_isSome ?_
  unfold LinkedImage.load
  simp only [bind, Except.bind, pure, Except.pure, hal', Bool.false_eq_true, ↓reduceIte,
    hwrap', hwf, Bool.not_true, hfold, Except.toOption, Option.isSome_some]

open Lean Elab Term Meta in
private meta def extractStrVal (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  if let .lit (.strVal s) := (← withTransparency .all (whnf e)) then return s
  throwError "expected string literal, got {e}"

open Lean Elab Term Meta in
private meta def mkListExpr (elemTy : Expr) (elems : Array Expr) : Expr := Id.run do
  let nilExpr := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  let mut acc := nilExpr
  for i in [0 : elems.size] do
    acc := mkApp2 consFn elems[elems.size - 1 - i]! acc
  return acc

open Lean Elab Term Meta in
private meta def elabSymListExpr (listExpr : Expr) : MetaM Expr := do
  let entries ← listElemsWhnf listExpr
  let charListType := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
  let natType := Lean.mkConst ``Nat
  let prodType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType natType
  let prodMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType natType
  let mut out : Array Expr := #[]
  for pairExpr in entries do
    let pairExpr ← if pairExpr.isAppOfArity ``Prod.mk 4 then pure pairExpr
      else withTransparency .all (whnf pairExpr)
    let s ← extractStrVal (pairExpr.getArg! 2)
    let offExpr := pairExpr.getArg! 3
    out := out.push (mkApp2 prodMk (toExpr s.toList) offExpr)
  return mkListExpr prodType out

open Lean Elab Term Meta in
/-- Reflect `<liId>.objSymbols` into `List (List Char × List (List Char × Nat))` at elaboration time. -/
scoped elab "obj_syms_chars_of% " liId:ident : term => do
  let c ← realizeGlobalConstNoOverload liId
  let entries ← listElemsWhnf (mkApp (Lean.mkConst ``LinkedImage.objSymbols) (Lean.mkConst c))
  let charListType := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
  let natType := Lean.mkConst ``Nat
  let innerProdType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType natType
  let innerListType := mkApp (Lean.mkConst ``List [Level.zero]) innerProdType
  let outerProdType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType innerListType
  let outerProdMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType innerListType
  let mut out : Array Expr := #[]
  for pairExpr in entries do
    let pairExpr ← if pairExpr.isAppOfArity ``Prod.mk 4 then pure pairExpr
      else withTransparency .all (whnf pairExpr)
    let s ← extractStrVal (pairExpr.getArg! 2)
    let symsExpr ← elabSymListExpr (pairExpr.getArg! 3)
    out := out.push (mkApp2 outerProdMk (toExpr s.toList) symsExpr)
  return mkListExpr outerProdType out

open Lean Elab Term Meta in
/-- Reflect `<liId>.objects` into `List CharObjectInfo` at elaboration time. -/
scoped elab "char_objects_of% " liId:ident : term => do
  let c ← realizeGlobalConstNoOverload liId
  let objExprs ← listElemsWhnf (mkApp (Lean.mkConst ``LinkedImage.objects) (Lean.mkConst c))
  let charListType := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
  let natType := Lean.mkConst ``Nat
  let bv8ListType := mkApp (Lean.mkConst ``List [Level.zero]) (mkApp (Lean.mkConst ``BitVec) (toExpr (8 : Nat)))
  let fnProdType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType bv8ListType
  let fnProdMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType bv8ListType
  let callPairType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natType charListType
  let callPairMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) natType charListType
  let callListType := mkApp (Lean.mkConst ``List [Level.zero]) callPairType
  let callFnInnerType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) bv8ListType callListType
  let callFnInnerMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) bv8ListType callListType
  let callFnType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType callFnInnerType
  let callFnMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType callFnInnerType
  let mut objsOut : Array Expr := #[]
  for objExpr in objExprs do
    let objWhnf ← withTransparency .all (whnf objExpr)
    let nameStr ← extractStrVal (objWhnf.getArg! 0)
    let fnsExpr := objWhnf.getArg! 1
    let callFnsExpr := objWhnf.getArg! 2
    let relocFnsExpr := objWhnf.getArg! 3
    let dataSymsExpr := objWhnf.getArg! 4
    let fnEntries ← listElemsWhnf fnsExpr
    let mut fnsOut : Array Expr := #[]
    for fnE in fnEntries do
      let fnE ← if fnE.isAppOfArity ``Prod.mk 4 then pure fnE else withTransparency .all (whnf fnE)
      let fStr ← extractStrVal (fnE.getArg! 2)
      let bsExpr := fnE.getArg! 3
      fnsOut := fnsOut.push (mkApp2 fnProdMk (toExpr fStr.toList) bsExpr)
    let callFnEntries ← listElemsWhnf callFnsExpr
    let mut callFnsOut : Array Expr := #[]
    for cfnE in callFnEntries do
      let cfnE ← if cfnE.isAppOfArity ``Prod.mk 4 then pure cfnE else withTransparency .all (whnf cfnE)
      let fStr ← extractStrVal (cfnE.getArg! 2)
      let restE ← if (cfnE.getArg! 3).isAppOfArity ``Prod.mk 4 then pure (cfnE.getArg! 3)
        else withTransparency .all (whnf (cfnE.getArg! 3))
      let bsExpr := restE.getArg! 2
      let callsExpr := restE.getArg! 3
      let callEntries ← listElemsWhnf callsExpr
      let mut callsOut : Array Expr := #[]
      for callE in callEntries do
        let callE ← if callE.isAppOfArity ``Prod.mk 4 then pure callE else withTransparency .all (whnf callE)
        let roffExpr := callE.getArg! 2
        let symStr ← extractStrVal (callE.getArg! 3)
        callsOut := callsOut.push (mkApp2 callPairMk roffExpr (toExpr symStr.toList))
      let callsListE := mkListExpr callPairType callsOut
      callFnsOut := callFnsOut.push (mkApp2 callFnMk (toExpr fStr.toList) (mkApp2 callFnInnerMk bsExpr callsListE))
    let coExpr := mkApp5 (Lean.mkConst ``CharObjectInfo.mk)
      (toExpr nameStr.toList)
      (mkListExpr fnProdType fnsOut)
      (mkListExpr callFnType callFnsOut)
      relocFnsExpr
      dataSymsExpr
    objsOut := objsOut.push coExpr
  return mkListExpr (Lean.mkConst ``CharObjectInfo) objsOut

open Lean Elab Term Meta in
/-- Build a `List (List Char × Nat)` symbol table from a `List (String × Nat)` expression
    at elaboration time, reusing the offset `Expr`s. -/
meta def elabCharSymTableExpr (listExpr : Expr) : MetaM Expr := do
  let entries ← listElemsWhnf listExpr
  let natType := Lean.mkConst ``Nat
  let charListType := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
  let entryType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType natType
  let entryMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType natType
  let mut out : Array Expr := #[]
  for pairExpr in entries do
    let pairExpr ← if pairExpr.isAppOfArity ``Prod.mk 4 then pure pairExpr
      else withTransparency .all (whnf pairExpr)
    unless pairExpr.isAppOfArity ``Prod.mk 4 do
      throwError "expected `Prod.mk` entry in symbol table, got {pairExpr}"
    let s ← extractStrVal (pairExpr.getArg! 2)
    let offExpr := pairExpr.getArg! 3
    out := out.push (mkApp2 entryMk (toExpr s.toList) offExpr)
  return mkListExpr entryType out

open Lean Elab Term Meta in
/-- Build a pre-encoded `EncSymTable Nat` (`List ((Nat × List Nat) × Nat)`) from a
    `List (String × Nat)` expression at elaboration time, reusing the offset `Expr`s. -/
meta def elabEncSymTableExpr (listExpr : Expr) : MetaM Expr := do
  let entries ← listElemsWhnf listExpr
  let natType := Lean.mkConst ``Nat
  let natListType := mkApp (Lean.mkConst ``List [Level.zero]) natType
  let keyType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natType natListType
  let keyMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) natType natListType
  let entryType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) keyType natType
  let entryMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) keyType natType
  let mut out : Array Expr := #[]
  for pairExpr in entries do
    let pairExpr ← if pairExpr.isAppOfArity ``Prod.mk 4 then pure pairExpr
      else withTransparency .all (whnf pairExpr)
    unless pairExpr.isAppOfArity ``Prod.mk 4 do
      throwError "expected `Prod.mk` entry in symbol table, got {pairExpr}"
    let s ← extractStrVal (pairExpr.getArg! 2)
    let offExpr := pairExpr.getArg! 3
    let cs := s.toList
    let keyExpr := mkApp2 keyMk (toExpr cs.length) (toExpr (cs.map Char.toNat))
    out := out.push (mkApp2 entryMk keyExpr offExpr)
  return mkListExpr entryType out

open Lean Elab Term Meta in
private meta def elabSymEncOfConst (id : Ident) (isStubs : Bool) : TermElabM Expr := do
  let c ← realizeGlobalConstNoOverload id
  let cExpr := Lean.mkConst c
  let cTy ← instantiateMVars (← inferType cExpr)
  let field :=
    if cTy.isConstOf ``Arm64.Obj.LinkedImage then
      if isStubs then ``Arm64.Obj.LinkedImage.stubs else ``Arm64.Obj.LinkedImage.symbols
    else
      if isStubs then ``Arm64.Program.stubs else ``Arm64.Program.symbols
  elabEncSymTableExpr (mkApp (Lean.mkConst field) cExpr)

open Lean Elab Term Meta in
/-- Build the pre-encoded `EncSymTable Nat` symbol table from `<prog>.symbols` (or `<li>.symbols`)
    at elaboration time, matching `prepareCharAssocVal <prog>_symChars`. -/
elab "sym_enc_of% " progId:ident : term => elabSymEncOfConst progId false

open Lean Elab Term Meta in
/-- Build the pre-encoded `EncSymTable Nat` extern-stub table from `<prog>.stubs` (or `<li>.stubs`)
    at elaboration time, matching `prepareCharAssocVal <prog>_stubChars`. -/
elab "stub_enc_of% " progId:ident : term => elabSymEncOfConst progId true

open Lean Elab Term Meta in
/-- Build the pre-encoded `EncSymTable Nat` from any `List (String × Nat)` table expression. -/
elab "enc_assoc_of% " tbl:term:arg : term => do
  let e ← elabTerm tbl none
  elabEncSymTableExpr (← instantiateMVars e)

theorem lookup_map_externData (b : BitVec 64) (sym : String) :
    ∀ (xs : List (String × Nat × Nat)),
      Arm64.Obj.lookup sym (xs.map fun (x, o, n) => (x, b + BitVec.ofNat 64 o, n)) =
        (Arm64.Obj.lookup sym xs).map (fun (o, n) => (b + BitVec.ofNat 64 o, n))
  | [] => rfl
  | (x, o, n) :: rest => by
    simp only [List.map_cons, Arm64.Obj.lookup, List.find?]
    cases (x == sym)
    · exact lookup_map_externData b sym rest
    · rfl

theorem Image.symtab_of_lookup_symbols {img : Image} {objName sym : String} {off : Nat}
    (hobj : Arm64.Obj.lookup objName img.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym img.symbols = some off) :
    img.symtab objName sym = some (img.base + BitVec.ofNat 64 off) := by
  simp [Image.symtab, hobj, hsym, Option.orElse]

theorem Image.symtab_eq_of_lookup_symbols {img : Image} {objName sym : String}
    {off : Nat} {addr : BitVec 64}
    (hobj : Arm64.Obj.lookup objName img.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym img.symbols = some off)
    (haddr : img.base + BitVec.ofNat 64 off = addr) :
    img.symtab objName sym = some addr := by
  rw [Image.symtab_of_lookup_symbols hobj hsym, haddr]

theorem Image.symtab_of_lookup_stubs {img : Image} {objName sym : String} {off : Nat}
    (hobj : Arm64.Obj.lookup objName img.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym img.symbols = none)
    (hstub : Arm64.Obj.lookup sym img.stubs = some off) :
    img.symtab objName sym = some (img.base + BitVec.ofNat 64 off) := by
  simp [Image.symtab, hobj, hsym, hstub, Option.orElse]

theorem Image.symtab_eq_of_lookup_stubs {img : Image} {objName sym : String}
    {off : Nat} {addr : BitVec 64}
    (hobj : Arm64.Obj.lookup objName img.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym img.symbols = none)
    (hstub : Arm64.Obj.lookup sym img.stubs = some off)
    (haddr : img.base + BitVec.ofNat 64 off = addr) :
    img.symtab objName sym = some addr := by
  rw [Image.symtab_of_lookup_stubs hobj hsym hstub, haddr]

theorem Image.symtab_of_lookup_externData {img : Image} {objName sym : String}
    {addr : BitVec 64} {sz : Nat}
    (hobj : Arm64.Obj.lookup objName img.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym img.symbols = none)
    (hstub : Arm64.Obj.lookup sym img.stubs = none)
    (hext : Arm64.Obj.lookup sym img.externData = some (addr, sz)) :
    img.symtab objName sym = some addr := by
  simp [Image.symtab, hobj, hsym, hstub, hext, Option.orElse, HOrElse.hOrElse, OrElse.orElse]

theorem Loads.symtab_of_lookup_symbols {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img) {objName sym : String} {off : Nat}
    (hobj : Arm64.Obj.lookup objName li.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym li.symbols = some off) :
    img.symtab objName sym = some (img.base + BitVec.ofNat 64 off) := by
  obtain ⟨_, _, hsyms, _, hobjSyms, _, _⟩ := load_ok h
  exact Image.symtab_of_lookup_symbols (by rw [hobjSyms, hobj]) (by rw [hsyms, hsym])

theorem Loads.symtab_eq_of_lookup_symbols {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img) {objName sym : String} {off : Nat} {addr : BitVec 64}
    (hobj : Arm64.Obj.lookup objName li.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym li.symbols = some off)
    (haddr : img.base + BitVec.ofNat 64 off = addr) :
    img.symtab objName sym = some addr := by
  rw [Loads.symtab_of_lookup_symbols h hobj hsym, haddr]

theorem Loads.symtab_of_lookup_stubs {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img) {objName sym : String} {off : Nat}
    (hobj : Arm64.Obj.lookup objName li.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym li.symbols = none)
    (hstub : Arm64.Obj.lookup sym li.stubs = some off) :
    img.symtab objName sym = some (img.base + BitVec.ofNat 64 off) := by
  obtain ⟨_, _, hsyms, hstubs, hobjSyms, _, _⟩ := load_ok h
  exact Image.symtab_of_lookup_stubs (by rw [hobjSyms, hobj]) (by rw [hsyms, hsym])
    (by rw [hstubs, hstub])

theorem Loads.symtab_eq_of_lookup_stubs {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img) {objName sym : String} {off : Nat} {addr : BitVec 64}
    (hobj : Arm64.Obj.lookup objName li.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym li.symbols = none)
    (hstub : Arm64.Obj.lookup sym li.stubs = some off)
    (haddr : img.base + BitVec.ofNat 64 off = addr) :
    img.symtab objName sym = some addr := by
  rw [Loads.symtab_of_lookup_stubs h hobj hsym hstub, haddr]

theorem Loads.symtab_of_lookup_externData {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img) {objName sym : String} {off sz : Nat}
    (hobj : Arm64.Obj.lookup objName li.objSymbols = none)
    (hsym : Arm64.Obj.lookup sym li.symbols = none)
    (hstub : Arm64.Obj.lookup sym li.stubs = none)
    (hext : Arm64.Obj.lookup sym li.externData = some (off, sz)) :
    img.symtab objName sym = some (img.base + BitVec.ofNat 64 off) := by
  obtain ⟨_, _, _, _, _, himg⟩ := load_eq_ok h
  have hobjSyms : img.objSymbols = li.objSymbols := by rw [himg]
  have hsyms : img.symbols = li.symbols := by rw [himg]
  have hstubs : img.stubs = li.stubs := by rw [himg]
  have hextImg : img.externData =
      li.externData.map (fun (x, o, n) => (x, img.base + BitVec.ofNat 64 o, n)) := by
    rw [himg]
  exact Image.symtab_of_lookup_externData (by rw [hobjSyms, hobj]) (by rw [hsyms, hsym])
    (by rw [hstubs, hstub]) (by rw [hextImg, lookup_map_externData, hext]; rfl)

theorem Program.fnAddr_eq_of_fnOff {P : Arm64.Program} {name : String} {off : Nat} {addr : BitVec 64}
    (hfn : P.fnOff name = off)
    (haddr : P.base + BitVec.ofNat 64 off = addr) :
    P.fnAddr name = addr := by
  unfold Arm64.Program.fnAddr
  rw [hfn, haddr]

theorem Loads.fnOff_ofImage {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img)
    (X O : String → Option (Arm64.State → Arm64.State) := fun _ => none)
    (name : String) :
    (Arm64.Program.ofImage img X O).fnOff name = li.toProgram.fnOff name := by
  obtain ⟨_, _, hsyms, hstubs, _, _, _⟩ := load_ok h
  simp [Arm64.Program.ofImage, LinkedImage.toProgram, Arm64.Program.fnOff,
    Arm64.Program.findSymbol?, hsyms, hstubs]

theorem Loads.fnAddr_ofImage_eq_of_fnOff {li : LinkedImage} {img : Image}
    (h : Arm64.Obj.Loads li img)
    {X O : String → Option (Arm64.State → Arm64.State)}
    {name : String} {off : Nat} {addr : BitVec 64}
    (hfn : li.toProgram.fnOff name = off)
    (haddr : img.base + BitVec.ofNat 64 off = addr) :
    (Arm64.Program.ofImage img X O).fnAddr name = addr := by
  apply Program.fnAddr_eq_of_fnOff
  · rw [Loads.fnOff_ofImage h X O name, hfn]
  · exact haddr

theorem add_off_add_eq {b off1 off2 off3 : BitVec 64}
    (h : off1 = off2 + off3) :
    b + off1 = b + off2 + off3 := by
  rw [h, BitVec.add_assoc]

theorem add_add_eq_add_off {b off1 off2 off3 : BitVec 64}
    (h : off1 + off2 = off3) :
    b + off1 + off2 = b + off3 := by
  rw [← h, BitVec.add_assoc]

theorem all_nil_eq_true {α : Type} (f : α → Bool) : ([] : List α).all f = true := rfl

theorem all_cons_eq_true {α : Type} {x : α} {xs : List α} {f : α → Bool}
    (hx : f x = true) (hxs : xs.all f = true) : (x :: xs).all f = true := by
  simp [hx, hxs]

theorem and_eq_true_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  simp [ha, hb]

theorem not_eq_true_intro {a : Bool} (ha : a = false) : (!a) = true := by
  simp [ha]

theorem not_eq_false_intro {a : Bool} (ha : a = true) : (!a) = false := by
  simp [ha]

theorem beq_eq_true_of_eq {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) :
    (a == b) = true :=
  beq_iff_eq.mpr h

end ProofLib.ObjectLoad

namespace Arm64.Obj

export ProofLib.ObjectLoad (exists_loads_of_isSome)

/-- Byte at address `a` in the canonical initial memory for `img`: code at `img.base`,
    data at `img.dataAddr`, GOT at `img.gotAddr`, and `0` elsewhere. -/
def Image.loadedBytes (img : Image) (a : BitVec 64) : BitVec 8 :=
  if (a - img.base).toNat < img.code.length then
    img.code.getD (a - img.base).toNat 0#8
  else if (a - img.dataAddr).toNat < img.data.length then
    img.data.getD (a - img.dataAddr).toNat 0#8
  else if (a - img.gotAddr).toNat < img.gotBytes.length then
    img.gotBytes.getD (a - img.gotAddr).toNat 0#8
  else
    0#8

/-- Permission at address `a` in the canonical initial memory for `img`: `r-x` for code at
    `img.base`, `img.dataPerm a` for data at `img.dataAddr`, `r--` for GOT at `img.gotAddr`,
    and unmapped (`none`) elsewhere. -/
def Image.loadedPerm (img : Image) (a : BitVec 64) : Option Perm :=
  if (a - img.base).toNat < img.code.length then
    some Perm.rx
  else if (a - img.dataAddr).toNat < img.data.length then
    some (img.dataPerm a)
  else if (a - img.gotAddr).toNat < img.gotBytes.length then
    some Perm.ro
  else
    none

/-- Canonical initial `Memory` mapping `img`'s code (`r-x`), data (`img.dataPerm`), and GOT (`r--`). -/
def Image.loadedMem (img : Image) : Memory :=
  Memory.ofFn img.loadedBytes img.loadedPerm

/-- Canonical initial `State` in which `img.Loaded` holds whenever `Obj.Loads li img`. -/
def Image.loadedState (img : Image) : State :=
  { mem := img.loadedMem
    symtab := img.symtab
    brkStart := img.brkStart
    brk := img.brkStart }

/-- Any image produced by `Obj.Loads li img` is `Loaded` in `img.loadedState`.
    Code/data/GOT disjointness and no-wrap follow from `li.wellFormed` (`code.length ≤ dataOff`
    and `dataEnd ≤ gotOff`) together with `LinkedImage.load`'s wrap check
    (`base.toNat + gotOff + 8 * got.length ≤ 2 ^ 64`). -/
theorem Image.loaded_loadedState_of_loads {li : LinkedImage} {img : Image}
    (h : Loads li img) : img.Loaded img.loadedState := by
  obtain ⟨data, hfold, hal, hwf, hwrap, himg_eq⟩ := ProofLib.ObjectLoad.load_eq_ok h
  simp only [LinkedImage.wellFormed, Bool.and_eq_true] at hwf
  have hcode_le : li.code.length ≤ li.dataOff := by
    simpa [decide_eq_true_eq] using hwf.1.1.1.1.1.1.1.1
  have hde_le : li.dataEnd ≤ li.gotOff := by
    simpa [decide_eq_true_eq] using hwf.1.1.1.1.1.1.2
  have hrel_wf := List.all_eq_true.mp hwf.1.1.2
  have hrel' : li.relocs.all (fun r => decide (r.off + r.width ≤ li.data.length)) = true := by
    rw [List.all_eq_true]
    intro r hr
    have := hrel_wf r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simpa using this.2
  have hdlen := ProofLib.ObjectLoad.RoDataFactsAux.foldlM_dataReloc_length li.relocs _ data hfold hrel'
    (by simp only [List.length_append]; omega)
  simp only [List.length_append, List.length_replicate] at hdlen
  have hcode_eq : img.code = li.code := congrArg Image.code himg_eq
  have hda_eq : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff := congrArg Image.dataAddr himg_eq
  have hdata_eq : img.data = data := congrArg Image.data himg_eq
  have hga_eq : img.gotAddr = img.base + BitVec.ofNat 64 li.gotOff := congrArg Image.gotAddr himg_eq
  have hgot_eq : img.got = li.got.map (GotEntry.value img.base) := congrArg Image.got himg_eq
  have hgot_len : img.gotBytes.length = 8 * li.got.length := by
    rw [ProofLib.ObjectLoad.gotBytes_length, hgot_eq, List.length_map]
  have hcode_len : img.code.length = li.code.length := congrArg List.length hcode_eq
  have hde_def : li.dataEnd = li.dataOff + li.data.length + li.bss := rfl
  have hdata_len : img.data.length = li.data.length + li.bss := hdata_eq.symm ▸ hdlen
  simp only [pageSize] at hal
  refine Image.loaded_iff.2 ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · refine Program.CodeLoaded.intro (by simp [Program.ofImage]; omega)
      (by simp [Program.ofImage, hcode_eq]; omega) ?_
    intro i hi
    simp only [Program.ofImage] at hi ⊢
    have hsub : (img.base + BitVec.ofNat 64 i - img.base).toNat = i := by
      have : img.base + BitVec.ofNat 64 i - img.base = BitVec.ofNat 64 i := by bv_lin
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [Image.loadedState, Image.loadedMem, Memory.read8_ofFn, Memory.perm_ofFn,
      Memory.isLazyFree_ofFn, Image.loadedBytes, Image.loadedPerm, hsub, hi, ↓reduceIte, List.getD,
      List.getElem?_eq_getElem hi, Option.getD_some, Option.map_some, Perm.rwx_rx, true_and]
    rfl
  · intro i hi
    have hsub_base : (img.dataAddr + BitVec.ofNat 64 i - img.base).toNat = li.dataOff + i := by
      have : img.dataAddr + BitVec.ofNat 64 i - img.base = BitVec.ofNat 64 (li.dataOff + i) := by
        rw [hda_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
        bv_lin
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hn_code : ¬ (img.dataAddr + BitVec.ofNat 64 i - img.base).toNat < img.code.length := by
      rw [hsub_base, hcode_eq]; omega
    have hsub_data : (img.dataAddr + BitVec.ofNat 64 i - img.dataAddr).toNat = i := by
      have : img.dataAddr + BitVec.ofNat 64 i - img.dataAddr = BitVec.ofNat 64 i := by bv_lin
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [Image.loadedState, Image.loadedMem, Memory.read8_ofFn, Memory.perm_ofFn,
      Memory.isLazyFree_ofFn, Image.loadedBytes, Image.loadedPerm, hn_code, hsub_data, hi,
      ↓reduceIte, List.getD, List.getElem?_eq_getElem hi, Option.getD_some, Option.map_some,
      true_and]
    unfold Image.dataPerm
    split <;> exact ⟨rfl, rfl⟩
  · intro i hi
    have hsub_base : (img.gotAddr + BitVec.ofNat 64 i - img.base).toNat = li.gotOff + i := by
      have : img.gotAddr + BitVec.ofNat 64 i - img.base = BitVec.ofNat 64 (li.gotOff + i) := by
        rw [hga_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
        bv_lin
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hn_code : ¬ (img.gotAddr + BitVec.ofNat 64 i - img.base).toNat < img.code.length := by
      rw [hsub_base, hcode_eq]; omega
    have hsub_data : (img.gotAddr + BitVec.ofNat 64 i - img.dataAddr).toNat = li.gotOff + i - li.dataOff := by
      have : img.gotAddr + BitVec.ofNat 64 i - img.dataAddr = BitVec.ofNat 64 (li.gotOff + i - li.dataOff) := by
        rw [hga_eq, hda_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact ProofLib.ObjectLoad.bv_add_sub_add_of_le img.base (by omega) (by omega)
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hn_data : ¬ (img.gotAddr + BitVec.ofNat 64 i - img.dataAddr).toNat < img.data.length := by
      rw [hsub_data]; omega
    have hsub_got : (img.gotAddr + BitVec.ofNat 64 i - img.gotAddr).toNat = i := by
      have : img.gotAddr + BitVec.ofNat 64 i - img.gotAddr = BitVec.ofNat 64 i := by bv_lin
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [Image.loadedState, Image.loadedMem, Memory.read8_ofFn, Memory.perm_ofFn,
      Memory.isLazyFree_ofFn, Image.loadedBytes, Image.loadedPerm, hn_code, hn_data, hsub_got, hi,
      ↓reduceIte, List.getD, List.getElem?_eq_getElem hi, Option.getD_some, Option.map_some,
      Perm.rwx_ro, true_and]
    rfl

/-- Every image `img` loaded from `li` (`Obj.Loads li img`) admits an initial `State` in which
    `img.Loaded` holds. -/
theorem Image.exists_loaded_of_loads {li : LinkedImage} {img : Image}
    (h : Loads li img) : ∃ s : State, img.Loaded s :=
  ⟨img.loadedState, img.loaded_loadedState_of_loads h⟩

/-- If `img.Loaded s`, then `(Program.ofImage img externs overrides).CodeLoaded s.mem` holds for
    any extern and override hook tables (`CodeLoaded` depends only on `base` and `code`). -/
theorem Image.Loaded.codeLoaded_ofImage {img : Image} {s : State} (hL : img.Loaded s)
    (externs overrides : String → Option (State → State) := fun _ => none) :
    (Program.ofImage img externs overrides).CodeLoaded s.mem :=
  hL.codeLoaded.of_base_code rfl rfl

/-- If `img.FrozenLoaded s`, then `(Program.ofImage img externs overrides).CodeLoaded s.mem` holds
    for any extern and override hook tables. -/
theorem Image.FrozenLoaded.codeLoaded_ofImage {img : Image} {s : State} (hF : img.FrozenLoaded s)
    (externs overrides : String → Option (State → State) := fun _ => none) :
    (Program.ofImage img externs overrides).CodeLoaded s.mem :=
  hF.codeLoaded.of_base_code rfl rfl

/-- Every image `img` loaded from `li` (`Obj.Loads li img`) admits an initial `State` satisfying
    `img.Loaded s` and `(Program.ofImage img externs overrides).CodeLoaded s.mem` for all hooks. -/
theorem Image.exists_codeLoaded_of_loads {li : LinkedImage} {img : Image}
    (h : Loads li img) :
    ∃ s : State, img.Loaded s ∧
      ∀ (externs overrides : String → Option (State → State)),
        (Program.ofImage img externs overrides).CodeLoaded s.mem :=
  ⟨img.loadedState, img.loaded_loadedState_of_loads h,
    fun externs overrides => (img.loaded_loadedState_of_loads h).codeLoaded_ofImage externs overrides⟩

end Arm64.Obj

namespace Arm64
export ProofLib.ObjectLoad (exists_loads_of_isSome exists_loads_of_tree)
end Arm64

namespace ProofLib
export ProofLib.ObjectLoad (
  exists_loads_of_isSome exists_loads_of_tree
  CharObjectInfo toStringObjects toStringObjSymbols checkAllHonoursChar
  base_aligned_of_loads base_aligned_mask page_align_of_loads
  adrp_page_base adrp_page_of_aligned adrp_page_add_zero adrp_page_add_eq
  findBaseAlignedProof? reduceAdrpPage
  rodata_perm rodata_bytes_disjoint readBytes_getElem?
  rodata_ro rodata_readBytes_disjoint holdsBytes_ro
  noRelocInRange splice_length splice_drop_take_eq
  dataReloc_apply_preserves_slice foldlM_dataReloc_preserves_slice
  loads_data_slice_eq inLiRoData bv_add_sub_add_of_le loads_rodata_holdsBytes
  holdsBytes_ro_of_keepsFrozen holdsBytes_cons_iff holdsBytes_append
  memSlice_of_holdsBytes_ro gotBytes_length
  EncSymTable prepareCharAssocVal lookupEnc filterEnc lookupUniqueEnc anyEnc
  toStringSymbols_eq_toStringAssoc
  lookupEnc_prepareCharAssocVal lookupUniqueEnc_prepareCharAssocVal
  filterEnc_length anyEnc_prepareCharAssocVal
  lookup_eq_lookupEnc lookupSymbols_eq_lookupEnc
  lookupUnique_eq_lookupUniqueEnc lookupUniqueSymbols_eq_lookupUniqueEnc
  filter_length_eq_filterEnc filterSymbols_length_eq_filterEnc
  any_eq_anyEnc anySymbols_eq_anyEnc
  lookup_prepareCharSymbols lookupUnique_prepareCharSymbols
  filter_length_prepareCharSymbols any_prepareCharSymbols
  toStringSymbols_getElem?_of_some
  fnOff_of_allFresh_chars fnOff_of_stub_chars
  lookup_of_allFresh_chars lookupUnique_of_allFresh_chars
  filter_of_allFresh_chars filter_length_of_allFresh_chars any_of_allFresh_chars
  lookup_stub_of_wf_chars lookupUnique_stub_of_wf_chars
  filter_length_stub_of_wf_chars any_stub_of_wf_chars
  lookup_symbols_none_of_stub_chars any_symbols_false_of_stub_chars
  any_stubs_false_of_symbol_chars
  lookup_map_externData
  add_off_add_eq add_add_eq_add_off
)
end ProofLib

namespace ProofLib.ProgramReflection
export ProofLib.ObjectLoad (
  EncSymTable prepareCharAssocVal lookupEnc filterEnc lookupUniqueEnc anyEnc
  toStringSymbols_eq_toStringAssoc
  lookupEnc_prepareCharAssocVal lookupUniqueEnc_prepareCharAssocVal
  filterEnc_length anyEnc_prepareCharAssocVal
  lookup_eq_lookupEnc lookupSymbols_eq_lookupEnc
  lookupUnique_eq_lookupUniqueEnc lookupUniqueSymbols_eq_lookupUniqueEnc
  filter_length_eq_filterEnc filterSymbols_length_eq_filterEnc
  any_eq_anyEnc anySymbols_eq_anyEnc
  toStringSymbols_getElem?_of_some
  fnOff_of_allFresh_chars fnOff_of_stub_chars
  lookup_of_allFresh_chars lookupUnique_of_allFresh_chars
  filter_of_allFresh_chars filter_length_of_allFresh_chars any_of_allFresh_chars
  lookup_stub_of_wf_chars lookupUnique_stub_of_wf_chars
  filter_length_stub_of_wf_chars any_stub_of_wf_chars
  lookup_symbols_none_of_stub_chars any_symbols_false_of_stub_chars
  any_stubs_false_of_symbol_chars
)
end ProofLib.ProgramReflection

/-! ## Program Rebasing -/

namespace Arm64.Program

variable {P : Program} {b : BitVec 64} {X O : String → Option (State → State)}

@[simp, arm64_norm] theorem rebase_base : (P.rebase b X O).base = b := by cases P; rfl
@[simp, arm64_norm] theorem rebase_code : (P.rebase b X O).code = P.code := by cases P; rfl
@[simp, arm64_norm] theorem rebase_symbols : (P.rebase b X O).symbols = P.symbols := by cases P; rfl
@[simp, arm64_norm] theorem rebase_stubs : (P.rebase b X O).stubs = P.stubs := by cases P; rfl
@[simp, arm64_norm] theorem rebase_externs : (P.rebase b X O).externs = X := by cases P; rfl
@[simp, arm64_norm] theorem rebase_overrides : (P.rebase b X O).overrides = O := by cases P; rfl
@[simp, arm64_norm] theorem rebase_svc : (P.rebase b X O).svc = P.svc := by cases P; rfl

@[simp, arm64_norm] theorem fnOff_rebase (n : String) : (P.rebase b X O).fnOff n = P.fnOff n := by cases P; rfl

/-- Rewrite a rebased program's `fnAddr` to `b + BitVec.ofNat 64 (P.fnOff n)`.
    Note: not marked `@[simp]` or `@[arm64_norm]` directly; `reduceFnAddrRebase` is the
    guarded `@[simp, arm64_norm]` simproc that normalizes `n` to a string literal and
    only rewrites when `P.fnOff n` simplifies cleanly (preventing unreduced `P.fnOff`
    terms in the goal when `n` is an unknown symbol or `*Code.lean` is not imported). -/
theorem fnAddr_rebase (n : String) :
    (P.rebase b X O).fnAddr n = b + BitVec.ofNat 64 (P.fnOff n) := by cases P; rfl

@[simp, arm64_norm] theorem readWordOff_rebase (off : Nat) :
    (P.rebase b X O).readWordOff off = P.readWordOff off := by cases P; rfl

@[simp, arm64_norm] theorem hookAtOff?_rebase (off : Nat) :
    (P.rebase b X O).hookAtOff? off = (P.rebase 0 X O).hookAtOff? off := by cases P; rfl

/-- Address of an internal callee relative to the caller's `fnAddr` in a rebased program. -/
theorem fnAddr_rel {name callee : String} {off off' k : Nat}
    (hfn : P.fnOff name = off) (hfn' : P.fnOff callee = off') (hk : off + k = off') :
    (P.rebase b X O).fnAddr callee = (P.rebase b X O).fnAddr name + BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hfn', BitVec.add_assoc,
    ← BitVec.ofNat_add, hk]

/-- Address of an internal callee placed `d` bytes before the caller (`off' + d = off`) in a rebased program. -/
theorem fnAddr_back {name callee : String} {off off' d : Nat}
    (hfn : P.fnOff name = off) (hfn' : P.fnOff callee = off') (hk : off' + d = off) :
    (P.rebase b X O).fnAddr callee = (P.rebase b X O).fnAddr name - BitVec.ofNat 64 d := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hfn', ← hk, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- Express a forward callee's `fnAddr` as `caller + k#64` on the same rebased program. -/
theorem fnAddr_callee_add_of_fnOff {caller callee : String} {callerOff calleeOff k : Nat}
    (hcaller : P.fnOff caller = callerOff) (hcallee : P.fnOff callee = calleeOff)
    (hk : (BitVec.ofNat 64 callerOff + BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff) :
    (P.rebase b X O).fnAddr callee =
      (P.rebase b X O).fnAddr caller + BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee, ← hk]
  bv_lin

/-- Express a backward callee's `fnAddr` as `caller - k#64` on the same rebased program. -/
theorem fnAddr_callee_sub_of_fnOff {caller callee : String} {callerOff calleeOff k : Nat}
    (hcaller : P.fnOff caller = callerOff) (hcallee : P.fnOff callee = calleeOff)
    (hk : (BitVec.ofNat 64 callerOff - BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff) :
    (P.rebase b X O).fnAddr callee =
      (P.rebase b X O).fnAddr caller - BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee, ← hk]
  bv_lin

/-- Rewrite a rebased program's `fnAddr` to `b + BitVec.ofNat 64 off` given `P.fnOff name = off`. -/
theorem fnAddr_rebase_add_of_fnOff {name : String} {off : Nat} (hfn : P.fnOff name = off) :
    (P.rebase b X O).fnAddr name = b + BitVec.ofNat 64 off := by
  rw [Program.fnAddr_rebase, hfn]

end Arm64.Program

end

public meta section

namespace Arm64.Program

open Lean Meta Simp

/-- If `e` is not already a syntactic `String` literal (`.lit (.strVal _)`), unfold reducible
    definitions, local `let`-bindings, or constant definitions step-by-step (without `whnfCore`'s
    `toCtorIfLit`, which expands string literals into `String.ofList`) to check whether `e`
    reduces to a `.lit (.strVal _)`. -/
def reduceToStringLit? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if let .lit (.strVal _) := e then
    return none
  let mut cur := e
  for _ in [:32] do
    cur := cur.consumeMData
    if let .lit (.strVal _) := cur then
      return some cur
    if let .fvar fvarId := cur then
      if let some decl ← fvarId.findDecl? then
        if let some val := decl.value? then
          cur := val
          continue
      return none
    if cur.hasFVar || cur.hasMVar then
      return none
    if let some next ← withReducible (unfoldDefinition? cur) then
      cur := next
      continue
    if cur.isConst then
      if let some next ← unfoldDefinition? cur then
        cur := next
        continue
    return none
  return none

/-- Normalize a non-literal `String` symbol-name argument of `Program.fnOff` (e.g.
    `abbrev fooName : String := "..."`) to a `.lit (.strVal _)` literal via an explicit
    `congrArg` step so generated `@[simp, arm64_norm]` `*_fnOff_0x*` lemmas (keyed in the
    `simp` discrimination tree on `Key.lit (.strVal _)`) match without `DiscrTree.whnfDT`
    expanding the `abbrev` to `String.ofList` and without kernel-reducing `Program.fnOff`. -/
simproc [simp, arm64_norm, wp_norm] reduceFnOffSym (Arm64.Program.fnOff _ _) := fun e => do
  if !e.isAppOfArity ``Arm64.Program.fnOff 2 then return .continue
  let prog := e.getArg! 0
  let name := e.getArg! 1
  let some lit ← reduceToStringLit? name | return .continue
  let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
  let prf ← mkCongrArg (mkApp e.getAppFn prog) hName
  return .visit { expr := mkApp2 e.getAppFn prog lit, proof? := some prf }

/-- Normalize a non-literal `String` symbol-name argument of `Program.fnAddr` (e.g.
    `abbrev fooName : String := "..."`) to a `.lit (.strVal _)` literal via an explicit
    `congrArg` step. -/
simproc [simp, arm64_norm, wp_norm] reduceFnAddrSym (Arm64.Program.fnAddr _ _) := fun e => do
  if !e.isAppOfArity ``Arm64.Program.fnAddr 2 then return .continue
  let prog := e.getArg! 0
  let name := e.getArg! 1
  let some lit ← reduceToStringLit? name | return .continue
  let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
  let prf ← mkCongrArg (mkApp e.getAppFn prog) hName
  return .visit { expr := mkApp2 e.getAppFn prog lit, proof? := some prf }

/-- Guarded `simproc` for `(P.rebase b X O).fnAddr n`: rewrites `(P.rebase b X O).fnAddr n`
    to `b + BitVec.ofNat 64 off` (via `Program.fnAddr_rebase_add_of_fnOff`) only when
    `P.fnOff n` simplifies to an offset expression `off` that no longer mentions `Program.fnOff`.
    If `P.fnOff n` does not simplify (e.g. for an unknown symbol or when `*Code.lean` is not
    imported), leaves `(P.rebase b X O).fnAddr n` intact so an unreduced `P.fnOff n` term is
    never introduced into the goal or local context. -/
simproc [simp, arm64_norm] reduceFnAddrRebase
    (Arm64.Program.fnAddr (Arm64.Program.rebase _ _ _ _) _) := fun e => do
  let e' ← if e.isAppOfArity ``Arm64.Program.fnAddr 2 then pure e else withReducible (whnf e)
  if !e'.isAppOfArity ``Arm64.Program.fnAddr 2 then return .continue
  let prog0 := e'.getArg! 0
  let prog ← if prog0.isAppOfArity ``Arm64.Program.rebase 4 then pure prog0 else withReducible (whnf prog0)
  if !prog.isAppOfArity ``Arm64.Program.rebase 4 then return .continue
  let name := e'.getArg! 1
  if let some lit ← reduceToStringLit? name then
    let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
    let prf0 ← mkCongrArg (mkApp e'.getAppFn prog0) hName
    let rhs0 := mkApp2 e'.getAppFn prog0 lit
    let prf ← if e == e' then pure prf0 else mkExpectedTypeHint prf0 (← mkEq e rhs0)
    return .visit { expr := rhs0, proof? := some prf }
  let P := prog.getArg! 0
  let b := prog.getArg! 1
  let X := prog.getArg! 2
  let O := prog.getArg! 3
  let fnOffExpr := mkApp2 (mkConst ``Arm64.Program.fnOff) P name
  let r ← Simp.simp fnOffExpr
  if (r.expr.find? (·.isAppOf ``Arm64.Program.fnOff)).isSome then
    return .continue
  let offExpr := r.expr
  let hfn ← r.getProof
  let prf0 := mkAppN (mkConst ``Arm64.Program.fnAddr_rebase_add_of_fnOff)
    #[P, b, X, O, name, offExpr, hfn]
  let bv64Off := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) offExpr
  let rhs ← mkAppM ``HAdd.hAdd #[b, bv64Off]
  let prf ← if e == e' && prog0 == prog then pure prf0 else mkExpectedTypeHint prf0 (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some prf }

/-- Normalize a non-literal `String` symbol-name argument of `Obj.fnSize` to a string literal. -/
simproc [simp, arm64_norm, wp_norm] reduceFnSizeSym (Arm64.Obj.fnSize _ _) := fun e => do
  if !e.isAppOfArity ``Arm64.Obj.fnSize 2 then return .continue
  let img := e.getArg! 0
  let name := e.getArg! 1
  let some lit ← reduceToStringLit? name | return .continue
  let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
  let prf ← mkCongrArg (mkApp e.getAppFn img) hName
  return .visit { expr := mkApp2 e.getAppFn img lit, proof? := some prf }

/-- Normalize a non-literal `String` symbol-name argument of `fnFrameBytes` to a string literal. -/
simproc [simp, arm64_norm, wp_norm] reduceFnFrameBytesSym (Arm64.fnFrameBytes _ _) := fun e => do
  if !e.isAppOfArity ``Arm64.fnFrameBytes 4 then return .continue
  let ty := e.getArg! 0
  let inst := e.getArg! 1
  let src := e.getArg! 2
  let name := e.getArg! 3
  let some lit ← reduceToStringLit? name | return .continue
  let hName ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq name lit)
  let fnPrefix := mkApp3 e.getAppFn ty inst src
  let prf ← mkCongrArg fnPrefix hName
  return .visit { expr := mkApp fnPrefix lit, proof? := some prf }

end Arm64.Program

end

@[expose] public section

namespace Arm64.Program

variable {P : Program} {b : BitVec 64} {X O : String → Option (State → State)}

/-- The hook at `b + off` of a rebased program is the hook at offset `off`. -/
theorem externAt?_rebase_add (off : Nat) (hoff : off < 2 ^ 64 := by decide) :
    (P.rebase b X O).externAt? (b + BitVec.ofNat 64 off) = (P.rebase 0 X O).hookAtOff? off := by
  rw [Program.externAt?, rebase_base, BitVec.add_comm, BitVec.add_sub_cancel,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rfl

/-- The extern reached at `fnAddr name + k` of `P.rebase b X O` for stub offset `off + k = stub`. -/
theorem externAt?_fnAddr_add {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64 := by decide) :
    (P.rebase b X O).externAt? ((P.rebase b X O).fnAddr name + BitVec.ofNat 64 k) =
      (P.rebase 0 X O).hookAtOff? stub := by
  rw [Program.fnAddr_rebase, hfn, BitVec.add_assoc, ← BitVec.ofNat_add, hk,
    Program.externAt?_rebase_add _ hs]

/-- Rewrite a rebased instruction fetch at `b + (off + k)` into a fetch at `fnAddr name + k`. -/
theorem fetch_fnAddr_add {name : String} {off k : Nat} {inst : Instr}
    (hfn : P.fnOff name = off)
    (h : (P.rebase b X O).fetch (b + BitVec.ofNat 64 (off + k)) = some inst) :
    (P.rebase b X O).fetch ((P.rebase b X O).fnAddr name + BitVec.ofNat 64 k) = some inst := by
  rwa [Program.fnAddr_rebase, hfn, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Rewrite a rebased instruction fetch at `b + (off + 0)` into a fetch at `fnAddr name`. -/
theorem fetch_fnAddr_entry {name : String} {off : Nat} {inst : Instr}
    (hfn : P.fnOff name = off)
    (h : (P.rebase b X O).fetch (b + BitVec.ofNat 64 (off + 0)) = some inst) :
    (P.rebase b X O).fetch ((P.rebase b X O).fnAddr name) = some inst := by
  simpa using fetch_fnAddr_add hfn h

/-- Fetch at `b + off` of a hook-free base-0 program rebased to `b` equals the base-0 fetch at
    `off`, provided no new hook sits at `off`. -/
theorem fetch_rebase_eq_of_hookAtOff? {P : Program} (hbase : P.base = 0)
    (hX : ∀ n, (P.externs n).isNone = true) (hO : ∀ n, (P.overrides n).isNone = true)
    {b : BitVec 64} {X O : String → Option (State → State)} {off : Nat} (hoff : off < 2 ^ 64)
    (hhook : (P.rebase b X O).hookAtOff? off = none) :
    (P.rebase b X O).fetch (b + BitVec.ofNat 64 off) = P.fetch (BitVec.ofNat 64 off) := by
  have h1 : (P.rebase b X O).fetch (b + BitVec.ofNat 64 off) = _ :=
    Program.fetch_base_add (prog := P.rebase b X O) hoff
  have h2 := Program.fetch_base_add (prog := P) hoff
  rw [hbase, show (0 : BitVec 64) + BitVec.ofNat 64 off = BitVec.ofNat 64 off from
    BitVec.zero_add _] at h2
  rw [h1, h2, hhook, ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone hX hO]
  rfl

/-- For a base-0 hook-free program `P` whose stubs all sit at offsets `≥ textEnd`,
    fetching at `b + off` (for `off < textEnd`) in `P.rebase b X` (with any externs `X` and
    no overrides) equals the base-0 fetch `P.fetch (BitVec.ofNat 64 off)`. -/
theorem fetch_rebase_of_noStubBefore {P : Program} (hbase : P.base = 0)
    (hX : ∀ n, (P.externs n).isNone = true) (hO : ∀ n, (P.overrides n).isNone = true)
    {textEnd : Nat} (hstubs : ProofLib.ProgramReflection.noStubBefore textEnd P.stubs = true)
    (b : BitVec 64) (X : String → Option (State → State))
    {off : Nat} (htext : off < textEnd) (hoff : off < 2 ^ 64) :
    (P.rebase b X).fetch (b + BitVec.ofNat 64 off) = P.fetch (BitVec.ofNat 64 off) :=
  fetch_rebase_eq_of_hookAtOff? hbase hX hO hoff
    (ProofLib.ProgramReflection.hookAtOff?_eq_none_of_noStubBefore hstubs (fun _ => rfl) htext)

/-- Every stub or symbol of `P` whose hook is set lies at an offset in `hooked`. -/
def hooksWithin (P : Program) (hooked : List Nat) : Bool :=
  (P.stubs.all fun (n, o) => hooked.contains o || (P.externs n).isNone) &&
  (P.symbols.all fun (n, o) => hooked.contains o || (P.overrides n).isNone)


/-- `hasWordsOff` transfers to a rebased program if its hooks avoid the range. The hook
    condition is stated at base 0 so that `decide` closes it for concrete hooks. -/
theorem hasWordsOff_rebase {off : Nat} {words : List (BitVec 32)} (h : P.hasWordsOff off words)
    (hfree : (P.rebase 0 X O).hookFree off (4 * words.length)) :
    (P.rebase b X O).hasWordsOff off words :=
  ⟨h.1, h.2.1, hfree⟩

/-- `codeAt` transfers to a rebased program if its hooks avoid the function's code. -/
theorem codeAt_rebase {n : String} {hex : List (BitVec 32)} (h : P.codeAt n hex)
    (hfree : (P.rebase 0 X O).hookFree (P.fnOff n) (4 * hex.length)) :
    (P.rebase b X O).codeAt n hex :=
  hasWordsOff_rebase h hfree

/-- `codeAtOff` transfers to a rebased program if its hooks avoid the function's code. -/
theorem codeAtOff_rebase {n : String} {hex : List (BitVec 32)} {off : Nat} (h : P.codeAtOff n off hex)
    (hfree : (P.rebase 0 X O).hookFree (P.fnOff n) (4 * hex.length)) :
    (P.rebase b X O).codeAtOff n off hex :=
  ⟨h.1, codeAt_rebase h.2 hfree⟩

/-- An image of `li` is the canonical program `P = li.toProgram` rebased to the image's base. -/
theorem ofImage_eq_rebase {li : Obj.LinkedImage} {img : Obj.Image} (hc : li.toProgram = P)
    (h : Obj.Loads li img) : Program.ofImage img X O = P.rebase img.base X O := by
  obtain ⟨hcode, hsyms, hstubs⟩ := ProofLib.ObjectLoad.Loads.canonical h
  subst hc
  simp only [ofImage, rebase, hcode, hsyms, hstubs, Obj.LinkedImage.toProgram]

/-- The code of a loaded image of `li` is loaded as the canonical program rebased to the
    image's base (with any hooks): `CodeLoaded` depends only on `base` and `code`. -/
theorem codeLoaded_rebase_of_loaded {li : Obj.LinkedImage} {img : Obj.Image} {s : State}
    (hc : li.toProgram = P) (h : Obj.Loads li img) (hL : img.Loaded s) :
    (P.rebase img.base X O).CodeLoaded s.mem := by
  rw [← ofImage_eq_rebase hc h]
  exact hL.codeLoaded.of_base_code rfl rfl

/-- Prefix-sliced counterpart of `ofImage_eq_rebase` for a canonical program `P` whose `code` is
    `li.code.take n` (e.g. `.text` without trailing external stub slots). -/
theorem ofImage_take_eq_rebase {li : Obj.LinkedImage} {img : Obj.Image} {n : Nat}
    (hc : { li.toProgram with code := li.code.take n } = P)
    (h : Obj.Loads li img) :
    { Program.ofImage img X O with code := img.code.take n } = P.rebase img.base X O := by
  obtain ⟨hcode, hsyms, hstubs⟩ := ProofLib.ObjectLoad.Loads.canonical h
  subst hc
  simp only [ofImage, rebase, hcode, hsyms, hstubs, Obj.LinkedImage.toProgram]

/-- Prefix-sliced counterpart of `codeLoaded_rebase_of_loaded`: `img.Loaded s` implies strict
    `CodeLoaded` for any `n`-byte prefix of `li.code` rebased to `img.base`. -/
theorem codeLoaded_rebase_take_of_loaded {li : Obj.LinkedImage} {img : Obj.Image} {s : State}
    {n : Nat} (hc : { li.toProgram with code := li.code.take n } = P)
    (h : Obj.Loads li img) (hL : img.Loaded s) :
    (P.rebase img.base X O).CodeLoaded s.mem := by
  rw [← ofImage_take_eq_rebase hc h]
  have hcl := hL.codeLoaded
  rw [Program.codeLoaded_iff] at hcl ⊢
  obtain ⟨halign, hwrap, hbytes⟩ := hcl
  refine ⟨halign, by simp only [ofImage, List.length_take] at hwrap ⊢; omega, fun i hi => ?_⟩
  have hi' : i < (ofImage img).code.length := by simp only [ofImage, List.length_take] at hi ⊢; omega
  simpa [ofImage, List.getElem_take] using hbytes i hi'

/-- Lift a base-quantified `Program.relocSubroutineOk` theorem on `P` (`li.toProgram = P`) to
    `li.subroutineOk`. -/
theorem relocSubroutineOk.toLinkedImage {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage} {P : Program} {fnName : String} {spec : S}
    {X O : String → Option (State → State)}
    (hc : li.toProgram = P) (h : P.relocSubroutineOk fnName spec X O) :
    li.subroutineOk fnName spec X O := by
  intro img himg
  rw [ofImage_eq_rebase hc himg]
  exact h img.base

/-- Lift a page-aligned base-quantified `Program.alignedSubroutineOk` theorem on `P`
    (`li.toProgram = P`) to `li.subroutineOk`. -/
theorem alignedSubroutineOk.toLinkedImage {S α : Type} [ToBaseSpec S α]
    {li : Obj.LinkedImage} {P : Program} {fnName : String} {spec : S}
    {X O : String → Option (State → State)}
    (hc : li.toProgram = P) (h : P.alignedSubroutineOk fnName spec X O) :
    li.subroutineOk fnName spec X O := by
  intro img himg
  rw [ofImage_eq_rebase hc himg]
  exact h img.base (ProofLib.ObjectLoad.base_aligned_of_loads himg)

end Arm64.Program

namespace Arm64.FnCode

/-- `c` is not pinned at an absolute address. -/
def unpinned (c : FnCode) : Bool :=
  match c.pin with
  | .addr _ => false
  | _ => true

/-- An unpinned code spec that holds for `P` rebased to 0 with hooks `X`, `O` (decidable for
    concrete programs, and it includes hook freedom) holds at every base. -/
theorem holds_rebase_of_zero {c : FnCode} {P : Program} {b : BitVec 64}
    {X O : String → Option (State → State)} (h : c.holds (P.rebase 0 X O))
    (hpin : c.unpinned = true) : c.holds (P.rebase b X O) := by
  rcases c with ⟨n, hex, _ | off | a⟩
  · exact h
  · exact h
  · simp [unpinned] at hpin

end Arm64.FnCode

namespace Arm64.Program

/-- Bundle version of `FnCode.holds_rebase_of_zero`: decide the bundle once at base 0. -/
theorem hasCodeBundle_rebase_of_zero {P : Program} {b : BitVec 64}
    {X O : String → Option (State → State)} :
    {cs : List FnCode} → (P.rebase 0 X O).hasCodeBundle cs →
      cs.all FnCode.unpinned = true → (P.rebase b X O).hasCodeBundle cs
  | [], _, _ => trivial
  | [c], h, hp => FnCode.holds_rebase_of_zero h (by simpa using hp)
  | c :: c2 :: cs, h, hp => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    exact ⟨FnCode.holds_rebase_of_zero h.1 hp.1,
      hasCodeBundle_rebase_of_zero (cs := c2 :: cs) h.2 (by simpa using hp.2)⟩

/-- Lift a `subroutineOk` proof on `P.rebase img.base X O` directly to `Program.ofImage img X O`
    when `img` loads `li` and `li.toProgram = P`. -/
theorem subroutineOk_of_rebase {α : Type} {li : Obj.LinkedImage} {img : Obj.Image}
    {P : Program} {sym : String} {spec : Spec α}
    {X O : String → Option (State → State)}
    (hc : li.toProgram = P) (hload : Obj.Loads li img)
    (hok : (P.rebase img.base X O).subroutineOk sym spec) :
    (Program.ofImage img X O).subroutineOk sym spec := by
  rw [Program.ofImage_eq_rebase hc hload]
  exact hok

end Arm64.Program

public meta section

namespace ProofLib.ObjectLoad

open Lean Elab Tactic Meta Arm64 Arm64.Obj ProofLib.ProgramReflection

/-- Metadata for a generated `<c>` / `<c>_symChars` / `<c>_stubChars` / `<c>_symEnc` reflection bundle. -/
structure ReflectedSymBundle where
  codeConst : Name
  symCharsConst : Name
  stubCharsConst : Name
  symbolsEqConst : Name
  stubsEqConst : Name
  symbolsFreshConst? : Option Name
  stubsWfConst? : Option Name
  symEncConst? : Option Name
  symEncEqConst? : Option Name
  stubEncConst? : Option Name
  stubEncEqConst? : Option Name

def extractNatLitFast? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.isAppOfArity ``OfNat.ofNat 3 then (e.getArg! 1).rawNatLit?
  else none

def extractCharFast? (e : Expr) : Option Char :=
  if e.isAppOfArity ``Char.ofNat 1 then
    (extractNatLitFast? (e.getArg! 0)).map Char.ofNat
  else if e.isAppOfArity ``Char.mk 2 then
    let u := e.getArg! 0
    if u.isAppOfArity ``UInt32.ofNat 1 || u.isAppOfArity ``UInt32.ofNatLT 2 then
      (extractNatLitFast? (u.getArg! 0)).map Char.ofNat
    else none
  else none

partial def matchCharListExpr (e : Expr) (target : List Char) : Bool :=
  match target with
  | [] => e.isAppOfArity ``List.nil 1
  | c :: cs =>
    if e.isAppOfArity ``List.cons 3 then
      match extractCharFast? (e.getArg! 1) with
      | some c' => c == c' && matchCharListExpr (e.getArg! 2) cs
      | none => false
    else false

/-- Scan the `List.cons` spine of a `<c>_symChars` / `<c>_stubChars` constant in the environment
    for `targetName`, returning `(index, csExpr, offExpr)` without running `whnf`. -/
def findInCharAssocConst? (charConst : Name) (targetName : String) :
    MetaM (Option (Nat × Expr × Expr)) := do
  let some cinfo := (← getEnv).find? charConst | return none
  let some val := cinfo.value? | return none
  let targetChars := targetName.toList
  let mut cur := val
  let mut k : Nat := 0
  while cur.isAppOfArity ``List.cons 3 do
    let pair := cur.getArg! 1
    if pair.isAppOfArity ``Prod.mk 4 then
      let csExpr := pair.getArg! 2
      let offExpr := pair.getArg! 3
      if matchCharListExpr csExpr targetChars then
        return some (k, csExpr, offExpr)
    cur := cur.getArg! 2
    k := k + 1
  return none

def findBundleForCodeConst? (c : Name) : MetaM (Option ReflectedSymBundle) := do
  let env ← getEnv
  let mkSub (s : String) : Name := c.appendAfter s
  let symChars := mkSub "_symChars"
  let stubChars := mkSub "_stubChars"
  let symsEq := mkSub "_symbols_eq"
  let stubsEq := mkSub "_stubs_eq"
  if env.contains symChars && env.contains symsEq then
    let optConst (s : String) : Option Name :=
      let n := mkSub s
      if env.contains n then some n else none
    return some {
      codeConst := c
      symCharsConst := symChars
      stubCharsConst := stubChars
      symbolsEqConst := symsEq
      stubsEqConst := stubsEq
      symbolsFreshConst? := optConst "_symbols_fresh"
      stubsWfConst? := optConst "_stubs_wf"
      symEncConst? := optConst "_symEnc"
      symEncEqConst? := optConst "_symEnc_eq"
      stubEncConst? := optConst "_stubEnc"
      stubEncEqConst? := optConst "_stubEnc_eq"
    }
  return none

def ensureAutoBundleForConst? (c : Name) : MetaM (Option ReflectedSymBundle) := do
  let env ← getEnv
  let modAutoBase := mkPrivateName env (c.appendAfter "_auto")
  if let some b ← findBundleForCodeConst? modAutoBase then
    return some b
  let ngen ← getDeclNGen
  let includeEnc := ngen.namePrefix.isAnonymous
  let rawBase := ngen.namePrefix ++ c.appendAfter "_auto"
  let autoBase := if isPrivateName rawBase then rawBase else mkPrivateName env rawBase
  if let some b ← findBundleForCodeConst? autoBase then
    return some b
  let cExpr := mkConst c
  let cTy ← instantiateMVars (← inferType cExpr)
  let (symsField, stubsField) ←
    if cTy.isConstOf ``Arm64.Obj.LinkedImage then
      pure (``Arm64.Obj.LinkedImage.symbols, ``Arm64.Obj.LinkedImage.stubs)
    else if cTy.isConstOf ``Arm64.Program then
      pure (``Arm64.Program.symbols, ``Arm64.Program.stubs)
    else
      return none
  let symsExpr := mkApp (mkConst symsField) cExpr
  let stubsExpr := mkApp (mkConst stubsField) cExpr
  let symCharsVal ← elabCharSymTableExpr symsExpr
  let stubCharsVal ← elabCharSymTableExpr stubsExpr
  let charAssocTy := mkApp (mkConst ``List [Level.zero])
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
      (mkApp (mkConst ``List [Level.zero]) (mkConst ``Char))
      (mkConst ``Nat))
  let symCharsNm := autoBase.appendAfter "_symChars"
  let stubCharsNm := autoBase.appendAfter "_stubChars"
  let symsEqNm := autoBase.appendAfter "_symbols_eq"
  let stubsEqNm := autoBase.appendAfter "_stubs_eq"
  let addNoncompDef (nm : Name) (ty val : Expr) : MetaM Unit :=
    addDecl (.defnDecl {
      name := nm, levelParams := [], type := ty, value := val
      hints := .abbrev, safety := .safe
    })
  addNoncompDef symCharsNm charAssocTy symCharsVal
  addNoncompDef stubCharsNm charAssocTy stubCharsVal
  let addRflThm (nm : Name) (lhs rhs : Expr) : MetaM Unit := do
    let eqTy ← mkEq lhs rhs
    let prf ← mkEqRefl rhs
    addDecl (.thmDecl { name := nm, levelParams := [], type := eqTy, value := prf })
  addRflThm symsEqNm symsExpr (mkApp (mkConst ``toStringSymbols) (mkConst symCharsNm))
  addRflThm stubsEqNm stubsExpr (mkApp (mkConst ``toStringSymbols) (mkConst stubCharsNm))
  let mut symEncConst? : Option Name := none
  let mut symEncEqConst? : Option Name := none
  let mut stubEncConst? : Option Name := none
  let mut stubEncEqConst? : Option Name := none
  if includeEnc then
    let encTy := mkApp (mkConst ``EncSymTable) (mkConst ``Nat)
    let symEncVal ← elabEncSymTableExpr symsExpr
    let stubEncVal ← elabEncSymTableExpr stubsExpr
    let symEncNm := autoBase.appendAfter "_symEnc"
    let stubEncNm := autoBase.appendAfter "_stubEnc"
    let symEncEqNm := autoBase.appendAfter "_symEnc_eq"
    let stubEncEqNm := autoBase.appendAfter "_stubEnc_eq"
    addNoncompDef symEncNm encTy symEncVal
    addNoncompDef stubEncNm encTy stubEncVal
    addRflThm symEncEqNm (mkApp2 (mkConst ``prepareCharAssocVal) (mkConst ``Nat) (mkConst symCharsNm)) (mkConst symEncNm)
    addRflThm stubEncEqNm (mkApp2 (mkConst ``prepareCharAssocVal) (mkConst ``Nat) (mkConst stubCharsNm)) (mkConst stubEncNm)
    symEncConst? := some symEncNm
    symEncEqConst? := some symEncEqNm
    stubEncConst? := some stubEncNm
    stubEncEqConst? := some stubEncEqNm
  return some {
    codeConst := c
    symCharsConst := symCharsNm
    stubCharsConst := stubCharsNm
    symbolsEqConst := symsEqNm
    stubsEqConst := stubsEqNm
    symbolsFreshConst? := none
    stubsWfConst? := none
    symEncConst?
    symEncEqConst?
    stubEncConst?
    stubEncEqConst?
  }

partial def findBundleForExpr? (e : Expr) : MetaM (Option ReflectedSymBundle) := do
  if e.isAppOfArity ``Arm64.Program.rebase 4 || e.isAppOfArity ``Arm64.Obj.LinkedImage.toProgram 1 then
    return ← findBundleForExpr? (e.getArg! 0)
  if let .const nm _ := e then
    if let some b ← findBundleForCodeConst? nm then
      return some b
    if let .str pre s := nm then
      let base :=
        if s.endsWith "LinkedImage" then (s.dropEnd 11).toString
        else if s.endsWith "Image" then (s.dropEnd 5).toString
        else if s.endsWith "Img" then (s.dropEnd 3).toString
        else s
      let codeNm := Name.mkStr pre (base ++ "Code")
      if let some b ← findBundleForCodeConst? codeNm then
        return some b
      let cands ← try realizeGlobalConst (mkIdent (Name.mkSimple (base ++ "Code")))
                  catch _ => pure []
      for cand in cands do
        if let some b ← findBundleForCodeConst? cand then
          return some b
    if let some (.defnInfo d) := (← getEnv).find? nm then
      if d.value.isConst || d.value.isAppOfArity ``Arm64.Obj.LinkedImage.toProgram 1 ||
          d.value.isAppOfArity ``Arm64.Program.rebase 4 then
        return ← findBundleForExpr? d.value
    if let some b ← ensureAutoBundleForConst? nm then
      return some b
  return none

/-- Find a local hypothesis `h : Obj.Loads li imgExpr` in the local context. -/
def findLoadsForImg? (imgExpr : Expr) : MetaM (Option (Expr × Expr)) := do
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``Arm64.Obj.Loads 2 then
        let liExpr := ty.getArg! 0
        let imgArg := ty.getArg! 1
        if imgArg == imgExpr || (← withReducible (isDefEq imgArg imgExpr)) then
          return some (liExpr, decl.toExpr)
  return none

def projOrApp1? (e : Expr) (fnName structName : Name) (idx : Nat) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity fnName 1 then
    some (e.getArg! 0).consumeMData
  else if let .proj s i b := e then
    if s == structName && i == idx then some b.consumeMData else none
  else
    none

/-- Resolve `tblExpr : List (String × Nat)` to `(bundle, isStubs, htbl : tblExpr = toStringSymbols <charConst>)`. -/
partial def resolveSymTable? (tblExpr : Expr) (fuel : Nat := 4) :
    MetaM (Option (ReflectedSymBundle × Bool × Expr)) := do
  let tbl := (← instantiateMVars tblExpr).consumeMData
  let finishDirect (bundle : ReflectedSymBundle) (isStubs : Bool) :
      MetaM (Option (ReflectedSymBundle × Bool × Expr)) := do
    let charConst := if isStubs then bundle.stubCharsConst else bundle.symCharsConst
    let eqConst := if isStubs then bundle.stubsEqConst else bundle.symbolsEqConst
    let rhs := mkApp (mkConst ``toStringSymbols) (mkConst charConst)
    let htbl ← mkExpectedTypeHint (mkConst eqConst) (← mkEq tblExpr rhs)
    return some (bundle, isStubs, htbl)
  if let some li := projOrApp1? tbl ``Arm64.Obj.LinkedImage.symbols ``Arm64.Obj.LinkedImage 9 then
    if let some bundle ← findBundleForExpr? li then
      return ← finishDirect bundle false
  if let some li := projOrApp1? tbl ``Arm64.Obj.LinkedImage.stubs ``Arm64.Obj.LinkedImage 11 then
    if let some bundle ← findBundleForExpr? li then
      return ← finishDirect bundle true
  if let some prog0 := projOrApp1? tbl ``Arm64.Program.symbols ``Arm64.Program 2 then
    let prog ← if prog0.isConst then (Option.getD · prog0) <$> unfoldDefinition? prog0 else pure prog0
    if prog.isAppOfArity ``Arm64.Program.ofImage 3 then
      if let some (b, isS, h) ← resolveSymTable? (mkApp (mkConst ``Arm64.Obj.Image.symbols) (prog.getArg! 0)) fuel then
        let rhs := mkApp (mkConst ``toStringSymbols) (mkConst b.symCharsConst)
        return some (b, isS, ← mkExpectedTypeHint h (← mkEq tblExpr rhs))
    if let some bundle ← findBundleForExpr? prog0 then
      return ← finishDirect bundle false
  if let some prog0 := projOrApp1? tbl ``Arm64.Program.stubs ``Arm64.Program 3 then
    let prog ← if prog0.isConst then (Option.getD · prog0) <$> unfoldDefinition? prog0 else pure prog0
    if prog.isAppOfArity ``Arm64.Program.ofImage 3 then
      if let some (b, isS, h) ← resolveSymTable? (mkApp (mkConst ``Arm64.Obj.Image.stubs) (prog.getArg! 0)) fuel then
        let rhs := mkApp (mkConst ``toStringSymbols) (mkConst b.stubCharsConst)
        return some (b, isS, ← mkExpectedTypeHint h (← mkEq tblExpr rhs))
    if let some bundle ← findBundleForExpr? prog0 then
      return ← finishDirect bundle true
  let imgMatch? :=
    match projOrApp1? tbl ``Arm64.Obj.Image.symbols ``Arm64.Obj.Image 8 with
    | some img => some (false, img)
    | none => (true, ·) <$> projOrApp1? tbl ``Arm64.Obj.Image.stubs ``Arm64.Obj.Image 10
  if let some (isStubs, imgExpr) := imgMatch? then
    if let some (liExpr, hLoad) ← findLoadsForImg? imgExpr then
      if let some bundle ← findBundleForExpr? liExpr then
        let fieldThm := if isStubs then ``Loads.stubs_eq else ``Loads.symbols_eq
        let hFieldEq := mkApp3 (mkConst fieldThm) liExpr imgExpr hLoad
        let charConst := if isStubs then bundle.stubCharsConst else bundle.symCharsConst
        let eqConst := if isStubs then bundle.stubsEqConst else bundle.symbolsEqConst
        let liField := if isStubs then ``Arm64.Obj.LinkedImage.stubs else ``Arm64.Obj.LinkedImage.symbols
        let rhs := mkApp (mkConst ``toStringSymbols) (mkConst charConst)
        let hCode ← mkExpectedTypeHint (mkConst eqConst) (← mkEq (mkApp (mkConst liField) liExpr) rhs)
        let hTrans ← mkEqTrans hFieldEq hCode
        return some (bundle, isStubs, ← mkExpectedTypeHint hTrans (← mkEq tblExpr rhs))
  if fuel > 0 && tbl.getAppFn.isConst then
    if let some tbl' ← unfoldDefinition? tbl then
      if let some (b, isS, h) ← resolveSymTable? tbl' (fuel - 1) then
        let charConst := if isS then b.stubCharsConst else b.symCharsConst
        let rhs := mkApp (mkConst ``toStringSymbols) (mkConst charConst)
        return some (b, isS, ← mkExpectedTypeHint h (← mkEq tblExpr rhs))
  return none

def evalStringExpr? (e : Expr) : MetaM (Option String) := do
  if let .lit (.strVal s) := e then return some s
  if let some lit ← Arm64.Program.reduceToStringLit? e then
    if let .lit (.strVal s) := lit then return some s
  let e' ← withTransparency .all (whnf e)
  if let .lit (.strVal s) := e' then return some s
  return none

def mkNameEqCharsProof (nameExpr csExpr : Expr) : MetaM Expr := do
  let rhs := mkApp (mkConst ``String.ofList) csExpr
  mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq nameExpr rhs)

def mkGetElemCharsProof (charConst : Name) (k : Nat) (csExpr offExpr : Expr) :
    MetaM Expr := do
  let charListType := mkApp (mkConst ``List [Level.zero]) (mkConst ``Char)
  let natType := mkConst ``Nat
  let prodType := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) charListType natType
  let pairExpr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) charListType natType csExpr offExpr
  let somePair := mkApp2 (mkConst ``Option.some [Level.zero]) prodType pairExpr
  let getElemExpr ← mkAppM ``GetElem?.getElem? #[mkConst charConst, toExpr k]
  mkExpectedTypeHint (← mkEqRefl somePair) (← mkEq getElemExpr somePair)

/-- Prove `Obj.lookup nameExpr tblExpr = some offExpr` (or `= none`), returning `(off?, proof)`. -/
def proveLookupNat? (nameExpr tblExpr : Expr) :
    MetaM (Option (Option Expr × Expr)) := do
  let some nameStr ← evalStringExpr? nameExpr | return none
  let some (bundle, isStubs, htbl) ← resolveSymTable? tblExpr | return none
  if !isStubs then
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
      if let some freshConst := bundle.symbolsFreshConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``lookup_of_allFresh_chars)
          #[tblExpr, mkConst bundle.symCharsConst, htbl, mkConst freshConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (some offExpr, prf)
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
        let stubsExpr := mkApp (mkConst ``Arm64.Program.stubs) (mkConst bundle.codeConst)
        let prf := mkAppN (mkConst ``lookup_symbols_none_of_stub_chars)
          #[tblExpr, stubsExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            htbl, mkConst bundle.stubsEqConst, mkConst wfConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (none, prf)
  else
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``lookup_stub_of_wf_chars)
          #[tblExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            htbl, mkConst wfConst, toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (some offExpr, prf)
  let charConst := if isStubs then bundle.stubCharsConst else bundle.symCharsConst
  let encConst? := if isStubs then bundle.stubEncConst? else bundle.symEncConst?
  let encEqConst? := if isStubs then bundle.stubEncEqConst? else bundle.symEncEqConst?
  let found? ← findInCharAssocConst? charConst nameStr
  let offOpt := found?.map (·.2.2)
  let rhs := match offOpt with
    | some o => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) o
    | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
  let csExpr := match found? with | some (_, cs, _) => cs | none => mkStrCharsExpr nameStr
  let hname ← mkNameEqCharsProof nameExpr csExpr
  if let (some encConst, some encEqConst) := (encConst?, encEqConst?) then
    let step1 := mkAppN (mkConst ``lookupSymbols_eq_lookupEnc)
      #[tblExpr, mkConst charConst, mkConst encConst, htbl, mkConst encEqConst,
        nameExpr, csExpr, hname]
    let encLhs := mkApp3 (mkConst ``lookupEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr) (mkConst encConst)
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (offOpt, ← mkEqTrans step1 step2)
  else
    let step1 := mkAppN (mkConst ``lookup_prepareCharSymbols)
      #[tblExpr, mkConst charConst, htbl, nameExpr, csExpr, hname]
    let encLhs := mkApp3 (mkConst ``lookupEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr)
      (mkApp2 (mkConst ``prepareCharAssocVal) (mkConst ``Nat) (mkConst charConst))
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (offOpt, ← mkEqTrans step1 step2)

/-- Prove `Obj.lookupUnique nameExpr tblExpr = some offExpr` (or `= none`), returning `(off?, proof)`. -/
def proveLookupUniqueNat? (nameExpr tblExpr : Expr) :
    MetaM (Option (Option Expr × Expr)) := do
  let some nameStr ← evalStringExpr? nameExpr | return none
  let some (bundle, isStubs, htbl) ← resolveSymTable? tblExpr | return none
  if !isStubs then
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
      if let some freshConst := bundle.symbolsFreshConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``lookupUnique_of_allFresh_chars)
          #[tblExpr, mkConst bundle.symCharsConst, htbl, mkConst freshConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (some offExpr, prf)
  else
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``lookupUnique_stub_of_wf_chars)
          #[tblExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            htbl, mkConst wfConst, toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (some offExpr, prf)
  let charConst := if isStubs then bundle.stubCharsConst else bundle.symCharsConst
  let encConst? := if isStubs then bundle.stubEncConst? else bundle.symEncConst?
  let encEqConst? := if isStubs then bundle.stubEncEqConst? else bundle.symEncEqConst?
  let found? ← findInCharAssocConst? charConst nameStr
  let offOpt := found?.map (·.2.2)
  let rhs := match offOpt with
    | some o => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) o
    | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
  let csExpr := match found? with | some (_, cs, _) => cs | none => mkStrCharsExpr nameStr
  let hname ← mkNameEqCharsProof nameExpr csExpr
  if let (some encConst, some encEqConst) := (encConst?, encEqConst?) then
    let step1 := mkAppN (mkConst ``lookupUniqueSymbols_eq_lookupUniqueEnc)
      #[tblExpr, mkConst charConst, mkConst encConst, htbl, mkConst encEqConst,
        nameExpr, csExpr, hname]
    let encLhs := mkApp3 (mkConst ``lookupUniqueEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr) (mkConst encConst)
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (offOpt, ← mkEqTrans step1 step2)
  else
    let step1 := mkAppN (mkConst ``lookupUnique_prepareCharSymbols)
      #[tblExpr, mkConst charConst, htbl, nameExpr, csExpr, hname]
    let encLhs := mkApp3 (mkConst ``lookupUniqueEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr)
      (mkApp2 (mkConst ``prepareCharAssocVal) (mkConst ``Nat) (mkConst charConst))
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (offOpt, ← mkEqTrans step1 step2)

/-- Prove `(tblExpr.filter (·.1 == nameExpr)).length = n`, returning `(nExpr, proof)`. -/
def proveFilterLengthNat? (nameExpr tblExpr : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some nameStr ← evalStringExpr? nameExpr | return none
  let some (bundle, isStubs, htbl) ← resolveSymTable? tblExpr | return none
  if !isStubs then
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
      if let some freshConst := bundle.symbolsFreshConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``filter_length_of_allFresh_chars)
          #[tblExpr, mkConst bundle.symCharsConst, htbl, mkConst freshConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (toExpr (1 : Nat), prf)
  else
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``filter_length_stub_of_wf_chars)
          #[tblExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            htbl, mkConst wfConst, toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (toExpr (1 : Nat), prf)
  let charConst := if isStubs then bundle.stubCharsConst else bundle.symCharsConst
  let encConst? := if isStubs then bundle.stubEncConst? else bundle.symEncConst?
  let encEqConst? := if isStubs then bundle.stubEncEqConst? else bundle.symEncEqConst?
  let found? ← findInCharAssocConst? charConst nameStr
  let rhs := toExpr (if found?.isSome then (1 : Nat) else 0)
  let csExpr := match found? with | some (_, cs, _) => cs | none => mkStrCharsExpr nameStr
  let hname ← mkNameEqCharsProof nameExpr csExpr
  let entryTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat)
      (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)))
    (mkConst ``Nat)
  if let (some encConst, some encEqConst) := (encConst?, encEqConst?) then
    let step1 := mkAppN (mkConst ``filterSymbols_length_eq_filterEnc)
      #[tblExpr, mkConst charConst, mkConst encConst, htbl, mkConst encEqConst,
        nameExpr, csExpr, hname]
    let filt := mkApp3 (mkConst ``filterEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr) (mkConst encConst)
    let encLhs := mkApp2 (mkConst ``List.length [Level.zero]) entryTy filt
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (rhs, ← mkEqTrans step1 step2)
  else
    let step1 := mkAppN (mkConst ``filter_length_prepareCharSymbols)
      #[tblExpr, mkConst charConst, htbl, nameExpr, csExpr, hname]
    let filt := mkApp3 (mkConst ``filterEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr)
      (mkApp2 (mkConst ``prepareCharAssocVal) (mkConst ``Nat) (mkConst charConst))
    let encLhs := mkApp2 (mkConst ``List.length [Level.zero]) entryTy filt
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (rhs, ← mkEqTrans step1 step2)

/-- Prove `tblExpr.filter (·.1 == nameExpr) = [(nameExpr, offExpr)]`, returning `(rhs, proof)`. -/
def proveFilterNat? (nameExpr tblExpr : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some nameStr ← evalStringExpr? nameExpr | return none
  let some (bundle, isStubs, htbl) ← resolveSymTable? tblExpr | return none
  if !isStubs then
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
      if let some freshConst := bundle.symbolsFreshConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``filter_of_allFresh_chars)
          #[tblExpr, mkConst bundle.symCharsConst, htbl, mkConst freshConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        let strTy := mkConst ``String
        let natTy := mkConst ``Nat
        let prodTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) strTy natTy
        let pairE := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) strTy natTy nameExpr offExpr
        let rhs := mkApp3 (mkConst ``List.cons [Level.zero]) prodTy pairE
          (mkApp (mkConst ``List.nil [Level.zero]) prodTy)
        return some (rhs, prf)
  return none

/-- Prove `tblExpr.any (·.1 == nameExpr) = b`, returning `(bExpr, proof)`. -/
def proveAnyNat? (nameExpr tblExpr : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some nameStr ← evalStringExpr? nameExpr | return none
  let some (bundle, isStubs, htbl) ← resolveSymTable? tblExpr | return none
  if !isStubs then
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
      if let some freshConst := bundle.symbolsFreshConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``any_of_allFresh_chars)
          #[tblExpr, mkConst bundle.symCharsConst, htbl, mkConst freshConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (mkConst ``true, prf)
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
        let stubsExpr := mkApp (mkConst ``Arm64.Program.stubs) (mkConst bundle.codeConst)
        let prf := mkAppN (mkConst ``any_symbols_false_of_stub_chars)
          #[tblExpr, stubsExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            htbl, mkConst bundle.stubsEqConst, mkConst wfConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (mkConst ``false, prf)
  else
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
        let prf := mkAppN (mkConst ``any_stub_of_wf_chars)
          #[tblExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            htbl, mkConst wfConst, toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (mkConst ``true, prf)
    if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
      if let some wfConst := bundle.stubsWfConst? then
        let hname ← mkNameEqCharsProof nameExpr csExpr
        let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
        let symsExpr := mkApp (mkConst ``Arm64.Program.symbols) (mkConst bundle.codeConst)
        let prf := mkAppN (mkConst ``any_stubs_false_of_symbol_chars)
          #[symsExpr, tblExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
            mkConst bundle.symbolsEqConst, htbl, mkConst wfConst,
            toExpr k, nameExpr, csExpr, offExpr, hname, hk]
        return some (mkConst ``false, prf)
  let charConst := if isStubs then bundle.stubCharsConst else bundle.symCharsConst
  let encConst? := if isStubs then bundle.stubEncConst? else bundle.symEncConst?
  let encEqConst? := if isStubs then bundle.stubEncEqConst? else bundle.symEncEqConst?
  let found? ← findInCharAssocConst? charConst nameStr
  let rhs := mkConst (if found?.isSome then ``true else ``false)
  let csExpr := match found? with | some (_, cs, _) => cs | none => mkStrCharsExpr nameStr
  let hname ← mkNameEqCharsProof nameExpr csExpr
  if let (some encConst, some encEqConst) := (encConst?, encEqConst?) then
    let step1 := mkAppN (mkConst ``anySymbols_eq_anyEnc)
      #[tblExpr, mkConst charConst, mkConst encConst, htbl, mkConst encEqConst,
        nameExpr, csExpr, hname]
    let encLhs := mkApp3 (mkConst ``anyEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr) (mkConst encConst)
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (rhs, ← mkEqTrans step1 step2)
  else
    let step1 := mkAppN (mkConst ``any_prepareCharSymbols)
      #[tblExpr, mkConst charConst, htbl, nameExpr, csExpr, hname]
    let encLhs := mkApp3 (mkConst ``anyEnc) (mkConst ``Nat)
      (mkApp (mkConst ``encodeCharKey) csExpr)
      (mkApp2 (mkConst ``prepareCharAssocVal) (mkConst ``Nat) (mkConst charConst))
    let step2 ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq encLhs rhs)
    return some (rhs, ← mkEqTrans step1 step2)

/-- Prove `progExpr.fnOff nameExpr = offExpr`, returning `(offExpr, proof)`. -/
def proveFnOffNat? (progExpr nameExpr : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some nameStr ← evalStringExpr? nameExpr | return none
  let symsTbl := mkApp (mkConst ``Arm64.Program.symbols) progExpr
  let some (bundle, _, hsyms) ← resolveSymTable? symsTbl | return none
  if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.symCharsConst nameStr then
    if let some freshConst := bundle.symbolsFreshConst? then
      let hname ← mkNameEqCharsProof nameExpr csExpr
      let hk ← mkGetElemCharsProof bundle.symCharsConst k csExpr offExpr
      let prf := mkAppN (mkConst ``fnOff_of_allFresh_chars)
        #[progExpr, mkConst bundle.symCharsConst, hsyms, mkConst freshConst,
          toExpr k, nameExpr, csExpr, offExpr, hname, hk]
      return some (offExpr, prf)
  if let some (k, csExpr, offExpr) ← findInCharAssocConst? bundle.stubCharsConst nameStr then
    if let some wfConst := bundle.stubsWfConst? then
      let stubsTbl := mkApp (mkConst ``Arm64.Program.stubs) progExpr
      let some (_, _, hstubs) ← resolveSymTable? stubsTbl | return none
      let hname ← mkNameEqCharsProof nameExpr csExpr
      let hk ← mkGetElemCharsProof bundle.stubCharsConst k csExpr offExpr
      let prf := mkAppN (mkConst ``fnOff_of_stub_chars)
        #[progExpr, mkConst bundle.symCharsConst, mkConst bundle.stubCharsConst,
          hsyms, hstubs, mkConst wfConst, toExpr k, nameExpr, csExpr, offExpr, hname, hk]
      return some (offExpr, prf)
  return none

/-- Extract `nameExpr` from a predicate `(·.1 == nameExpr)` or `(fun (n, _) => n == nameExpr)`. -/
def extractFstEqName? (predExpr : Expr) : MetaM (Option Expr) := do
  let strTy := mkConst ``String
  let natTy := mkConst ``Nat
  withLocalDeclD `n strTy fun nVar =>
    withLocalDeclD `o natTy fun oVar => do
      let pair := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) strTy natTy nVar oVar
      let app ← whnfCore (mkApp predExpr pair)
      if app.isAppOfArity ``BEq.beq 4 then
        let lhs ← withReducible (whnf (app.getArg! 2))
        let rhs := app.getArg! 3
        if lhs == nVar && !rhs.containsFVar nVar.fvarId! && !rhs.containsFVar oVar.fvarId! then
          return some rhs
      return none

partial def unfoldToAdd (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``HAdd.hAdd 6 then return e
  if let some e' ← unfoldDefinition? e then return ← unfoldToAdd e'
  return e

/-- Prove `lhs = rhs` by `rfl` or `BitVec.add_assoc` (`add_off_add_eq` / `add_add_eq_add_off`). -/
def proveBvEqFast? (lhs rhs : Expr) : MetaM (Option Expr) := do
  let eqTy ← mkEq lhs rhs
  if ← withReducibleAndInstances (isDefEq lhs rhs) then
    return some (← mkExpectedTypeHint (← mkEqRefl rhs) eqTy)
  if !lhs.hasFVar && !rhs.hasFVar then
    if ← isDefEq lhs rhs then
      return some (← mkExpectedTypeHint (← mkEqRefl rhs) eqTy)
  let lhs' ← unfoldToAdd lhs
  let rhs' ← unfoldToAdd rhs
  if lhs'.isAppOfArity ``HAdd.hAdd 6 && rhs'.isAppOfArity ``HAdd.hAdd 6 then
    let l1 := lhs'.getArg! 4
    let l2 := lhs'.getArg! 5
    let r1 ← unfoldToAdd (rhs'.getArg! 4)
    let r2 := rhs'.getArg! 5
    if r1.isAppOfArity ``HAdd.hAdd 6 then
      let b2 := r1.getArg! 4
      let off2 := r1.getArg! 5
      if ← isDefEq l1 b2 then
        let sum23 ← mkAppM ``HAdd.hAdd #[off2, r2]
        if ← isDefEq l2 sum23 then
          let hOff ← mkExpectedTypeHint (← mkEqRefl sum23) (← mkEq l2 sum23)
          let prf := mkApp5 (mkConst ``add_off_add_eq) l1 l2 off2 r2 hOff
          return some (← mkExpectedTypeHint prf eqTy)
    let l1' ← unfoldToAdd l1
    if l1'.isAppOfArity ``HAdd.hAdd 6 then
      let b1 := l1'.getArg! 4
      let off1 := l1'.getArg! 5
      if ← isDefEq b1 r1 then
        let sum12 ← mkAppM ``HAdd.hAdd #[off1, l2]
        if ← isDefEq sum12 r2 then
          let hOff ← mkExpectedTypeHint (← mkEqRefl r2) (← mkEq sum12 r2)
          let prf := mkApp5 (mkConst ``add_add_eq_add_off) b1 off1 l2 r2 hOff
          return some (← mkExpectedTypeHint prf eqTy)
  return none

def mkLookupObjSymbolsNoneProof (objNameExpr tblExpr : Expr) : MetaM Expr := do
  let innerTy := mkApp (mkConst ``List [Level.zero])
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``Nat))
  let noneExpr := mkApp (mkConst ``Option.none [Level.zero]) innerTy
  let lookupExpr := mkApp3 (mkConst ``Arm64.Obj.lookup [Level.zero]) innerTy objNameExpr tblExpr
  mkExpectedTypeHint (← mkEqRefl noneExpr) (← mkEq lookupExpr noneExpr)

/-- Prove `imgExpr.symtab objNameExpr symExpr = targetRhs`. -/
def proveSymtabEq? (imgExpr objNameExpr symExpr targetRhs : Expr) :
    MetaM (Option Expr) := do
  let rhs' ← whnfCore targetRhs
  unless rhs'.isAppOfArity ``Option.some 2 do return none
  let addrExpr := rhs'.getArg! 1
  let baseExpr := mkApp (mkConst ``Arm64.Obj.Image.base) imgExpr
  if let some (liExpr, hLoad) ← findLoadsForImg? imgExpr then
    let hobj ← mkLookupObjSymbolsNoneProof objNameExpr
      (mkApp (mkConst ``Arm64.Obj.LinkedImage.objSymbols) liExpr)
    let liSyms := mkApp (mkConst ``Arm64.Obj.LinkedImage.symbols) liExpr
    if let some (some offExpr, hsym) ← proveLookupNat? symExpr liSyms then
      let bvOff := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) offExpr
      let lhsAddr ← mkAppM ``HAdd.hAdd #[baseExpr, bvOff]
      let some haddr ← proveBvEqFast? lhsAddr addrExpr | return none
      let prf := mkAppN (mkConst ``Loads.symtab_eq_of_lookup_symbols)
        #[liExpr, imgExpr, hLoad, objNameExpr, symExpr, offExpr, addrExpr, hobj, hsym, haddr]
      return some (← mkExpectedTypeHint prf (← mkEq (mkApp3 (mkConst ``Arm64.Obj.Image.symtab) imgExpr objNameExpr symExpr) targetRhs))
    if let some (none, hsym) ← proveLookupNat? symExpr liSyms then
      let liStubs := mkApp (mkConst ``Arm64.Obj.LinkedImage.stubs) liExpr
      if let some (some offExpr, hstub) ← proveLookupNat? symExpr liStubs then
        let bvOff := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) offExpr
        let lhsAddr ← mkAppM ``HAdd.hAdd #[baseExpr, bvOff]
        let some haddr ← proveBvEqFast? lhsAddr addrExpr | return none
        let prf := mkAppN (mkConst ``Loads.symtab_eq_of_lookup_stubs)
          #[liExpr, imgExpr, hLoad, objNameExpr, symExpr, offExpr, addrExpr, hobj, hsym, hstub, haddr]
        return some (← mkExpectedTypeHint prf (← mkEq (mkApp3 (mkConst ``Arm64.Obj.Image.symtab) imgExpr objNameExpr symExpr) targetRhs))
  let hobj ← mkLookupObjSymbolsNoneProof objNameExpr
    (mkApp (mkConst ``Arm64.Obj.Image.objSymbols) imgExpr)
  let imgSyms := mkApp (mkConst ``Arm64.Obj.Image.symbols) imgExpr
  if let some (some offExpr, hsym) ← proveLookupNat? symExpr imgSyms then
    let bvOff := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) offExpr
    let lhsAddr ← mkAppM ``HAdd.hAdd #[baseExpr, bvOff]
    let some haddr ← proveBvEqFast? lhsAddr addrExpr | return none
    let prf := mkAppN (mkConst ``Image.symtab_eq_of_lookup_symbols)
      #[imgExpr, objNameExpr, symExpr, offExpr, addrExpr, hobj, hsym, haddr]
    return some (← mkExpectedTypeHint prf (← mkEq (mkApp3 (mkConst ``Arm64.Obj.Image.symtab) imgExpr objNameExpr symExpr) targetRhs))
  if let some (none, hsym) ← proveLookupNat? symExpr imgSyms then
    let imgStubs := mkApp (mkConst ``Arm64.Obj.Image.stubs) imgExpr
    if let some (some offExpr, hstub) ← proveLookupNat? symExpr imgStubs then
      let bvOff := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) offExpr
      let lhsAddr ← mkAppM ``HAdd.hAdd #[baseExpr, bvOff]
      let some haddr ← proveBvEqFast? lhsAddr addrExpr | return none
      let prf := mkAppN (mkConst ``Image.symtab_eq_of_lookup_stubs)
        #[imgExpr, objNameExpr, symExpr, offExpr, addrExpr, hobj, hsym, hstub, haddr]
      return some (← mkExpectedTypeHint prf (← mkEq (mkApp3 (mkConst ``Arm64.Obj.Image.symtab) imgExpr objNameExpr symExpr) targetRhs))
  return none

/-- Prove an atomic symbol-table equality `lhs = rhs`. -/
partial def proveAtomicSymEq? (lhs rhs : Expr) (fuel : Nat := 4) :
    MetaM (Option Expr) := do
  let eqTy ← mkEq lhs rhs
  if lhs.isAppOfArity ``Arm64.Obj.lookup 3 then
    if let some (offOpt, prf) ← proveLookupNat? (lhs.getArg! 1) (lhs.getArg! 2) then
      let actualRhs := match offOpt with
        | some o => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) o
        | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
      if ← isDefEq actualRhs rhs then
        return some (← mkExpectedTypeHint prf eqTy)
    return none
  if lhs.isAppOfArity ``Arm64.Obj.lookupUnique 3 then
    if let some (offOpt, prf) ← proveLookupUniqueNat? (lhs.getArg! 1) (lhs.getArg! 2) then
      let actualRhs := match offOpt with
        | some o => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) o
        | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
      if ← isDefEq actualRhs rhs then
        return some (← mkExpectedTypeHint prf eqTy)
    return none
  if lhs.isAppOfArity ``List.length 2 && (lhs.getArg! 1).isAppOfArity ``List.filter 3 then
    let filt := lhs.getArg! 1
    if let some nameExpr ← extractFstEqName? (filt.getArg! 1) then
      if let some (nExpr, prf) ← proveFilterLengthNat? nameExpr (filt.getArg! 2) then
        if ← isDefEq nExpr rhs then
          return some (← mkExpectedTypeHint prf eqTy)
    return none
  if lhs.isAppOfArity ``List.filter 3 then
    if let some nameExpr ← extractFstEqName? (lhs.getArg! 1) then
      if let some (rhsExpr, prf) ← proveFilterNat? nameExpr (lhs.getArg! 2) then
        if ← isDefEq rhsExpr rhs then
          return some (← mkExpectedTypeHint prf eqTy)
    return none
  if lhs.isAppOfArity ``List.any 3 then
    if let some nameExpr ← extractFstEqName? (lhs.getArg! 2) then
      if let some (bExpr, prf) ← proveAnyNat? nameExpr (lhs.getArg! 1) then
        if ← isDefEq bExpr rhs then
          return some (← mkExpectedTypeHint prf eqTy)
    return none
  if lhs.isAppOfArity ``Arm64.Program.fnOff 2 then
    if let some (offExpr, prf) ← proveFnOffNat? (lhs.getArg! 0) (lhs.getArg! 1) then
      if ← isDefEq offExpr rhs then
        return some (← mkExpectedTypeHint prf eqTy)
    return none
  if lhs.isAppOfArity ``Arm64.Obj.Image.symtab 3 then
    return ← proveSymtabEq? (lhs.getArg! 0) (lhs.getArg! 1) (lhs.getArg! 2) rhs
  if lhs.isAppOfArity ``Arm64.Program.fnAddr 2 then
    let progExpr := lhs.getArg! 0
    let nameExpr := lhs.getArg! 1
    if let some (offExpr, hfn) ← proveFnOffNat? progExpr nameExpr then
      let progWhnf ← if progExpr.isConst then (Option.getD · progExpr) <$> unfoldDefinition? progExpr else pure progExpr
      let baseExpr ←
        if progWhnf.isAppOfArity ``Arm64.Program.ofImage 3 then
          pure (mkApp (mkConst ``Arm64.Obj.Image.base) (progWhnf.getArg! 0))
        else if progWhnf.isAppOfArity ``Arm64.Program.rebase 4 then
          pure (progWhnf.getArg! 1)
        else
          whnf (mkApp (mkConst ``Arm64.Program.base) progExpr)
      let bvOff := mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) offExpr
      let lhsAddr ← mkAppM ``HAdd.hAdd #[baseExpr, bvOff]
      if let some haddr ← proveBvEqFast? lhsAddr rhs then
        let prf := mkAppN (mkConst ``Program.fnAddr_eq_of_fnOff)
          #[progExpr, nameExpr, offExpr, rhs, hfn, haddr]
        return some (← mkExpectedTypeHint prf eqTy)
    return none
  if fuel > 0 then
    let fn := lhs.getAppFn
    if fn.isConst && !fn.isConstOf ``List.all && !fn.isConstOf ``BEq.beq &&
        !fn.isConstOf ``and && !fn.isConstOf ``not && !fn.isConstOf ``HAdd.hAdd &&
        !fn.isConstOf ``BitVec.ofNat then
      if let some lhs' ← unfoldDefinition? lhs then
        if let some prf ← proveAtomicSymEq? lhs' rhs (fuel - 1) then
          return some (← mkExpectedTypeHint prf eqTy)
  return none

/-- Recursively prove a `sym_guard` goal `goalTy` (`∧`, `List.all`, `&&`, `!`, `==`, symbol/address equalities). -/
partial def proveSymGuardExpr? (goalTy : Expr) : MetaM (Option Expr) := do
  let goalTy ← instantiateMVars goalTy
  if goalTy.isAppOfArity ``And 2 then
    let p := goalTy.getArg! 0
    let q := goalTy.getArg! 1
    let some hp ← proveSymGuardExpr? p | return none
    let some hq ← proveSymGuardExpr? q | return none
    return some (mkApp4 (mkConst ``And.intro) p q hp hq)
  let some (_, lhs, rhs) := goalTy.eq? | return none
  if lhs.isAppOfArity ``and 2 && rhs.isConstOf ``true then
    let a := lhs.getArg! 0
    let b := lhs.getArg! 1
    let some ha ← proveSymGuardExpr? (← mkEq a (mkConst ``true)) | return none
    let some hb ← proveSymGuardExpr? (← mkEq b (mkConst ``true)) | return none
    return some (mkApp4 (mkConst ``and_eq_true_intro) a b ha hb)
  if lhs.isAppOfArity ``not 1 && rhs.isConstOf ``true then
    let a := lhs.getArg! 0
    let some ha ← proveSymGuardExpr? (← mkEq a (mkConst ``false)) | return none
    return some (mkApp2 (mkConst ``not_eq_true_intro) a ha)
  if lhs.isAppOfArity ``not 1 && rhs.isConstOf ``false then
    let a := lhs.getArg! 0
    let some ha ← proveSymGuardExpr? (← mkEq a (mkConst ``true)) | return none
    return some (mkApp2 (mkConst ``not_eq_false_intro) a ha)
  if lhs.isAppOfArity ``List.all 3 && rhs.isConstOf ``true then
    let elemTy := lhs.getArg! 0
    let xs0 := lhs.getArg! 1
    let fExpr := lhs.getArg! 2
    let xs ← if xs0.isConst then (Option.getD · xs0) <$> unfoldDefinition? xs0 else whnfCore xs0
    if xs.isAppOfArity ``List.nil 1 then
      let prf := mkApp2 (mkConst ``all_nil_eq_true) elemTy fExpr
      return some (← mkExpectedTypeHint prf goalTy)
    if xs.isAppOfArity ``List.cons 3 then
      let head := xs.getArg! 1
      let tail := xs.getArg! 2
      let fExpr' ← if fExpr.isLambda then pure fExpr else whnfCore fExpr
      let mut headGoal := (mkApp fExpr' head).headBeta
      for _ in [:4] do
        headGoal ← whnfCore headGoal
        if headGoal.isAppOf ``and || headGoal.isAppOf ``not || headGoal.isAppOf ``BEq.beq ||
            headGoal.isAppOf ``List.any || headGoal.isAppOf ``List.all then
          break
        let some next ← unfoldDefinition? headGoal | break
        headGoal := next
      let some hHead ← proveSymGuardExpr? (← mkEq headGoal (mkConst ``true)) | return none
      let hHeadTyped ← mkExpectedTypeHint hHead (← mkEq (mkApp fExpr head) (mkConst ``true))
      let tailAll := mkApp3 (mkConst ``List.all [Level.zero]) elemTy tail fExpr
      let some hTail ← proveSymGuardExpr? (← mkEq tailAll (mkConst ``true)) | return none
      let prf := mkApp6 (mkConst ``all_cons_eq_true) elemTy head tail fExpr hHeadTyped hTail
      return some (← mkExpectedTypeHint prf goalTy)
  if lhs.isAppOfArity ``BEq.beq 4 && rhs.isConstOf ``true then
    let a := lhs.getArg! 2
    let b := lhs.getArg! 3
    if let some hab ← proveAtomicSymEq? a b then
      return some (← mkAppM ``beq_eq_true_of_eq #[hab])
    if let some hab ← proveBvEqFast? a b then
      return some (← mkAppM ``beq_eq_true_of_eq #[hab])
  if let some prf ← proveAtomicSymEq? lhs rhs then
    return some prf
  if let some prf ← proveBvEqFast? lhs rhs then
    return some prf
  return none

/-- Fast reflected tactic for symbol-table guards (`Obj.lookup`, `Obj.lookupUnique`,
    `symbols.filter`, `(symbols.filter _).length`, `symbols.any`, `Program.fnOff`,
    `Program.fnAddr`, `Image.symtab`, and boolean/conjunction combinations thereof). -/
elab "sym_guard" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  if let some prf ← proveSymGuardExpr? goalTy then
    closeMainGoal `sym_guard prf
  else
    throwTacticEx `sym_guard goal m!"could not discharge symbol guard"

end ProofLib.ObjectLoad

end

namespace ProofLib.ObjectLoad

open Arm64.Obj

/-! ## Linear Relocation Evaluator and `FrozenLoaded` Assembly -/

/-- Apply a run `rs` of 8-byte relocations, sorted by offset and non-overlapping, to `tail`, which
    starts at data offset `cur` and has length `len`. Fails if the run is not of that shape. -/
def relocRun (b : BitVec 64) : Nat → Nat → List (BitVec 8) → List DataReloc →
    Option (List (BitVec 8))
  | _, _, tail, [] => some tail
  | cur, len, tail, r :: rs =>
    if cur ≤ r.off && r.width == 8 && r.off - cur + 8 ≤ len then
      (relocRun b (r.off + 8) (len - (r.off - cur + 8)) (tail.drop (r.off - cur + 8)) rs).map
        fun rest => tail.take (r.off - cur) ++ bytesLE 8 (b + BitVec.ofNat 64 r.target) ++ rest
    else none

theorem relocRun_spec (b : BitVec 64) :
    ∀ (rs : List DataReloc) (pfx tail out : List (BitVec 8)) (cur : Nat),
      pfx.length = cur → relocRun b cur tail.length tail rs = some out →
      rs.foldlM (DataReloc.apply b) (pfx ++ tail) = .ok (pfx ++ out) ∧
        out.length = tail.length
  | [], _, _, _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | r :: rs, pfx, tail, out, cur, hpfx, h => by
    simp only [relocRun, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    split at h
    · rename_i hc
      obtain ⟨⟨hcur, hw⟩, hlen⟩ := hc
      obtain ⟨rest, hrec, rfl⟩ := Option.map_eq_some_iff.mp h
      have hd : (tail.drop (r.off - cur + 8)).length = tail.length - (r.off - cur + 8) := by
        simp
      rw [← hd] at hrec
      obtain ⟨ih, hrl⟩ := relocRun_spec b rs
        (pfx ++ tail.take (r.off - cur) ++ bytesLE 8 (b + BitVec.ofNat 64 r.target)) _ rest
        (r.off + 8) (by simp [hpfx, bytesLE]; omega) hrec
      have htake : (pfx ++ tail).take r.off = pfx ++ tail.take (r.off - cur) := by
        rw [List.take_append, hpfx, List.take_of_length_le (by omega)]
      have hdrop : (pfx ++ tail).drop (r.off + 8) = tail.drop (r.off - cur + 8) := by
        rw [List.drop_append, hpfx, List.drop_eq_nil_of_le (by omega), List.nil_append]
        congr 1; omega
      simp only [List.foldlM_cons, DataReloc.apply, hw, show (8 == 4) = false from rfl,
        Bool.false_and, bind, Except.bind, pure, Except.pure, htake, hdrop]
      refine ⟨by simpa [List.append_assoc] using ih, ?_⟩
      simp only [List.length_append, List.length_take, hrl, hd, bytesLE, List.length_map,
        List.length_range]
      omega
    · cases h

/-- Apply each run of `runs` in turn, each starting at data offset `0`. -/
def relocChunks (b : BitVec 64) (data : List (BitVec 8)) :
    List (List DataReloc) → Option (List (BitVec 8))
  | [] => some data
  | rs :: runs => (relocRun b 0 data.length data rs).bind fun d => relocChunks b d runs

theorem relocChunks_spec (b : BitVec 64) :
    ∀ (runs : List (List DataReloc)) (data out : List (BitVec 8)),
      relocChunks b data runs = some out → runs.flatten.foldlM (DataReloc.apply b) data = .ok out
  | [], _, _, h => by cases h; rfl
  | rs :: runs, data, out, h => by
    obtain ⟨d, hd, hrest⟩ := Option.bind_eq_some_iff.mp h
    have h1 := (relocRun_spec b rs [] data d 0 rfl hd).1
    rw [List.nil_append, List.nil_append] at h1
    rw [List.flatten_cons, List.foldlM_append, h1]
    exact relocChunks_spec b runs d out hrest

/-- If `li` loads at `b` as `img`, then `img.FrozenLoaded s` follows from: the code held `r-x` at
    `b`, the relocated data equal to `ro ++ rest` with `ro` held `r--` at the data address and
    covering every rodata section, and the GOT held `r--`. -/
theorem frozenLoaded_of_loads {li : LinkedImage} {img : Image} {s : Arm64.State} {b : BitVec 64}
    {ro rest : List (BitVec 8)} {n : Nat}
    (hL : Loads li img) (hb : img.base = b) (hcwrap : b.toNat + li.code.length ≤ 2 ^ 64)
    (hdwrap : li.dataOff + (ro ++ rest).length < 2 ^ 64)
    (hrelocs : li.relocs.foldlM (DataReloc.apply b) (li.data ++ List.replicate li.bss 0) =
      .ok (ro ++ rest))
    (hn : ro.length = n)
    (hcover : (li.roData.all fun r => decide (li.dataOff ≤ r.1 ∧ r.1 + r.2 ≤ li.dataOff + n)) = true)
    (hcode : HoldsBytes s.mem b li.code (fun _ => Arm64.Perm.rx))
    (hro : HoldsBytes s.mem (b + BitVec.ofNat 64 li.dataOff) ro (fun _ => Arm64.Perm.ro))
    (hgot : HoldsBytes s.mem (b + BitVec.ofNat 64 li.gotOff)
      ((li.got.map (GotEntry.value b)).flatMap (bytesLE 8)) (fun _ => Arm64.Perm.ro)) :
    img.FrozenLoaded s := by
  unfold Loads at hL
  rw [hb] at hL
  obtain ⟨data, hd, hal, -, -, rfl⟩ := ProofLib.ObjectLoad.load_eq_ok hL
  rw [hrelocs] at hd
  cases hd
  refine Image.frozenLoaded_iff.2
    ⟨Arm64.Program.CodeLoaded.intro ?_ hcwrap hcode, ?_, hgot⟩
  · show b.toNat % 4 = 0
    simp only [pageSize] at hal; omega
  · intro i hi a hisro
    dsimp only [Image.isRoData, a] at hisro ⊢
    simp only [List.any_map, List.any_eq_true, Function.comp_def, decide_eq_true_eq] at hisro
    obtain ⟨⟨o, len⟩, hmem, hlt⟩ := hisro
    have hc := List.all_eq_true.mp hcover _ hmem
    simp only [decide_eq_true_eq] at hc
    have hi' : i < ro.length := by
      refine Nat.lt_of_not_le fun hge => ?_
      simp only [List.length_append] at hi hdwrap
      subst hn
      have hsub : (b + BitVec.ofNat 64 li.dataOff + BitVec.ofNat 64 i -
          (b + BitVec.ofNat 64 o)).toNat = li.dataOff + i - o := by
        have heq : b + BitVec.ofNat 64 li.dataOff + BitVec.ofNat 64 i - (b + BitVec.ofNat 64 o) =
            BitVec.ofNat 64 (li.dataOff + i - o) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact ProofLib.ObjectLoad.bv_add_sub_add_of_le b (by omega) (by omega)
        rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at hlt
      omega
    rw [List.getElem_append_left hi']
    exact hro i hi'

end ProofLib.ObjectLoad

namespace ProofLib
export Arm64.Program (
  fnAddr_back fnAddr_callee_add_of_fnOff fnAddr_callee_sub_of_fnOff fnAddr_rebase_add_of_fnOff
  reduceToStringLit? reduceFnOffSym reduceFnAddrSym reduceFnAddrRebase
  reduceFnSizeSym reduceFnFrameBytesSym
  subroutineOk_of_rebase
)
export ProofLib.ObjectLoad (
  relocRun relocRun_spec relocChunks relocChunks_spec frozenLoaded_of_loads
)

private meta def elabDeclareFixedRebasedProgram (rebasedName : Lean.Ident)
    (baseTerm progTerm : Lean.Syntax.Term) : Lean.Elab.Command.CommandElabM Unit := do
  let thmId := Lean.mkIdentFrom rebasedName (rebasedName.getId.appendAfter "_subroutineOk")
  Lean.Elab.Command.elabCommand (← `(command|
    @[irreducible, wp_unfold] def $rebasedName : Arm64.Program :=
      Arm64.Program.rebase $progTerm $baseTerm))
  Lean.Elab.Command.elabCommand (← `(command|
    theorem $thmId {α : Type} {S : Type} [Arm64.ToBaseSpec S α]
        {sym : String} {spec : S}
        (hok : Arm64.Program.subroutineOk (Arm64.Program.rebase $progTerm $baseTerm) sym spec) :
        Arm64.Program.subroutineOk $rebasedName sym spec := by
      delta $rebasedName
      exact hok))

private meta def elabDeclareImageRebasedProgram (rebasedName : Lean.Ident)
    (progTerm imgTerm : Lean.Syntax.Term) : Lean.Elab.Command.CommandElabM Unit := do
  let thmId := Lean.mkIdentFrom rebasedName (rebasedName.getId.appendAfter "_subroutineOk")
  Lean.Elab.Command.elabCommand (← `(command|
    @[irreducible, wp_unfold] def $rebasedName (b : BitVec 64)
        (hooks : String → Option (Arm64.State → Arm64.State) := fun _ => none) : Arm64.Program :=
      Arm64.Program.rebase $progTerm b hooks))
  Lean.Elab.Command.elabCommand (← `(command|
    theorem $thmId {α : Type} {img : Arm64.Obj.Image}
        {hooks : String → Option (Arm64.State → Arm64.State)} {sym : String} {spec : Arm64.Spec α}
        (hload : Arm64.Obj.Loads $imgTerm img)
        (hok : Arm64.Program.subroutineOk ($rebasedName img.base hooks) sym spec) :
        Arm64.Program.subroutineOk (Arm64.Program.ofImage img hooks) sym spec := by
      delta $rebasedName at hok
      exact Arm64.Program.subroutineOk_of_rebase rfl hload hok))

/-- Declare an `@[irreducible]` rebased `Program` together with its `<rebasedName>_subroutineOk`
    transport theorem in a single line:
    - `declare_rebased_program <rebasedName> <baseConst> <rawProgram>` for `(baseConst : BitVec 64)`
      and `(rawProgram : Arm64.Program)`.
    - `declare_rebased_program <rebasedName> <rawProgram> <linkedImage>` for
      `(rawProgram : Arm64.Program)` and `(linkedImage : Arm64.Obj.LinkedImage)`. -/
elab "declare_rebased_program " rebasedName:ident arg2:term:arg arg3:term:arg : command => do
  let kind ← Lean.Elab.Command.liftTermElabM do
    let e2 ← Lean.Elab.Term.elabTerm arg2 none
    let e3 ← Lean.Elab.Term.elabTerm arg3 none
    let ty2 ← Lean.instantiateMVars (← Lean.Meta.inferType e2)
    let ty3 ← Lean.instantiateMVars (← Lean.Meta.inferType e3)
    let bv64Ty := Lean.mkApp (Lean.mkConst ``BitVec) (Lean.toExpr (64 : Nat))
    let progTy := Lean.mkConst ``Arm64.Program
    let liTy := Lean.mkConst ``Arm64.Obj.LinkedImage
    if (← Lean.Meta.isDefEq ty2 bv64Ty) && (← Lean.Meta.isDefEq ty3 progTy) then
      return Sum.inl ()
    else if (← Lean.Meta.isDefEq ty2 progTy) && (← Lean.Meta.isDefEq ty3 liTy) then
      return Sum.inr ()
    else
      throwError "declare_rebased_program: expected `(baseConst : BitVec 64) (rawProgram : Program)` or `(rawProgram : Program) (linkedImage : Obj.LinkedImage)`, got arguments of types `{ty2}` and `{ty3}`"
  match kind with
  | .inl () => elabDeclareFixedRebasedProgram rebasedName arg2 arg3
  | .inr () => elabDeclareImageRebasedProgram rebasedName arg2 arg3

end ProofLib

end
