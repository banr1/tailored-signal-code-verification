/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.Invariant
public import ProofLib.Library
public import ProofLib.LiteralFetchLint
import Arm64.Trusted.Spec.SepLogic

/-!
# Call-Site Relocation Verification

Layout-generic verification of relocatable `LibrarySpec` functions containing 26-bit PC-relative
branch relocations (`B`/`BL`, `R_AARCH64_JUMP26`/`R_AARCH64_CALL26`). Models linker call-site
patching via `Obj.patchCalls` and proves `Contract.holds_of_callFn` for functions calling
intra-library or external symbols.
-/

@[expose] public section

namespace Arm64
namespace Obj

def Image.Resolves (img : Image) (li : LinkedImage)
    (names : List String) (resolve : String → BitVec 64) : Prop :=
  Loads li img ∧
  ∀ n ∈ names, ∃ off, li.resolveSym n = some off ∧
    resolve n = img.base + BitVec.ofNat 64 off

end Obj

def Obj.Image.CallCtx (img : Obj.Image) (libs trusted : List LibrarySpec) (names : List String)
    (resolve : String → BitVec 64) : Prop :=
  ∃ li : Obj.LinkedImage,
    (∀ D ∈ libs, D.ObjectLoaded li ∨ (D ∈ trusted ∧ D.ProvidedAsExterns li)) ∧
    img.Resolves li names resolve

namespace Obj

def patchCalls (calls : List (Nat × String)) (words : List (BitVec 32)) (a : BitVec 64)
    (resolve : String → BitVec 64) : List (BitVec 32) :=
  words.mapIdx fun j w =>
    match calls.find? (·.1 == 4 * j) with
    | some (_, sym) => branchWord w (a + BitVec.ofNat 64 (4 * j)) (resolve sym)
    | none => w

theorem branchWord_imm {w : BitVec 32} {place target : BitVec 64}
    (hr : BranchInRange place target) :
    ((branchWord w place target).extractLsb' 0 26).signExtend 64 <<< 2 = target - place := by
  obtain ⟨h4, hfit1, hfit2⟩ := hr
  unfold branchWord
  generalize target - place = d at h4 hfit1 hfit2 ⊢
  have hlt : d + 0x8000000#64 < 0x10000000#64 := by
    rw [BitVec.toInt_eq_toNat_cond] at hfit1 hfit2
    rw [BitVec.lt_def, BitVec.toNat_add]
    have := d.isLt
    simp only [BitVec.toNat_ofNat]
    split at hfit1 <;> omega
  have hal : d &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h4
  bv_bits

theorem branchWord_mask {w : BitVec 32} {place target : BitVec 64} :
    branchWord w place target &&& 0xfc000000#32 = w &&& 0xfc000000#32 := by
  unfold branchWord
  generalize (target - place) >>> 2 = d
  bv_bits

set_option linter.deprecated false in
theorem decode_branch {v : BitVec 32} {off : BitVec 64}
    (hv : v &&& 0x7c000000#32 = 0x14000000#32)
    (himm : (v.extractLsb' 0 26).signExtend 64 <<< 2 = off) :
    decode v = if v.getLsbD 31 then some (.bl off)
      else some (.b off) := by
  have h1 : (v == 0xd503201f#32) = false := by bv_bits
  have h2 : (v &&& 0xffe0001f#32 == 0xd4000001#32) = false := by bv_bits
  have h3 : (v &&& 0xffe0001f#32 == 0xd4200000#32) = false := by bv_bits
  have h3a : (v &&& 0xfffff01f#32 == 0xd503201f#32) = false := by bv_bits
  have h3b : (v &&& 0xffff0000#32 == 0x00000000#32) = false := by bv_bits
  have h3c : (v &&& 0xffffffe0#32 == 0xd50b7420#32) = false := by bv_bits
  have h4 : (v &&& 0x1f000000#32 == 0x10000000#32) = false := by bv_bits
  have h5 : (v &&& 0x1f800000#32 == 0x11000000#32) = false := by bv_bits
  have h6 : (v &&& 0x1f800000#32 == 0x12000000#32) = false := by bv_bits
  have h7 : (v &&& 0x1f800000#32 == 0x12800000#32) = false := by bv_bits
  have h8 : (v &&& 0x1f800000#32 == 0x13000000#32) = false := by bv_bits
  have h9 : (v &&& 0x7f800000#32 == 0x13800000#32) = false := by bv_bits
  have h10 : (v &&& 0x7c000000#32 == 0x14000000#32) = true := by bv_bits
  unfold decode
  rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3]),
    if_neg (by simp [h3a]), if_neg (by simp [h3b]), if_neg (by simp [h3c]), if_neg (by simp [h4]),
    if_neg (by simp [h5]), if_neg (by simp [h6]), if_neg (by simp [h7]), if_neg (by simp [h8]),
    if_neg (by simp [h9]), if_pos (by simp [h10])]
  simp only [himm]

theorem decode_branchWord_bl {w : BitVec 32} (hw : w &&& 0xfc000000#32 = 0x94000000#32)
    {place target : BitVec 64} (hr : BranchInRange place target) :
    decode (branchWord w place target) =
      some (.bl (target - place)) := by
  have himm := branchWord_imm (w := w) hr
  have hv := (branchWord_mask (w := w) (place := place) (target := target)).trans hw
  generalize branchWord w place target = v at himm hv ⊢
  have hc : v &&& 0x7c000000#32 = 0x14000000#32 := by bv_bits
  have h11 : v.getLsbD 31 = true := by bv_bits
  rw [decode_branch hc himm, h11]; rfl

theorem decode_branchWord_b {w : BitVec 32} (hw : w &&& 0xfc000000#32 = 0x14000000#32)
    {place target : BitVec 64} (hr : BranchInRange place target) :
    decode (branchWord w place target) =
      some (.b (target - place)) := by
  have himm := branchWord_imm (w := w) hr
  have hv := (branchWord_mask (w := w) (place := place) (target := target)).trans hw
  generalize branchWord w place target = v at himm hv ⊢
  have hc : v &&& 0x7c000000#32 = 0x14000000#32 := by bv_bits
  have h11 : v.getLsbD 31 = false := by bv_bits
  rw [decode_branch hc himm, h11]; rfl

set_option linter.literalFetch false in
theorem fetch_patchCalls_bl {prog : Program} {calls : List (Nat × String)}
    {words : List (BitVec 32)} {a : BitVec 64} {resolve : String → BitVec 64} {r : Nat × String}
    (h : prog.hasWords a (patchCalls calls words a resolve))
    (hr : calls.find? (·.1 == r.1) = some r) (h4 : r.1 % 4 = 0)
    (hlen : r.1 / 4 < words.length)
    (hw : words[r.1 / 4] &&& 0xfc000000#32 = 0x94000000#32)
    (hrange : BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2)) :
    prog.fetch (a + BitVec.ofNat 64 r.1) =
      some (.bl (resolve r.2 - (a + BitVec.ofNat 64 r.1))) := by
  have hj : r.1 = 4 * (r.1 / 4) := by omega
  have hlen' : r.1 / 4 < (patchCalls calls words a resolve).length := by
    simp [patchCalls, hlen]
  have hf := Program.fetch_of_hasWords h (r.1 / 4) hlen'
  rw [← hj] at hf
  rw [hf]
  have hget : (patchCalls calls words a resolve)[r.1 / 4] =
      branchWord words[r.1 / 4] (a + BitVec.ofNat 64 r.1) (resolve r.2) := by
    simp only [patchCalls, List.getElem_mapIdx]
    rw [← hj, hr]
  rw [hget]
  exact decode_branchWord_bl hw hrange

/-- A call-free word slice `(words.drop k).take n` of a linker-patched function is held unpatched
    at `a + 4 * k`. -/
theorem hasWords_patchCalls_slice {prog : Program} {calls : List (Nat × String)}
    {words : List (BitVec 32)} {a : BitVec 64} {resolve : String → BitVec 64} (k n : Nat)
    (h : prog.hasWords a (patchCalls calls words a resolve))
    (hn : 0 < n) (hkn : k + n ≤ words.length)
    (hfree : ∀ j < n, calls.find? (·.1 == 4 * (k + j)) = none) :
    prog.hasWords (a + BitVec.ofNat 64 (4 * k)) ((words.drop k).take n) := by
  obtain ⟨hb, hr, hs, ho⟩ := h
  have hlen : (patchCalls calls words a resolve).length = words.length := List.length_mapIdx
  have hsl : ((words.drop k).take n).length = n := by simp; omega
  rw [hlen] at hb hs ho
  have hoff : (a + BitVec.ofNat 64 (4 * k) - prog.base).toNat = (a - prog.base).toNat + 4 * k := by
    rw [show a + BitVec.ofNat 64 (4 * k) - prog.base = (a - prog.base) + BitVec.ofNat 64 (4 * k)
      by bv_bits, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold Program.hasWords Program.hasWordsOff Program.hookFree
  simp only [hoff, hsl]
  refine ⟨by omega, fun i hi => ?_, ?_, ?_⟩
  · have hi' : k + i < (patchCalls calls words a resolve).length := by omega
    rw [show (a - prog.base).toNat + 4 * k + 4 * i = (a - prog.base).toNat + 4 * (k + i) by omega,
      hr (k + i) hi']
    simp [patchCalls, hfree i (by omega)]
  all_goals
    rw [List.all_eq_true] at hs ho ⊢
    rintro ⟨nm, o⟩ hx
    first | have := hs _ hx | have := ho _ hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at this ⊢
    exact this.imp_left fun _ => by omega

theorem disp_sub_eq (base : BitVec 64) (off k t : Nat) :
    (base + BitVec.ofNat 64 t) - (base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      BitVec.ofNat 64 t - BitVec.ofNat 64 (off + k) := by
  have h1 : BitVec.ofNat 64 (off + k) = BitVec.ofNat 64 off + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [h1]
  bv_bits

theorem branchInRange_to_prop {base : BitVec 64} {off roff t : Nat}
    (h : branchInRange (off + roff) t = true) :
    BranchInRange (base + BitVec.ofNat 64 off + BitVec.ofNat 64 roff)
      (base + BitVec.ofNat 64 t) := by
  unfold branchInRange at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold BranchInRange
  rw [disp_sub_eq]
  exact ⟨h1, h2, h3⟩

theorem readWordOff_patchBranchBytes {prog : Program} {bs : List (BitVec 8)}
    {base : BitVec 64} {off j t : Nat} {w w' : BitVec 32}
    (hal : off % 4 = 0)
    (htake : (prog.code.drop (off + 4 * j)).take 4 =
      patchBranchBytes ((bs.drop (4 * j)).take 4) (off + 4 * j) t)
    (hread : ({ code := bs } : Program).readWordOff (4 * j) = some w')
    (hmask : (w' &&& 0xfc000000#32) = (w &&& 0xfc000000#32)) :
    prog.readWordOff (off + 4 * j) =
      some (branchWord w (base + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * j))
        (base + BitVec.ofNat 64 t)) := by
  have hk1 : (off + 4 * j) % 4 = 0 := by omega
  have hk2 : (4 * j) % 4 = 0 := by omega
  simp only [Program.readWordOff, hk1, hk2, ne_eq, not_true_eq_false, ↓reduceIte] at hread ⊢
  rcases hbs : bs.drop (4 * j) with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _⟩⟩⟩⟩ <;>
    simp [hbs] at hread
  subst hread
  rcases hprog : prog.code.drop (off + 4 * j) with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _⟩⟩⟩⟩ <;>
    simp [hbs, hprog, patchBranchBytes, bytesLE, List.range_succ, List.range_zero] at htake
  obtain ⟨rfl, rfl, rfl, rfl⟩ := htake
  simp only [Option.some.injEq]
  unfold branchWord
  rw [disp_sub_eq]
  generalize BitVec.ofNat 64 t - BitVec.ofNat 64 (off + 4 * j) = d
  revert hmask
  bv_bits

/-- Establish `li.honours o = true` for an object with `o.relocFns = []` and `o.dataSyms = []`
    from its `fns` and `callFns` checks without unfolding `li` at the call site. -/
theorem LinkedImage.honours_of_fns_callFns {li : LinkedImage} {o : ObjectInfo}
    {syms : List (String × Nat)}
    (hlookup : lookup o.name li.objSymbols = some syms)
    (hreloc : o.relocFns = [])
    (hdata : o.dataSyms = [])
    (hfn : (o.fns.all fun (f, bs) =>
      match lookupUnique f syms with
      | none => false
      | some off =>
        lookup f li.symbols == some off &&
        off % 4 == 0 && bytesAt li.code off bs &&
          li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true)
    (hcf : (o.callFns.all fun (f, bs, calls) =>
      match lookupUnique f syms with
      | none => false
      | some off =>
        lookup f li.symbols == some off &&
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
        li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true) :
    li.honours o = true := by
  unfold LinkedImage.honours
  rw [hlookup, hreloc, hdata]
  simp only [List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hfn, hcf⟩

theorem LinkedImage.honours_callFn {li : LinkedImage} {o : ObjectInfo} (h : li.honours o = true)
    {f : String} {bs : List (BitVec 8)} {calls : List (Nat × String)}
    (hf : (f, bs, calls) ∈ o.callFns) :
    ∃ syms off, lookup o.name li.objSymbols = some syms ∧ lookupUnique f syms = some off ∧
      off % 4 = 0 ∧ bs.length % 4 = 0 ∧ off + bs.length ≤ li.code.length ∧
      (∀ r ∈ calls, ∃ t, li.resolveSym r.2 = some t ∧ branchInRange (off + r.1) t = true) ∧
      (∀ j < bs.length / 4,
        (li.code.drop (off + 4 * j)).take 4 =
          let w := (bs.drop (4 * j)).take 4
          match calls.find? (·.1 == 4 * j) with
          | some (_, sym) => patchBranchBytes w (off + 4 * j) ((li.resolveSym sym).getD 0)
          | none => w) ∧
      ∀ s ∈ li.stubs, ¬(off ≤ s.2 ∧ s.2 < off + bs.length) := by
  unfold LinkedImage.honours at h
  split at h
  · contradiction
  rename_i syms hsyms
  simp only [Bool.and_eq_true] at h
  have hfn := List.all_eq_true.1 h.1.1.2 _ hf
  simp only at hfn
  split at hfn
  · contradiction
  rename_i off hoff
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.all_eq_true, List.mem_range] at hfn
  obtain ⟨⟨⟨⟨⟨⟨_hsym, hal⟩, hbmod⟩, hlen⟩, hcalls⟩, hwords⟩, hstubs⟩ := hfn
  refine ⟨syms, off, hsyms, hoff, hal, hbmod, hlen, ?_, hwords, ?_⟩
  · intro ⟨roff, sym⟩ hr
    have hc := hcalls (roff, sym) hr
    simp only at hc
    split at hc
    · rename_i t ht
      exact ⟨t, ht, hc⟩
    · contradiction
  · intro s hs
    have := hstubs s hs
    simp at this
    omega

end Obj

/-- Decidable check that `o.callFns` records `(symName, bs, calls)` where `bs` has the same words
    as `words` outside `calls` and the same 6-bit branch opcode at each offset in `calls`. -/
def checkCallFn (o : Obj.ObjectInfo) (symName : String) (calls : List (Nat × String))
    (words : List (BitVec 32)) : Bool :=
  match Obj.lookup symName o.callFns with
  | some (bs, calls') =>
    calls' == calls &&
    decide (0 < words.length) &&
    decide (4 * words.length = bs.length) &&
    (List.range words.length).all fun j =>
      match ({ code := bs } : Program).readWordOff (4 * j), words[j]? with
      | some w', some w =>
        if (calls.find? (·.1 == 4 * j)).isSome then
          (w' &&& 0xfc000000#32) == (w &&& 0xfc000000#32)
        else
          w' == w
      | _, _ => false
  | none => false

/-- Layout-generic contract verification for a function whose text section has only direct branch
    relocations (`B`/`BL`, addend 0) to external symbols. -/
theorem Contract.holds_of_callFn {libs trusted : List LibrarySpec} {img : Obj.Image}
    {X : String → Option (State → State)} {D : LibrarySpec} {c : Contract}
    {o : Obj.ObjectInfo} {calls : List (Nat × String)} {words : List (BitVec 32)}
    (hLinks : LinksIn libs img trusted) (hD : D ∈ libs) (hDT : D ∉ trusted)
    (ho : D.obj = some o)
    (hcheck : checkCallFn o c.sym calls words = true)
    (habs : ∀ a resolve,
      img.CallCtx libs trusted (calls.map (·.2)) resolve →
      (∀ r ∈ calls, Obj.BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2)) →
      (Program.ofImage img (Rust.withPanics X)).hasWords a
        (Obj.patchCalls calls words a resolve) →
      subroutine_ok (Program.ofImage img (Rust.withPanics X)) a (c.spec.inImage img)) :
    Contract.Holds D img X c := by
  unfold checkCallFn at hcheck
  split at hcheck <;> try contradiction
  rename_i bs calls' hbs
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hcheck
  obtain ⟨⟨⟨hc_eq, hwpos⟩, hlen⟩, hwordsCheck⟩ := hcheck
  subst calls'
  obtain ⟨li, hobjs, hl⟩ := hLinks
  have ho_mem : o ∈ li.objects := LinksIn.objectLoaded hobjs hD hDT ho
  obtain ⟨_, _, _, hwf, hwrap, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
  obtain ⟨_, hcode, _, hstubsEq, hobjSyms, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  have hcodeLe := Obj.LinkedImage.wellFormed_code_le hwf
  obtain ⟨syms, off, hsyms, hoff, hal, _hbmod, hend, hcalls, hwords_li, hstubs⟩ :=
    Obj.LinkedImage.honours_callFn (Obj.LinkedImage.wellFormed_objects hwf o ho_mem)
      (Obj.lookup_mem hbs)
  let a : BitVec 64 := img.base + BitVec.ofNat 64 off
  let resolve : String → BitVec 64 := fun n =>
    img.base + BitVec.ofNat 64 ((li.resolveSym n).getD 0)
  have haddr : D.addr? img c.sym = some a := by
    simp [LibrarySpec.addr?, ho, hobjSyms, hsyms, hoff, a]
  have hctx : img.CallCtx libs trusted (calls.map (·.2)) resolve := by
    refine ⟨li, hobjs, hl, ?_⟩
    intro n hn
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hn
    obtain ⟨t, ht, -⟩ := hcalls r hr
    exact ⟨t, ht, by simp [resolve, ht]⟩
  have hrange : ∀ r ∈ calls, Obj.BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2) := by
    intro r hr
    obtain ⟨t, ht, hbr⟩ := hcalls r hr
    simp only [a, resolve, ht, Option.getD_some]
    exact Obj.branchInRange_to_prop hbr
  have hoff_sub : (a - (Program.ofImage img (Rust.withPanics X)).base).toNat = off := by
    have : a - (Program.ofImage img (Rust.withPanics X)).base = BitVec.ofNat 64 off := by
      show img.base + BitVec.ofNat 64 off - img.base = _
      bv_arith
    rw [this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hwords : (Program.ofImage img (Rust.withPanics X)).hasWords a
      (Obj.patchCalls calls words a resolve) := by
    unfold Program.hasWords Program.hasWordsOff
    rw [hoff_sub]
    have hp_len : (Obj.patchCalls calls words a resolve).length = words.length := by
      simp [Obj.patchCalls]
    refine ⟨by omega, fun j hj => ?_, ?_⟩
    · have hj' : j < words.length := by omega
      have hj_bs : j < bs.length / 4 := by omega
      have htake_li := hwords_li j hj_bs
      have htake_prog : ((Program.ofImage img (Rust.withPanics X)).code.drop (off + 4 * j)).take 4 =
          (li.code.drop (off + 4 * j)).take 4 := by
        show (img.code.drop (off + 4 * j)).take 4 = _
        rw [hcode]
      rw [htake_li] at htake_prog
      have hwc := hwordsCheck j hj'
      rw [List.getElem?_eq_getElem hj'] at hwc
      split at hwc
      case h_2 => contradiction
      rename_i w' _ hw' hw_eq
      cases hw_eq
      simp only [Obj.patchCalls, List.getElem_mapIdx]
      cases hfind : calls.find? (·.1 == 4 * j) with
      | none =>
        simp only [hfind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hwc
        simp only [hfind] at htake_prog
        rw [Obj.readWordOff_eq_of_take4 (prog2 := { code := bs }) (k2 := 4 * j) (by omega) (by omega) htake_prog, hw', hwc]
      | some r =>
        obtain ⟨roff, sym⟩ := r
        simp only [hfind, Option.isSome_some, ↓reduceIte, beq_iff_eq] at hwc
        simp only [hfind] at htake_prog
        exact Obj.readWordOff_patchBranchBytes hal htake_prog hw' hwc
    · unfold Program.hookFree
      rw [List.all_eq_true, List.all_eq_true]
      refine ⟨?_, ?_⟩
      · rintro ⟨n, stubOff⟩ hstub
        rw [Bool.or_eq_true]
        left
        have hge := hstubs (n, stubOff) (by
          have hstub' : (n, stubOff) ∈ img.stubs := hstub
          rwa [hstubsEq] at hstub')
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
          decide_eq_false_iff_not]
        intro _
        simp only at hge
        omega
      · rintro ⟨n, symOff⟩ _
        rw [Bool.or_eq_true]
        right
        rfl
  exact ⟨a, haddr, habs a resolve hctx hrange hwords⟩

/-- A relocation-free function `n` recorded in library `T`'s `ObjectInfo` `oT` (when `oT` is in
    the linked image `li`): the linker's `li.resolveSym n` resolves `n` to the address `T.addr?`
    gives. -/
theorem LibrarySpec.addr?_eq_of_resolveSym {T : LibrarySpec} {img : Obj.Image}
    {li : Obj.LinkedImage} {oT : Obj.ObjectInfo} {n : String} {off : Nat}
    (hl : Obj.Loads li img) (hT : T.obj = some oT) (hmem : oT ∈ li.objects)
    (hfn : (Obj.lookup n oT.fns).isSome = true)
    (hres : li.resolveSym n = some off) :
    T.addr? img n = some (img.base + BitVec.ofNat 64 off) := by
  obtain ⟨_, _, _, hwf, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok hl
  obtain ⟨_, _, _, _, hobjSyms, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hfn
  obtain ⟨syms, off', hsyms, hoff', hsym_eq⟩ :=
    Obj.LinkedImage.honours_fn_sym (Obj.LinkedImage.wellFormed_objects hwf oT hmem)
      (Obj.lookup_mem hbs)
  unfold Obj.LinkedImage.resolveSym at hres
  rw [hsym_eq] at hres
  simp only [Option.orElse_some, Option.some.injEq] at hres
  subst hres
  simp [LibrarySpec.addr?, hT, hobjSyms, hsyms, hoff']

/-- A contracted symbol `c.sym` of a library `T` provided as externs: the linker's
    `li.resolveSym c.sym` resolves it to its extern stub, which is the address `T.addr?` gives. -/
theorem LibrarySpec.addr?_eq_of_resolveSym_extern {T : LibrarySpec} {img : Obj.Image}
    {li : Obj.LinkedImage} {oT : Obj.ObjectInfo} {c : Contract} {off : Nat}
    (hl : Obj.Loads li img) (hT : T.obj = some oT) (hx : T.ProvidedAsExterns li)
    (hc : c ∈ T.contracts) (hres : li.resolveSym c.sym = some off) :
    T.addr? img c.sym = some (img.base + BitVec.ofNat 64 off) := by
  obtain ⟨_, _, _, hstubs, hobjSyms, _, _⟩ := ProofLib.ObjectLoad.load_ok hl
  unfold Obj.LinkedImage.resolveSym at hres
  rw [hx.2 c hc, Option.orElse_none] at hres
  simp [LibrarySpec.addr?, hT, hobjSyms, hstubs, hx.1 oT hT, hres]

end Arm64
