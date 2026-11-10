/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.OpcodeExclusion
public import ProofLib.Placed.Fetch
import ProofLib.BV.ReflectROBDD

/-!
# Opcode Exclusion for Placed Libraries

Placement-independent word-pattern exclusion for relocatable code blocks (`Obj.CodeBlock.patchSafe`).
Every word produced by `patchedWord` at a site satisfies an `Obj.WordShape` whose `keep` mask fixes
bits independently of placement; `patchSafe` checks in one linear pass over template bytes and
sorted relocations that every possible output word avoids a forbidden `Obj.WordPat`:
```
have hsvc : ∀ pl, my_lib.Placeable pl →
    (my_lib.program pl).allInstrs (fun i => !i.isSvc0) = true := fun pl _ =>
  Obj.PlacedLib.program_noSvc0_of_patchSafe (by decide +kernel)
```
The check rejects `R_AARCH64_PREL32` relocations in code, whose patched word is an arbitrary
32-bit value.
-/

@[expose] public section

namespace Arm64.Obj

/-! ## Word patterns and placement-independent word shapes -/

/-- A forbidden instruction-word pattern: `w` matches when `w &&& mask = value`. -/
structure WordPat where
  mask : BitVec 32
  value : BitVec 32
  deriving DecidableEq, Repr, Inhabited

/-- `w` matches the pattern `p`. -/
def WordPat.matches (p : WordPat) (w : BitVec 32) : Bool :=
  (w &&& p.mask) == p.value

/-- `SVC #0` (`0xd4000001`). -/
def svc0Pat : WordPat := ⟨0xffffffff#32, 0xd4000001#32⟩

/-- `MSR TPIDR_EL0, Xt` (`0xd51bd040 | Rt`). -/
def msrTpidrEl0Pat : WordPat := ⟨0xffffffe0#32, 0xd51bd040#32⟩

theorem svc0Pat_matches (w : BitVec 32) : svc0Pat.matches w = isSvc0Word w := by
  simp only [WordPat.matches, svc0Pat, isSvc0Word]
  rw [show (0xffffffff#32 : BitVec 32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]

theorem msrTpidrEl0Pat_matches (w : BitVec 32) :
    msrTpidrEl0Pat.matches w = isMsrTpidrEl0Word w := rfl

/-- The bits of a word under `keep` are fixed to `fixed &&& keep` (`fixed` may depend on the
    template word, never on the placement). -/
structure WordShape where
  keep : BitVec 32
  fixed : BitVec 32
  deriving DecidableEq, Repr, Inhabited

/-- `o` has shape `s`. -/
def WordShape.Holds (s : WordShape) (o : BitVec 32) : Prop :=
  o &&& s.keep = s.fixed &&& s.keep

/-- No word of shape `s` matches `p`: the pattern and the shape disagree on a bit both fix. -/
def WordShape.avoids (s : WordShape) (p : WordPat) : Bool :=
  (s.fixed &&& (s.keep &&& p.mask)) != (p.value &&& s.keep)

theorem WordShape.not_matches {s : WordShape} {p : WordPat} {o : BitVec 32}
    (hs : s.Holds o) (ha : s.avoids p = true) : p.matches o = false := by
  unfold WordPat.matches
  unfold WordShape.avoids at ha
  unfold WordShape.Holds at hs
  cases hm : (o &&& p.mask == p.value) with
  | false => rfl
  | true =>
    exfalso
    have hm' : o &&& p.mask = p.value := by simpa using hm
    have h1 : s.fixed &&& (s.keep &&& p.mask) = p.value &&& s.keep := by
      calc s.fixed &&& (s.keep &&& p.mask)
          = (s.fixed &&& s.keep) &&& p.mask := by rw [BitVec.and_assoc]
        _ = (o &&& s.keep) &&& p.mask := by rw [hs]
        _ = (o &&& p.mask) &&& s.keep := by
            rw [BitVec.and_assoc, BitVec.and_comm s.keep, ← BitVec.and_assoc]
        _ = p.value &&& s.keep := by rw [hm']
    simp [h1] at ha

/-! ## Shapes of relocation rewrites -/

/-- Shape of `patchRelocWord kind w place target` for every `place` and `target`. -/
def patchShape (kind : RelocKind) (w : BitVec 32) : WordShape :=
  match kind with
  | .tlsdescAdrPage21 => ⟨0xffe0001f#32, 0xd2a00000#32⟩
  | .tlsdescLd64Lo12 => ⟨0xffe0001f#32, 0xf2800000#32⟩
  | .tlsdescAddLo12 | .tlsdescCall => ⟨0xffffffff#32, nopWord⟩
  | .tlsleMovwTprelG1 | .tlsleMovwTprelG0 => ⟨0xbfe0001f#32, w⟩
  | _ => ⟨relocOpcodeMask kind, w⟩

/-- Shape of `patchGotOrTlsIeRelaxed w place target kind` for every `place` and `target`. -/
def relaxShape (kind : RelocKind) (w : BitVec 32) : WordShape :=
  match kind with
  | .adrGotPage => ⟨0xffffffff#32, nopWord⟩
  | .ld64GotLo12Nc => ⟨0xffc00000#32, 0x91000000#32⟩
  | .tlsieAdrGottprelPage21 => ⟨0xffe00000#32, 0xd2a00000#32⟩
  | .tlsieLd64GottprelLo12Nc => ⟨0xffe00000#32, 0xf2800000#32⟩
  | _ => patchShape kind w

/-- Shape of `nopWord`. -/
def nopShape : WordShape := ⟨0xffffffff#32, nopWord⟩

/-- Shape of `adrWord (adrTemplate w) place target` for every `w`, `place` and `target`. -/
def adrShape : WordShape := ⟨0x1f000000#32, 0x10000000#32⟩

-- Shape facts on generalized 32-bit operands so bit-blasting avoids 64-bit placement arithmetic.

private theorem branch_shape (w z : BitVec 32) :
    ((w &&& 0xfc000000#32) ||| (z &&& 0x03ffffff#32)) &&& 0xfc000000#32 =
      w &&& 0xfc000000#32 := by bv_slice

private theorem adr_shape (w a b : BitVec 32) :
    ((w &&& 0x9f00001f#32) ||| (((a &&& 0x3#32) <<< 29) ||| ((b &&& 0x7ffff#32) <<< 5))) &&&
      0x9f00001f#32 = w &&& 0x9f00001f#32 := by bv_slice

private theorem lo12_shape (w z : BitVec 32) :
    ((w &&& 0xffc003ff#32) ||| ((z &&& 0xfff#32) <<< 10)) &&& 0xffc003ff#32 =
      w &&& 0xffc003ff#32 := by bv_slice

private theorem imm19_shape (w z : BitVec 32) :
    ((w &&& 0xff00001f#32) ||| ((z &&& 0x7ffff#32) <<< 5)) &&& 0xff00001f#32 =
      w &&& 0xff00001f#32 := by bv_slice

private theorem tstbr14_shape (w z : BitVec 32) :
    ((w &&& 0xfff8001f#32) ||| ((z &&& 0x3fff#32) <<< 5)) &&& 0xfff8001f#32 =
      w &&& 0xfff8001f#32 := by bv_slice

private theorem movwNc_shape (w z : BitVec 32) :
    ((w &&& 0xffe0001f#32) ||| ((z &&& 0xffff#32) <<< 5)) &&& 0xffe0001f#32 =
      w &&& 0xffe0001f#32 := by bv_slice

private theorem movz_shape (w z : BitVec 32) :
    (((w &&& 0xbfe0001f#32) ||| 0x40000000#32) ||| ((z &&& 0xffff#32) <<< 5)) &&&
      0xbfe0001f#32 = w &&& 0xbfe0001f#32 := by bv_slice

private theorem movn_shape (w z : BitVec 32) :
    ((w &&& 0xbfe0001f#32) ||| ((z &&& 0xffff#32) <<< 5)) &&& 0xbfe0001f#32 =
      w &&& 0xbfe0001f#32 := by bv_slice

private theorem movzConst_shape (z : BitVec 32) :
    (0xd2a00000#32 ||| ((z &&& 0xffff#32) <<< 5)) &&& 0xffe0001f#32 =
      0xd2a00000#32 &&& 0xffe0001f#32 := by bv_slice

private theorem movkConst_shape (z : BitVec 32) :
    (0xf2800000#32 ||| ((z &&& 0xffff#32) <<< 5)) &&& 0xffe0001f#32 =
      0xf2800000#32 &&& 0xffe0001f#32 := by bv_slice

private theorem ldrToAdd_shape (w z : BitVec 32) :
    (((0x91000000#32 ||| (w &&& 0x3ff#32)) &&& 0xffc003ff#32) ||| ((z &&& 0xfff#32) <<< 10)) &&&
      0xffc00000#32 = 0x91000000#32 &&& 0xffc00000#32 := by bv_slice

private theorem tlsieMovz_shape (w z : BitVec 32) :
    (0xd2a00000#32 ||| (w &&& 0x1f#32) ||| ((z &&& 0xffff#32) <<< 5)) &&& 0xffe00000#32 =
      0xd2a00000#32 &&& 0xffe00000#32 := by bv_slice

private theorem tlsieMovk_shape (w z : BitVec 32) :
    (0xf2800000#32 ||| (w &&& 0x1f#32) ||| ((z &&& 0xffff#32) <<< 5)) &&& 0xffe00000#32 =
      0xf2800000#32 &&& 0xffe00000#32 := by bv_slice

private theorem adrTemplate_shape (w a b : BitVec 32) :
    (((0x10000000#32 ||| (w &&& 0x1f#32)) &&& 0x9f00001f#32) |||
      (((a &&& 0x3#32) <<< 29) ||| ((b &&& 0x7ffff#32) <<< 5))) &&& 0x1f000000#32 =
      0x10000000#32 &&& 0x1f000000#32 := by bv_slice

private theorem movwSigned_shape (shift : Nat) (w : BitVec 32) (target : BitVec 64) :
    movwSignedWord shift w target &&& 0xbfe0001f#32 = w &&& 0xbfe0001f#32 := by
  unfold movwSignedWord
  split
  · exact movz_shape w _
  · exact movn_shape w _

private theorem and_zero_shape (x w : BitVec 32) : x &&& 0#32 = w &&& 0#32 := by
  rw [BitVec.and_zero, BitVec.and_zero]

theorem patchShape_holds (kind : RelocKind) (w : BitVec 32) (place target : BitVec 64) :
    (patchShape kind w).Holds (patchRelocWord kind w place target) := by
  cases kind
  all_goals first
    | exact branch_shape w _
    | exact adr_shape w _ _
    | exact lo12_shape w _
    | exact imm19_shape w _
    | exact tstbr14_shape w _
    | exact movwNc_shape w _
    | exact movwSigned_shape _ w target
    | exact movzConst_shape _
    | exact movkConst_shape _
    | exact and_zero_shape _ w
    | exact rfl

theorem relaxShape_holds (kind : RelocKind) (w : BitVec 32) (place target : BitVec 64) :
    (relaxShape kind w).Holds (CodeBlock.patchGotOrTlsIeRelaxed w place target kind) := by
  cases kind
  case adrGotPage => exact rfl
  case ld64GotLo12Nc => exact ldrToAdd_shape w _
  case tlsieAdrGottprelPage21 => exact tlsieMovz_shape w _
  case tlsieLd64GottprelLo12Nc => exact tlsieMovk_shape w _
  all_goals exact patchShape_holds _ w place target

theorem adrShape_holds (w : BitVec 32) (place target : BitVec 64) :
    adrShape.Holds (adrWord (adrTemplate w) place target) :=
  adrTemplate_shape w _ _

theorem nopShape_holds : nopShape.Holds nopWord := rfl

/-- Every rewrite `patchedWord` may apply to a site with relocation `kind` and template word `w`
    avoids `p`. -/
def siteSafe (p : WordPat) (kind : RelocKind) (w : BitVec 32) : Bool :=
  (patchShape kind w).avoids p && (!kind.isGotOrTlsIe || (relaxShape kind w).avoids p)

/-! ## Placement-independent check -/

/-- One linear pass over the template bytes `bs` (starting at byte offset `o`) and the
    relocations `rs`: at the offset of the head relocation `r` it checks `siteSafe p r.kind w`
    and consumes `r`; elsewhere it checks that the template word does not match `p`. Succeeds
    only if every relocation is consumed, so relocations must be listed by increasing offset. -/
def patchSafeWalk (p : WordPat) : Nat → List RelocEntry → List (BitVec 8) → Bool
  | _, [], [] => true
  | _, _ :: _, [] => false
  | o, rs, b0 :: b1 :: b2 :: b3 :: bs =>
    let w := b3 ++ b2 ++ b1 ++ b0
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then siteSafe p r.kind w && patchSafeWalk p (o + 4) rs' bs
      else !p.matches w && patchSafeWalk p (o + 4) rs bs
    | [] => !p.matches w && patchSafeWalk p (o + 4) [] bs
  | _, rs, _ :: _ => rs.isEmpty

namespace CodeBlock

/-- Placement-independent check that no patched word of `blk` matches `p`, for every placement:
    `nopShape` and `adrShape` avoid `p`, and `patchSafeWalk` succeeds on the template code and
    the relocations. -/
def patchSafe (p : WordPat) (blk : CodeBlock) : Bool :=
  nopShape.avoids p && adrShape.avoids p && patchSafeWalk p 0 blk.relocs blk.code

end CodeBlock

/-! ## Soundness -/

private theorem patchSafeWalk_off_ge {p : WordPat} :
    ∀ {o : Nat} {rs : List RelocEntry} {bs : List (BitVec 8)},
      patchSafeWalk p o rs bs = true → ∀ r ∈ rs, o ≤ r.off
  | _, [], _, _ => by simp
  | _, _ :: _, [], h => by simp [patchSafeWalk] at h
  | _, _ :: _, [_], h => by simp [patchSafeWalk] at h
  | _, _ :: _, [_, _], h => by simp [patchSafeWalk] at h
  | _, _ :: _, [_, _, _], h => by simp [patchSafeWalk] at h
  | o, r :: rs', b0 :: b1 :: b2 :: b3 :: bs, h => by
    simp only [patchSafeWalk] at h
    cases hb : Nat.beq r.off o
    case true =>
      have hro : r.off = o := Nat.eq_of_beq_eq_true hb
      simp only [hb, ite_true, Bool.and_eq_true] at h
      have ih := patchSafeWalk_off_ge h.2
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := ih x hx; omega
    case false =>
      have hro : r.off ≠ o := Nat.ne_of_beq_eq_false hb
      simp only [hb, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
      have ih := patchSafeWalk_off_ge h.2
      intro x hx
      have := ih x hx; omega

/-- What a successful walk gives at every word index `j` of `bs`: the first relocation of `rs` at
    offset `o + 4 * j`, if any, is safe for the template word there, and otherwise that word does
    not match `p`. -/
theorem patchSafeWalk_spec {p : WordPat} :
    ∀ {o : Nat} {rs : List RelocEntry} {bs : List (BitVec 8)},
      patchSafeWalk p o rs bs = true → ∀ j, 4 * j + 4 ≤ bs.length →
      match rs.find? (·.off == o + 4 * j) with
      | some r => siteSafe p r.kind (wordOfBytesLE bs (4 * j)) = true
      | none => p.matches (wordOfBytesLE bs (4 * j)) = false
  | _, _, [], _, j, hj => by simp at hj
  | _, _, [_], _, j, hj => by simp at hj; try omega
  | _, _, [_, _], _, j, hj => by simp at hj; try omega
  | _, _, [_, _, _], _, j, hj => by simp at hj; try omega
  | o, rs, b0 :: b1 :: b2 :: b3 :: bs, h, j, hj => by
    have hw0 : wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: bs) 0 = b3 ++ b2 ++ b1 ++ b0 :=
      wordOfBytesLE_cons4_zero b0 b1 b2 b3 bs
    match rs with
    | [] =>
      simp only [patchSafeWalk, Bool.and_eq_true, Bool.not_eq_true'] at h
      simp only [List.find?_nil]
      cases j with
      | zero => simpa [hw0] using h.1
      | succ j =>
        have ih := patchSafeWalk_spec h.2 j (by simp at hj; omega)
        simp only [List.find?_nil] at ih
        rw [wordOfBytesLE_cons4]
        exact ih
    | r :: rs' =>
      simp only [patchSafeWalk] at h
      cases hb : Nat.beq r.off o
      case true =>
        have hro : r.off = o := Nat.eq_of_beq_eq_true hb
        simp only [hb, ite_true, Bool.and_eq_true] at h
        cases j with
        | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, List.find?_cons, hro, BEq.rfl]
          simpa [hw0] using h.1
        | succ j =>
          have hne : (r.off == o + 4 * (j + 1)) = false := by simp; omega
          simp only [List.find?_cons, hne]
          have ih := patchSafeWalk_spec h.2 j (by simp at hj; omega)
          rw [show o + 4 * (j + 1) = o + 4 + 4 * j by omega, wordOfBytesLE_cons4]
          exact ih
      case false =>
        have hro : r.off ≠ o := Nat.ne_of_beq_eq_false hb
        simp only [hb, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.not_eq_true'] at h
        have hge := patchSafeWalk_off_ge h.2
        cases j with
        | zero =>
          simp only [Nat.mul_zero, Nat.add_zero]
          have hnone : (r :: rs').find? (·.off == o) = none := by
            rw [List.find?_eq_none]
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · simpa using hro
            · have := hge x (List.mem_cons_of_mem _ hx); simp; omega
          rw [hnone]
          simpa [hw0] using h.1
        | succ j =>
          have ih := patchSafeWalk_spec h.2 j (by simp at hj; omega)
          rw [show o + 4 * (j + 1) = o + 4 + 4 * j by omega, wordOfBytesLE_cons4]
          exact ih

namespace CodeBlock

/-- `patchSafe p blk` excludes `p` from the patched word at every in-bounds word offset, for
    every placement. -/
theorem patchedWord_not_matches {p : WordPat} {blk : CodeBlock} (h : blk.patchSafe p = true)
    (pl : Placement) {j : Nat} (hj : 4 * j + 4 ≤ blk.code.length) :
    p.matches (blk.patchedWord pl (4 * j)) = false := by
  simp only [patchSafe, Bool.and_eq_true] at h
  obtain ⟨⟨hnop, hadr⟩, hwalk⟩ := h
  have hs := patchSafeWalk_spec hwalk j hj
  simp only [Nat.zero_add] at hs
  have hra : blk.relocAt? (4 * j) = blk.relocs.find? (·.off == 4 * j) := rfl
  unfold patchedWord
  rw [hra]
  revert hs
  cases blk.relocs.find? (·.off == 4 * j) with
  | none => intro hs; exact hs
  | some r =>
    intro hs
    simp only [siteSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨hpatch, hrelax⟩ := hs
    simp only
    split
    · exact WordShape.not_matches nopShape_holds hnop
    split
    · exact WordShape.not_matches (adrShape_holds _ _ _) hadr
    split
    · exact WordShape.not_matches (adrShape_holds _ _ _) hadr
    split
    · rename_i hg
      simp only [Bool.and_eq_true] at hg
      have hk : r.kind.isGotOrTlsIe = true := hg.1.1
      exact WordShape.not_matches (relaxShape_holds _ _ _ _) (hrelax.resolve_left (by simp [hk]))
    · exact WordShape.not_matches (patchShape_holds _ _ _ _) hpatch

end CodeBlock

private theorem bytesOfWordLE_split (x : BitVec 32) :
    bytesOfWordLE x =
      [(x.zeroExtend 64).extractLsb' 0 8, (x.zeroExtend 64).extractLsb' 8 8,
        (x.zeroExtend 64).extractLsb' 16 8, (x.zeroExtend 64).extractLsb' 24 8] := rfl

private theorem concat_bytesOfWordLE (x : BitVec 32) :
    (x.zeroExtend 64).extractLsb' 24 8 ++ (x.zeroExtend 64).extractLsb' 16 8 ++
      (x.zeroExtend 64).extractLsb' 8 8 ++ (x.zeroExtend 64).extractLsb' 0 8 = x := by
  bv_slice

/-- `bytesAllWords` over a list of little-endian encoded words checks every word. -/
theorem bytesAllWords_flatMap_bytesOfWordLE {α : Type} (pw : BitVec 32 → Bool)
    (g : α → BitVec 32) :
    ∀ L : List α, bytesAllWords pw (L.flatMap fun a => bytesOfWordLE (g a)) = L.all (pw ∘ g)
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, bytesOfWordLE_split]
    simp only [List.cons_append, List.nil_append, bytesAllWords, concat_bytesOfWordLE,
      bytesAllWords_flatMap_bytesOfWordLE pw g L, List.all_cons, Function.comp]

namespace CodeBlock

/-- `patchSafe p blk` gives `bytesAllWords (!p.matches ·)` on the patched code of every
    placement. -/
theorem patched_allWords_of_patchSafe {p : WordPat} {blk : CodeBlock}
    (h : blk.patchSafe p = true) (pl : Placement) :
    bytesAllWords (fun w => !p.matches w) (blk.patched pl) = true := by
  unfold patched
  rw [bytesAllWords_flatMap_bytesOfWordLE (fun w => !p.matches w)
    (fun j => blk.patchedWord pl (4 * j))]
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  simp only [Function.comp, Bool.not_eq_true']
  exact patchedWord_not_matches h pl (by omega)

end CodeBlock

namespace PlacedLib

/-- If every word matching `p` decodes (if at all) to an instruction failing `q`, then
    `lib.text.patchSafe p` gives `(lib.program pl ...).allInstrs (!q ·)` for every placement `pl`
    (no `Placeable` hypothesis needed). -/
theorem program_allInstrs_of_patchSafe {p : WordPat} {q : Instr → Bool} {lib : PlacedLib}
    (himp : ∀ w i, decode w = some i → p.matches w = false → q i = false)
    (h : lib.text.patchSafe p = true) (pl : Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (lib.program pl externs overrides svc).allInstrs (fun i => !q i) = true :=
  Program.allInstrs_of_allWords (pw := p.matches) himp
    (CodeBlock.patched_allWords_of_patchSafe h pl)

/-- No placement of `lib` contains `SVC #0` when `lib.text.patchSafe svc0Pat = true`. -/
theorem program_noSvc0_of_patchSafe {lib : PlacedLib} (h : lib.text.patchSafe svc0Pat = true)
    (pl : Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (lib.program pl externs overrides svc).allInstrs (fun i => !i.isSvc0) = true :=
  program_allInstrs_of_patchSafe
    (fun w _ hd hw => decode_not_isSvc0 hd (by rw [← svc0Pat_matches]; exact hw)) h pl
    externs overrides svc

/-- No placement of `lib` contains `MSR TPIDR_EL0, Xt` when
    `lib.text.patchSafe msrTpidrEl0Pat = true`. -/
theorem program_noMsrTpidrEl0_of_patchSafe {lib : PlacedLib}
    (h : lib.text.patchSafe msrTpidrEl0Pat = true) (pl : Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (lib.program pl externs overrides svc).allInstrs (fun i => !i.isMsrTpidrEl0) = true :=
  program_allInstrs_of_patchSafe
    (fun w _ hd hw => decode_not_isMsrTpidrEl0 hd (by rw [← msrTpidrEl0Pat_matches]; exact hw))
    h pl externs overrides svc

end PlacedLib

end Arm64.Obj
