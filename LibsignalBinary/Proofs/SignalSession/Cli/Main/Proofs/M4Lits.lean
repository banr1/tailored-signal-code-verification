/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Lits

/-!
# Read-Only Literal Duplication, `Stores::open()` Packaging, and `adrp` Helpers (`main_m4`)

Read-only `.rodata` literal duplication (`m4RoLits_dup`), assembly of `storesAt ... StoresGhost.opened`
from the 40 stack words written in `main_m4`, and page-aligned `adrp` + offset identities.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## 1. Read-only literal duplication -/

def m4RoLits (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) : SepProp :=
  ls.foldr (fun l P => ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ P) emp

@[simp] theorem m4RoLits_nil (base : BitVec 64) : m4RoLits base [] = emp := rfl

@[simp] theorem m4RoLits_cons (base : BitVec 64) (l : Nat × List (BitVec 8))
    (ls : List (Nat × List (BitVec 8))) :
    m4RoLits base (l :: ls) = ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ m4RoLits base ls := rfl

@[simp] theorem m4RoLits_dup (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) :
    (m4RoLits base ls ∗ m4RoLits base ls) = m4RoLits base ls := by
  induction ls with
  | nil => rw [m4RoLits_nil, emp_sepConj]
  | cons l ls ih =>
    rw [m4RoLits_cons, sepConj_assoc, sepConj_left_comm (m4RoLits base ls), ← sepConj_assoc,
      pointsToBytesRO_dup, ih]

private def m4LitList : List (Nat × List (BitVec 8)) :=
  (coinsLitOff.toNat, utf8 "coins") :: dirLits.map fun l => (l.1.toNat, utf8 l.2)

private theorem m4_foldr_lits_eq_roLits (base : BitVec 64) (ls : List (BitVec 64 × String)) :
    ls.foldr (fun l P => ((base + l.1) ↦ᵣ utf8 l.2) ∗ P) emp =
      m4RoLits base (ls.map fun l => (l.1.toNat, utf8 l.2)) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldr_cons, ih, List.map_cons, m4RoLits_cons, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem mainLits_eq_m4RoLits (img : Obj.Image) :
    mainLits img = m4RoLits img.base m4LitList := by
  rw [mainLits, m4_foldr_lits_eq_roLits, m4LitList, m4RoLits_cons, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-! ## 2. Named directory-literal offsets & `Stores::open()` packaging -/

abbrev dirLit0Off : BitVec 64 := (dirLits[0]).1
abbrev dirLit1Off : BitVec 64 := (dirLits[1]).1
abbrev dirLit2Off : BitVec 64 := (dirLits[2]).1
abbrev dirLit3Off : BitVec 64 := (dirLits[3]).1
abbrev dirLit4Off : BitVec 64 := (dirLits[4]).1
abbrev dirLit5Off : BitVec 64 := (dirLits[5]).1
abbrev dirLit6Off : BitVec 64 := (dirLits[6]).1

theorem dirAt_new_intro (A : RustAlloc) (d p : BitVec 64) (bs : List (BitVec 8)) :
    ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64) ∗
      ((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs)) ⊢
      dirAt A d (.new bs) := by
  unfold dirAt DirGhost.new
  have hvec :
      ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ⊢
        RustHeap.vecOf A 48 8 (dirEntryAt A) d [] := by
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
    change ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ⊢
      ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ∗
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 48 < 2 ^ 63 ∧
        (8#64 : BitVec 64) ≠ 0⌝ ∗ emp
    have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 48 < 2 ^ 63 ∧
        (8#64 : BitVec 64) ≠ 0) = True := eq_true ⟨by decide, by decide, by decide⟩
    rw [hpure, pure_true, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  have hstr :
      (((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs)) ⊢
        strRefAt (d + 0x18#64) bs := by
    unfold strRefAt
    refine Entails.sepExists_right p ?_
    have h32 : d + 0x18#64 + 8#64 = d + 32#64 := by bv_omega
    rw [h32]
    exact Entails.refl _
  have hassoc :
      ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64) ∗
        ((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs)) =
      (((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ 8#64) ∗ ((d + 16#64) ↦₆₄ 0#64)) ∗
        (((d + 24#64) ↦₆₄ p) ∗ ((d + 32#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (p ↦ᵣ bs))) := by
    ac_rfl
  rw [hassoc]
  exact sepConj_mono hvec hstr

/-- The 5 stack words of an opened empty `Dir` at stack offset `fsp + base` with path `(p, len)`. -/
def openDirWords (fsp : BitVec 64) (base : Nat) (p : BitVec 64) (len : Nat) : SepProp :=
  ((fsp + BitVec.ofNat 64 base) ↦₆₄ 0#64) ∗
  ((fsp + BitVec.ofNat 64 (base + 8)) ↦₆₄ 8#64) ∗
  ((fsp + BitVec.ofNat 64 (base + 16)) ↦₆₄ 0#64) ∗
  ((fsp + BitVec.ofNat 64 (base + 24)) ↦₆₄ p) ∗
  ((fsp + BitVec.ofNat 64 (base + 32)) ↦₆₄ BitVec.ofNat 64 len)

theorem openDirWords_to_dirAt (A : RustAlloc) (fsp : BitVec 64) (base : Nat)
    (p : BitVec 64) (bs : List (BitVec 8)) {len : Nat} (hlen : bs.length = len) :
    openDirWords fsp base p len ∗ (p ↦ᵣ bs) ⊢
      dirAt A (fsp + BitVec.ofNat 64 base) (.new bs) := by
  subst hlen
  unfold openDirWords
  simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (dirAt_new_intro A (fsp + BitVec.ofNat 64 base) p bs)

theorem openDir0_to_dirAt (A : RustAlloc) (fsp : BitVec 64) :
    openDirWords fsp 0x310 1#64 0 ⊢ dirAt A (fsp + 0x310#64) (.new []) := by
  have h := openDirWords_to_dirAt A fsp 0x310 1#64 [] rfl
  rwa [pointsToBytesRO_nil, sepConj_emp] at h

/-- All 40 words written into `fsp + 0x310 .. fsp + 0x448` by `Stores::open()` in `main_m4`. -/
def m4OpenStoresWords (img : Obj.Image) (fsp : BitVec 64) : SepProp :=
  openDirWords fsp 0x310 1#64 0 ∗
  openDirWords fsp 0x338 (img.base + dirLit0Off) 10 ∗
  openDirWords fsp 0x360 (img.base + dirLit1Off) 15 ∗
  openDirWords fsp 0x388 (img.base + dirLit2Off) 23 ∗
  openDirWords fsp 0x3b0 (img.base + dirLit3Off) 26 ∗
  openDirWords fsp 0x3d8 (img.base + dirLit4Off) 17 ∗
  openDirWords fsp 0x400 (img.base + dirLit5Off) 8 ∗
  openDirWords fsp 0x428 (img.base + dirLit6Off) 6

theorem mainLits_expand (img : Obj.Image) :
    mainLits img =
      ((img.base + coinsLitOff) ↦ᵣ utf8 "coins") ∗
      ((img.base + dirLit0Off) ↦ᵣ utf8 "identities") ∗
      ((img.base + dirLit1Off) ↦ᵣ utf8 "signed-pre-keys") ∗
      ((img.base + dirLit2Off) ↦ᵣ utf8 "one-time-kyber-pre-keys") ∗
      ((img.base + dirLit3Off) ↦ᵣ utf8 "last-resort-kyber-pre-keys") ∗
      ((img.base + dirLit4Off) ↦ᵣ utf8 "one-time-pre-keys") ∗
      ((img.base + dirLit5Off) ↦ᵣ utf8 "sessions") ∗
      ((img.base + dirLit6Off) ↦ᵣ utf8 "public") := by
  simp only [mainLits, dirLit0Off, dirLit1Off, dirLit2Off, dirLit3Off, dirLit4Off, dirLit5Off,
    dirLit6Off, dirLits, List.getElem_cons_zero, List.getElem_cons_succ, List.foldr_cons,
    List.foldr_nil, sepConj_emp]

/-- Combine `m4OpenStoresWords img fsp` with `mainLits img` (duplicating `mainLits img` so both
`((img.base + coinsLitOff) ↦ᵣ utf8 "coins")` and `mainLits img` remain available if needed). -/
theorem m4OpenStores_pack (A : RustAlloc) (img : Obj.Image) (fsp : BitVec 64) :
    m4OpenStoresWords img fsp ∗ mainLits img ⊢
      storesAt A (fsp + 0x310#64) StoresGhost.opened ∗
        ((img.base + coinsLitOff) ↦ᵣ utf8 "coins") ∗ mainLits img := by
  conv =>
    lhs
    arg 2
    rw [← mainLits_dup img]
    arg 1
    rw [mainLits_expand img]
  unfold m4OpenStoresWords storesAt StoresGhost.opened
  dsimp only []
  have h0 := openDir0_to_dirAt A fsp
  have h1 := openDirWords_to_dirAt A fsp 0x338 (img.base + dirLit0Off)
    (utf8 "identities") (by decide +kernel : (utf8 "identities").length = 10)
  have h2 := openDirWords_to_dirAt A fsp 0x360 (img.base + dirLit1Off)
    (utf8 "signed-pre-keys") (by decide +kernel : (utf8 "signed-pre-keys").length = 15)
  have h3 := openDirWords_to_dirAt A fsp 0x388 (img.base + dirLit2Off)
    (utf8 "one-time-kyber-pre-keys")
    (by decide +kernel : (utf8 "one-time-kyber-pre-keys").length = 23)
  have h4 := openDirWords_to_dirAt A fsp 0x3b0 (img.base + dirLit3Off)
    (utf8 "last-resort-kyber-pre-keys")
    (by decide +kernel : (utf8 "last-resort-kyber-pre-keys").length = 26)
  have h5 := openDirWords_to_dirAt A fsp 0x3d8 (img.base + dirLit4Off)
    (utf8 "one-time-pre-keys") (by decide +kernel : (utf8 "one-time-pre-keys").length = 17)
  have h6 := openDirWords_to_dirAt A fsp 0x400 (img.base + dirLit5Off)
    (utf8 "sessions") (by decide +kernel : (utf8 "sessions").length = 8)
  have h7 := openDirWords_to_dirAt A fsp 0x428 (img.base + dirLit6Off)
    (utf8 "public") (by decide +kernel : (utf8 "public").length = 6)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans (Q :=
    openDirWords fsp 0x310 1#64 0 ∗
    ((openDirWords fsp 0x338 (img.base + dirLit0Off) 10 ∗
        ((img.base + dirLit0Off) ↦ᵣ utf8 "identities")) ∗
      (openDirWords fsp 0x360 (img.base + dirLit1Off) 15 ∗
        ((img.base + dirLit1Off) ↦ᵣ utf8 "signed-pre-keys")) ∗
      (openDirWords fsp 0x388 (img.base + dirLit2Off) 23 ∗
        ((img.base + dirLit2Off) ↦ᵣ utf8 "one-time-kyber-pre-keys")) ∗
      (openDirWords fsp 0x3b0 (img.base + dirLit3Off) 26 ∗
        ((img.base + dirLit3Off) ↦ᵣ utf8 "last-resort-kyber-pre-keys")) ∗
      (openDirWords fsp 0x3d8 (img.base + dirLit4Off) 17 ∗
        ((img.base + dirLit4Off) ↦ᵣ utf8 "one-time-pre-keys")) ∗
      (openDirWords fsp 0x400 (img.base + dirLit5Off) 8 ∗
        ((img.base + dirLit5Off) ↦ᵣ utf8 "sessions")) ∗
      (openDirWords fsp 0x428 (img.base + dirLit6Off) 6 ∗
        ((img.base + dirLit6Off) ↦ᵣ utf8 "public")) ∗
      ((img.base + coinsLitOff) ↦ᵣ utf8 "coins") ∗ mainLits img)) ?_ ?_
  · refine Entails.of_eq ?_
    simp only [sepConj_assoc]
    sep_focus
  · exact sepConj_mono h0
      (sepConj_mono h1
        (sepConj_mono h2
          (sepConj_mono h3
            (sepConj_mono h4
              (sepConj_mono h5
                (sepConj_mono h6
                  (sepConj_mono h7 (Entails.refl _))))))))

/-! ## 3. PC-relative `ADRP` + low-12-bit offset identities for all 9 sites of `main_m4` -/

theorem m4_adrp_coinsNext {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x5d4#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% coinsNextOff.toNat - page% (ls_off% "main" + 0x5d4))) +
      bv% (coinsNextOff.toNat % 4096) =
      b + coinsNextOff := by
  subst hfn; dsimp only [coinsNextOff]; bv_arith

theorem m4_adrp_coinsLeft {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x5e0#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% coinsLeftOff.toNat - page% (ls_off% "main" + 0x5e0))) +
      bv% (coinsLeftOff.toNat % 4096) =
      b + coinsLeftOff := by
  subst hfn; dsimp only [coinsLeftOff]; bv_arith

theorem m4_adrp_dir0 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x61c#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit0Off.toNat - page% (ls_off% "main" + 0x61c))) +
      bv% (dirLit0Off.toNat % 4096) =
      b + dirLit0Off := by
  subst hfn; simp only [dirLit0Off, dirLits, List.getElem_cons_zero]; bv_arith

theorem m4_adrp_dir1 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x628#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit1Off.toNat - page% (ls_off% "main" + 0x628))) +
      bv% (dirLit1Off.toNat % 4096) =
      b + dirLit1Off := by
  subst hfn; simp only [dirLit1Off, dirLits, List.getElem_cons_succ, List.getElem_cons_zero]; bv_arith

theorem m4_adrp_dir2 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x63c#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit2Off.toNat - page% (ls_off% "main" + 0x63c))) +
      bv% (dirLit2Off.toNat % 4096) =
      b + dirLit2Off := by
  subst hfn; simp only [dirLit2Off, dirLits, List.getElem_cons_succ, List.getElem_cons_zero]; bv_arith

theorem m4_adrp_dir3 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x648#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit3Off.toNat - page% (ls_off% "main" + 0x648))) +
      bv% (dirLit3Off.toNat % 4096) =
      b + dirLit3Off := by
  subst hfn; simp only [dirLit3Off, dirLits, List.getElem_cons_succ, List.getElem_cons_zero]; bv_arith

theorem m4_adrp_dir4 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x668#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit4Off.toNat - page% (ls_off% "main" + 0x668))) +
      bv% (dirLit4Off.toNat % 4096) =
      b + dirLit4Off := by
  subst hfn; simp only [dirLit4Off, dirLits, List.getElem_cons_succ, List.getElem_cons_zero]; bv_arith

theorem m4_adrp_dir5 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x67c#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit5Off.toNat - page% (ls_off% "main" + 0x67c))) +
      bv% (dirLit5Off.toNat % 4096) =
      b + dirLit5Off := by
  subst hfn; simp only [dirLit5Off, dirLits, List.getElem_cons_succ, List.getElem_cons_zero]; bv_arith

theorem m4_adrp_dir6 {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x6b0#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% dirLit6Off.toNat - page% (ls_off% "main" + 0x6b0))) +
      bv% (dirLit6Off.toNat % 4096) =
      b + dirLit6Off := by
  subst hfn; simp only [dirLit6Off, dirLits, List.getElem_cons_succ, List.getElem_cons_zero]; bv_arith

end CryptoVerification.SignalSession.Cli.MainHops
