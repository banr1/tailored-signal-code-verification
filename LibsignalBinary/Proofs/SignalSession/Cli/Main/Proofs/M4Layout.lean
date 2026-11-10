/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Lits
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame

/-!
# Frame Layout, Instruction Decodes, and Buffer Helpers for `main_m4`

Instruction decode trees, `ownedBytes` / `m4CallWords` / `runOkAt` packaging lemmas, and stack-frame
slot partitions (`m4Cells`, `m5Cells`) for `main_m4`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. `SepWPp` & Call-Target Helpers -/

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem run_fnOff_m4 :
    libsignalSessionCode.fnOff runName = num% (ls_off% "libsignal_cli::run") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::run")

theorem dealloc_fnOff_m4 :
    libsignalSessionCode.fnOff deallocName = num% (ls_off% "__rustc::__rust_dealloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "__rustc::__rust_dealloc")

theorem dealloc_fnAddr_eq_rel (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (mProg img ext).fnAddr deallocName =
      (mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "main") :=
  Program.fnAddr_callee_add_of_fnOff main_fnOff dealloc_fnOff_m4 rfl

theorem m4_deallocFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "main"))
      ((rustDeallocExternSpecWithStack A extHookStack).keepsFs.inImage img) := by
  have h := hc.allocFs.dealloc
  rw [dealloc_fnAddr_eq_rel img ext] at h
  exact h

/-! ## 2. Split Decode Trees for `main_m4` & Error Exit Blocks -/

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecP1
  [(ls_off% "main" + 1488) → (ls_off% "main" + 1612)]

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecP2
  [(ls_off% "main" + 1616) → (ls_off% "main" + 1716)]

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecP3
  [(ls_off% "main" + 1720) → (ls_off% "main" + 1808)]

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecChk
  [(ls_off% "main" + 1812) → (ls_off% "main" + 1820)]

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecAb8
  [(ls_off% "main" + 2744) → (ls_off% "main" + 2772)]

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecB14
  [(ls_off% "main" + 2836) → (ls_off% "main" + 2848)]

gen_decodes CryptoVerification.libsignalSessionCode_tree m4DecB84
  [(ls_off% "main" + 2948) → (ls_off% "main" + 2956)]

/-! ## 3. Buffer, `Call`, and `runOkAt` Packaging/Opening Helpers -/

theorem pointsToBytes_to_memRegion (p : BitVec 64) (bs : List (BitVec 8)) :
    (p ↦ₛ bs) ⊢ memRegion p bs.length :=
  (IsBlock.pointsToBytes p bs).entails_memRegion

/-- Remainder of `ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs` when `(ptr ↦ₛ bs)` is borrowed. -/
def ownedBytesRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem ownedBytes_split (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs ⊢
      (ptr ↦ₛ bs) ∗ ownedBytesRest A cap ptr bs := by
  unfold ownedBytes ownedBytesRest
  apply Entails.pure_left
  rintro ⟨-, hle, hlt, hne⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hle)
    subst hnil
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl emp)
  · simp only [hcap, ↓reduceIte]
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _)))
    ac_rfl

theorem ownedBytes_merge (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ ownedBytesRest A cap ptr bs ⊢
      ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold ownedBytes ownedBytesRest
  rw [sepConj_comm, sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hne⟩
  apply Entails.pure_right ⟨rfl, hle, hlt, hne⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hle)
    subst hnil
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl emp
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem ownedBytes_zero_entails_emp (A : RustAlloc) (ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A 0 ptr len bs ⊢ emp := by
  unfold ownedBytes
  simp only [↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem ownedBytes_dealloc (A : RustAlloc) {cap ptr len : BitVec 64} {bs : List (BitVec 8)}
    (hcap : cap ≠ 0) :
    ownedBytes A cap ptr len bs ⊢
      ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold ownedBytes
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left
  rintro ⟨-, hle, hlt, _⟩
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  apply Entails.pure_right hlay
  have hmerge :
      memRegion ptr bs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      memRegion ptr cap.toNat := by
    have hsum : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
    conv => rhs; rw [← hsum]
    exact (ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)).symm
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (pointsToBytes_to_memRegion ptr bs))) ?_
  rw [hmerge]
  exact Entails.refl _

/-- The 7 stack words of `Call` written at `fsp + 0x78 .. fsp + 0xa8` in `M+0x610 .. M+0x6b8`. -/
def m4CallWords (fsp : BitVec 64) (w : CallW) : SepProp :=
  ((fsp + 0x78#64) ↦₆₄ w.w0) ∗
  ((fsp + 0x80#64) ↦₆₄ w.w1) ∗
  ((fsp + 0x88#64) ↦₆₄ w.w2) ∗
  ((fsp + 0x90#64) ↦₆₄ w.w3) ∗
  ((fsp + 0x98#64) ↦₆₄ w.w4) ∗
  ((fsp + 0xa0#64) ↦₆₄ w.w5) ∗
  ((fsp + 0xa8#64) ↦₆₄ w.w6)

theorem m4CallWords_pack (A : RustAlloc) (fsp : BitVec 64) (w : CallW) (c : CallV) :
    m4CallWords fsp w ∗ callHeap A w c ⊢ callAt A (fsp + 0x78#64) c := by
  unfold m4CallWords callAt
  refine Entails.sepExists_right w ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem vecOf_open_cap {α : Type} (A : RustAlloc) (sz align : Nat) (elem : α → BitVec 64 → SepProp)
    (hsz : sz > 0) (r : BitVec 64) (xs : List α) :
    RustHeap.vecOf A sz align elem r xs ⊢
      ∃∗ cap : BitVec 64, ∃∗ R_vec : SepProp,
        ⌜cap.toNat < 2 ^ 63 ∧ ((r ↦₆₄ cap) ∗ R_vec ⊢ RustHeap.vecOf A sz align elem r xs)⌝ ∗
          (r ↦₆₄ cap) ∗ R_vec := by
  unfold RustHeap.vecOf
  dsimp only [vecAt, vecHeader]
  apply Entails.sepExists_mono; intro cap
  apply Entails.sepExists_elim; intro ptr
  let R_vec : SepProp :=
    ((r + 8#64) ↦₆₄ ptr) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      vecBuf A sz align elem cap ptr xs
  have hpure_buf :
      vecBuf A sz align elem cap ptr xs ⊢
        ⌜cap.toNat < 2 ^ 63⌝ ∗ vecBuf A sz align elem cap ptr xs := by
    unfold vecBuf
    apply Entails.pure_left
    rintro ⟨hle, hlt, hptr⟩
    have h1 : cap.toNat * 1 ≤ cap.toNat * sz := Nat.mul_le_mul_left cap.toNat hsz
    exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))
  have hclose : (r ↦₆₄ cap) ∗ R_vec ⊢ RustHeap.vecOf A sz align elem r xs := by
    unfold RustHeap.vecOf
    dsimp only [vecAt, vecHeader, R_vec]
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    exact Entails.of_eq (by ac_rfl)
  refine Entails.sepExists_right R_vec ?_
  have hassoc1 :
      ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length)) ∗
        vecBuf A sz align elem cap ptr xs =
      vecBuf A sz align elem cap ptr xs ∗
        ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length)) := by
    ac_rfl
  rw [hassoc1]
  refine Entails.trans (sepConj_mono_left hpure_buf) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨hcap_lt, hclose⟩ ?_
  dsimp only [R_vec]
  exact Entails.of_eq (by ac_rfl)

/-- Open word 0 (`r ↦₆₄ cap`) of `runOkAt A r g out` together with `cap.toNat < 2 ^ 63` and a
closing entailment back to `runOkAt A r g out`, keeping all 8 `Dir`s opaque during `M+0x714..71c`. -/
theorem runOkAt_open (A : RustAlloc) (r : BitVec 64) (g : StoresGhost) (out : List (BitVec 8)) :
    runOkAt A r g out ⊢
      ∃∗ cap : BitVec 64, ∃∗ R_ok : SepProp,
        ⌜cap.toNat < 2 ^ 63 ∧ ((r ↦₆₄ cap) ∗ R_ok ⊢ runOkAt A r g out)⌝ ∗
          (r ↦₆₄ cap) ∗ R_ok := by
  let tailDirs : SepProp :=
    strRefAt (r + 0x18#64) g.identity.own.path ∗
      dirAt A (r + 0x28#64) g.identity.peers ∗
      dirAt A (r + 0x50#64) g.signed ∗
      dirAt A (r + 0x78#64) g.kyber.oneTime ∗
      dirAt A (r + 0xa0#64) g.kyber.lastResort ∗
      dirAt A (r + 0xc8#64) g.oneTime ∗
      dirAt A (r + 0xf0#64) g.sessions ∗
      dirAt A (r + 0x118#64) g.pub ∗
      vecU8 A (r + 0x140#64) out
  have hsplit :
      runOkAt A r g out =
        RustHeap.vecOf A 48 8 (dirEntryAt A) r g.identity.own.changed ∗ tailDirs := by
    dsimp only [runOkAt, storesAt, dirAt, tailDirs]
    ac_rfl
  conv => lhs; rw [hsplit]
  refine Entails.trans
    (sepConj_mono_left (vecOf_open_cap A 48 8 (dirEntryAt A) (by decide) r g.identity.own.changed)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_mono; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro R_vec
  have hassoc :
      (⌜cap.toNat < 2 ^ 63 ∧
          ((r ↦₆₄ cap) ∗ R_vec ⊢ RustHeap.vecOf A 48 8 (dirEntryAt A) r g.identity.own.changed)⌝ ∗
        (r ↦₆₄ cap) ∗ R_vec) ∗ tailDirs =
      ⌜cap.toNat < 2 ^ 63 ∧
          ((r ↦₆₄ cap) ∗ R_vec ⊢ RustHeap.vecOf A 48 8 (dirEntryAt A) r g.identity.own.changed)⌝ ∗
        ((r ↦₆₄ cap) ∗ (R_vec ∗ tailDirs)) := by
    ac_rfl
  rw [hassoc]
  apply Entails.pure_left
  rintro ⟨hcap_lt, hclose_vec⟩
  refine Entails.sepExists_right (R_vec ∗ tailDirs) ?_
  refine Entails.pure_right ⟨hcap_lt, ?_⟩ (Entails.of_eq (by ac_rfl))
  rw [hsplit]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hclose_vec)

/-! ## 4. Stack-Frame Open & Close Lemmas for `main_m4` -/

/-- Untouched uninitialized frame gaps of `main`'s `0x480`-byte local frame during `main_m4`. -/
def m4Gaps (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x40 ∗
  memRegion (fsp + 0x60#64) 0x18 ∗
  memRegion (fsp + 0xb0#64) 0x108 ∗
  memRegion (fsp + 0x450#64) 0x30

/-- Untouched portion of `main`'s `0x480`-byte local frame across `signal_session::run`. -/
def m4RestFrame (fsp : BitVec 64) (w : CallW) : SepProp :=
  m4Gaps fsp ∗
  ((fsp + 0x40#64) ↦₆₄ w.w6) ∗
  ((fsp + 0x48#64) ↦₆₄ w.w3) ∗
  ((fsp + 0x50#64) ↦₆₄ w.w4)

theorem m4_resSlot_merge (fsp : BitVec 64) (v : BitVec 64) :
    ((fsp + 0x1c8#64) ↦₆₄ v) ∗
      memRegion (fsp + 0x1b8#64) 0x10 ∗
      memRegion (fsp + 0x1d0#64) 0x140 ⊢
      memRegion (fsp + 0x1b8#64) runResSize := by
  refine Entails.trans
    (sepConj_mono_left (pointsTo64_entails_memRegion (fsp + 0x1c8#64) v)) ?_
  have h1 :
      memRegion (fsp + 0x1b8#64) 0x10 ∗ memRegion (fsp + 0x1c8#64) 8 =
        memRegion (fsp + 0x1b8#64) 0x18 := by
    have hsplit := ProofLib.memRegion_split (fsp + 0x1b8#64) 0x10 8 (by decide)
    rw [BitVec.add_assoc, show (0x1b8#64 + BitVec.ofNat 64 0x10 : BitVec 64) = 0x1c8#64 from rfl]
      at hsplit
    exact hsplit.symm
  have h2 :
      memRegion (fsp + 0x1b8#64) 0x18 ∗ memRegion (fsp + 0x1d0#64) 0x140 =
        memRegion (fsp + 0x1b8#64) runResSize := by
    have hsplit := ProofLib.memRegion_split (fsp + 0x1b8#64) 0x18 0x140 (by decide)
    rw [BitVec.add_assoc, show (0x1b8#64 + BitVec.ofNat 64 0x18 : BitVec 64) = 0x1d0#64 from rfl]
      at hsplit
    exact hsplit.symm
  have hassoc :
      memRegion (fsp + 0x1c8#64) 8 ∗
        memRegion (fsp + 0x1b8#64) 0x10 ∗
        memRegion (fsp + 0x1d0#64) 0x140 =
      (memRegion (fsp + 0x1b8#64) 0x10 ∗ memRegion (fsp + 0x1c8#64) 8) ∗
        memRegion (fsp + 0x1d0#64) 0x140 := by
    ac_rfl
  rw [hassoc, h1, h2]
  exact Entails.refl _

theorem m4_locals_open (fsp : BitVec 64) (w : CallW) (inPtr : BitVec 64) (coinsLen : Nat) :
    locals fsp (m4Cells fsp w inPtr coinsLen) ⊢
      m4Gaps fsp ∗
      ((fsp + 0x40#64) ↦₆₄ w.w6) ∗
      ((fsp + 0x48#64) ↦₆₄ w.w3) ∗
      ((fsp + 0x50#64) ↦₆₄ w.w4) ∗
      ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 coinsLen) ∗
      memRegion (fsp + 0x1b8#64) 0x10 ∗
      memRegion (fsp + 0x1d0#64) 0x140 ∗
      cells (fsp + 0x78#64) 7 ∗
      cells (fsp + 0x310#64) 40 := by
  have hc1 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr]
    0x78 56
    [cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]
    (by dsimp [localsEnd, cell]; omega)
    (by dsimp [localsBound]; omega)
    (by dsimp [localsBound, cell, mainFrameSize]; omega)
  have hc2 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
      (0x78, 56, memRegion (fsp + 0x78#64) 56)]
    0x1b8 0x10
    [cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]
    (by dsimp [localsEnd, cell]; omega)
    (by dsimp [localsBound]; omega)
    (by dsimp [localsBound, cell, mainFrameSize]; omega)
  have hc3 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
      (0x78, 56, memRegion (fsp + 0x78#64) 56),
      (0x1b8, 0x10, memRegion (fsp + 0x1b8#64) 0x10),
      cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]
    0x310 320
    []
    (by dsimp [localsEnd, cell]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
  change locals fsp
      ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr] ++
        [cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]) ⊢ _
  rw [hc1]
  change locals fsp
      ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
          (0x78, 56, memRegion (fsp + 0x78#64) 56)] ++
        [cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]) ⊢ _
  rw [hc2]
  change locals fsp
      ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
          (0x78, 56, memRegion (fsp + 0x78#64) 56),
          (0x1b8, 0x10, memRegion (fsp + 0x1b8#64) 0x10),
          cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)] ++ []) ⊢ _
  rw [hc3]
  dsimp only [locals, localsFrom, cell, m4Gaps, List.cons_append, List.nil_append]
  rw [BitVec.add_zero,
      show (56 : Nat) = 8 * 7 by rfl,
      ProofLib.memRegion_cells (fsp + 0x78#64) 7 (by decide),
      show (320 : Nat) = 8 * 40 by rfl,
      ProofLib.memRegion_cells (fsp + 0x310#64) 40 (by decide)]
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
    ProofLib.memRegion_zero, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem m4_locals_close_ok (A : RustAlloc) (fsp : BitVec 64) (w : CallW) (inPtr : BitVec 64)
    (g : StoresGhost) (out : List (BitVec 8)) :
    m4RestFrame fsp w ∗
      ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
      memRegion (fsp + 0x78#64) 56 ∗
      runOkAt A (fsp + 0x1b8#64) g out ∗
      memRegion (fsp + 0x310#64) 320 ⊢
      locals fsp (m5Cells A fsp inPtr g out) := by
  have hc1 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr]
    0x78 56
    [(0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]
    (by dsimp [localsEnd, cell]; omega)
    (by dsimp [localsBound]; omega)
    (by dsimp [localsBound, runResSize]; omega)
  have hc2 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
      (0x78, 56, memRegion (fsp + 0x78#64) 56),
      (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]
    0x310 320
    []
    (by dsimp [localsEnd, cell, runResSize]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
  have h1 :
      m4RestFrame fsp w ∗
        ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗
        runOkAt A (fsp + 0x1b8#64) g out ∗
        memRegion (fsp + 0x310#64) 320 =
      locals fsp
        ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
            (0x78, 56, memRegion (fsp + 0x78#64) 56),
            (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)] ++
          [(0x310, 320, memRegion (fsp + 0x310#64) 320)]) := by
    dsimp only [m4RestFrame, m4Gaps, locals, localsFrom, cell, runResSize,
      List.cons_append, List.nil_append]
    rw [BitVec.add_zero]
    simp only [Nat.reduceAdd, Nat.reduceSub,
      ProofLib.memRegion_zero, emp_sepConj]
    ac_rfl
  rw [h1, ← hc2]
  change locals fsp
      ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr] ++
        (0x78, 56, memRegion (fsp + 0x78#64) 56) ::
        [(0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]) ⊢ _
  rw [← hc1]
  refine Entails.trans
    (locals_forget_cell fsp [] 0x40 w.w6
      [cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
        (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]
      (by dsimp [localsEnd]; omega)
      (by dsimp [localsBound, cell]; omega)
      (by dsimp [localsBound, cell, runResSize, mainFrameSize]; omega)) ?_
  refine Entails.trans
    (locals_forget_cell fsp [] 0x48 w.w3
      [cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
        (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]
      (by dsimp [localsEnd]; omega)
      (by dsimp [localsBound, cell]; omega)
      (by dsimp [localsBound, cell, runResSize, mainFrameSize]; omega)) ?_
  exact locals_forget_cell fsp [] 0x50 w.w4
    [cell fsp 0x58 inPtr, (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]
    (by dsimp [localsEnd]; omega)
    (by dsimp [localsBound, cell]; omega)
    (by dsimp [localsBound, cell, runResSize, mainFrameSize]; omega)

theorem m4_locals_close_err_cell (fsp : BitVec 64) (w : CallW) (inPtr tag : BitVec 64) :
    m4RestFrame fsp w ∗
      ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
      memRegion (fsp + 0x78#64) 56 ∗
      ((fsp + 0x1b8#64) ↦₆₄ tag) ∗
      memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
      memRegion (fsp + 0x310#64) 320 ⊢
      locals fsp [cell fsp 0x58 inPtr] := by
  have htag_merge :
      ((fsp + 0x1b8#64) ↦₆₄ tag) ∗ memRegion (fsp + 0x1c0#64) (runResSize - 8) ⊢
        memRegion (fsp + 0x1b8#64) runResSize := by
    refine Entails.trans
      (sepConj_mono_left (pointsTo64_entails_memRegion (fsp + 0x1b8#64) tag)) ?_
    have hsplit := ProofLib.memRegion_split (fsp + 0x1b8#64) 8 (runResSize - 8) (by decide)
    rw [BitVec.add_assoc, show (0x1b8#64 + BitVec.ofNat 64 8 : BitVec 64) = 0x1c0#64 from rfl]
      at hsplit
    exact Entails.of_eq hsplit.symm
  have hpre :
      m4RestFrame fsp w ∗
        ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗
        ((fsp + 0x1b8#64) ↦₆₄ tag) ∗
        memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
        memRegion (fsp + 0x310#64) 320 ⊢
      m4RestFrame fsp w ∗
        ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗
        memRegion (fsp + 0x1b8#64) runResSize ∗
        memRegion (fsp + 0x310#64) 320 :=
    sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (by rw [← sepConj_assoc]; exact sepConj_mono_left htag_merge)))
  refine Entails.trans hpre ?_
  have hc1 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr]
    0x78 56
    [(0x1b8, runResSize, memRegion (fsp + 0x1b8#64) runResSize)]
    (by dsimp [localsEnd, cell]; omega)
    (by dsimp [localsBound]; omega)
    (by dsimp [localsBound, runResSize]; omega)
  have hc2 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
      (0x78, 56, memRegion (fsp + 0x78#64) 56),
      (0x1b8, runResSize, memRegion (fsp + 0x1b8#64) runResSize)]
    0x310 320
    []
    (by dsimp [localsEnd, cell, runResSize]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
  have hc0 := locals_carve_region fsp
    [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr]
    0x1b8 runResSize
    []
    (by dsimp [localsEnd, cell]; omega)
    (by dsimp [localsBound, runResSize, mainFrameSize]; omega)
    (by dsimp [localsBound, mainFrameSize]; omega)
  have h1 :
      m4RestFrame fsp w ∗
        ((fsp + 0x58#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗
        memRegion (fsp + 0x1b8#64) runResSize ∗
        memRegion (fsp + 0x310#64) 320 =
      locals fsp
        ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
            (0x78, 56, memRegion (fsp + 0x78#64) 56),
            (0x1b8, runResSize, memRegion (fsp + 0x1b8#64) runResSize)] ++
          [(0x310, 320, memRegion (fsp + 0x310#64) 320)]) := by
    dsimp only [m4RestFrame, m4Gaps, locals, localsFrom, cell, runResSize,
      List.cons_append, List.nil_append]
    rw [BitVec.add_zero]
    simp only [Nat.reduceAdd, Nat.reduceSub,
      ProofLib.memRegion_zero, emp_sepConj]
    ac_rfl
  rw [h1, ← hc2]
  change locals fsp
      ([cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr] ++
        (0x78, 56, memRegion (fsp + 0x78#64) 56) ::
        [(0x1b8, runResSize, memRegion (fsp + 0x1b8#64) runResSize)]) ⊢ _
  rw [← hc1, ← hc0]
  refine Entails.trans
    (locals_forget_cell fsp [] 0x40 w.w6
      [cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr]
      (by dsimp [localsEnd]; omega)
      (by dsimp [localsBound, cell]; omega)
      (by dsimp [localsBound, cell, mainFrameSize]; omega)) ?_
  refine Entails.trans
    (locals_forget_cell fsp [] 0x48 w.w3
      [cell fsp 0x50 w.w4, cell fsp 0x58 inPtr]
      (by dsimp [localsEnd]; omega)
      (by dsimp [localsBound, cell]; omega)
      (by dsimp [localsBound, cell, mainFrameSize]; omega)) ?_
  exact locals_forget_cell fsp [] 0x50 w.w4 [cell fsp 0x58 inPtr]
    (by dsimp [localsEnd]; omega)
    (by dsimp [localsBound, cell]; omega)
    (by dsimp [localsBound, cell, mainFrameSize]; omega)

/-! ## 5. Per-Block Slot Partitions for Fast `wp_steps` in `M4Steps.lean` -/

/-- One uninitialized 64-bit word at `fsp + off`. -/
def m4Slot (fsp : BitVec 64) (off : Nat) : SepProp :=
  ∃∗ v : BitVec 64, (fsp + BitVec.ofNat 64 off) ↦₆₄ v

/-- `k` consecutive `m4Slot`s starting at `fsp + off`. -/
def m4SlotsFrom (fsp : BitVec 64) (off : Nat) : Nat → SepProp
  | 0 => emp
  | k + 1 => m4Slot fsp off ∗ m4SlotsFrom fsp (off + 8) k

theorem memRegion_to_m4SlotsFrom (fsp : BitVec 64) :
    ∀ (k off : Nat), 8 * k ≤ 2 ^ 64 →
      memRegion (fsp + BitVec.ofNat 64 off) (8 * k) ⊢ m4SlotsFrom fsp off k
  | 0, _, _ => by
    rw [Nat.mul_zero, ProofLib.memRegion_zero]
    exact Entails.refl emp
  | k + 1, off, hk => by
    have hsplit := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 off) 8 (8 * k) (by omega)
    have hnext : fsp + BitVec.ofNat 64 off + 8#64 = fsp + BitVec.ofNat 64 (off + 8) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, hsplit, hnext, ProofLib.memRegion_eight]
    exact sepConj_mono (Entails.refl _) (memRegion_to_m4SlotsFrom fsp k (off + 8) (by omega))

/-- Uninitialized slots written by `M+0x5d0 .. M+0x64c` (9 words). -/
def m4UninitP1 (fsp : BitVec 64) : SepProp :=
  m4Slot fsp 0x88 ∗ m4Slot fsp 0x90 ∗
  m4Slot fsp 0x328 ∗ m4Slot fsp 0x350 ∗ m4Slot fsp 0x358 ∗
  m4Slot fsp 0x378 ∗ m4Slot fsp 0x380 ∗ m4Slot fsp 0x3a0 ∗ m4Slot fsp 0x3a8

/-- Uninitialized slots written by `M+0x650 .. M+0x6b4` (16 words). -/
def m4UninitP2 (fsp : BitVec 64) : SepProp :=
  m4Slot fsp 0x98 ∗ m4Slot fsp 0xa0 ∗ m4Slot fsp 0xa8 ∗
  m4Slot fsp 0x318 ∗ m4Slot fsp 0x340 ∗ m4Slot fsp 0x368 ∗ m4Slot fsp 0x390 ∗
  m4Slot fsp 0x3b8 ∗ m4Slot fsp 0x3c8 ∗ m4Slot fsp 0x3d0 ∗ m4Slot fsp 0x3e0 ∗
  m4Slot fsp 0x3f0 ∗ m4Slot fsp 0x408 ∗ m4Slot fsp 0x418 ∗ m4Slot fsp 0x420 ∗
  m4Slot fsp 0x430

/-- Uninitialized slots written by `M+0x6b8 .. M+0x710` (22 words). -/
def m4UninitP3 (fsp : BitVec 64) : SepProp :=
  m4Slot fsp 0x78 ∗ m4Slot fsp 0x80 ∗
  m4Slot fsp 0x310 ∗ m4Slot fsp 0x320 ∗ m4Slot fsp 0x330 ∗ m4Slot fsp 0x338 ∗
  m4Slot fsp 0x348 ∗ m4Slot fsp 0x360 ∗ m4Slot fsp 0x370 ∗ m4Slot fsp 0x388 ∗
  m4Slot fsp 0x398 ∗ m4Slot fsp 0x3b0 ∗ m4Slot fsp 0x3c0 ∗ m4Slot fsp 0x3d8 ∗
  m4Slot fsp 0x3e8 ∗ m4Slot fsp 0x3f8 ∗ m4Slot fsp 0x400 ∗ m4Slot fsp 0x410 ∗
  m4Slot fsp 0x428 ∗ m4Slot fsp 0x438 ∗ m4Slot fsp 0x440 ∗ m4Slot fsp 0x448

/-- Concrete words written by `M+0x5d0 .. M+0x64c` (9 stack words). -/
def m4WrittenP1 (img : Obj.Image) (fsp : BitVec 64) (w : CallW) : SepProp :=
  ((fsp + 0x88#64) ↦₆₄ w.w2) ∗
  ((fsp + 0x90#64) ↦₆₄ w.w3) ∗
  ((fsp + 0x328#64) ↦₆₄ 1#64) ∗
  ((fsp + 0x350#64) ↦₆₄ (img.base + dirLit0Off)) ∗
  ((fsp + 0x358#64) ↦₆₄ 10#64) ∗
  ((fsp + 0x378#64) ↦₆₄ (img.base + dirLit1Off)) ∗
  ((fsp + 0x380#64) ↦₆₄ 15#64) ∗
  ((fsp + 0x3a0#64) ↦₆₄ (img.base + dirLit2Off)) ∗
  ((fsp + 0x3a8#64) ↦₆₄ 23#64)

/-- Concrete words written by `M+0x650 .. M+0x6b4` (16 stack words). -/
def m4WrittenP2 (img : Obj.Image) (fsp : BitVec 64) (w : CallW) : SepProp :=
  ((fsp + 0x98#64) ↦₆₄ w.w4) ∗
  ((fsp + 0xa0#64) ↦₆₄ w.w5) ∗
  ((fsp + 0xa8#64) ↦₆₄ w.w6) ∗
  ((fsp + 0x318#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x340#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x368#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x390#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x3b8#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x3c8#64) ↦₆₄ (img.base + dirLit3Off)) ∗
  ((fsp + 0x3d0#64) ↦₆₄ 26#64) ∗
  ((fsp + 0x3e0#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x3f0#64) ↦₆₄ (img.base + dirLit4Off)) ∗
  ((fsp + 0x408#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x418#64) ↦₆₄ (img.base + dirLit5Off)) ∗
  ((fsp + 0x420#64) ↦₆₄ 8#64) ∗
  ((fsp + 0x430#64) ↦₆₄ 8#64)

/-- Concrete words written by `M+0x6b8 .. M+0x710` (22 stack words). -/
def m4WrittenP3 (img : Obj.Image) (fsp : BitVec 64) (w : CallW) : SepProp :=
  ((fsp + 0x78#64) ↦₆₄ w.w0) ∗
  ((fsp + 0x80#64) ↦₆₄ w.w1) ∗
  ((fsp + 0x310#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x320#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x330#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x338#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x348#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x360#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x370#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x388#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x398#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x3b0#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x3c0#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x3d8#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x3e8#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x3f8#64) ↦₆₄ 17#64) ∗
  ((fsp + 0x400#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x410#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x428#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x438#64) ↦₆₄ 0#64) ∗
  ((fsp + 0x440#64) ↦₆₄ (img.base + dirLit6Off)) ∗
  ((fsp + 0x448#64) ↦₆₄ 6#64)

theorem m4_uninit_split (fsp : BitVec 64) :
    cells (fsp + 0x78#64) 7 ∗ cells (fsp + 0x310#64) 40 ⊢
      m4UninitP1 fsp ∗ m4UninitP2 fsp ∗ m4UninitP3 fsp := by
  rw [← ProofLib.memRegion_cells (fsp + 0x78#64) 7 (by decide),
      ← ProofLib.memRegion_cells (fsp + 0x310#64) 40 (by decide)]
  refine Entails.trans
    (sepConj_mono
      (memRegion_to_m4SlotsFrom fsp 7 0x78 (by decide))
      (memRegion_to_m4SlotsFrom fsp 40 0x310 (by decide))) ?_
  refine Entails.of_eq ?_
  dsimp only [m4SlotsFrom, m4UninitP1, m4UninitP2, m4UninitP3]
  simp only [Nat.reduceAdd, sepConj_emp]
  ac_rfl

theorem m4_written_pack (img : Obj.Image) (fsp : BitVec 64) (w : CallW) :
    m4WrittenP1 img fsp w ∗ m4WrittenP2 img fsp w ∗ m4WrittenP3 img fsp w =
      m4CallWords fsp w ∗ m4OpenStoresWords img fsp := by
  dsimp only [m4WrittenP1, m4WrittenP2, m4WrittenP3, m4CallWords, m4OpenStoresWords, openDirWords]
  simp only [Nat.reduceAdd]
  ac_rfl

end CryptoVerification.SignalSession.Cli.MainHops
