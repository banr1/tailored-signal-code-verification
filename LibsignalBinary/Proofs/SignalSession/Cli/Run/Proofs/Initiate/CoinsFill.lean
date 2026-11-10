/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.Apply

/-!
# `signal_session_coins_fill` Separation-Logic Contract

Proves `coinsFillSpec` for `signal_session_coins_fill(dst, len)` against `coinsCursorAt` on both
`initProg img W` (`signal_session_coins_fill_ok`) and `initProgExt img ext`
(`signal_session_coins_fill_ext_ok`), combining the copied prefix and zero-padded suffix into
`((padCoins coins).toList.drop pos).take len`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev cliCoinsFillName : String := "signal_session_coins_fill"

theorem cliCoinsFill_fnOff :
    libsignalSessionCode.fnOff cliCoinsFillName =
      num% (ls_off% "signal_session_coins_fill") :=
  ls_lemma% fnOff "signal_session_coins_fill"

/-- Stack budget for `signal_session_coins_fill` (`0x20` frame + `extHookStack`). -/
abbrev cliCoinsFillStack : Nat := 0x20 + extHookStack

/-! ## Specification and proof -/

/-- Ghost state for a `signal_session_coins_fill(dst, len)` call over `padCoins coins`. -/
structure CoinsFillGhost where
  dst : BitVec 64
  len : Nat
  p₀ : BitVec 64
  coins : List (BitVec 8)
  pos : Nat

/-- Separation-logic contract for `signal_session_coins_fill` within `initiateTapeLen` (`192` bytes). -/
def coinsFillSpec (img : Obj.Image) (stk : Nat) : Spec CoinsFillGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.len ∧
          x.coins.length < 2 ^ 63 ∧ x.pos + x.len ≤ initiateTapeLen⌝ ∗
          coinsCursorAt img x.p₀ x.coins x.pos ∗
          memRegion x.dst x.len ∗
          stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
          coinsCursorAt img x.p₀ x.coins (x.pos + x.len) ∗
          (x.dst ↦ₛ ((padCoins x.coins).toList.drop x.pos).take x.len) ∗
          stackAt s0.sp stk
      onPanic := fun _ _ _ => ⌜False⌝
      onOom := fun _ _ _ => ⌜False⌝ }
    img

set_option maxRecDepth 200000

section Helpers

open ProofLib.ProgramReflection CryptoVerification.CodeLayout

gen_decodes libsignalSessionCode_tree cliCoinsFillDec
  [(ls_off% "signal_session_coins_fill") → (ls_off% "signal_session_coins_fill" + 116)]

private theorem coinsFill_adrp_next {b fnBase : BitVec 64}
    (hb : (b &&& 4095#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "signal_session_coins_fill")) :
    (((fnBase + 24#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% coinsNextOff.toNat - page% (ls_off% "signal_session_coins_fill" + 24))) +
      bv% (coinsNextOff.toNat % 4096) =
      b + coinsNextOff := by
  subst hfn; dsimp only [coinsNextOff]; bv_arith

private theorem coinsFill_adrp_left {b fnBase : BitVec 64}
    (hb : (b &&& 4095#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "signal_session_coins_fill")) :
    (((fnBase + 28#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% coinsLeftOff.toNat - page% (ls_off% "signal_session_coins_fill" + 28))) +
      bv% (coinsLeftOff.toNat % 4096) =
      b + coinsLeftOff := by
  subst hfn; dsimp only [coinsLeftOff]; bv_arith

private theorem coinsFill_stack_split (sp : BitVec 64) {stk : Nat}
    (hstk : cliCoinsFillStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      stackAt (sp - 80#64) 0 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
  have hge : 80 ≤ stk := by
    unfold cliCoinsFillStack extHookStack at hstk
    omega
  have hsplit : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗ stackAt sp 80 := by
    have hs0 := stackAt_split_bottom sp 80 (stk - 80) (by omega)
    rwa [Nat.add_sub_of_le hge] at hs0
  have h1 := ProofLib.stackAt_split_cells sp 0 10 (by omega)
  change stackAt sp 80 = stackAt (sp - 80#64) 0 ∗ cells (sp - 80#64) 10 at h1
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [hsplit, h1, hc10]

private theorem coinsFill_bv_sub {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [BitVec.le_def, BitVec.toNat_ofNat]
    omega

private theorem coinsFill_coins_split (p₀ : BitVec 64) (coins : List (BitVec 8))
    (m k : Nat) (hmk : m + k ≤ coins.length) :
    (p₀ ↦ₛ coins) =
      (p₀ ↦ₛ coins.take m) ∗
      ((p₀ + BitVec.ofNat 64 m) ↦ₛ (coins.drop m).take k) ∗
      ((p₀ + BitVec.ofNat 64 (m + k)) ↦ₛ coins.drop (m + k)) := by
  have heq : coins = coins.take m ++ ((coins.drop m).take k ++ coins.drop (m + k)) := by
    have hdrop : (coins.drop m).drop k = coins.drop (m + k) := List.drop_drop
    rw [← hdrop, List.take_append_drop, List.take_append_drop]
  have hlm : (coins.take m).length = m := by simp; omega
  have hlk : ((coins.drop m).take k).length = k := by simp; omega
  conv => lhs; rw [heq]
  rw [pointsToBytes_append, hlm, pointsToBytes_append, hlk, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem coinsFill_slice_eq (coins : List (BitVec 8)) (pos len : Nat)
    (hpad : pos + len ≤ initiateTapeLen) :
    (coins.drop (min pos coins.length)).take (min (coins.length - min pos coins.length) len) ++
      List.replicate (len - min (coins.length - min pos coins.length) len) 0#8 =
      ((padCoins coins).toList.drop pos).take len := by
  have hpad_list : (padCoins coins).toList =
      coins.take initiateTapeLen ++ List.replicate (initiateTapeLen - coins.length) 0#8 := by
    simp [padCoins]
  apply List.ext_getElem
  · rw [hpad_list]
    simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate,
      initiateTapeLen] at hpad ⊢
    omega
  · intro i h1 h2
    have hi_lt : i < len := by
      rw [hpad_list] at h2
      simp only [List.length_take, List.length_drop, List.length_append,
        List.length_replicate, initiateTapeLen] at h2 hpad
      omega
    simp only [hpad_list, List.getElem_take, List.getElem_drop]
    by_cases hik : i < min (coins.length - min pos coins.length) len
    · have hlt_t : pos + i < (coins.take initiateTapeLen).length := by
        simp only [List.length_take]; omega
      rw [List.getElem_append_left (by simp only [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop,
        List.getElem_append_left hlt_t, List.getElem_take]
      congr 1
      omega
    · have hge_c : (coins.take initiateTapeLen).length ≤ pos + i := by
        simp only [List.length_take]; omega
      rw [List.getElem_append_right (by simp only [List.length_take, List.length_drop]; omega),
        List.getElem_replicate, List.getElem_append_right hge_c, List.getElem_replicate]

private theorem coinsFill_csel_eq (cLen pos len : Nat)
    (hc : cLen < 2 ^ 64) (hl : len < 2 ^ 64) :
    (if (BitVec.ofNat 64 (cLen - min pos cLen)).ult (BitVec.ofNat 64 len) = true then
      BitVec.ofNat 64 (cLen - min pos cLen)
    else BitVec.ofNat 64 len) =
      BitVec.ofNat 64 (min (cLen - min pos cLen) len) := by
  have hleft : cLen - min pos cLen < 2 ^ 64 := by omega
  have hult : (BitVec.ofNat 64 (cLen - min pos cLen)).ult (BitVec.ofNat 64 len) =
      decide (cLen - min pos cLen < len) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hl]
  rw [hult]
  by_cases hlt : cLen - min pos cLen < len
  · simp [hlt, Nat.min_eq_left (Nat.le_of_lt hlt)]
  · simp [hlt, Nat.min_eq_right (Nat.le_of_not_lt hlt)]

private theorem coinsFill_dst_join (dst : BitVec 64) (coins : List (BitVec 8))
    (pos len : Nat) (hpad : pos + len ≤ initiateTapeLen) (R' : SepProp) :
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
    ((dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ R') := by
  have hmid : ((coins.drop (min pos coins.length)).take
      (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hmerge :
      ((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len)) =
      (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) := by
    rw [sepConj_comm]
    conv => lhs; arg 2; arg 1; arg 2; rw [← hmid]
    rw [← pointsToBytes_append, coinsFill_slice_eq coins pos len hpad]
  rw [← sepConj_assoc, hmerge]

private def coinsFillMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗
      (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (dst ↦ₛ bs) ∗
      (src ↦ₛ bs)

private def coinsFillMemzeroSpec : Spec (BitVec 64 × Nat) where
  pre := fun (p, n) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      BitVec.truncate 8 (s0.readReg32 .x1) = 0#8 ∧
      (s0.readReg64 .x2).toNat = n ∧
      n ≤ 2 ^ 64⌝ ∗
      memRegion p n
  post := fun (p, n) s0 sf =>
    ⌜sf.readReg64 .x0 = p ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (p ↦ₛ List.replicate n 0#8)

private theorem coinsFill_fnAddr_rebase_off {b : BitVec 64}
    {H : String → Option (State → State)} {name1 name2 : String} {off1 off2 k : Nat}
    (h1 : libsignalSessionCode.fnOff name1 = off1)
    (h2 : libsignalSessionCode.fnOff name2 = off2)
    (hk : BitVec.ofNat 64 off1 + BitVec.ofNat 64 k = BitVec.ofNat 64 off2) :
    (libsignalSessionCode.rebase b H).fnAddr name1 + BitVec.ofNat 64 k =
      (libsignalSessionCode.rebase b H).fnAddr name2 :=
  (congrArg (· + BitVec.ofNat 64 k) (Program.fnAddr_rebase_add_of_fnOff h1)).trans
    ((BitVec.add_assoc _ _ _).trans
      ((congrArg (b + ·) hk).trans (Program.fnAddr_rebase_add_of_fnOff h2).symm))

private theorem coinsFill_memcpy_ok (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliCoinsFillName +
        bv% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill"))
      coinsFillMemcpySpec := by
  have haddr : (initProg img W).fnAddr cliCoinsFillName +
      bv% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill") =
      (mProg img (cliExterns W)).fnAddr memcpyName :=
    coinsFill_fnAddr_rebase_off cliCoinsFill_fnOff memcpy_fnOff (by decide)
  rw [haddr]
  refine memcpy_stub_ok W img ?_
  intro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ :=
    (hookMemcpy_region_trace_ok.keepsFs hookMemcpy_fs) (dst, src, bs) R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs, sessionMemcpyRegionSpec, coinsFillMemcpySpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem coinsFill_memzero_ok (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliCoinsFillName +
        bv% (ls_off% "memset" - ls_off% "signal_session_coins_fill"))
      coinsFillMemzeroSpec := by
  have haddr : (initProg img W).fnAddr cliCoinsFillName +
      bv% (ls_off% "memset" - ls_off% "signal_session_coins_fill") =
      (mProg img (cliExterns W)).fnAddr memsetName :=
    coinsFill_fnAddr_rebase_off cliCoinsFill_fnOff memset_fnOff (by decide)
  rw [haddr]
  refine memset_stub_ok W img ?_
  intro ⟨p, n⟩ R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ :=
    (hookMemset_region_trace_ok.keepsFs hookMemset_fs) (p, 0#8, n) R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs, sessionMemsetRegionSpec, coinsFillMemzeroSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

end Helpers

section FixedTable

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 400000 in
/-- Proves `coinsFillSpec` for `signal_session_coins_fill` on `initProg img W`. -/
theorem signal_session_coins_fill_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : cliCoinsFillStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliCoinsFillName)
      (coinsFillSpec img stk) := by
  let _ := hh
  have hb : (img.base &&& 4095#64) = 0#64 := base_aligned himg
  have hstk_split : ∀ sp : BitVec 64, stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      stackAt (sp - 80#64) 0 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) :=
    fun sp => coinsFill_stack_split sp hstk hstk64
  have hmc := coinsFill_memcpy_ok W img
  have hms := coinsFill_memzero_ok W img
  have hfn := cliCoinsFill_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliCoinsFillDec img.base
    (Rust.withPanics (cliExterns W)) hfn (num% (ls_off% "signal_session_coins_fill")) 0 120
  clear hfn
  simp only [coinsFillSpec, Spec.inImage, hstk_split, sepExists_sepConj_right]
  clear hstk_split hstk hstk64
  dsimp only [initProg, tripleRatchetProgAtExt] at hmc hms ⊢
  generalize hfnB :
    (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W))).fnAddr
      cliCoinsFillName = fnBase at *
  have hfn_eq : fnBase = img.base + bv% (ls_off% "signal_session_coins_fill") := by
    rw [← hfnB, Program.fnAddr_rebase, cliCoinsFill_fnOff]
  clear hfnB himg
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hcn := coinsFill_adrp_next (fnBase := fnBase) hb hfn_eq
  have hcl := coinsFill_adrp_left (fnBase := fnBase) hb hfn_eq
  clear hfn_eq hb
  obtain ⟨dst, len, p₀, coins, pos⟩ := x
  dsimp only [coinsCursorAt] at *
  have hcoins63 : coins.length < 2 ^ 63 := ‹_›
  have hpad : pos + len ≤ initiateTapeLen := ‹_›
  have htape : initiateTapeLen = 192 := rfl
  have hc64 : coins.length < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have hleft64 : coins.length - min pos coins.length < 2 ^ 64 := by omega
  have hk64 : min (coins.length - min pos coins.length) len < 2 ^ 64 := by omega
  have hmk_le : min pos coins.length + min (coins.length - min pos coins.length) len ≤
      coins.length := by omega
  have hrem_le64 : len - min (coins.length - min pos coins.length) len ≤ 2 ^ 64 := by omega
  have hmid_len :
      ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hcsel := coinsFill_csel_eq coins.length pos len hc64 hlen64
  have hnext_bv1 :
      p₀ + BitVec.ofNat 64 (min pos coins.length) +
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      p₀ + BitVec.ofNat 64 (min (pos + len) coins.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show min pos coins.length + min (coins.length - min pos coins.length) len =
        min (pos + len) coins.length by omega]
  have hnext_bv2 :
      p₀ + (BitVec.ofNat 64 (min pos coins.length) +
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) =
      p₀ + BitVec.ofNat 64 (min (pos + len) coins.length) := by
    rw [← BitVec.add_assoc, hnext_bv1]
  have hleft_bv :
      BitVec.ofNat 64 (coins.length - min pos coins.length) -
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      BitVec.ofNat 64 (coins.length - min (pos + len) coins.length) := by
    rw [coinsFill_bv_sub (by omega) hleft64,
      show (coins.length - min pos coins.length) -
          min (coins.length - min pos coins.length) len =
        coins.length - min (pos + len) coins.length by omega]
  have hrem_bv :
      BitVec.ofNat 64 len -
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      BitVec.ofNat 64 (len - min (coins.length - min pos coins.length) len) :=
    coinsFill_bv_sub (by omega) hlen64
  have htoNat_k :
      (BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)).toNat =
      ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, hmid_len]
  have htoNat_rem :
      (BitVec.ofNat 64 (len - min (coins.length - min pos coins.length) len)).toNat =
      len - min (coins.length - min pos coins.length) len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdst_split : memRegion dst len =
      memRegion dst ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length ∗
      memRegion (dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len))
        (len - min (coins.length - min pos coins.length) len) := by
    conv =>
      lhs
      rw [show len = min (coins.length - min pos coins.length) len +
        (len - min (coins.length - min pos coins.length) len) by omega]
    rw [ProofLib.memRegion_split dst _ _ (by omega), hmid_len]
  rw [coinsFill_coins_split p₀ coins (min pos coins.length)
        (min (coins.length - min pos coins.length) len) hmk_le]
  wp_conv_pre => rw [hdst_split]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_apply using hmc
  wp_steps
  wp_apply using hms
  wp_steps
  wp_conv_pre => rw [coinsFill_dst_join dst coins pos len hpad]
  wp_done

end FixedTable

/-! ## Extern-parameterized contract (`CliExternsOk`) -/

theorem coinsFill_memHookStack_fits :
    80 + CliExt.memHookStack ≤ cliCoinsFillStack := by
  dsimp only [CliExt.memHookStack, cliCoinsFillStack, extHookStack]; decide

section ExtHelpers

open ProofLib.ProgramReflection CryptoVerification.CodeLayout

private theorem coinsFill_stack_split_ext (sp : BitVec 64) {stk : Nat}
    (hstk : cliCoinsFillStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - (80 + CliExt.memHookStack)) ∗
      stackAt (sp - 80#64) CliExt.memHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
  have hfit := coinsFill_memHookStack_fits
  have hge : 80 + CliExt.memHookStack ≤ stk := Nat.le_trans hfit hstk
  have hsplit : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - (80 + CliExt.memHookStack)) ∗
        stackAt sp (80 + CliExt.memHookStack) := by
    have hs0 := stackAt_split_bottom sp (80 + CliExt.memHookStack)
      (stk - (80 + CliExt.memHookStack)) (by dsimp only [CliExt.memHookStack] at *; omega)
    rwa [Nat.add_sub_of_le hge] at hs0
  have h1 := ProofLib.stackAt_split_cells sp CliExt.memHookStack 10
    (by dsimp only [CliExt.memHookStack]; omega)
  change stackAt sp (80 + CliExt.memHookStack) =
      stackAt (sp - 80#64) CliExt.memHookStack ∗ cells (sp - 80#64) 10 at h1
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [hsplit, h1, hc10]

private theorem coinsFill_dst_join_ext (dst : BitVec 64) (coins : List (BitVec 8))
    (pos len : Nat) (hpad : pos + len ≤ initiateTapeLen) (S R' : SepProp) :
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      S ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
    ((dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ S ∗ R') := by
  have hmid : ((coins.drop (min pos coins.length)).take
      (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hmerge :
      ((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len)) =
      (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) := by
    rw [sepConj_comm]
    conv => lhs; arg 2; arg 1; arg 2; rw [← hmid]
    rw [← pointsToBytes_append, coinsFill_slice_eq coins pos len hpad]
  calc
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      S ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
      (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len))) ∗ S ∗ R' := by ac_rfl
    _ = (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ S ∗ R' := by rw [hmerge]

private def coinsFillMemcpyExtSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗
      (src ↦ₛ bs) ∗
      stackAt s0.sp CliExt.memHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (dst ↦ₛ bs) ∗
      (src ↦ₛ bs) ∗
      stackAt s0.sp CliExt.memHookStack

private def coinsFillMemzeroExtSpec : Spec (BitVec 64 × Nat) where
  pre := fun (p, n) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      BitVec.truncate 8 (s0.readReg32 .x1) = 0#8 ∧
      (s0.readReg64 .x2).toNat = n⌝ ∗
      memRegion p n ∗
      stackAt s0.sp CliExt.memHookStack
  post := fun (p, n) s0 sf =>
    ⌜sf.readReg64 .x0 = p ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (p ↦ₛ List.replicate n 0#8) ∗
      stackAt s0.sp CliExt.memHookStack

private theorem coinsFill_memcpy_ext_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCoinsFillName +
        bv% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill"))
      coinsFillMemcpyExtSpec := by
  have haddr : (initProgExt img ext).fnAddr cliCoinsFillName +
      bv% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill") =
      (initProgExt img ext).fnAddr memcpyName :=
    coinsFill_fnAddr_rebase_off cliCoinsFill_fnOff memcpy_fnOff (by decide)
  rw [haddr]
  rcases hookSat_keepsFs_of_ok hOk (by decide) hOk.memcpy with ⟨f, hf, hok⟩
  refine ext_stub_ok img memcpy_fnOff (by decide) (ls_hook% "memcpy")
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memcpyName]) ⟨f, hf, ?_⟩
  intro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ CliExt.memcpySpec.keepsFs.pre (dst, src, bs) s0 ∗ R := by
    simpa only [Arm64.Spec.keepsFs, CliExt.memcpySpec, libcMemcpySpec, coinsFillMemcpyExtSpec]
      using hpre
  obtain ⟨hkf, hsym, hout⟩ := hok (dst, src, bs) R s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs, CliExt.memcpySpec, coinsFillMemcpyExtSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem coinsFill_memzero_ext_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCoinsFillName +
        bv% (ls_off% "memset" - ls_off% "signal_session_coins_fill"))
      coinsFillMemzeroExtSpec := by
  have haddr : (initProgExt img ext).fnAddr cliCoinsFillName +
      bv% (ls_off% "memset" - ls_off% "signal_session_coins_fill") =
      (initProgExt img ext).fnAddr memsetName :=
    coinsFill_fnAddr_rebase_off cliCoinsFill_fnOff memset_fnOff (by decide)
  rw [haddr]
  rcases hookSat_keepsFs_of_ok hOk (by decide) hOk.memset with ⟨f, hf, hok⟩
  refine ext_stub_ok img memset_fnOff (by decide) (ls_hook% "memset")
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memsetName]) ⟨f, hf, ?_⟩
  intro ⟨p, n⟩ R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ CliExt.memsetSpec.keepsFs.pre (p, 0#8, n) s0 ∗ R := by
    simpa only [Arm64.Spec.keepsFs, CliExt.memsetSpec, libcMemsetSpec, coinsFillMemzeroExtSpec]
      using hpre
  obtain ⟨hkf, hsym, hout⟩ := hok (p, 0#8, n) R s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs, CliExt.memsetSpec, coinsFillMemzeroExtSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

end ExtHelpers

section ExtBody

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 400000 in
/-- Proves `coinsFillSpec` for `signal_session_coins_fill` on `initProgExt img ext` under `CliExternsOk P A ext`. -/
theorem signal_session_coins_fill_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    {stk : Nat} (hstk : cliCoinsFillStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCoinsFillName)
      (coinsFillSpec img stk) := by
  have hb : (img.base &&& 4095#64) = 0#64 := base_aligned himg
  have hstk_split : ∀ sp : BitVec 64, stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - (80 + CliExt.memHookStack)) ∗
      stackAt (sp - 80#64) CliExt.memHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) :=
    fun sp => coinsFill_stack_split_ext sp hstk hstk64
  have hmc := coinsFill_memcpy_ext_ok img hOk
  have hms := coinsFill_memzero_ext_ok img hOk
  have hfn := cliCoinsFill_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.SignalSession.Cli.RunProofs.Initiate.cliCoinsFillDec img.base
    (Rust.withPanics (cliExternsWith ext)) hfn (num% (ls_off% "signal_session_coins_fill")) 0 120
  clear hfn
  simp only [coinsFillSpec, Spec.inImage, hstk_split, sepExists_sepConj_right]
  clear hstk_split hstk hstk64
  dsimp only [initProgExt, tripleRatchetProgAtExt] at hmc hms ⊢
  generalize hfnB :
    (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr
      cliCoinsFillName = fnBase at *
  have hfn_eq : fnBase = img.base + bv% (ls_off% "signal_session_coins_fill") := by
    rw [← hfnB, Program.fnAddr_rebase, cliCoinsFill_fnOff]
  clear hfnB himg hOk
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hcn := coinsFill_adrp_next (fnBase := fnBase) hb hfn_eq
  have hcl := coinsFill_adrp_left (fnBase := fnBase) hb hfn_eq
  clear hfn_eq hb
  obtain ⟨dst, len, p₀, coins, pos⟩ := x
  dsimp only [coinsCursorAt] at *
  have hcoins63 : coins.length < 2 ^ 63 := ‹_›
  have hpad : pos + len ≤ initiateTapeLen := ‹_›
  have htape : initiateTapeLen = 192 := rfl
  have hc64 : coins.length < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have hleft64 : coins.length - min pos coins.length < 2 ^ 64 := by omega
  have hk64 : min (coins.length - min pos coins.length) len < 2 ^ 64 := by omega
  have hmk_le : min pos coins.length + min (coins.length - min pos coins.length) len ≤
      coins.length := by omega
  have hmid_len :
      ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hcsel := coinsFill_csel_eq coins.length pos len hc64 hlen64
  have hnext_bv1 :
      p₀ + BitVec.ofNat 64 (min pos coins.length) +
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      p₀ + BitVec.ofNat 64 (min (pos + len) coins.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show min pos coins.length + min (coins.length - min pos coins.length) len =
        min (pos + len) coins.length by omega]
  have hnext_bv2 :
      p₀ + (BitVec.ofNat 64 (min pos coins.length) +
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) =
      p₀ + BitVec.ofNat 64 (min (pos + len) coins.length) := by
    rw [← BitVec.add_assoc, hnext_bv1]
  have hleft_bv :
      BitVec.ofNat 64 (coins.length - min pos coins.length) -
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      BitVec.ofNat 64 (coins.length - min (pos + len) coins.length) := by
    rw [coinsFill_bv_sub (by omega) hleft64,
      show (coins.length - min pos coins.length) -
          min (coins.length - min pos coins.length) len =
        coins.length - min (pos + len) coins.length by omega]
  have hrem_bv :
      BitVec.ofNat 64 len -
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      BitVec.ofNat 64 (len - min (coins.length - min pos coins.length) len) :=
    coinsFill_bv_sub (by omega) hlen64
  have htoNat_k :
      (BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)).toNat =
      ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, hmid_len]
  have htoNat_rem :
      (BitVec.ofNat 64 (len - min (coins.length - min pos coins.length) len)).toNat =
      len - min (coins.length - min pos coins.length) len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdst_split : memRegion dst len =
      memRegion dst ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length ∗
      memRegion (dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len))
        (len - min (coins.length - min pos coins.length) len) := by
    conv =>
      lhs
      rw [show len = min (coins.length - min pos coins.length) len +
        (len - min (coins.length - min pos coins.length) len) by omega]
    rw [ProofLib.memRegion_split dst _ _ (by omega), hmid_len]
  rw [coinsFill_coins_split p₀ coins (min pos coins.length)
        (min (coins.length - min pos coins.length) len) hmk_le]
  wp_conv_pre => rw [hdst_split]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_apply using hmc
  wp_steps
  wp_apply using hms
  wp_steps
  wp_conv_pre => rw [coinsFill_dst_join_ext dst coins pos len hpad]
  wp_done

end ExtBody

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
