/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (`0xcf68`)

Verifies `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (`0xcf68`, 25 instructions)
against `chainKeyToPbSpec A` on `tripleRatchetProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
  CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSession
  CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::raw_vec::handle_error")

private theorem keyToBytes32_len (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem stackAt_chainKeyToPb_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem leBytes4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  have d0 : w.toNat / 256 ^ 0 = w.toNat := Nat.div_one w.toNat
  have d1 : w.toNat / 256 ^ 1 = (w >>> 8).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have d2 : w.toNat / 256 ^ 2 = (w >>> 16).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have d3 : w.toNat / 256 ^ 3 = (w >>> 24).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.extractLsb' 0 8 := by
    rw [d0, BitVec.ofNat_toNat]; bv_kernel
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = w.extractLsb' 8 8 := by
    rw [d1, BitVec.ofNat_toNat]; bv_kernel
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = w.extractLsb' 16 8 := by
    rw [d2, BitVec.ofNat_toNat]; bv_kernel
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = w.extractLsb' 24 8 := by
    rw [d3, BitVec.ofNat_toNat]; bv_kernel
  simp only [leBytes, List.range, List.range.loop, List.map, unpack32, h0, h1, h2, h3]

private theorem pointsToBytes_leBytes4 (a : BitVec 64) (w : BitVec 32) :
    (a ↦ₛ leBytes 4 w.toNat) = (a ↦₃₂ w) := by
  rw [leBytes4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

private theorem memRegion_ret32 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 32, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗
        ((a + 24#64) ↦₃₂ v0) ∗ memRegion (a + 28#64) 4) := by
  rw [memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 4 4 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u2) ∗ ((a + 16#64) ↦₆₄ u1) ∗ ((a + 24#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem chain_key_to_pb_ok_of_hooks_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName)
      (specWithOptInv oimg (chainKeyToPbSpecWithStack A hookStack)) := by
  unfold specWithOptInv
  simp only [chainKeyToPbSpecWithStack, chainKeyBytes, pointsToBytes_append, keyToBytes32_len,
    pointsToBytes_leBytes4, memRegion_ret32, stackAt_chainKeyToPb_opt hstack,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := chainKeyToPbName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb"))
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainKeyToPbName = num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalTripleRatchetBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")) 100
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr chainKeyToPbName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainKeyToPbName = entry
  examples_hide_fetches
  obtain ⟨self, ck, ret⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ :=
    exists_unpack64_of_length_32 (keyToBytes32_len ck.key)
  rw [hkey_cells self]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (44))
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_32_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [optChainKeyAt, vecU8At, vecHeader, keyToBytes32_len,
      (by decide : (32#64 : BitVec 64) = 0 ↔ False),
      ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
      Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
    wp_done

theorem chain_key_to_pb_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec A) :=
  subroutine_ok_of_optNone <|
    chain_key_to_pb_ok_of_hooks_opt (by decide)
      (shim_opt_of_base hA (name := chainKeyToPbName)
        (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))
      (alloc_opt_of_base hA (name := chainKeyToPbName)
        (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))

theorem chain_key_to_pb_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec A) :=
  chain_key_to_pb_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

/-- `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (`0xcf68`) meets `chainKeyToPbSpec A`
on `tripleRatchetProgAt`. -/
theorem chain_key_to_pb_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs chainKeyToPbName).rec
    (motive := fun addr _ => subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (chainKeyToPbSpec A))
    (subroutine_ok_kit_of_trTrap (chain_key_to_pb_ok_trap hA))

theorem chain_key_to_pb_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainKeyToPbName)
      ((chainKeyToPbSpecX A).inImage img) :=
  chain_key_to_pb_ok_of_hooks_opt (oimg := some img) (by decide)
    (shim_opt_of_x hA (name := chainKeyToPbName)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))
    (alloc_opt_of_x hA (name := chainKeyToPbName)
      (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `22`) -/

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  refine subroutine_ok_mono (subroutine_ok_withStack_of_subroutine_ok h hookStack)
    (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

theorem chain_key_to_pb_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_22).rebase (blkPl_22).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_22).rebase (blkPl_22).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hpanic : ((blkPC_22).rebase (blkPl_22).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpecWithStack A hookStack) := by
  simp only [chainKeyToPbSpecWithStack, chainKeyBytes, pointsToBytes_append, keyToBytes32_len,
    pointsToBytes_leBytes4, memRegion_ret32, stackAt_chainKeyToPb_opt hstack,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wpp_init x s0
  obtain ⟨self, ck, ret⟩ := x
  dsimp only at *
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ :=
    exists_unpack64_of_length_32 (keyToBytes32_len ck.key)
  rw [hkey_cells self]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_22).base + bv% (44))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm, wp_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_32_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [optChainKeyAt, vecU8At, vecHeader, keyToBytes32_len,
      (by decide : (32#64 : BitVec 64) = 0 ↔ False),
      ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
      Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
    wp_done

/-- Relocatable `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (Block `22`) meets
`chainKeyToPbSpec A`. -/
theorem chain_key_to_pb_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpec A) :=
  chain_key_to_pb_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    ((ls_externAt?_of_mem).trans hpanic)

theorem chain_key_to_pb_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpecX A) :=
  chain_key_to_pb_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide))
    ((ls_externAt?_of_mem).trans hpanic)

end CryptoVerification.LibsignalTripleRatchet
