/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMap
public import LibsignalBinary.Proofs.Cli.TripleRatchet.CliRatchetCodeSymA
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WP.Apply

/-!
# Relocatable CLI `kyberMap` Closure Proof

Verifies the Kyber payload `Option::map` closure (`blkPl_430`) on `lsProg_430 H` under
`[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap

open Arm64 ProofLib ProofLib.ProgramReflection
open Arm64.Obj CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap hiding lsHandleAllocErrorSym kyberMap_placed_ok
open CryptoVerification.CliRatchet.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_kyberMap (sp : BitVec 64) :
    stackAt sp (allocHookStack + 0x40) =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)

private theorem memRegion_24_none (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ u0 : BitVec 64, (p ↦₆₄ u0) ∗ memRegion (p + 8#64) 16) := by
  rw [memRegion_split p 8 16 (by decide), ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left]

private theorem memRegion_24_some (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₃₂ u2) ∗ memRegion (p + 20#64) 4) := by
  rw [memRegion_split p 8 16 (by decide),
    memRegion_split (p + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64) 4 4 (by decide),
    memRegion_four, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem optKyberAt_none_exists (A : RustAlloc) (out : BitVec 64) :
    (∃∗ bp : BitVec 64, optKyberAt A out bp none) =
      (out ↦₆₄ 0#64) ∗ memRegion (out + 8#64) 16 := by
  apply ProofLib.sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun _ => by simp only [optKyberAt]; exact Entails.refl _
  · exact Entails.sepExists_right 0#64 (by simp only [optKyberAt]; exact Entails.refl _)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/



abbrev lsHandleAllocErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

set_option maxHeartbeats 1600000 in
theorem kyberMap_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_430 H) (blkPl_430).base (kyberMapSpec A) := by
  simp only [kyberMapSpec, stackAt_kyberMap]
  cells_unfold
  have h_shim : subroutine_ok (lsProg_430 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec :=
    ls_hook_ok_of_mem hshim
  have h_alloc : subroutine_ok (lsProg_430 H) (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have h_memcpy : subroutine_ok (lsProg_430 H) (lsρ lsMemcpySym) framelessMemcpySpec :=
    ls_hook_ok_of_mem hmemcpy
  have h_pan : (lsProg_430 H).externAt? (lsρ lsHandleAllocErrorSym) = some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := lsProg_430 H) (sym := lsHandleAllocErrorSym)]; exact hpanic
  dsimp only [noAllocShimSpec] at h_shim
  dsimp only [framelessMemcpySpec] at h_memcpy
  wpp_init x s0
  obtain ⟨out, arg, ptr, kp⟩ := x
  dsimp only at *
  cases kp with
  | none =>
    simp only [kyberArgAt, optKyberAt_none_exists, memRegion_24_none, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  | some k =>
    simp only [kyberArgAt, optKyberAt, boxU8At, memRegion_24_some, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine SepWPp.pure_elim fun ⟨hptr_ne, hlen_lt32⟩ => ?_
    have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    have hlen_lt63 : k.ciphertext.length < 2 ^ 63 := by omega
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, sepConj_emp, emp_sepConj]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_ne0 : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hpow2 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
      have hbound : k.ciphertext.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk k.ciphertext.length 1 := ⟨hpos, hpow2, hbound⟩
      simp only [hbs, ite_false]
      apply SepWPp.of_sepWP (mid := (blkPl_430).base + 60#64)
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      apply SepWP.done (by simp_all) (by simp_all)
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_mid fun htrace => ?_
        apply SepWPp.of_sepWP (mid := lsρ lsHandleAllocErrorSym)
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
      · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_apply
        wp_steps
        wp_done


end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap
