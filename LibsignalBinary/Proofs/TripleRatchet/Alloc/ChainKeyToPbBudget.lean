/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public meta import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Contract for `<ChainKey>::to_pb` (Block `22`)

Verifies `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` against `chainKeyToPbSpec M A lim`
on `tripleRatchetProgAt{,Ext}` and under `[LibsignalPlacement]` (Block `22`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement blkPC_22 blkPl_22 libsignalSessionCode lsRustAllocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem lsρ
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack vecHeader vecU8At)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes leBytes optChainKeyAt)
open CryptoVerification.LibsignalTripleRatchet (
  SepWP.seq_optImage extHookStack specWithOptInv
  subroutine_ok_kit_of_trTrap subroutine_ok_of_optNone trTrapProgAt
  tripleRatchetProgAt tripleRatchetProgAtExt
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsBudget AllocContractsXBudget chainKeyToPbEvents chainKeyToPbName
  chainKeyToPbSpec chainKeyToPbSpecX fitsEnv_chainKeyToPb_iff noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  allocNoOomExtern_opt_of_base allocNoOomExtern_opt_of_x chainKeyToPbSpecWithStack
  rebase_trapHooks_fnAddr rustAllocNoOomExternSpecWithStack rustAllocNoOomExternSpecWithStackBase
  sepWP_optImage_rebase_vm shimSpecWithStack shimWithStack_of_noAllocShim shim_opt_of_base
  shim_opt_of_x
)

private theorem fetch_rebase_withSvc_noSyscalls (P : Program) (b : BitVec 64)
    (Hk : String → Option (State → State)) (pc : BitVec 64) :
    ((P.rebase b Hk).withSvc noSyscalls).fetch pc = (P.rebase b Hk).fetch pc := rfl

private theorem sepWP_seq_optImage_lr {prog : Program} {oimg : Option Obj.Image}
    {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : OptCallInv oimg s)
    (h : SepWP prog (s.readReg64 .lr) s P
      (fun sm Pm => OptCallInv oimg sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq_optImage (mid := s.readReg64 .lr) hinv h

local macro "wp_steps_opt_vm " mid:term:max hinv:term:max : tactic => `(tactic| (
  apply sepWP_optImage_rebase_vm (mid := $mid) $hinv
  wp_steps
  refine ProofLib.SepWP.done
    (by first | rfl | wp_norm_lhs | simp only [wp_norm, arm64_norm])
    (by first | assumption | wp_norm_lhs)
    ⟨by first | rfl | simp only [wp_norm, arm64_norm], fun hinv_next hvm_next => ?_⟩
  refine ProofLib.SepWP.transport_budgetPool hvm_next (hnext := ?_)
))

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

private theorem optCallInv_none (s : State) : OptCallInv none s := trivial

section FixedBaseSteps

attribute [local irreducible] Program.fnOff

theorem chain_key_to_pb_ok_of_hooks_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
      (specWithOptInv oimg (rustAllocNoOomExternSpecWithStackBase M A lim false hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName)
      (specWithOptInv oimg (chainKeyToPbSpecWithStack M A lim hookStack)) := by
  unfold specWithOptInv tripleRatchetProgAtExt at hshim halloc ⊢
  unfold chainKeyToPbSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.chainKeyToPbSpecWithStack
  simp only [fitsEnv_chainKeyToPb_iff, chainKeyToPbEvents,
    chainKeyBytes, pointsToBytes_append, keyToBytes32_len,
    pointsToBytes_leBytes4, memRegion_ret32, stackAt_chainKeyToPb_opt hstack,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [rustAllocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStackBase,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  have hfn : libsignalSessionCode.fnOff chainKeyToPbName =
      num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    trapHooks hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")) 100
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode b (Rust.withPanics ext) chainKeyToPbName]
    at hshim halloc ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr chainKeyToPbName = entry
  simp (config := { singlePass := true }) only [← fetch_rebase_withSvc_noSyscalls] at *
  examples_hide_fetches
  wp_init g s0
  rcases g with ⟨⟨self, ck, ret⟩, st⟩
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ :=
    exists_unpack64_of_length_32 (keyToBytes32_len ck.key)
  rw [hkey_cells self]
  have hfe_raw : FitsEvents M lim st [.alloc 32] := by
    simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 32 1)›
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (32 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_opt_vm
    (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb"))
    hinv0
  apply sepWP_seq_optImage_lr (by assumption)
  wp_call hshim ()
  refine ProofLib.SepWP.done (by assumption) (by assumption) ?_
  intro hinv1
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_opt_vm
    (entry + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb"))
    hinv1
  wp_call halloc (32, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by tauto
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
  simp only [optChainKeyAt, vecU8At, vecHeader, keyToBytes32_len,
    (by decide : (32#64 : BitVec 64) = 0 ↔ False),
    ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
    Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
  wp_done

end FixedBaseSteps

theorem chain_key_to_pb_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec M A lim) :=
  subroutine_ok_of_optNone <|
    chain_key_to_pb_ok_of_hooks_opt (by decide)
      (shim_opt_of_base hA (name := chainKeyToPbName)
        (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))
      (allocNoOomExtern_opt_of_base hA (name := chainKeyToPbName)
        (k := num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))

theorem chain_key_to_pb_ok_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec M A lim) :=
  chain_key_to_pb_ok_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA)

/-- `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` meets `chainKeyToPbSpec M A lim`
on `tripleRatchetProgAt`. -/
theorem chain_key_to_pb_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec M A lim) :=
  subroutine_ok_kit_of_trTrap (chain_key_to_pb_ok_trap hA)

theorem chain_key_to_pb_ok_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainKeyToPbName)
      ((chainKeyToPbSpecX M A lim).inImage img) :=
  chain_key_to_pb_ok_of_hooks_opt (oimg := some img) (by decide)
    (shim_opt_of_x hA (name := chainKeyToPbName)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))
    (allocNoOomExtern_opt_of_x hA (name := chainKeyToPbName)
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `22`) -/

theorem chain_key_to_pb_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_22).rebase (blkPl_22).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_22).rebase (blkPl_22).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpecWithStack M A lim hookStack) := by
  unfold chainKeyToPbSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.chainKeyToPbSpecWithStack
  simp only [fitsEnv_chainKeyToPb_iff, chainKeyToPbEvents,
    chainKeyBytes, pointsToBytes_append, keyToBytes32_len,
    pointsToBytes_leBytes4, memRegion_ret32, stackAt_chainKeyToPb_opt hstack,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  wp_init g s0
  rcases g with ⟨⟨self, ck, ret⟩, st⟩
  dsimp only at *
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ :=
    exists_unpack64_of_length_32 (keyToBytes32_len ck.key)
  rw [hkey_cells self]
  have hfe_raw : FitsEvents M lim st [.alloc 32] := by
    simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 32 1)›
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (32 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (32, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, optChainKeyAt, vecU8At, vecHeader, keyToBytes32_len,
    (by decide : (32#64 : BitVec 64) = 0 ↔ False),
    ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
    Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
  wp_done

/-- Relocatable `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (Block `22`) meets
`chainKeyToPbSpec M A lim`. -/
theorem chain_key_to_pb_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpec M A lim) :=
  chain_key_to_pb_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem chain_key_to_pb_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpecX M A lim) :=
  chain_key_to_pb_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem chain_key_to_pb_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpec M A lim) :=
  chain_key_to_pb_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))

theorem chain_key_to_pb_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok ((blkPC_22).rebase (blkPl_22).base H) (blkPl_22).base
      (chainKeyToPbSpecX M A lim) :=
  chain_key_to_pb_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))

end LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget
