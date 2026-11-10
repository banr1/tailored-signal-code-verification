/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Decodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.FallibleWithCapacity
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<RawTable<(ProtocolAddress, V)>>::reserve_rehash` on an Empty Table

Proves `reserveRehashIdentityEmpty_ok` (`0x0081c`, `stride = 64`) and
`reserveRehashSessionEmpty_ok` (`0x00a44`, `stride = 400`).
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownModel
open FallibleWithCapacity

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

namespace ReserveRehash

theorem fallibleWithCapacity_fnAddr_of_id (b : BitVec 64) (ext : HookMap) :
    (RebasedProg b ext).fnAddr fallibleWithCapacityName =
      (RebasedProg b ext).fnAddr reserveRehashIdName + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") :=
  Program.fnAddr_rel reserveRehashId_fnOff fallibleWithCapacity_fnOff (by decide)

theorem fallibleWithCapacity_fnAddr_of_sess (b : BitVec 64) (ext : HookMap) :
    (RebasedProg b ext).fnAddr fallibleWithCapacityName =
      (RebasedProg b ext).fnAddr reserveRehashSessionName + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") :=
  Program.fnAddr_rel reserveRehashSession_fnOff fallibleWithCapacity_fnOff (by decide)

theorem stackAt_reserveRehash_id (sp : BitVec 64) :
    stackAt sp reserveRehashStack =
      memRegion (sp - 4416#64) 32 ∗
        stackAt (sp - 160#64) fallibleWithCapacityStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
         ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
         ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
          ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗
          ((sp - 144#64) ↦₆₄ v2) ∗ ((sp - 136#64) ↦₆₄ v3) ∗
          ((sp - 128#64) ↦₆₄ v4) ∗ ((sp - 120#64) ↦₆₄ v5) ∗
          ((sp - 112#64) ↦₆₄ v6) ∗ ((sp - 104#64) ↦₆₄ v7) ∗
          ((sp - 96#64) ↦₆₄ v8) ∗ ((sp - 88#64) ↦₆₄ v9) ∗
          ((sp - 80#64) ↦₆₄ v10) ∗ ((sp - 72#64) ↦₆₄ v11) ∗
          ((sp - 64#64) ↦₆₄ v12) ∗ ((sp - 56#64) ↦₆₄ v13) ∗
          ((sp - 48#64) ↦₆₄ v14) ∗ ((sp - 40#64) ↦₆₄ v15) ∗
          ((sp - 32#64) ↦₆₄ v16) ∗ ((sp - 24#64) ↦₆₄ v17) ∗
          ((sp - 16#64) ↦₆₄ v18) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
  have h1 := stackAt_split_bottom sp 4384 32 (by decide)
  have h2 := stackAt_split_cells sp 4224 20 (by decide)
  change stackAt sp reserveRehashStack = memRegion (sp - 4416#64) 32 ∗ stackAt sp 4384 at h1
  change stackAt sp 4384 = stackAt (sp - 160#64) fallibleWithCapacityStack ∗ cells (sp - 160#64) 20 at h2
  have hc20 : cells (sp - 160#64) 20 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
        ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗
        ((sp - 144#64) ↦₆₄ v2) ∗ ((sp - 136#64) ↦₆₄ v3) ∗
        ((sp - 128#64) ↦₆₄ v4) ∗ ((sp - 120#64) ↦₆₄ v5) ∗
        ((sp - 112#64) ↦₆₄ v6) ∗ ((sp - 104#64) ↦₆₄ v7) ∗
        ((sp - 96#64) ↦₆₄ v8) ∗ ((sp - 88#64) ↦₆₄ v9) ∗
        ((sp - 80#64) ↦₆₄ v10) ∗ ((sp - 72#64) ↦₆₄ v11) ∗
        ((sp - 64#64) ↦₆₄ v12) ∗ ((sp - 56#64) ↦₆₄ v13) ∗
        ((sp - 48#64) ↦₆₄ v14) ∗ ((sp - 40#64) ↦₆₄ v15) ∗
        ((sp - 32#64) ↦₆₄ v16) ∗ ((sp - 24#64) ↦₆₄ v17) ∗
        ((sp - 16#64) ↦₆₄ v18) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
    cells_unfold
  rw [h1, h2, hc20, ← sepConj_assoc]

theorem stackAt_reserveRehash_sess (sp : BitVec 64) :
    stackAt sp reserveRehashStack =
      memRegion (sp - 4416#64) 16 ∗
        stackAt (sp - 176#64) fallibleWithCapacityStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
         ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
         ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
         ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
          ((sp - 176#64) ↦₆₄ v0) ∗ ((sp - 168#64) ↦₆₄ v1) ∗
          ((sp - 160#64) ↦₆₄ v2) ∗ ((sp - 152#64) ↦₆₄ v3) ∗
          ((sp - 144#64) ↦₆₄ v4) ∗ ((sp - 136#64) ↦₆₄ v5) ∗
          ((sp - 128#64) ↦₆₄ v6) ∗ ((sp - 120#64) ↦₆₄ v7) ∗
          ((sp - 112#64) ↦₆₄ v8) ∗ ((sp - 104#64) ↦₆₄ v9) ∗
          ((sp - 96#64) ↦₆₄ v10) ∗ ((sp - 88#64) ↦₆₄ v11) ∗
          ((sp - 80#64) ↦₆₄ v12) ∗ ((sp - 72#64) ↦₆₄ v13) ∗
          ((sp - 64#64) ↦₆₄ v14) ∗ ((sp - 56#64) ↦₆₄ v15) ∗
          ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗
          ((sp - 32#64) ↦₆₄ v18) ∗ ((sp - 24#64) ↦₆₄ v19) ∗
          ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v21)) := by
  have h1 := stackAt_split_bottom sp 4400 16 (by decide)
  have h2 := stackAt_split_cells sp 4224 22 (by decide)
  change stackAt sp reserveRehashStack = memRegion (sp - 4416#64) 16 ∗ stackAt sp 4400 at h1
  change stackAt sp 4400 = stackAt (sp - 176#64) fallibleWithCapacityStack ∗ cells (sp - 176#64) 22 at h2
  have hc22 : cells (sp - 176#64) 22 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
       ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
        ((sp - 176#64) ↦₆₄ v0) ∗ ((sp - 168#64) ↦₆₄ v1) ∗
        ((sp - 160#64) ↦₆₄ v2) ∗ ((sp - 152#64) ↦₆₄ v3) ∗
        ((sp - 144#64) ↦₆₄ v4) ∗ ((sp - 136#64) ↦₆₄ v5) ∗
        ((sp - 128#64) ↦₆₄ v6) ∗ ((sp - 120#64) ↦₆₄ v7) ∗
        ((sp - 112#64) ↦₆₄ v8) ∗ ((sp - 104#64) ↦₆₄ v9) ∗
        ((sp - 96#64) ↦₆₄ v10) ∗ ((sp - 88#64) ↦₆₄ v11) ∗
        ((sp - 80#64) ↦₆₄ v12) ∗ ((sp - 72#64) ↦₆₄ v13) ∗
        ((sp - 64#64) ↦₆₄ v14) ∗ ((sp - 56#64) ↦₆₄ v15) ∗
        ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗
        ((sp - 32#64) ↦₆₄ v18) ∗ ((sp - 24#64) ↦₆₄ v19) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v21)) := by
    cells_unfold
  rw [h1, h2, hc22, ← sepConj_assoc]

theorem fold_memRegion_32_sub128 (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 128#64) ↦₆₄ v0) ∗ ((sp - 120#64) ↦₆₄ v1) ∗
    ((sp - 112#64) ↦₆₄ v2) ∗ ((sp - 104#64) ↦₆₄ v3) ⊢
    memRegion (sp - 128#64) 32 := by
  rw [memRegion_32_cells (sp - 128#64)]
  simp (config := { decide := true }) only [bv_sub_add_lit]
  refine Entails.sepExists_right v3 ?_
  refine Entails.sepExists_right v2 ?_
  refine Entails.sepExists_right v1 ?_
  refine Entails.sepExists_right v0 ?_
  exact Entails.refl _

theorem trace_eq_of_eq {s0 s sf : Arm64.State} (hs : s.trace = s0.trace)
    (h : allocFailedIn s sf ∧ s.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢
  rw [← hs]
  exact h

theorem elim_fwc_post {prog : Program} {ret : BitVec 64} {A : RustAlloc}
    {x : FallibleWithCapacityGhost} {s sf1 : Arm64.State} {F : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop}
    (h : ∀ (ctrl : BitVec 64),
      sf1.trace = s.trace →
      ctrl ≠ 0#64 → ctrl.toNat % 8 = 0 →
      4 * x.stride ≤ ctrl.toNat → ctrl.toNat + 12 < 2 ^ 64 →
      SepWPp prog ret sf1
        ((x.sret ↦₆₄ ctrl) ∗
         ((x.sret + 8#64) ↦₆₄ 3#64) ∗
         ((x.sret + 16#64) ↦₆₄ 3#64) ∗
         ((x.sret + 24#64) ↦₆₄ 0#64) ∗
         A.live (ctrl - BitVec.ofNat 64 (4 * x.stride)) (tableAllocSize 4 x.stride) (asm% hashbrownTableAlign) ∗
         (ctrl ↦ₛ emptyCtrl4) ∗
         arrayAt (fun _ a => memRegion a x.stride) x.stride
           (ctrl - BitVec.ofNat 64 (4 * x.stride)) (List.range 4).reverse ∗
         A.pool ∗ stackAt s.sp fallibleWithCapacityStack ∗ F) Q Qp) :
    SepWPp prog ret sf1 ((fallibleWithCapacity4Spec A).post x s sf1 ∗ F) Q Qp := by
  dsimp only [fallibleWithCapacity4Spec, rawTableInner4EmptyAt]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.pure_elim fun htr => ?_
  refine SepWPp.exists_elim fun ctrl => ?_
  refine SepWPp.pure_elim fun ⟨hc0, hc8, hcle, hclt⟩ => ?_
  exact h ctrl htr hc0 hc8 hcle hclt

theorem fold_table4EmptyAt (A : RustAlloc) (stride : Nat) (mp k0 k1 ctrl : BitVec 64)
    (hc0 : ctrl ≠ 0#64) (hc8 : ctrl.toNat % 8 = 0)
    (hcle : 4 * stride ≤ ctrl.toNat) (hclt : ctrl.toNat + 12 < 2 ^ 64) :
    ((mp ↦₆₄ ctrl) ∗
      ((mp + 8#64) ↦₆₄ 3#64) ∗
      ((mp + 16#64) ↦₆₄ 3#64) ∗
      ((mp + 24#64) ↦₆₄ 0#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗
      ((mp + 40#64) ↦₆₄ k1) ∗
      A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) (asm% hashbrownTableAlign) ∗
      (ctrl ↦ₛ emptyCtrl4) ∗
      arrayAt (fun _ a => memRegion a stride) stride
        (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse) ⊢
    table4EmptyAt A stride mp k0 k1 := by
  unfold table4EmptyAt table4At
  refine Entails.sepExists_right ctrl ?_
  have hlen : ([] : List Nat).length = 4 → (3#64 : BitVec 64) = 0#64 := by decide
  refine Entails.pure_right ⟨hc0, hc8, hcle, hclt, hlen, ctrlMirrorInv_emptyCtrl4, fullBucketsInv_emptyCtrl4⟩ ?_
  have h24 : mp + asm64% tableHasherOff + 8#64 = mp + 40#64 := by bv_lin
  have harr :
      arrayAt (fun i a => if i ∈ ([] : List Nat) then memRegion a stride else memRegion a stride)
        stride (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse =
      arrayAt (fun _ a => memRegion a stride)
        stride (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse := by
    simp
  rw [h24, harr]
  exact Entails.refl _

end ReserveRehash

open ReserveRehash

#arm64_check_no_rfl_state_lemmas

theorem reserveRehashIdentityEmpty_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashIdName)
      (reserveRehashIdentityEmptySpec A) := by
  simp only [reserveRehashIdentityEmptySpec, reserveRehashEmptySpec, emptyTableAt,
    stackAt_reserveRehash_id]
  have hfn : libsignalSessionCode.fnOff reserveRehashIdName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") := reserveRehashId_fnOff
  have hfwc : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashIdName + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
      (fallibleWithCapacity4Spec A) := by
    rw [← fallibleWithCapacity_fnAddr_of_id]
    exact fallibleWithCapacity4_ok b ext A hHooks
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>")) 552
  dsimp only [RebasedProg] at hfwc ⊢
  clear hfn hHooks
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr reserveRehashIdName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨base, mp, rsPtr, k0, k1⟩ := x
  dsimp only at *
  refine SepWPp.fold (fold_memRegion_32_sub128 s0.sp _ _ _ _) (by sep_focus) ?_
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (ret_pc := entry + bv% (116))
    (x := ⟨s0.sp - 128#64, identityBucketStride, 1⟩)
    (T := memRegion (s0.sp - 128#64) 32 ∗ A.pool ∗ stackAt (s0.sp - 160#64) fallibleWithCapacityStack)
    hfwc
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    (by dsimp only [fallibleWithCapacity4Spec]; congr 3)
    (by simp only [wp_norm, arm64_norm, *]; decide)
    (by sep_focus)
    (fun _ _ _ _ he => allowPanic_not_exited he)
    (fun sf _ hm => allowPanic_frame (trace_eq_of_eq (by simp only [wp_norm, arm64_norm, *])) hm)
    ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp1 hcs1
  rcases hcs1 with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  refine elim_fwc_post fun ctrl htr hc0 hc8 hcle hclt => ?_
  dsimp only at *
  simp only [trace_setPC_pre, wp_norm, arm64_norm] at htr
  have hctrl_beq : (ctrl == 0#64) = false := beq_eq_false_iff_ne.mpr hc0
  apply SepWPp.of_sepWP_ret
  wp_simp_pre only [bv_sub_add_lit, wp_norm, arm64_norm]
  wp_steps
  have hfold := fold_table4EmptyAt A identityBucketStride mp k0 k1 ctrl hc0 hc8 hcle hclt
  refine SepWP.fold hfold (by sep_focus) ?_
  wp_done

theorem reserveRehashSessionEmpty_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashSessionName)
      (reserveRehashSessionEmptySpec A) := by
  simp only [reserveRehashSessionEmptySpec, reserveRehashEmptySpec, emptyTableAt,
    stackAt_reserveRehash_sess]
  have hfn : libsignalSessionCode.fnOff reserveRehashSessionName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") := reserveRehashSession_fnOff
  have hfwc : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashSessionName + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
      (fallibleWithCapacity4Spec A) := by
    rw [← fallibleWithCapacity_fnAddr_of_sess]
    exact fallibleWithCapacity4_ok b ext A hHooks
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>")) 564
  dsimp only [RebasedProg] at hfwc ⊢
  clear hfn hHooks
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr reserveRehashSessionName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨base, mp, rsPtr, k0, k1⟩ := x
  dsimp only at *
  refine SepWPp.fold (fold_memRegion_32_sub128 s0.sp _ _ _ _) (by sep_focus) ?_
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (ret_pc := entry + bv% (116))
    (x := ⟨s0.sp - 128#64, sessionBucketStride, 1⟩)
    (T := memRegion (s0.sp - 128#64) 32 ∗ A.pool ∗ stackAt (s0.sp - 176#64) fallibleWithCapacityStack)
    hfwc
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    (by dsimp only [fallibleWithCapacity4Spec]; congr 3)
    (by simp only [wp_norm, arm64_norm, *]; decide)
    (by sep_focus)
    (fun _ _ _ _ he => allowPanic_not_exited he)
    (fun sf _ hm => allowPanic_frame (trace_eq_of_eq (by simp only [wp_norm, arm64_norm, *])) hm)
    ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp1 hcs1
  rcases hcs1 with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  refine elim_fwc_post fun ctrl htr hc0 hc8 hcle hclt => ?_
  dsimp only at *
  simp only [trace_setPC_pre, wp_norm, arm64_norm] at htr
  have hctrl_beq : (ctrl == 0#64) = false := beq_eq_false_iff_ne.mpr hc0
  apply SepWPp.of_sepWP_ret
  wp_simp_pre only [bv_sub_add_lit, wp_norm, arm64_norm]
  wp_steps
  have hfold := fold_table4EmptyAt A sessionBucketStride mp k0 k1 ctrl hc0 hc8 hcle hclt
  refine SepWP.fold hfold (by sep_focus) ?_
  wp_done

end CryptoVerification.E2E.InMem.HashbrownBin
