/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.DecodesIsTrusted
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.IsTrusted
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadDecodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreEmptyHelpers
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Empty-Table `InMemSessionStore` and `InMemIdentityKeyStore` Poll Closures

Proves `subroutine_ok` for the empty-table (`emptyTableAt`) fast paths of
`InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`) and
`InMemSessionStore::load_session::{closure#0}` (`0x08ce4`), together with
`get_identity_key_pair` (`0x2de88`, `0x07b34`), `get_local_registration_id` (`0x2ded4`, `0x07b7c`),
and unaligned 64-byte `KeyPair` repack helpers.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
open CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.IsTrusted
open CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_sp_storeEmpty (s : Arm64.State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) (m : Memory)
  (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

/-! ## 1. `is_trusted_identity::{closure#0}` (`0x079c4`) on `emptyTableAt` -/

/-- Ghost parameters for `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`)
on an empty table (`emptyTableAt`). -/
structure IsTrustedIdentityEmptyGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  qAddrPtr : BitVec 64
  qKeyPtr : BitVec 64
  direction : BitVec 8

/-- Specification of `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`)
on an empty table (`emptyTableAt base mp k0 k1`):
reads `items == 0` at `mp + 24`, branches at `0x7a04` (`cbz x8, 0x7adc`) directly to `mov w0, #1`,
writes `Ready(Ok(true))` (`pollBoolResultAt sret true`) and `[futPtr + 24] = 1#8`, and returns. -/
def isTrustedIdentityEmptySpec : Spec IsTrustedIdentityEmptyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      ((x.futPtr + 25#64) ↦₈ x.direction) ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      memRegion x.sret 48 ∗
      stackAt s.sp isTrustedIdentityClosureStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.qKeyPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      ((x.futPtr + 25#64) ↦₈ x.direction) ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      pollBoolResultAt x.sret true ∗
      stackAt s0.sp isTrustedIdentityClosureStack

theorem isTrustedIdentityEmpty_ok (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName)
      isTrustedIdentityEmptySpec := by
  simp only [isTrustedIdentityEmptySpec]
  have hfn : libsignalSessionCode.fnOff isTrustedIdentityClosureName = 0x079c4 :=
    isTrustedIdentityClosure_fnOff
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn 31172 368
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat]
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr isTrustedIdentityClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, base, mp, k0, k1, qAddrPtr, qKeyPtr, direction⟩ := x
  dsimp only at *
  wp_conv_pre => rw [emptyTableAt_eq]
  wp_conv_pre => rw [sret48_isTrusted_split_eq sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply IsTrusted.sepWP_exists_elim; intro _)
  wp_conv_pre => rw [stackAt_isTrusted_eq s0.sp]
  simp only [sepExists_sepConj_right]
  repeat' (apply IsTrusted.sepWP_exists_elim; intro _)
  wp_steps
  refine SepWP.fold (pollBoolResultAt_true_of_cells sret) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (emptyTableAt_eq base mp k0 k1).symm) (by sep_focus) ?_
  refine SepWP.fold (stackAt_isTrusted_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

/-! ## 2. `load_session::{closure#0}` (`0x08ce4`) on `emptyTableAt` -/

/-- Ghost parameters for `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`)
on an empty table (`emptyTableAt`). -/
structure LoadSessionEmptyGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  qAddrPtr : BitVec 64

/-- Specification of `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`)
on an empty table (`emptyTableAt base mp k0 k1`):
reads `items == 0` at `mp + 24`, branches at `0x8d24` (`cbz x8, 0x8e10`) directly to the
`None` return path (`0x8e98`), writes `Ready(Ok(None))` (`pollOptSessionRecordResultAt A sret none`)
and `[futPtr + 16] = 1#8`, and returns. -/
def loadSessionEmptySpec (A : RustAlloc) : Spec LoadSessionEmptyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 0#8) ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      memRegion x.sret 368 ∗
      stackAt s.sp loadSessionClosureStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 1#8) ∗
      emptyTableAt x.base x.mp x.k0 x.k1 ∗
      pollOptSessionRecordResultAt A x.sret none ∗
      stackAt s0.sp loadSessionClosureStack

theorem loadSessionEmpty_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName)
      (loadSessionEmptySpec A) := by
  have hMemcpyReg := memcpy_region_ok_at_loadSessionClosure b hHooks
  simp only [loadSessionEmptySpec]
  have hfn : libsignalSessionCode.fnOff loadSessionClosureName = 0x08ce4 :=
    libsignalSessionCode_fnOff_0x8ce4
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn 36068 512
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hMemcpyReg ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr loadSessionClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, base, mp, k0, k1, qAddrPtr⟩ := x
  dsimp only at *
  wp_conv_pre => rw [emptyTableAt_eq]
  wp_conv_pre => rw [LoadSingle.sret368_split_eq sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply LoadSingle.sepWP_exists_elim; intro c_sret0
  wp_conv_pre => rw [LoadSingle.stackAt_load_eq s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply LoadSingle.sepWP_exists_elim; intro _)
  refine step_stpSimd64_sp_pre (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_sep_access_fast) (by wp_sep_access_fast) fun _ => ?_
  wp_norm_state
  wp_steps
  wp_conv_pre => rw [LoadSingle.stackAt_load_sub_eq (s0.sp - 1200#64) 4096 (by decide),
    memRegion_eq_exists_bytes (s0.sp - 1184#64) 360 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply LoadSingle.sepWP_exists_elim; intro bs_uninit
  refine LoadSingle.sepWP_extract_pure (P := bs_uninit.length =
    360) (by sep_focus) fun hbs_uninit => ?_
  wp_call hMemcpyReg (sret + 8#64, s0.sp - 1184#64, bs_uninit)
  refine SepWP.fold (Entails.of_eq (LoadSingle.stackAt_load_sub_eq (s0.sp - 1200#64) 4096
    (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (sret + 8#64) bs_uninit)
    (by sep_focus) ?_
  refine SepWP.fold (hbs_uninit ▸ pointsToBytes_entails_memRegion (s0.sp - 1184#64) bs_uninit)
    (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (LoadSingle.pollOptSessionRecordResultAt_none_of_parts A sret)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (emptyTableAt_eq base mp k0 k1).symm)
    (by sep_focus) ?_
  refine SepWP.fold (LoadSingle.stackAt_load_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  wp_done

/-! ## 3. `get_identity_key_pair` (`0x2de88`, `0x07b34`) & `get_local_registration_id`
(`0x2ded4`, `0x07b7c`) -/

open ProofLib.ProgramReflection
open CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

abbrev getIdentityKeyPairClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::\
    storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"

abbrev getLocalRegistrationIdClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::\
    storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"

theorem getIdentityKeyPairClosure_fnOff :
    libsignalSessionCode.fnOff getIdentityKeyPairClosureName = 0x07b34 :=
  libsignalSessionCode_fnOff_0x7b34

theorem getLocalRegistrationIdClosure_fnOff :
    libsignalSessionCode.fnOff getLocalRegistrationIdClosureName = 0x07b7c :=
  libsignalSessionCode_fnOff_0x7b7c

gen_decodes libsignalSessionCode_tree storeEmpty [0x2df6c → 0x2e004]
gen_decodes libsignalSessionCode_tree storeEmpty [0x7b34 → 0x7b68]
gen_decodes libsignalSessionCode_tree storeEmpty [0x7b7c → 0x7ba4]

/-- 16-byte boxed future for `get_identity_key_pair` and `get_local_registration_id`:
`[self, state : u8, 7 uninitialized bytes]`. -/
def inMemId16BoxAt (box self : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₈ st) ∗ memRegion (box + 9#64) 7

theorem inMemId16BoxAt_memRegion (box self : BitVec 64) (st : BitVec 8) :
    inMemId16BoxAt box self st ⊢ memRegion box 16 := by
  unfold inMemId16BoxAt
  rw [show (16 : Nat) = 8 + (1 + 7) from rfl,
    memRegion_split box 8 8 (by decide),
    memRegion_split (box + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

private theorem memRegion_16_id_box (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₈ b0) ∗ memRegion (p + 9#64) 7) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Stack budget for `get_identity_key_pair` and `get_local_registration_id` shims
(`allocHookStack + 32`). -/
abbrev inMemId16ShimStack : Nat := allocHookStack + 32

private theorem stackAt_inMemId16Shim (sp : BitVec 64) :
    stackAt sp inMemId16ShimStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem fnAddr_tripleRatchetProgAt_storeEmpty_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (Arm64.State → Arm64.State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (trTrapProgAt b C abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, h]

private theorem fnAddr_tripleRatchetProgAt_storeEmpty {b : BitVec 64} {C : Crypto} {ctl : BitVec
  64} 
    {abs : String → Option (Arm64.State → Arm64.State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name = b + BitVec.ofNat 64 off := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact fnAddr_tripleRatchetProgAt_storeEmpty_trap h

private theorem sepWPp_pure_mid_storeEmpty {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {A B C : SepProp} {φ : Prop} {Q Qp : Arm64.State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem idKp_shim_adrp {b : BitVec 64} {H : String → Option (Arm64.State → Arm64.State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr getIdentityKeyPairShimName + 36#64) &&&
      0xfffffffffffff000#64) = b + 0x2d000#64 := by
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x2df6c, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem regId_shim_adrp {b : BitVec 64} {H : String → Option (Arm64.State → Arm64.State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr getLocalRegistrationIdShimName + 36#64) &&&
      0xfffffffffffff000#64) = b + 0x2d000#64 := by
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x2dfb8, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

/-- Specification of `<InMemIdentityKeyStore as IdentityKeyStore>::get_identity_key_pair`
(`0x2de88`). -/
def getIdentityKeyPairShimSpec (A : RustAlloc) (b : BitVec 64) : Spec (BitVec 64) :=
  ({ pre := fun self s =>
      ⌜s.readReg64 .x0 = self⌝ ∗
        A.pool ∗ stackAt s.sp inMemId16ShimStack
     post := fun self s0 sf =>
      (∃∗ box : BitVec 64,
        ⌜sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = b + bv% (ls_reloc% 0x7b34 - 24) ∧ sf.trace = s0.trace⌝ ∗
        A.live box 16 8 ∗ inMemId16BoxAt box self 0#8 ∗
        A.pool ∗ stackAt s0.sp inMemId16ShimStack) } : Spec (BitVec 64)).allowPanicWhen
    (fun _ s0 sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)

/-- Specification of `<InMemIdentityKeyStore as IdentityKeyStore>::get_local_registration_id`
(`0x2ded4`). -/
def getLocalRegIdShimSpec (A : RustAlloc) (b : BitVec 64) : Spec (BitVec 64) :=
  ({ pre := fun self s =>
      ⌜s.readReg64 .x0 = self⌝ ∗
        A.pool ∗ stackAt s.sp inMemId16ShimStack
     post := fun self s0 sf =>
      (∃∗ box : BitVec 64,
        ⌜sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = b + bv% (ls_reloc% 0x7b7c - 24) ∧ sf.trace = s0.trace⌝ ∗
        A.live box 16 8 ∗ inMemId16BoxAt box self 0#8 ∗
        A.pool ∗ stackAt s0.sp inMemId16ShimStack) } : Spec (BitVec 64)).allowPanicWhen
    (fun _ s0 sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)

set_option maxHeartbeats 1200000 in
theorem getIdentityKeyPairShim_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (Arm64.State → Arm64.State)}
    (hA : AllocHooks A abs)
    (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (trTrapProgAt b C abs)
      (b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
      (getIdentityKeyPairShimSpec A b) := by
  have hfn : libsignalSessionCode.fnOff getIdentityKeyPairShimName =
      num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") :=
    getIdentityKeyPairShim_fnOff
  change subroutine_ok (trTrapProgAt b C abs)
    (b + BitVec.ofNat 64 (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")))
    (getIdentityKeyPairShimSpec A b)
  rw [← fnAddr_tripleRatchetProgAt_storeEmpty_trap (b := b) (C := C) (abs := abs) hfn]
  simp only [getIdentityKeyPairShimSpec, inMemId16BoxAt, inMemId16ShimStack, stackAt_inMemId16Shim]
  cells_unfold
  have hAc := AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA
  have hshim := shim_ok_at2_ext hAc
    (name := getIdentityKeyPairShimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext hAc
    (name := getIdentityKeyPairShimName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  clear hAc
  dsimp only [tripleRatchetProgAtExt] at hshim halloc
  have hpanic : (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr getIdentityKeyPairShimName + BitVec.ofNat 64
        (num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))) =
      some Rust.panicked :=
    panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") hfn
      (show _ = num% (ls_off% "alloc::alloc::handle_alloc_error") from rfl)
      (by decide)
      (fun H => (ls_hook% "alloc::alloc::handle_alloc_error") H)
      (by simp [Rust.isPanicSymbol])
  code_fetches CryptoVerification.libsignalSessionCode storeEmpty b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") 76
  wpp_init self s0
  have hadrp := idKp_shim_adrp (H := Rust.withPanics (trTrapExterns C abs)) hb
  examples_generalize_entry
  examples_hide_fetches
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (16, 8)
  apply SepWP.done (by simp_all) (by simp_all)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_storeEmpty fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_id_box, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_storeEmpty fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

set_option maxHeartbeats 1600000 in
theorem getIdentityKeyPairShim_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} 
    {abs : String → Option (Arm64.State → Arm64.State)}
    (hA : AllocHooks A abs)
    (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + 0x2df6c#64)
      (getIdentityKeyPairShimSpec A b) :=
  subroutine_ok_kit_of_trTrap (getIdentityKeyPairShim_ok_trap hA hb)

set_option maxHeartbeats 1200000 in
theorem getLocalRegIdShim_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (Arm64.State → Arm64.State)}
    (hA : AllocHooks A abs)
    (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (trTrapProgAt b C abs)
      (b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
      (getLocalRegIdShimSpec A b) := by
  have hfn : libsignalSessionCode.fnOff getLocalRegistrationIdShimName =
      num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") :=
    getLocalRegistrationIdShim_fnOff
  change subroutine_ok (trTrapProgAt b C abs)
    (b + BitVec.ofNat 64 (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")))
    (getLocalRegIdShimSpec A b)
  rw [← fnAddr_tripleRatchetProgAt_storeEmpty_trap (b := b) (C := C) (abs := abs) hfn]
  simp only [getLocalRegIdShimSpec, inMemId16BoxAt, inMemId16ShimStack, stackAt_inMemId16Shim]
  cells_unfold
  have hAc := AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA
  have hshim := shim_ok_at2_ext hAc
    (name := getLocalRegistrationIdShimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext hAc
    (name := getLocalRegistrationIdShimName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  clear hAc
  dsimp only [tripleRatchetProgAtExt] at hshim halloc
  have hpanic : (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr getLocalRegistrationIdShimName + BitVec.ofNat 64
        (num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))) =
      some Rust.panicked :=
    panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") hfn
      (show _ = num% (ls_off% "alloc::alloc::handle_alloc_error") from rfl)
      (by decide)
      (fun H => (ls_hook% "alloc::alloc::handle_alloc_error") H)
      (by simp [Rust.isPanicSymbol])
  code_fetches CryptoVerification.libsignalSessionCode storeEmpty b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") 76
  wpp_init self s0
  have hadrp := regId_shim_adrp (H := Rust.withPanics (trTrapExterns C abs)) hb
  examples_generalize_entry
  examples_hide_fetches
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (16, 8)
  apply SepWP.done (by simp_all) (by simp_all)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_storeEmpty fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_id_box, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_storeEmpty fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

set_option maxHeartbeats 1600000 in
theorem getLocalRegIdShim_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} 
    {abs : String → Option (Arm64.State → Arm64.State)}
    (hA : AllocHooks A abs)
    (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + 0x2dfb8#64)
      (getLocalRegIdShimSpec A b) :=
  subroutine_ok_kit_of_trTrap (getLocalRegIdShim_ok_trap hA hb)

structure GetIdentityKeyPairPollGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  self : BitVec 64
  ik0 : BitVec 64
  ik1 : BitVec 64
  ik2 : BitVec 64
  ik3 : BitVec 64
  ik4 : BitVec 64
  ik5 : BitVec 64
  ik6 : BitVec 64
  ik7 : BitVec 64
  b_sret0 : BitVec 8
  u0 : BitVec 64
  u1 : BitVec 64
  u2 : BitVec 64
  u3 : BitVec 64
  u4 : BitVec 64
  u5 : BitVec 64
  u6 : BitVec 64
  u7 : BitVec 64

/-- Specification of `<InMemIdentityKeyStore as
IdentityKeyStore>::get_identity_key_pair::{closure#0}` (`0x07b34`). -/
def getIdentityKeyPairPollSpec : Spec GetIdentityKeyPairPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 0#8) ∗
      ((x.self + 0x30#64) ↦₆₄ x.ik0) ∗ ((x.self + 0x38#64) ↦₆₄ x.ik1) ∗
      ((x.self + 0x40#64) ↦₆₄ x.ik2) ∗ ((x.self + 0x48#64) ↦₆₄ x.ik3) ∗
      ((x.self + 0x50#64) ↦₆₄ x.ik4) ∗ ((x.self + 0x58#64) ↦₆₄ x.ik5) ∗
      ((x.self + 0x60#64) ↦₆₄ x.ik6) ∗ ((x.self + 0x68#64) ↦₆₄ x.ik7) ∗
      (x.sret ↦₈ x.b_sret0) ∗
      ((x.sret + 0x01#64) ↦₆₄ x.u0) ∗ ((x.sret + 0x09#64) ↦₆₄ x.u1) ∗
      ((x.sret + 0x11#64) ↦₆₄ x.u2) ∗ ((x.sret + 0x19#64) ↦₆₄ x.u3) ∗
      ((x.sret + 0x21#64) ↦₆₄ x.u4) ∗ ((x.sret + 0x29#64) ↦₆₄ x.u5) ∗
      ((x.sret + 0x31#64) ↦₆₄ x.u6) ∗ ((x.sret + 0x39#64) ↦₆₄ x.u7)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 1#8) ∗
      ((x.self + 0x30#64) ↦₆₄ x.ik0) ∗ ((x.self + 0x38#64) ↦₆₄ x.ik1) ∗
      ((x.self + 0x40#64) ↦₆₄ x.ik2) ∗ ((x.self + 0x48#64) ↦₆₄ x.ik3) ∗
      ((x.self + 0x50#64) ↦₆₄ x.ik4) ∗ ((x.self + 0x58#64) ↦₆₄ x.ik5) ∗
      ((x.self + 0x60#64) ↦₆₄ x.ik6) ∗ ((x.self + 0x68#64) ↦₆₄ x.ik7) ∗
      (x.sret ↦₈ 0#8) ∗
      ((x.sret + 0x01#64) ↦₆₄ x.ik0) ∗ ((x.sret + 0x09#64) ↦₆₄ x.ik1) ∗
      ((x.sret + 0x11#64) ↦₆₄ x.ik2) ∗ ((x.sret + 0x19#64) ↦₆₄ x.ik3) ∗
      ((x.sret + 0x21#64) ↦₆₄ x.ik4) ∗ ((x.sret + 0x29#64) ↦₆₄ x.ik5) ∗
      ((x.sret + 0x31#64) ↦₆₄ x.ik6) ∗ ((x.sret + 0x39#64) ↦₆₄ x.ik7)

theorem getIdentityKeyPairPoll_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (Arm64.State → Arm64.State)} :
    subroutine_ok (trTrapProgAt b C abs)
      (b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"))
      getIdentityKeyPairPollSpec := by
  have hfn : libsignalSessionCode.fnOff getIdentityKeyPairClosureName =
      num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") :=
    getIdentityKeyPairClosure_fnOff
  change subroutine_ok (trTrapProgAt b C abs)
    (b + BitVec.ofNat 64 (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")))
    getIdentityKeyPairPollSpec
  rw [← fnAddr_tripleRatchetProgAt_storeEmpty_trap (b := b) (C := C) (abs := abs) hfn]
  simp only [getIdentityKeyPairPollSpec]
  code_fetches CryptoVerification.libsignalSessionCode storeEmpty b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") 52
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨futPtr, sret, self, ik0, ik1, ik2, ik3, ik4, ik5, ik6, ik7,
    b_sret0, u0, u1, u2, u3, u4, u5, u6, u7⟩ := x
  dsimp only at *
  wp_steps
  wp_done

theorem getIdentityKeyPairPoll_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} 
    {abs : String → Option (Arm64.State → Arm64.State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + 0x07b34#64)
      getIdentityKeyPairPollSpec :=
  subroutine_ok_kit_of_trTrap getIdentityKeyPairPoll_ok_trap

structure GetLocalRegIdPollGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  self : BitVec 64
  regId : BitVec 32
  u_sret0 : BitVec 64
  u_sret8 : BitVec 32

/-- Specification of `<InMemIdentityKeyStore as
IdentityKeyStore>::get_local_registration_id::{closure#0}` (`0x07b7c`). -/
def getLocalRegIdPollSpec : Spec GetLocalRegIdPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 0#8) ∗
      ((x.self + 0x70#64) ↦₃₂ x.regId) ∗
      (x.sret ↦₆₄ x.u_sret0) ∗ ((x.sret + 8#64) ↦₃₂ x.u_sret8)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 1#8) ∗
      ((x.self + 0x70#64) ↦₃₂ x.regId) ∗
      (x.sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((x.sret + 8#64) ↦₃₂ x.regId)

theorem getLocalRegIdPoll_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (Arm64.State → Arm64.State)} :
    subroutine_ok (trTrapProgAt b C abs)
      (b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"))
      getLocalRegIdPollSpec := by
  have hfn : libsignalSessionCode.fnOff getLocalRegistrationIdClosureName =
      num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") :=
    getLocalRegistrationIdClosure_fnOff
  change subroutine_ok (trTrapProgAt b C abs)
    (b + BitVec.ofNat 64 (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")))
    getLocalRegIdPollSpec
  rw [← fnAddr_tripleRatchetProgAt_storeEmpty_trap (b := b) (C := C) (abs := abs) hfn]
  simp only [getLocalRegIdPollSpec]
  code_fetches CryptoVerification.libsignalSessionCode storeEmpty b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") 40
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨futPtr, sret, self, regId, u_sret0, u_sret8⟩ := x
  dsimp only at *
  wp_steps
  wp_done

theorem getLocalRegIdPoll_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} 
    {abs : String → Option (Arm64.State → Arm64.State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + 0x07b7c#64)
      getLocalRegIdPollSpec :=
  subroutine_ok_kit_of_trTrap getLocalRegIdPoll_ok_trap

/-! ## 4. Unaligned 64-Byte `KeyPair` Repack Lemmas (`bytes7_byte_fold`, `bytes7_word_shift`) -/

/-- Pure std3 helper for byte extraction at offsets `8..56` of `y[0..56] ++ x[56..64]`. -/
private theorem extract56_8_hi (x y : BitVec 64) (k : Nat) (hk : 8 ≤ k) (hk2 : k + 8 ≤ 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' k 8 = y.extractLsb' (k - 8) 8 := by
  ext i hi
  have h1 : ¬ (k + i < 8) := by omega
  have h3 : k + i - 8 = k - 8 + i := by omega
  have hlt : k - 8 + i < 56 := by omega
  rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb', h1, ↓reduceIte, h3, hlt, decide_true, Bool.true_and,
    Nat.zero_add]

private theorem extract56_8_0 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', Nat.zero_add, BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb', hi, ↓reduceIte, decide_true, Bool.true_and]
private theorem extract56_8_8 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 8 8 = y.extractLsb' 0 8 :=
  extract56_8_hi x y 8 (by decide) (by decide)
private theorem extract56_8_16 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 16 8 = y.extractLsb' 8 8 :=
  extract56_8_hi x y 16 (by decide) (by decide)
private theorem extract56_8_24 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 24 8 = y.extractLsb' 16 8 :=
  extract56_8_hi x y 24 (by decide) (by decide)
private theorem extract56_8_32 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 32 8 = y.extractLsb' 24 8 :=
  extract56_8_hi x y 32 (by decide) (by decide)
private theorem extract56_8_40 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 40 8 = y.extractLsb' 32 8 :=
  extract56_8_hi x y 40 (by decide) (by decide)
private theorem extract56_8_48 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 48 8 = y.extractLsb' 40 8 :=
  extract56_8_hi x y 48 (by decide) (by decide)
private theorem extract56_8_56 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 56 8 = y.extractLsb' 48 8 :=
  extract56_8_hi x y 56 (by decide) (by decide)

theorem bytes7_byte_fold (a x : BitVec 64) :
    bytes7At a
      (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8)
      (x.extractLsb' 32 8) (x.extractLsb' 40 8) (x.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₈ (x.extractLsb' 56 8)) =
    (a ↦₆₄ x) := by
  simp only [bytes7At, pointsTo64, BitVec.add_zero, sepConj_assoc]

theorem bytes7_word_shift (a x y : BitVec 64) :
    bytes7At a
      (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8)
      (x.extractLsb' 32 8) (x.extractLsb' 40 8) (x.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (y.extractLsb' 0 56 ++ x.extractLsb' 56 8)) =
    (a ↦₆₄ x) ∗
    bytes7At (a + 0x08#64)
      (y.extractLsb' 0 8) (y.extractLsb' 8 8) (y.extractLsb' 16 8) (y.extractLsb' 24 8)
      (y.extractLsb' 32 8) (y.extractLsb' 40 8) (y.extractLsb' 48 8) := by
  simp only [bytes7At, pointsTo64,
    extract56_8_0, extract56_8_8, extract56_8_16, extract56_8_24,
    extract56_8_32, extract56_8_40, extract56_8_48, extract56_8_56,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem keyPair39_eq_words4_bytes7 (a ik0 ik1 ik2 ik3 ik4 : BitVec 64) :
    bytes7At a
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
    ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
    ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
    ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
    (a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
    bytes7At (a + 0x20#64)
      (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
      (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
  have h1 := bytes7_word_shift a ik0 ik1
  have h2 := bytes7_word_shift (a + 0x08#64) ik1 ik2
  have h3 := bytes7_word_shift (a + 0x10#64) ik2 ik3
  have h4 := bytes7_word_shift (a + 0x18#64) ik3 ik4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (a + 8#64) _ _ _ _ _ _ _), h2, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (a + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc]
  rw [h4]

theorem keyPair32Hi_eq_words4 (b ik4 ik5 ik6 ik7 : BitVec 64) :
    bytes7At b
      (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
      (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
    ((b + 0x07#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
    ((b + 0x0f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
    ((b + 0x17#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
    ((b + 0x1f#64) ↦₈ (ik7.extractLsb' 56 8)) =
    (b ↦₆₄ ik4) ∗ ((b + 0x08#64) ↦₆₄ ik5) ∗ ((b + 0x10#64) ↦₆₄ ik6) ∗ ((b + 0x18#64) ↦₆₄ ik7) := by
  have h1 := bytes7_word_shift b ik4 ik5
  have h2 := bytes7_word_shift (b + 0x08#64) ik5 ik6
  have h3 := bytes7_word_shift (b + 0x10#64) ik6 ik7
  have h4 := bytes7_byte_fold (b + 0x18#64) ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (b + 8#64) _ _ _ _ _ _ _), h2, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (b + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc]
  rw [h4]

theorem words8_eq_keyPair64UnalignedAt (a ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 : BitVec 64) :
    ((a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
     ((a + 0x20#64) ↦₆₄ ik4) ∗ ((a + 0x28#64) ↦₆₄ ik5) ∗ ((a + 0x30#64) ↦₆₄ ik6) ∗
       ((a + 0x38#64) ↦₆₄ ik7)) =
    keyPair64UnalignedAt a
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)
      (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
      (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
      (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
      (ik7.extractLsb' 56 8) := by
  have hlo := keyPair39_eq_words4_bytes7 a ik0 ik1 ik2 ik3 ik4
  have hhi := keyPair32Hi_eq_words4 (a + 0x20#64) ik4 ik5 ik6 ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhi
  unfold keyPair64UnalignedAt
  rw [← hhi]
  symm
  calc _ = (bytes7At a
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
    ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
    ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
    ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8))) ∗
    (((a + 0x27#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
    ((a + 0x2f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
    ((a + 0x37#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
    ((a + 0x3f#64) ↦₈ (ik7.extractLsb' 56 8))) := by ac_rfl
    _ = _ := by rw [hlo]; ac_rfl

end CryptoVerification.E2E.Pqxdh.ResponderClosure
