/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp

/-!
# `OneKeyStore` Trait Methods, Drop Glues, and Vtable Guards

Proves `subroutine_ok` contracts on `tripleRatchetProgAt` for the `OneKeyStore` trait methods,
store drop glues, and `.data.rel.ro` vtable guards in `libsignalSessionCode_tree`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_oks (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_oks (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_oks (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_oks (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_oks (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_oks (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_oks (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_oks (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth)
  (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := rfl

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3e2c4
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "alloc::alloc::handle_alloc_error")
  (ls_hook% "alloc::alloc::handle_alloc_error")

theorem panic_at_handle_alloc_error2_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_alloc_error_trap b C abs name k hk

theorem panic_at_handle_alloc_error2 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_alloc_error b C ctl abs name k hk

macro "responder_fetches " b:term:max H:term:max hfn:ident
    off:num len:num : tactic =>
  `(tactic| responder_fetches_from $b $H $hfn $off 0 $len)

/-! ## Symbol Names, Vtable Guards, and Helper Lemmas -/

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def dropOneKeyFutName : String :=
  "core::ptr::drop_glue::<<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::\
    storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}>"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def dropOneKeyStoreName : String :=
  "core::ptr::drop_glue::<libsignal_pqxdh_e2e::OneKeyStore>"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def dropStringLocal4Name : String :=
  "core::ptr::drop_glue::<alloc::string::String> [local#7]"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def dropInMemSessionStoreName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::storage::inmem::InMemSessionStore> [local#2]"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def dropInMemIdentityStoreName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::storage::inmem::InMemIdentityKeyStore> [local#2]"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyGetSpkName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    SignedPreKeyStore>::get_signed_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeySaveSpkName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    SignedPreKeyStore>::save_signed_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyGetKyberName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    KyberPreKeyStore>::get_kyber_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeySaveKyberName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    KyberPreKeyStore>::save_kyber_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyMarkKyberName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    KyberPreKeyStore>::mark_kyber_pre_key_used"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyGetPreKeyName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::PreKeyStore>::\
    get_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeySavePreKeyName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::PreKeyStore>::\
    save_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyRemovePreKeyName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::PreKeyStore>::\
    remove_pre_key"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def spkRecordCloneName : String :=
  "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as core::clone::\
    Clone>::clone [local#2]"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyGetSpkClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    SignedPreKeyStore>::get_signed_pre_key::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeySaveSpkClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    SignedPreKeyStore>::save_signed_pre_key::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyGetKyberClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeySaveKyberClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    KyberPreKeyStore>::save_kyber_pre_key::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyMarkKyberClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::\
    KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyGetPreKeyClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::PreKeyStore>::\
    get_pre_key::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeySavePreKeyClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::PreKeyStore>::\
    save_pre_key::{closure#0}"

@[local simp, local arm64_norm ↓, local wp_norm ↓]
def oneKeyRemovePreKeyClosureName : String :=
  "<libsignal_pqxdh_e2e::OneKeyStore as libsignal_protocol::storage::traits::PreKeyStore>::\
    remove_pre_key::{closure#0}"

/-- Trivial no-op `drop_in_place` contract for boxed store futures (`0x70c20`). -/
def oneKeyFutNoopDropSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

@[local arm64_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo :=
  BitVec.extractLsb'_append_eq_right

@[local arm64_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi :=
  BitVec.extractLsb'_append_eq_left

@[local simp, local wp_norm, local arm64_norm]
theorem hi32_append_lo32 (x : BitVec 64) :
    (x.ushiftRight 32).setWidth 32 ++ x.setWidth 32 = x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.ushiftRight_eq, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 32
  · simp only [h, ↓reduceIte, decide_true, Bool.true_and]
  · have hsub : i - 32 < 32 := by omega
    have hadd : 32 + (i - 32) = i := by omega
    simp only [h, ↓reduceIte, hsub, decide_true, Bool.true_and, hadd]

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_adds64_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_adds64_pos_1 {c : BitVec 64} (hc : c ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have h2 := congrArg (· - 1#64) heq
  rw [BitVec.add_sub_cancel] at h2
  exact hc h2

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs32_self (w : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 w w) = false := by
  rw [conditionHolds_ne_subsPState32]
  simp only [bne_self_eq_false]

def satIncU8 (c : BitVec 8) : BitVec 8 :=
  if c == 0xff#8 then 0xff#8 else c + 1#8

@[local simp, local wp_norm, local arm64_norm]
theorem csinc_satIncU8_norm (c : BitVec 8) :
    (if (255#32).ule (BitVec.zeroExtend 32 c + 1#32) = true then 255#8
     else BitVec.zeroExtend 8 (BitVec.zeroExtend 64 c + 1#64)) = satIncU8 c := by
  simp only [satIncU8]
  bv_bits

/-- Repack 5 consecutive 64-bit words at `p + 0x10 .. p + 0x38` into:
`↦₃₂` at `+0x10`, four `↦₆₄` words at `+0x14`, `+0x1c`, `+0x24`, `+0x2c` (two unaligned `Q128`
pairs),
and `↦₃₂` at `+0x34`. -/
theorem words5_repack_w32_4w64_w32 (p w2 w3 w4 w5 w6 : BitVec 64) :
    ((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
        ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6) =
      ((p + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((p + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((p + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((p + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((p + 0x2c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((p + 0x34#64) ↦₃₂ w6.extractLsb' 32 32) := by
  rw [← pointsTo32_pair (p + 0x14#64), ← pointsTo32_pair (p + 0x1c#64),
      ← pointsTo32_pair (p + 0x24#64), ← pointsTo32_pair (p + 0x2c#64)]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem subroutine_ok_rel_call {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {callee caller : String} {calleeOff callerOff : Nat} {k : Int} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr callee) spec)
    (hcallee : libsignalSessionCode.fnOff callee = calleeOff)
    (hcaller : libsignalSessionCode.fnOff caller = callerOff)
    (hk : BitVec.ofNat 64 callerOff + BitVec.ofInt 64 k = BitVec.ofNat 64 calleeOff) :
    subroutine_ok
      (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      ((libsignalSessionCode.rebase b
          (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr caller +
        BitVec.ofInt 64 k)
      spec := by
  dsimp only [tripleRatchetProgAt] at h
  have haddr :
      (libsignalSessionCode.rebase b
          (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr caller +
        BitVec.ofInt 64 k =
      (libsignalSessionCode.rebase b
          (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr callee := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee, BitVec.add_assoc, hk]
  rwa [haddr]

/-! ## Drop Glues (`0x70c20`, `0x70cf0`, `0x70ed4`, `0x71068`, `0x70c24`) -/

/-- Spec for `drop_glue::<alloc::string::String> [local#4]` (`0x70cf0`, 6 insns) on an empty
`String`. -/
def dropStringEmptySpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ptr) s =>
    ⌜s.readReg64 .x0 = p⌝ ∗
    stackAt s.sp 0 ∗
    (p ↦₆₄ 0#64) ∗
    ((p + 8#64) ↦₆₄ ptr)
  post := fun (p, ptr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    stackAt s0.sp 0 ∗
    (p ↦₆₄ 0#64) ∗
    ((p + 8#64) ↦₆₄ ptr)

/-- Spec for `drop_glue::<alloc::string::String> [local#4]` (`0x70cf0`, 6 insns) on a non-empty
`String`. -/
def dropStringNonemptySpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (p, ptr, cap) s =>
    ⌜BitVec.ofNat 64 cap ≠ 0#64 ∧ cap < 2 ^ 64 ∧ s.readReg64 .x0 = p⌝ ∗
    stackAt s.sp allocHookStack ∗
    A.pool ∗
    A.live ptr cap 1 ∗
    memRegion ptr cap ∗
    (p ↦₆₄ BitVec.ofNat 64 cap) ∗
    ((p + 8#64) ↦₆₄ ptr)
  post := fun (p, ptr, cap) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    stackAt s0.sp allocHookStack ∗
    A.pool ∗
    (p ↦₆₄ BitVec.ofNat 64 cap) ∗
    ((p + 8#64) ↦₆₄ ptr)

private theorem stackAt_112_cells (sp : BitVec 64) :
    stackAt sp 112 = cells (sp - 112#64) 14 := by
  unfold stackAt
  exact ProofLib.memRegion_cells (sp - 112#64) 14 (by decide)

/-- Spec for `drop_glue::<InMemSessionStore> [local#2]` (`0x70ed4`, 101 insns) when `bucket_mask
= 0`. -/
def dropInMemSessionStoreEmptySpec : Spec (BitVec 64) where
  pre := fun p s =>
    ⌜s.readReg64 .x0 = p⌝ ∗
    stackAt s.sp 112 ∗
    ((p + 8#64) ↦₆₄ 0#64)
  post := fun p s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    stackAt s0.sp 112 ∗
    ((p + 8#64) ↦₆₄ 0#64)

private theorem stackAt_64_cells (sp : BitVec 64) :
    stackAt sp 64 = cells (sp - 64#64) 8 := by
  unfold stackAt
  exact ProofLib.memRegion_cells (sp - 64#64) 8 (by decide)

/-- Spec for `drop_glue::<InMemIdentityKeyStore> [local#2]` (`0x71068`, 57 insns) when
`bucket_mask = 0`. -/
def dropInMemIdentityStoreEmptySpec : Spec (BitVec 64) where
  pre := fun p s =>
    ⌜s.readReg64 .x0 = p⌝ ∗
    stackAt s.sp 64 ∗
    ((p + 8#64) ↦₆₄ 0#64)
  post := fun p s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    stackAt s0.sp 64 ∗
    ((p + 8#64) ↦₆₄ 0#64)

structure DropOneKeyStoreNoneArgs where
  p : BitVec 64
  spkPubPtr : BitVec 64
  spkPubCap : Nat
  spkPrivPtr : BitVec 64
  spkPrivCap : Nat
  spkSigPtr : BitVec 64
  kpkPubPtr : BitVec 64
  kpkPubCap : Nat
  kpkPrivPtr : BitVec 64
  kpkPrivCap : Nat
  kpkSigPtr : BitVec 64

/-- Spec for `drop_glue::<OneKeyStore>` (`0x70c24`) when `one_time = None` (`[p + 0xb0] = -1`). -/
def dropOneKeyStoreNoneSpec (A : RustAlloc) : Spec DropOneKeyStoreNoneArgs where
  pre := fun x s =>
    ⌜BitVec.ofNat 64 x.spkPubCap ≠ 0#64 ∧ x.spkPubCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.spkPrivCap ≠ 0#64 ∧ x.spkPrivCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.kpkPubCap ≠ 0#64 ∧ x.kpkPubCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.kpkPrivCap ≠ 0#64 ∧ x.kpkPrivCap < 2 ^ 64 ∧
      s.readReg64 .x0 = x.p⌝ ∗
    stackAt s.sp (32 + allocHookStack) ∗
    A.pool ∗
    A.live x.spkPubPtr x.spkPubCap 1 ∗ memRegion x.spkPubPtr x.spkPubCap ∗
    A.live x.spkPrivPtr x.spkPrivCap 1 ∗ memRegion x.spkPrivPtr x.spkPrivCap ∗
    A.live x.kpkPubPtr x.kpkPubCap 1 ∗ memRegion x.kpkPubPtr x.kpkPubCap ∗
    A.live x.kpkPrivPtr x.kpkPrivCap 1 ∗ memRegion x.kpkPrivPtr x.kpkPrivCap ∗
    (x.p ↦₆₄ BitVec.ofNat 64 x.spkPubCap) ∗
    ((x.p + 0x08#64) ↦₆₄ x.spkPubPtr) ∗
    ((x.p + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.spkPrivCap) ∗
    ((x.p + 0x20#64) ↦₆₄ x.spkPrivPtr) ∗
    ((x.p + 0x30#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x38#64) ↦₆₄ x.spkSigPtr) ∗
    ((x.p + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.kpkPubCap) ∗
    ((x.p + 0x60#64) ↦₆₄ x.kpkPubPtr) ∗
    ((x.p + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.kpkPrivCap) ∗
    ((x.p + 0x78#64) ↦₆₄ x.kpkPrivPtr) ∗
    ((x.p + 0x88#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x90#64) ↦₆₄ x.kpkSigPtr) ∗
    ((x.p + 0xb0#64) ↦₆₄ 0xffffffffffffffff#64)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    stackAt s0.sp (32 + allocHookStack) ∗
    A.pool ∗
    (x.p ↦₆₄ BitVec.ofNat 64 x.spkPubCap) ∗
    ((x.p + 0x08#64) ↦₆₄ x.spkPubPtr) ∗
    ((x.p + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.spkPrivCap) ∗
    ((x.p + 0x20#64) ↦₆₄ x.spkPrivPtr) ∗
    ((x.p + 0x30#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x38#64) ↦₆₄ x.spkSigPtr) ∗
    ((x.p + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.kpkPubCap) ∗
    ((x.p + 0x60#64) ↦₆₄ x.kpkPubPtr) ∗
    ((x.p + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.kpkPrivCap) ∗
    ((x.p + 0x78#64) ↦₆₄ x.kpkPrivPtr) ∗
    ((x.p + 0x88#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x90#64) ↦₆₄ x.kpkSigPtr) ∗
    ((x.p + 0xb0#64) ↦₆₄ 0xffffffffffffffff#64)

private theorem stackAt_dropOneKeyStore (sp : BitVec 64) :
    stackAt sp (32 + allocHookStack) =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp 4096 4 (by decide)

structure DropOneKeyStoreSomeArgs where
  p : BitVec 64
  spkPubPtr : BitVec 64
  spkPubCap : Nat
  spkPrivPtr : BitVec 64
  spkPrivCap : Nat
  spkSigPtr : BitVec 64
  kpkPubPtr : BitVec 64
  kpkPubCap : Nat
  kpkPrivPtr : BitVec 64
  kpkPrivCap : Nat
  kpkSigPtr : BitVec 64
  opkPubPtr : BitVec 64
  opkPubCap : Nat
  opkPrivPtr : BitVec 64
  opkPrivCap : Nat

def dropOneKeyStoreSomeSpec (A : RustAlloc) : Spec DropOneKeyStoreSomeArgs where
  pre := fun x s =>
    ⌜BitVec.ofNat 64 x.spkPubCap ≠ 0#64 ∧ x.spkPubCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.spkPrivCap ≠ 0#64 ∧ x.spkPrivCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.kpkPubCap ≠ 0#64 ∧ x.kpkPubCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.kpkPrivCap ≠ 0#64 ∧ x.kpkPrivCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.opkPubCap ≠ 0#64 ∧ BitVec.ofNat 64 x.opkPubCap ≠ 0xffffffffffffffff#64 ∧
      x.opkPubCap < 2 ^ 64 ∧
      BitVec.ofNat 64 x.opkPrivCap ≠ 0#64 ∧ x.opkPrivCap < 2 ^ 64 ∧
      s.readReg64 .x0 = x.p⌝ ∗
    stackAt s.sp (32 + allocHookStack) ∗
    A.pool ∗
    A.live x.spkPubPtr x.spkPubCap 1 ∗ memRegion x.spkPubPtr x.spkPubCap ∗
    A.live x.spkPrivPtr x.spkPrivCap 1 ∗ memRegion x.spkPrivPtr x.spkPrivCap ∗
    A.live x.kpkPubPtr x.kpkPubCap 1 ∗ memRegion x.kpkPubPtr x.kpkPubCap ∗
    A.live x.kpkPrivPtr x.kpkPrivCap 1 ∗ memRegion x.kpkPrivPtr x.kpkPrivCap ∗
    A.live x.opkPubPtr x.opkPubCap 1 ∗ memRegion x.opkPubPtr x.opkPubCap ∗
    A.live x.opkPrivPtr x.opkPrivCap 1 ∗ memRegion x.opkPrivPtr x.opkPrivCap ∗
    (x.p ↦₆₄ BitVec.ofNat 64 x.spkPubCap) ∗
    ((x.p + 0x08#64) ↦₆₄ x.spkPubPtr) ∗
    ((x.p + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.spkPrivCap) ∗
    ((x.p + 0x20#64) ↦₆₄ x.spkPrivPtr) ∗
    ((x.p + 0x30#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x38#64) ↦₆₄ x.spkSigPtr) ∗
    ((x.p + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.kpkPubCap) ∗
    ((x.p + 0x60#64) ↦₆₄ x.kpkPubPtr) ∗
    ((x.p + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.kpkPrivCap) ∗
    ((x.p + 0x78#64) ↦₆₄ x.kpkPrivPtr) ∗
    ((x.p + 0x88#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x90#64) ↦₆₄ x.kpkSigPtr) ∗
    ((x.p + 0xb0#64) ↦₆₄ BitVec.ofNat 64 x.opkPubCap) ∗
    ((x.p + 0xb8#64) ↦₆₄ x.opkPubPtr) ∗
    ((x.p + 0xc8#64) ↦₆₄ BitVec.ofNat 64 x.opkPrivCap) ∗
    ((x.p + 0xd0#64) ↦₆₄ x.opkPrivPtr)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    memRegion (s0.sp - 4128#64) 32 ∗
    stackAt s0.sp allocHookStack ∗
    A.pool ∗
    (x.p ↦₆₄ BitVec.ofNat 64 x.spkPubCap) ∗
    ((x.p + 0x08#64) ↦₆₄ x.spkPubPtr) ∗
    ((x.p + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.spkPrivCap) ∗
    ((x.p + 0x20#64) ↦₆₄ x.spkPrivPtr) ∗
    ((x.p + 0x30#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x38#64) ↦₆₄ x.spkSigPtr) ∗
    ((x.p + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.kpkPubCap) ∗
    ((x.p + 0x60#64) ↦₆₄ x.kpkPubPtr) ∗
    ((x.p + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.kpkPrivCap) ∗
    ((x.p + 0x78#64) ↦₆₄ x.kpkPrivPtr) ∗
    ((x.p + 0x88#64) ↦₆₄ 0#64) ∗
    ((x.p + 0x90#64) ↦₆₄ x.kpkSigPtr) ∗
    ((x.p + 0xb0#64) ↦₆₄ BitVec.ofNat 64 x.opkPubCap) ∗
    ((x.p + 0xb8#64) ↦₆₄ x.opkPubPtr) ∗
    ((x.p + 0xc8#64) ↦₆₄ BitVec.ofNat 64 x.opkPrivCap) ∗
    ((x.p + 0xd0#64) ↦₆₄ x.opkPrivPtr)

/-! ## `OneKeyStore` Trait Methods (`0x76a30..0x76d2c`) -/

def oneKeyBox16At (a storePtr : BitVec 64) (id : BitVec 32) (state : BitVec 8) : SepProp :=
  (a ↦₆₄ storePtr) ∗ ((a + 8#64) ↦₃₂ id) ∗ ((a + 12#64) ↦₈ state) ∗ memRegion (a + 13#64) 3

private theorem memRegion_16_onekey_box (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ b12 : BitVec 8, ∃∗ u8 : BitVec 32, ∃∗ u0 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₃₂ u8) ∗ ((a + 12#64) ↦₈ b12) ∗ memRegion (a + 13#64) 3) := by
  rw [memRegion_split a 8 8 (by decide),
    memRegion_split (a + 8#64) 4 4 (by decide),
    memRegion_split (a + 8#64 + 4#64) 1 3 (by decide),
    ProofLib.memRegion_eight, memRegion_four, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem oneKeyBox16At_entails_memRegion (a storePtr : BitVec 64) (id : BitVec 32)
  (state : BitVec 8) :
    oneKeyBox16At a storePtr id state ⊢ memRegion a 16 := by
  unfold oneKeyBox16At
  rw [memRegion_16_onekey_box a]
  exact Entails.sepExists_right state
    (Entails.sepExists_right id
      (Entails.sepExists_right storePtr (Entails.refl _)))

def oneKeyMarkBox32At (a storePtr baseKeyPtr : BitVec 64)
    (kyberId spkId : BitVec 32) (state : BitVec 8) : SepProp :=
  (a ↦₆₄ storePtr) ∗ ((a + 8#64) ↦₆₄ baseKeyPtr) ∗
  ((a + 16#64) ↦₃₂ kyberId) ∗ ((a + 20#64) ↦₃₂ spkId) ∗
  ((a + 24#64) ↦₈ state) ∗ memRegion (a + 25#64) 7

private theorem memRegion_32_mark_box (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ b24 : BitVec 8, ∃∗ u20 : BitVec 32, ∃∗ u16 : BitVec 32, ∃∗ u8 : BitVec 64,
        ∃∗ u0 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗ ((a + 16#64) ↦₃₂ u16) ∗
        ((a + 20#64) ↦₃₂ u20) ∗ ((a + 24#64) ↦₈ b24) ∗ memRegion (a + 25#64) 7) := by
  rw [memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 4 12 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 4#64) 4 8 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 4#64 + 4#64) 1 7 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, memRegion_four, memRegion_four,
      memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem oneKeyMarkBox32At_entails_memRegion (a storePtr baseKeyPtr : BitVec 64)
    (kyberId spkId : BitVec 32) (state : BitVec 8) :
    oneKeyMarkBox32At a storePtr baseKeyPtr kyberId spkId state ⊢ memRegion a 32 := by
  unfold oneKeyMarkBox32At
  rw [memRegion_32_mark_box a]
  exact Entails.sepExists_right state
    (Entails.sepExists_right spkId
      (Entails.sepExists_right kyberId
        (Entails.sepExists_right baseKeyPtr
          (Entails.sepExists_right storePtr (Entails.refl _)))))

/-- Shared spec for the 7 16-byte-box `OneKeyStore` trait methods parameterized by `vtOff`. -/
def oneKeyTrait16Spec (A : RustAlloc) (b vtOff : BitVec 64) : Spec (BitVec 64 × BitVec 32) where
  pre := fun (storePtr, id) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧
      s.readReg64 .x0 = storePtr ∧
      (s.readReg64 .x1).setWidth 32 = id⌝ ∗
    stackAt s.sp (32 + allocHookStack) ∗
    A.pool
  post := fun (storePtr, id) s0 sf =>
    ∃∗ boxPtr : BitVec 64,
      ⌜sf.readReg64 .x0 = boxPtr ∧
        sf.readReg64 .x1 = b + vtOff ∧
        boxPtr ≠ 0#64 ∧
        boxPtr.toNat % 8 = 0 ∧
        sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (32 + allocHookStack) ∗
      A.pool ∗
      A.live boxPtr 16 8 ∗
      oneKeyBox16At boxPtr storePtr id 0#8
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem stackAt_markKyber (sp : BitVec 64) :
    stackAt sp (48 + allocHookStack) =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 4096 6 (by decide)

end CryptoVerification.E2E.Pqxdh.ResponderStore
