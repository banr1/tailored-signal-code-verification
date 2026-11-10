/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.OneKeyStoreBase
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::clone` and `OneKeyStore` Async Poll Closures

Proves `subroutine_ok` contracts on `tripleRatchetProgAt` for
`<SignedPreKeyRecordStructure as Clone>::clone` (`0x76f88`) and the `OneKeyStore` async poll
closures (`0x75b08..0x75ef0`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 500000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb_lo_append64 extractLsb_hi_append64
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_oks sp_setMem_setPC_oks
  readReg64_setPC_oks readReg64_setMem_setPC_oks
  readReg32_setPC_oks readReg32_setMem_setPC_oks
  readReg_setPC_oks readReg_setMem_setPC_oks
  hi32_append_lo32 cond_eq_adds64_neg1_1 cond_eq_adds64_pos_1
  cond_ne_subs32_self csinc_satIncU8_norm
  dropOneKeyFutName dropOneKeyStoreName dropStringLocal4Name
  dropInMemSessionStoreName dropInMemIdentityStoreName
  oneKeyGetSpkName oneKeySaveSpkName oneKeyGetKyberName
  oneKeySaveKyberName oneKeyMarkKyberName oneKeyGetPreKeyName
  oneKeySavePreKeyName oneKeyRemovePreKeyName spkRecordCloneName
  oneKeyGetSpkClosureName oneKeySaveSpkClosureName
  oneKeyGetKyberClosureName oneKeySaveKyberClosureName
  oneKeyMarkKyberClosureName oneKeyGetPreKeyClosureName
  oneKeySavePreKeyClosureName oneKeyRemovePreKeyClosureName
  libsignalSessionCode_fnOff_0x3e2c4
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "alloc::alloc::handle_alloc_error")
  (ls_hook% "alloc::alloc::handle_alloc_error")

/-! ## `<SignedPreKeyRecordStructure as Clone>::clone` (`0x76f88`) -/

def spkRecordSrcAt (src pubPtr pubLen privPtr privLen sigPtr sigLen timestamp : BitVec 64)
    (id : BitVec 32) : SepProp :=
  ((src + 0x08#64) ↦₆₄ pubPtr) ∗
  ((src + 0x10#64) ↦₆₄ pubLen) ∗
  ((src + 0x20#64) ↦₆₄ privPtr) ∗
  ((src + 0x28#64) ↦₆₄ privLen) ∗
  ((src + 0x38#64) ↦₆₄ sigPtr) ∗
  ((src + 0x40#64) ↦₆₄ sigLen) ∗
  ((src + 0x48#64) ↦₆₄ timestamp) ∗
  ((src + 0x50#64) ↦₃₂ id)

def spkRecordDstUninitAt (dst u0 u8 u10 u18 u20 u28 u30 u38 u40 u48 : BitVec 64)
    (u50 : BitVec 32) : SepProp :=
  (dst ↦₆₄ u0) ∗
  ((dst + 0x08#64) ↦₆₄ u8) ∗
  ((dst + 0x10#64) ↦₆₄ u10) ∗
  ((dst + 0x18#64) ↦₆₄ u18) ∗
  ((dst + 0x20#64) ↦₆₄ u20) ∗
  ((dst + 0x28#64) ↦₆₄ u28) ∗
  ((dst + 0x30#64) ↦₆₄ u30) ∗
  ((dst + 0x38#64) ↦₆₄ u38) ∗
  ((dst + 0x40#64) ↦₆₄ u40) ∗
  ((dst + 0x48#64) ↦₆₄ u48) ∗
  ((dst + 0x50#64) ↦₃₂ u50)

def spkRecordDstAt (dst pubLen pubPtr privLen privPtr sigLen sigPtr timestamp : BitVec 64)
    (id : BitVec 32) : SepProp :=
  (dst ↦₆₄ pubLen) ∗
  ((dst + 0x08#64) ↦₆₄ pubPtr) ∗
  ((dst + 0x10#64) ↦₆₄ pubLen) ∗
  ((dst + 0x18#64) ↦₆₄ privLen) ∗
  ((dst + 0x20#64) ↦₆₄ privPtr) ∗
  ((dst + 0x28#64) ↦₆₄ privLen) ∗
  ((dst + 0x30#64) ↦₆₄ sigLen) ∗
  ((dst + 0x38#64) ↦₆₄ sigPtr) ∗
  ((dst + 0x40#64) ↦₆₄ sigLen) ∗
  ((dst + 0x48#64) ↦₆₄ timestamp) ∗
  ((dst + 0x50#64) ↦₃₂ id)

private theorem stackAt_spkClone (sp : BitVec 64) :
    stackAt sp (96 + allocHookStack) =
      stackAt (sp - 96#64) allocHookStack ∗ cells (sp - 96#64) 12 :=
  ProofLib.stackAt_split_cells sp 4096 12 (by decide)

structure SpkCloneEmptySigArgs where
  dst : BitVec 64
  src : BitVec 64
  pubPtr : BitVec 64
  pubBytes : List (BitVec 8)
  privPtr : BitVec 64
  privBytes : List (BitVec 8)
  sigPtr : BitVec 64
  timestamp : BitVec 64
  id : BitVec 32
  u0 : BitVec 64
  u8 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64
  u28 : BitVec 64
  u30 : BitVec 64
  u38 : BitVec 64
  u40 : BitVec 64
  u48 : BitVec 64
  u50 : BitVec 32

def spkRecordCloneEmptySigSpec (A : RustAlloc) : Spec SpkCloneEmptySigArgs where
  pre := fun x s =>
    ⌜BitVec.ofNat 64 x.pubBytes.length ≠ 0#64 ∧
      x.pubBytes.length < 2 ^ 63 ∧
      BitVec.ofNat 64 x.privBytes.length ≠ 0#64 ∧
      x.privBytes.length < 2 ^ 63 ∧
      s.readReg64 .x0 = x.dst ∧
      s.readReg64 .x1 = x.src⌝ ∗
    stackAt s.sp (96 + allocHookStack) ∗
    A.pool ∗
    (x.pubPtr ↦ₛ x.pubBytes) ∗
    (x.privPtr ↦ₛ x.privBytes) ∗
    spkRecordSrcAt x.src x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
      x.privPtr (BitVec.ofNat 64 x.privBytes.length) x.sigPtr 0#64 x.timestamp x.id ∗
    spkRecordDstUninitAt x.dst x.u0 x.u8 x.u10 x.u18 x.u20 x.u28 x.u30 x.u38 x.u40 x.u48 x.u50
  post := fun x s0 sf =>
    ∃∗ newPubPtr : BitVec 64, ∃∗ newPrivPtr : BitVec 64,
      ⌜newPubPtr ≠ 0#64 ∧ newPrivPtr ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (96 + allocHookStack) ∗
      A.pool ∗
      (x.pubPtr ↦ₛ x.pubBytes) ∗
      (x.privPtr ↦ₛ x.privBytes) ∗
      A.live newPubPtr x.pubBytes.length 1 ∗ (newPubPtr ↦ₛ x.pubBytes) ∗
      A.live newPrivPtr x.privBytes.length 1 ∗ (newPrivPtr ↦ₛ x.privBytes) ∗
      spkRecordSrcAt x.src x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
        x.privPtr (BitVec.ofNat 64 x.privBytes.length) x.sigPtr 0#64 x.timestamp x.id ∗
      spkRecordDstAt x.dst (BitVec.ofNat 64 x.pubBytes.length) newPubPtr
        (BitVec.ofNat 64 x.privBytes.length) newPrivPtr 0#64 1#64 x.timestamp x.id
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure SpkCloneNonemptySigArgs where
  dst : BitVec 64
  src : BitVec 64
  pubPtr : BitVec 64
  pubBytes : List (BitVec 8)
  privPtr : BitVec 64
  privBytes : List (BitVec 8)
  sigPtr : BitVec 64
  sigBytes : List (BitVec 8)
  timestamp : BitVec 64
  id : BitVec 32
  u0 : BitVec 64
  u8 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64
  u28 : BitVec 64
  u30 : BitVec 64
  u38 : BitVec 64
  u40 : BitVec 64
  u48 : BitVec 64
  u50 : BitVec 32

def spkRecordCloneNonemptySigSpec (A : RustAlloc) : Spec SpkCloneNonemptySigArgs where
  pre := fun x s =>
    ⌜BitVec.ofNat 64 x.pubBytes.length ≠ 0#64 ∧
      x.pubBytes.length < 2 ^ 63 ∧
      BitVec.ofNat 64 x.privBytes.length ≠ 0#64 ∧
      x.privBytes.length < 2 ^ 63 ∧
      BitVec.ofNat 64 x.sigBytes.length ≠ 0#64 ∧
      x.sigBytes.length < 2 ^ 63 ∧
      s.readReg64 .x0 = x.dst ∧
      s.readReg64 .x1 = x.src⌝ ∗
    stackAt s.sp (96 + allocHookStack) ∗
    A.pool ∗
    (x.pubPtr ↦ₛ x.pubBytes) ∗
    (x.privPtr ↦ₛ x.privBytes) ∗
    (x.sigPtr ↦ₛ x.sigBytes) ∗
    spkRecordSrcAt x.src x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
      x.privPtr (BitVec.ofNat 64 x.privBytes.length)
      x.sigPtr (BitVec.ofNat 64 x.sigBytes.length) x.timestamp x.id ∗
    spkRecordDstUninitAt x.dst x.u0 x.u8 x.u10 x.u18 x.u20 x.u28 x.u30 x.u38 x.u40 x.u48 x.u50
  post := fun x s0 sf =>
    ∃∗ newPubPtr : BitVec 64, ∃∗ newPrivPtr : BitVec 64, ∃∗ newSigPtr : BitVec 64,
      ⌜newPubPtr ≠ 0#64 ∧ newPrivPtr ≠ 0#64 ∧ newSigPtr ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (96 + allocHookStack) ∗
      A.pool ∗
      (x.pubPtr ↦ₛ x.pubBytes) ∗
      (x.privPtr ↦ₛ x.privBytes) ∗
      (x.sigPtr ↦ₛ x.sigBytes) ∗
      A.live newPubPtr x.pubBytes.length 1 ∗ (newPubPtr ↦ₛ x.pubBytes) ∗
      A.live newPrivPtr x.privBytes.length 1 ∗ (newPrivPtr ↦ₛ x.privBytes) ∗
      A.live newSigPtr x.sigBytes.length 1 ∗ (newSigPtr ↦ₛ x.sigBytes) ∗
      spkRecordSrcAt x.src x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
        x.privPtr (BitVec.ofNat 64 x.privBytes.length)
        x.sigPtr (BitVec.ofNat 64 x.sigBytes.length) x.timestamp x.id ∗
      spkRecordDstAt x.dst (BitVec.ofNat 64 x.pubBytes.length) newPubPtr
        (BitVec.ofNat 64 x.privBytes.length) newPrivPtr
        (BitVec.ofNat 64 x.sigBytes.length) newSigPtr x.timestamp x.id
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `OneKeyStore` Async Poll Closures (`0x75b08..0x75ef0`) -/

/-- Shared spec for the 3 no-op save closures (`0x75bd4`, `0x75cd0`, `0x75ec4`). -/
def oneKeySaveClosureSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (boxPtr, retPtr, u0) s =>
    ⌜s.readReg64 .x0 = boxPtr ∧
      s.readReg64 .x8 = retPtr⌝ ∗
    ((boxPtr + 12#64) ↦₈ 0#8) ∗
    (retPtr ↦₆₄ u0)
  post := fun (boxPtr, retPtr, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((boxPtr + 12#64) ↦₈ 1#8) ∗
    (retPtr ↦₆₄ 0xfffffffffffffffe#64)

@[local simp, local wp_norm, local arm64_norm]
theorem csinc_satIncU8 (c : BitVec 8) :
    (if ConditionHolds CondCode.CS (subsPState32 (c.zeroExtend 32 + 1#32) 255#32) then
      255#64
    else
      (c.zeroExtend 32).zeroExtend 64 + 1#64).setWidth 8 = satIncU8 c := by
  simp only [ConditionHolds, subsPState32, AddWithCarry32, satIncU8]
  bv_bits

structure OneKeyRemovePreKeyClosureArgs where
  boxPtr : BitVec 64
  storePtr : BitVec 64
  retPtr : BitVec 64
  id : BitVec 32
  oldOpkId : BitVec 32
  oldOpkRemoved : BitVec 8
  u0 : BitVec 64

def oneKeyRemovePreKeyClosureSpec : Spec OneKeyRemovePreKeyClosureArgs where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    oneKeyBox16At x.boxPtr x.storePtr x.id 0#8 ∗
    ((x.storePtr + 0xf0#64) ↦₃₂ x.oldOpkId) ∗
    ((x.storePtr + 0x116#64) ↦₈ x.oldOpkRemoved) ∗
    (x.retPtr ↦₆₄ x.u0)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    oneKeyBox16At x.boxPtr x.storePtr x.id 1#8 ∗
    ((x.storePtr + 0xf0#64) ↦₃₂ x.id) ∗
    ((x.storePtr + 0x116#64) ↦₈ satIncU8 x.oldOpkRemoved) ∗
    (x.retPtr ↦₆₄ 0xfffffffffffffffe#64)

private theorem stackAt_getPreKeyClosure (sp : BitVec 64) :
    stackAt sp (80 + allocHookStack) =
      stackAt (sp - 80#64) allocHookStack ∗ cells (sp - 80#64) 10 :=
  ProofLib.stackAt_split_cells sp 4096 10 (by decide)

def preKeyRecordOutAt (dst pubLen pubPtr privLen privPtr : BitVec 64) (id : BitVec 32) : SepProp :=
  (dst ↦₆₄ pubLen) ∗
  ((dst + 0x08#64) ↦₆₄ pubPtr) ∗
  ((dst + 0x10#64) ↦₆₄ pubLen) ∗
  ((dst + 0x18#64) ↦₆₄ privLen) ∗
  ((dst + 0x20#64) ↦₆₄ privPtr) ∗
  ((dst + 0x28#64) ↦₆₄ privLen) ∗
  ((dst + 0x30#64) ↦₃₂ id)

structure OneKeyGetPreKeyClosureArgs where
  boxPtr : BitVec 64
  storePtr : BitVec 64
  retPtr : BitVec 64
  id : BitVec 32
  opkPubCap : BitVec 64
  opkPubPtr : BitVec 64
  opkPubBytes : List (BitVec 8)
  opkPrivPtr : BitVec 64
  opkPrivBytes : List (BitVec 8)
  u0 : BitVec 64
  u8 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64
  u28 : BitVec 64
  u30 : BitVec 32

def oneKeyGetPreKeyClosureSpec (A : RustAlloc) : Spec OneKeyGetPreKeyClosureArgs where
  pre := fun x s =>
    ⌜x.opkPubCap ≠ 0xffffffffffffffff#64 ∧
      BitVec.ofNat 64 x.opkPubBytes.length ≠ 0#64 ∧
      x.opkPubBytes.length < 2 ^ 63 ∧
      BitVec.ofNat 64 x.opkPrivBytes.length ≠ 0#64 ∧
      x.opkPrivBytes.length < 2 ^ 63 ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp (80 + allocHookStack) ∗
    A.pool ∗
    oneKeyBox16At x.boxPtr x.storePtr x.id 0#8 ∗
    (x.opkPubPtr ↦ₛ x.opkPubBytes) ∗
    (x.opkPrivPtr ↦ₛ x.opkPrivBytes) ∗
    ((x.storePtr + 0xb0#64) ↦₆₄ x.opkPubCap) ∗
    ((x.storePtr + 0xb8#64) ↦₆₄ x.opkPubPtr) ∗
    ((x.storePtr + 0xc0#64) ↦₆₄ BitVec.ofNat 64 x.opkPubBytes.length) ∗
    ((x.storePtr + 0xd0#64) ↦₆₄ x.opkPrivPtr) ∗
    ((x.storePtr + 0xd8#64) ↦₆₄ BitVec.ofNat 64 x.opkPrivBytes.length) ∗
    ((x.storePtr + 0xe0#64) ↦₃₂ x.id) ∗
    (x.retPtr ↦₆₄ x.u0) ∗
    ((x.retPtr + 0x08#64) ↦₆₄ x.u8) ∗
    ((x.retPtr + 0x10#64) ↦₆₄ x.u10) ∗
    ((x.retPtr + 0x18#64) ↦₆₄ x.u18) ∗
    ((x.retPtr + 0x20#64) ↦₆₄ x.u20) ∗
    ((x.retPtr + 0x28#64) ↦₆₄ x.u28) ∗
    ((x.retPtr + 0x30#64) ↦₃₂ x.u30)
  post := fun x s0 sf =>
    ∃∗ newPubPtr : BitVec 64, ∃∗ newPrivPtr : BitVec 64,
      ⌜newPubPtr ≠ 0#64 ∧ newPrivPtr ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (80 + allocHookStack) ∗
      A.pool ∗
      oneKeyBox16At x.boxPtr x.storePtr x.id 1#8 ∗
      (x.opkPubPtr ↦ₛ x.opkPubBytes) ∗
      (x.opkPrivPtr ↦ₛ x.opkPrivBytes) ∗
      A.live newPubPtr x.opkPubBytes.length 1 ∗ (newPubPtr ↦ₛ x.opkPubBytes) ∗
      A.live newPrivPtr x.opkPrivBytes.length 1 ∗ (newPrivPtr ↦ₛ x.opkPrivBytes) ∗
      ((x.storePtr + 0xb0#64) ↦₆₄ x.opkPubCap) ∗
      ((x.storePtr + 0xb8#64) ↦₆₄ x.opkPubPtr) ∗
      ((x.storePtr + 0xc0#64) ↦₆₄ BitVec.ofNat 64 x.opkPubBytes.length) ∗
      ((x.storePtr + 0xd0#64) ↦₆₄ x.opkPrivPtr) ∗
      ((x.storePtr + 0xd8#64) ↦₆₄ BitVec.ofNat 64 x.opkPrivBytes.length) ∗
      ((x.storePtr + 0xe0#64) ↦₃₂ x.id) ∗
      preKeyRecordOutAt x.retPtr (BitVec.ofNat 64 x.opkPubBytes.length) newPubPtr
        (BitVec.ofNat 64 x.opkPrivBytes.length) newPrivPtr x.id
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ### `mark_kyber_pre_key_used::{closure#0}` (`0x75d00`) -/

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs64_one :
    ConditionHolds CondCode.NE (subsPState64 1#64 1#64) = false := by
  simp only [ConditionHolds, subsPState64]; decide

private theorem stackAt_markKyberClosure (sp : BitVec 64) :
    stackAt sp (48 + publicKeySerializeStack) =
      stackAt (sp - 48#64) publicKeySerializeStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp (32 + 4096) 6 (by decide)

private theorem spAligned_sub_48 {s0 : State} (h : (s0.sp &&& 15#64 == 0#64) = true) :
    ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := by
  bv_bits

private theorem sepConj_swap12 (A B C : SepProp) : A ∗ B ∗ C = B ∗ A ∗ C := by
  ac_rfl

private theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases h with ⟨ha, hp⟩
  unfold allocFailedIn at ha ⊢
  rw [← htr]
  exact ⟨ha, hp⟩

private theorem call_pk_serialize {prog : Program} {ret callee : BitVec 64}
    {A : RustAlloc} {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee (publicKeySerializeSpec A))
    (ret_pc sp_cur keyA : BitVec 64) (key : PublicKey)
    (hP : P = ((keyA ↦ₛ key.bytes.toList) ∗ A.pool ∗
      stackAt sp_cur publicKeySerializeStack) ∗ F)
    (hside : s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      s.readReg64 (Reg.gpr 0#5) = keyA)
    (hnext : ∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → sf.spAligned = true →
      CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 → sf.readReg64 (Reg.gpr 1#5) = 33#64 →
      sf.trace = s0.trace →
      SepWPp prog ret sf
        ((keyA ↦ₛ key.bytes.toList) ∗
          A.live (sf.readReg64 (Reg.gpr 0#5)) key.serialize.length 1 ∗
          (sf.readReg64 (Reg.gpr 0#5) ↦ₛ key.serialize) ∗
          A.pool ∗ stackAt sp_cur publicKeySerializeStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases hside with ⟨hpc, hrun, hsp, hsp_cur, hlr, htr, hφ⟩
  refine SepWPp.call_frame (x := ⟨keyA, key⟩) hcall hpc hrun hsp hlr
    (by simp only [publicKeySerializeSpec, hsp_cur, Reg.x0, sepConj_assoc]) hφ hP
    (fun sf code R' _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [publicKeySerializeSpec] at hm
      exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm)
    (fun sf hpcm hrunm hspm hcsm => ?_)
  have hne : key.serialize ≠ [] := by simp [PublicKey.serialize]
  conv =>
    arg 4
    simp only [publicKeySerializeSpec, boxU8Buf, hne, ite_false, hsp_cur, Reg.x0, Reg.x1,
      sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1, htr'⟩ => ?_
  conv =>
    arg 4
    rw [sepConj_swap12 (keyA ↦ₛ key.bytes.toList)]
  refine SepWPp.pure_elim fun ⟨hx0, _⟩ => ?_
  have hsp_sf : sf.spAligned = true := by
    rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
  exact hnext sf hpcm hrunm (hspm.trans hsp_cur) hsp_sf hcsm hx0 hx1 (htr'.trans htr)

private theorem markKyber_copy_loop {prog : Program} {ret entry : BitVec 64}
    (hloop :
      prog.fetch (entry + 96#64) =
        some (.ldr .W32 .B8 false .x10 (.PostIndex .x0 1#64)) ∧
      prog.fetch (entry + 100#64) =
        some (.addSubImm .W64 .SUBS .x8 .x8 1#12 false) ∧
      prog.fetch (entry + 104#64) =
        some (.str .B8 .x10 (.PostIndex .x9 1#64)) ∧
      prog.fetch (entry + 108#64) = some (.bCond .NE (-12#64)))
    (bs : List (BitVec 8)) :
    ∀ (b0 : BitVec 8) (d0 : BitVec 8) (ds : List (BitVec 8))
      (_hlen : ds.length = bs.length) (_hlt : bs.length + 1 < 2 ^ 64)
      (src dst : BitVec 64) (s : State) {R : SepProp} {Q Qp : State → SepProp → Prop}
      (_hrun : s.status = .Running)
      (_hpc : s.pc = entry + 96#64)
      (_hx0 : s.readReg64 .x0 = src)
      (_hx9 : s.readReg64 .x9 = dst)
      (_hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bs.length + 1))
      (_hcont : ∀ s' : State,
        s'.status = .Running →
        s'.pc = entry + 112#64 →
        s'.sp = s.sp →
        s'.trace = s.trace →
        CalleeSavedPreserved s s' →
        s'.readReg64 .x30 = s.readReg64 .x30 →
        SepWPp prog ret s' ((src ↦ₛ (b0 :: bs)) ∗ (dst ↦ₛ (b0 :: bs)) ∗ R) Q Qp),
      SepWPp prog ret s ((src ↦ₛ (b0 :: bs)) ∗ (dst ↦ₛ (d0 :: ds)) ∗ R) Q Qp := by
  obtain ⟨hf96, hf100, hf104, hf108⟩ := hloop
  examples_hide_fetches
  induction bs with
  | nil =>
    intro b0 d0 ds hlen _hlt src dst s R Q Qp hrun hpc hx0 hx9 hx8 hcont
    cases ds with
    | cons _ _ => simp at hlen
    | nil =>
      simp only [List.length_nil] at hx8
      rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_nil]
      simp only [sepConj_emp, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + 112#64)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.weaken_pre ?_
        (hcont _ (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [CalleeSavedPreserved]; wp_norm_goal) (by wp_norm_goal))
      simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc]
      exact Entails.refl _
  | cons b1 bs' ih =>
    intro b0 d0 ds hlen hlt src dst s R Q Qp hrun hpc hx0 hx9 hx8 hcont
    cases ds with
    | nil => simp at hlen
    | cons d1 ds' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hlt' : bs'.length + 1 < 2 ^ 64 := by simp only [List.length_cons] at hlt; omega
      have hne1 : (BitVec.ofNat 64 ((b1 :: bs').length + 1) != 1#64) = true := by
        simp only [bne_iff_ne, ne_eq, List.length_cons] at hlt ⊢; bv_omega
      have hdec : BitVec.ofNat 64 ((b1 :: bs').length + 1) - 1#64 =
          BitVec.ofNat 64 (bs'.length + 1) := by
        simp only [List.length_cons] at hlt ⊢; bv_omega
      rw [pointsToBytes_cons src b0, pointsToBytes_cons dst d0]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + 100#64)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      apply SepWPp.of_sepWP (mid := entry + 96#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, hx8, hne1, ite_true]) (by wp_norm_lhs)
      have hprop_in :
          ((src ↦₈ b0) ∗ ((src + 1#64) ↦ₛ (b1 :: bs')) ∗ (dst ↦₈ b0) ∗
            ((dst + 1#64) ↦ₛ (d1 :: ds')) ∗ R) =
          (((src + 1#64) ↦ₛ (b1 :: bs')) ∗ ((dst + 1#64) ↦ₛ (d1 :: ds')) ∗ ((src ↦₈ b0) ∗
            (dst ↦₈ b0) ∗ R)) := by
        ac_rfl
      rw [hprop_in]
      refine ih b1 d1 ds' hlen hlt' (src + 1#64) (dst + 1#64) _
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, hx8, hdec]) (fun s' hrun' hpc' hsp' htr' hcs' hx30' => ?_)
      have hgoal := hcont s' hrun' hpc'
        (by simp only [arm64_norm] at hsp' ⊢; exact hsp')
        (by simp only [arm64_norm] at htr' ⊢; exact htr')
        (by simp only [CalleeSavedPreserved, arm64_norm] at hcs' ⊢; exact hcs')
        (by simp only [arm64_norm] at hx30' ⊢; exact hx30')
      rw [pointsToBytes_cons src b0, pointsToBytes_cons dst b0] at hgoal
      simp only [sepConj_assoc] at hgoal ⊢
      have hprop_out :
          ((src ↦₈ b0) ∗ ((src + 1#64) ↦ₛ (b1 :: bs')) ∗ (dst ↦₈ b0) ∗
            ((dst + 1#64) ↦ₛ (b1 :: bs')) ∗ R) =
          (((src + 1#64) ↦ₛ (b1 :: bs')) ∗ ((dst + 1#64) ↦ₛ (b1 :: bs')) ∗ (src ↦₈ b0) ∗
            (dst ↦₈ b0) ∗ R) := by
        ac_rfl
      exact hprop_out ▸ hgoal

private theorem run_markKyber_copy_loop {prog : Program} {ret entry : BitVec 64}
    (hloop :
      prog.fetch (entry + 96#64) =
        some (.ldr .W32 .B8 false .x10 (.PostIndex .x0 1#64)) ∧
      prog.fetch (entry + 100#64) =
        some (.addSubImm .W64 .SUBS .x8 .x8 1#12 false) ∧
      prog.fetch (entry + 104#64) =
        some (.str .B8 .x10 (.PostIndex .x9 1#64)) ∧
      prog.fetch (entry + 108#64) = some (.bCond .NE (-12#64)))
    (bs : List (BitVec 8)) (b0 d0 : BitVec 8) (ds : List (BitVec 8))
    (hlen : ds.length = bs.length) (hlt : bs.length + 1 < 2 ^ 64)
    (src dst : BitVec 64) (s : State) {P R : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = ((src ↦ₛ (b0 :: bs)) ∗ (dst ↦ₛ (d0 :: ds))) ∗ R)
    (hrun : s.status = .Running)
    (hpc : s.pc = entry + 96#64)
    (hx0 : s.readReg64 .x0 = src)
    (hx9 : s.readReg64 .x9 = dst)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bs.length + 1))
    (hcont : ∀ s' : State,
      s'.status = .Running →
      s'.pc = entry + 112#64 →
      s'.sp = s.sp →
      s'.trace = s.trace →
      CalleeSavedPreserved s s' →
      s'.readReg64 .x30 = s.readReg64 .x30 →
      SepWPp prog ret s' ((src ↦ₛ (b0 :: bs)) ∗ (dst ↦ₛ (b0 :: bs)) ∗ R) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hP, sepConj_assoc]
  exact markKyber_copy_loop hloop bs b0 d0 ds hlen hlt src dst s hrun hpc hx0 hx9 hx8 hcont

structure MarkKyberClosureArgs where
  boxPtr : BitVec 64
  storePtr : BitVec 64
  baseKeyPtr : BitVec 64
  retPtr : BitVec 64
  kyberId : BitVec 32
  spkId : BitVec 32
  pk : PublicKey
  kyberUsed : BitVec 8
  oldKyberId : BitVec 32
  oldSpkId : BitVec 32
  oldB0 : BitVec 8
  oldBs : List (BitVec 8)
  u0 : BitVec 64

def oneKeyMarkKyberClosureSpec (A : RustAlloc) : Spec MarkKyberClosureArgs where
  pre := fun x s =>
    ⌜x.oldBs.length = 32 ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp (48 + publicKeySerializeStack) ∗
    A.pool ∗
    oneKeyMarkBox32At x.boxPtr x.storePtr x.baseKeyPtr x.kyberId x.spkId 0#8 ∗
    (x.baseKeyPtr ↦ₛ x.pk.bytes.toList) ∗
    ((x.storePtr + 0xf4#64) ↦₈ x.kyberUsed) ∗
    ((x.storePtr + 0xe8#64) ↦₃₂ x.oldKyberId) ∗
    ((x.storePtr + 0xec#64) ↦₃₂ x.oldSpkId) ∗
    ((x.storePtr + 0xf5#64) ↦ₛ (x.oldB0 :: x.oldBs)) ∗
    (x.retPtr ↦₆₄ x.u0)
  post := fun x s0 sf =>
    ∃∗ serPtr : BitVec 64,
      ⌜serPtr ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (48 + publicKeySerializeStack) ∗
      A.pool ∗
      oneKeyMarkBox32At x.boxPtr x.storePtr x.baseKeyPtr x.kyberId x.spkId 1#8 ∗
      (x.baseKeyPtr ↦ₛ x.pk.bytes.toList) ∗
      A.live serPtr 33 1 ∗
      (serPtr ↦ₛ x.pk.serialize) ∗
      ((x.storePtr + 0xf4#64) ↦₈ satIncU8 x.kyberUsed) ∗
      ((x.storePtr + 0xe8#64) ↦₃₂ x.kyberId) ∗
      ((x.storePtr + 0xec#64) ↦₃₂ x.spkId) ∗
      ((x.storePtr + 0xf5#64) ↦ₛ x.pk.serialize) ∗
      (x.retPtr ↦₆₄ 0xfffffffffffffffe#64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ### `get_signed_pre_key::{closure#0}` (`0x75b08`) and `get_kyber_pre_key::{closure#0}` (`0x75c04`) -/

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

@[local simp, local wp_norm, local arm64_norm]
theorem extractLsb_lo32_append32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 0 32 = lo :=
  BitVec.extractLsb'_append_eq_right

@[local simp, local wp_norm, local arm64_norm]
theorem extractLsb_hi32_append32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi :=
  BitVec.extractLsb'_append_eq_left

theorem words5_repack_w32_4w64_w32_assoc (p w2 w3 w4 w5 w6 : BitVec 64) (R : SepProp) :
    ((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
        ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6) ∗ R =
      ((p + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((p + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((p + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((p + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((p + 0x2c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((p + 0x34#64) ↦₃₂ w6.extractLsb' 32 32) ∗ R := by
  have h := congrArg (· ∗ R) (words5_repack_w32_4w64_w32 p w2 w3 w4 w5 w6)
  simpa only [sepConj_assoc] using h

theorem words5_repack_zero_assoc (p w2 w3 w4 w5 : BitVec 64) (R : SepProp) :
    ((p + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗
      ((p + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
      ((p + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
      ((p + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
      ((p + 0x2c#64) ↦₆₄ (0#32 ++ w5.extractLsb' 32 32)) ∗
      ((p + 0x34#64) ↦₃₂ 0#32) ∗ R =
    ((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
      ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ 0#64) ∗ R :=
  (words5_repack_w32_4w64_w32_assoc p w2 w3 w4 w5 0#64 R).symm

theorem pointsTo32_pair_assoc (a : BitVec 64) (lo hi : BitVec 32) (R : SepProp) :
    (a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi) ∗ R = (a ↦₆₄ (hi ++ lo)) ∗ R := by
  rw [← sepConj_assoc, pointsTo32_pair]

theorem sp_words5_repack_assoc (sp w2 w3 w4 w5 w6 : BitVec 64) (R : SepProp) :
    ((sp - 120#64) ↦₆₄ w2) ∗ ((sp - 112#64) ↦₆₄ w3) ∗ ((sp - 104#64) ↦₆₄ w4) ∗
        ((sp - 96#64) ↦₆₄ w5) ∗ ((sp - 88#64) ↦₆₄ w6) ∗ R =
      ((sp - 120#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp - 116#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((sp - 108#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((sp - 100#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp - 92#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((sp - 84#64) ↦₃₂ w6.extractLsb' 32 32) ∗ R := by
  have h := words5_repack_w32_4w64_w32_assoc (sp - 136#64) w2 w3 w4 w5 w6 R
  rwa [show sp - 136#64 + 0x10#64 = sp - 120#64 by bv_omega,
       show sp - 136#64 + 0x18#64 = sp - 112#64 by bv_omega,
       show sp - 136#64 + 0x20#64 = sp - 104#64 by bv_omega,
       show sp - 136#64 + 0x28#64 = sp - 96#64 by bv_omega,
       show sp - 136#64 + 0x30#64 = sp - 88#64 by bv_omega,
       show sp - 136#64 + 0x14#64 = sp - 116#64 by bv_omega,
       show sp - 136#64 + 0x1c#64 = sp - 108#64 by bv_omega,
       show sp - 136#64 + 0x24#64 = sp - 100#64 by bv_omega,
       show sp - 136#64 + 0x2c#64 = sp - 92#64 by bv_omega,
       show sp - 136#64 + 0x34#64 = sp - 84#64 by bv_omega] at h

theorem sp144_pair_assoc (sp : BitVec 64) (lo hi : BitVec 32) (R : SepProp) :
    ((sp - 144#64) ↦₃₂ lo) ∗ ((sp - 140#64) ↦₃₂ hi) ∗ R =
      ((sp - 144#64) ↦₆₄ (hi ++ lo)) ∗ R := by
  have h := pointsTo32_pair_assoc (sp - 144#64) lo hi R
  rwa [show sp - 144#64 + 4#64 = sp - 140#64 by bv_omega] at h

private theorem stackAt_getSpkClosure (sp : BitVec 64) :
    stackAt sp (304 + allocHookStack) =
      stackAt (sp - 208#64) (96 + allocHookStack) ∗ cells (sp - 208#64) 26 :=
  ProofLib.stackAt_split_cells sp (96 + 4096) 26 (by decide)

local macro "cells_unfold_big" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) (disch := decide) only [
    ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right] at *)

private theorem fold_spkRecordDstUninitAt_sp (sp u0 u8 u10 u18 u20 u28 u30 u38 u40 u48 : BitVec 64)
    (u50 : BitVec 32) :
    ((sp - 136#64) ↦₆₄ u0) ∗ ((sp - 128#64) ↦₆₄ u8) ∗ ((sp - 120#64) ↦₆₄ u10) ∗
    ((sp - 112#64) ↦₆₄ u18) ∗ ((sp - 104#64) ↦₆₄ u20) ∗ ((sp - 96#64) ↦₆₄ u28) ∗
    ((sp - 88#64) ↦₆₄ u30) ∗ ((sp - 80#64) ↦₆₄ u38) ∗ ((sp - 72#64) ↦₆₄ u40) ∗
    ((sp - 64#64) ↦₆₄ u48) ∗ ((sp - 56#64) ↦₃₂ u50) ⊢
      spkRecordDstUninitAt (sp - 136#64) u0 u8 u10 u18 u20 u28 u30 u38 u40 u48 u50 := by
  unfold spkRecordDstUninitAt
  rw [show sp - 136#64 + 0x08#64 = sp - 128#64 by bv_omega,
      show sp - 136#64 + 0x10#64 = sp - 120#64 by bv_omega,
      show sp - 136#64 + 0x18#64 = sp - 112#64 by bv_omega,
      show sp - 136#64 + 0x20#64 = sp - 104#64 by bv_omega,
      show sp - 136#64 + 0x28#64 = sp - 96#64 by bv_omega,
      show sp - 136#64 + 0x30#64 = sp - 88#64 by bv_omega,
      show sp - 136#64 + 0x38#64 = sp - 80#64 by bv_omega,
      show sp - 136#64 + 0x40#64 = sp - 72#64 by bv_omega,
      show sp - 136#64 + 0x48#64 = sp - 64#64 by bv_omega,
      show sp - 136#64 + 0x50#64 = sp - 56#64 by bv_omega]
  exact Entails.refl _

private theorem fold_spkRecordSrcAt
  (src pubPtr pubLen privPtr privLen sigPtr sigLen timestamp : BitVec 64)
    (id : BitVec 32) :
    ((src + 8#64) ↦₆₄ pubPtr) ∗ ((src + 16#64) ↦₆₄ pubLen) ∗
    ((src + 32#64) ↦₆₄ privPtr) ∗ ((src + 40#64) ↦₆₄ privLen) ∗
    ((src + 56#64) ↦₆₄ sigPtr) ∗ ((src + 64#64) ↦₆₄ sigLen) ∗
    ((src + 72#64) ↦₆₄ timestamp) ∗ ((src + 80#64) ↦₃₂ id) ⊢
      spkRecordSrcAt src pubPtr pubLen privPtr privLen sigPtr sigLen timestamp id :=
  Entails.refl _

private theorem fold_spkRecordSrcAt_kyber
  (storePtr pubPtr pubLen privPtr privLen sigPtr sigLen timestamp : BitVec 64)
    (id : BitVec 32) :
    ((storePtr + 96#64) ↦₆₄ pubPtr) ∗ ((storePtr + 104#64) ↦₆₄ pubLen) ∗
    ((storePtr + 120#64) ↦₆₄ privPtr) ∗ ((storePtr + 128#64) ↦₆₄ privLen) ∗
    ((storePtr + 144#64) ↦₆₄ sigPtr) ∗ ((storePtr + 152#64) ↦₆₄ sigLen) ∗
    ((storePtr + 160#64) ↦₆₄ timestamp) ∗ ((storePtr + 168#64) ↦₃₂ id) ⊢
      spkRecordSrcAt
        (storePtr + 0x58#64) pubPtr pubLen privPtr privLen sigPtr sigLen timestamp id := by
  unfold spkRecordSrcAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

private theorem call_spk_clone {prog : Program} {ret callee : BitVec 64}
    {A : RustAlloc} {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee (spkRecordCloneEmptySigSpec A))
    (ret_pc sp_cur : BitVec 64) (args : SpkCloneEmptySigArgs)
    (hP : P = (stackAt sp_cur (96 + allocHookStack) ∗ A.pool ∗
      (args.pubPtr ↦ₛ args.pubBytes) ∗ (args.privPtr ↦ₛ args.privBytes) ∗
      spkRecordSrcAt args.src args.pubPtr (BitVec.ofNat 64 args.pubBytes.length)
        args.privPtr
          (BitVec.ofNat 64 args.privBytes.length) args.sigPtr 0#64 args.timestamp args.id ∗
      spkRecordDstUninitAt args.dst args.u0 args.u8 args.u10 args.u18 args.u20 args.u28
        args.u30 args.u38 args.u40 args.u48 args.u50) ∗ F)
    (hside : s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      (BitVec.ofNat 64 args.pubBytes.length ≠ 0#64 ∧
        args.pubBytes.length < 2 ^ 63 ∧
        BitVec.ofNat 64 args.privBytes.length ≠ 0#64 ∧
        args.privBytes.length < 2 ^ 63 ∧
        s.readReg64 .x0 = args.dst ∧
        s.readReg64 .x1 = args.src))
    (hnext : ∀ (sf : State) (newPubPtr newPrivPtr : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → sf.spAligned = true →
      CalleeSavedPreserved s sf →
      newPubPtr ≠ 0#64 → newPrivPtr ≠ 0#64 → sf.trace = s0.trace →
      SepWPp prog ret sf
        (stackAt sp_cur (96 + allocHookStack) ∗ A.pool ∗
          (args.pubPtr ↦ₛ args.pubBytes) ∗ (args.privPtr ↦ₛ args.privBytes) ∗
          A.live newPubPtr args.pubBytes.length 1 ∗ (newPubPtr ↦ₛ args.pubBytes) ∗
          A.live newPrivPtr args.privBytes.length 1 ∗ (newPrivPtr ↦ₛ args.privBytes) ∗
          spkRecordSrcAt args.src args.pubPtr (BitVec.ofNat 64 args.pubBytes.length)
            args.privPtr
              (BitVec.ofNat 64 args.privBytes.length) args.sigPtr 0#64 args.timestamp args.id ∗
          spkRecordDstAt args.dst (BitVec.ofNat 64 args.pubBytes.length) newPubPtr
            (BitVec.ofNat 64 args.privBytes.length) newPrivPtr 0#64 1#64 args.timestamp args.id ∗
              F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  rcases hside with ⟨hpc, hrun, hsp, hsp_cur, hlr, htr, hφ⟩
  refine SepWPp.call_frame (x := args) hcall hpc hrun hsp hlr
    (by simp only [spkRecordCloneEmptySigSpec, hsp_cur, sepConj_assoc]) hφ hP
    (fun sf code R' _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [spkRecordCloneEmptySigSpec] at hm
      rw [← sepConj_assoc]
      exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm)
    (fun sf hpcm hrunm hspm hcsm => ?_)
  dsimp only [spkRecordCloneEmptySigSpec]
  rw [hsp_cur]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun newPubPtr => SepWPp.exists_elim fun newPrivPtr => ?_
  refine SepWPp.pure_elim fun ⟨hnpub, hnpriv, htr'⟩ => ?_
  have hsp_sf : sf.spAligned = true := by
    rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
  exact hnext sf newPubPtr newPrivPtr hpcm hrunm (hspm.trans hsp_cur) hsp_sf hcsm
    hnpub hnpriv (htr'.trans htr)

def spkPollOutUninitAt (retPtr u0 u8 u10 u18 u20 u28 u30 u38 u40 u48 u50 : BitVec 64) : SepProp :=
  (retPtr ↦₆₄ u0) ∗
  ((retPtr + 0x08#64) ↦₆₄ u8) ∗
  ((retPtr + 0x10#64) ↦₆₄ u10) ∗
  ((retPtr + 0x18#64) ↦₆₄ u18) ∗
  ((retPtr + 0x20#64) ↦₆₄ u20) ∗
  ((retPtr + 0x28#64) ↦₆₄ u28) ∗
  ((retPtr + 0x30#64) ↦₆₄ u30) ∗
  ((retPtr + 0x38#64) ↦₆₄ u38) ∗
  ((retPtr + 0x40#64) ↦₆₄ u40) ∗
  ((retPtr + 0x48#64) ↦₆₄ u48) ∗
  ((retPtr + 0x50#64) ↦₆₄ u50)

structure GetSpkClosureArgs where
  boxPtr : BitVec 64
  storePtr : BitVec 64
  retPtr : BitVec 64
  id : BitVec 32
  pubPtr : BitVec 64
  pubBytes : List (BitVec 8)
  privPtr : BitVec 64
  privBytes : List (BitVec 8)
  sigPtr : BitVec 64
  timestamp : BitVec 64
  u0 : BitVec 64
  u8 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64
  u28 : BitVec 64
  u30 : BitVec 64
  u38 : BitVec 64
  u40 : BitVec 64
  u48 : BitVec 64
  u50 : BitVec 64

def oneKeyGetSpkClosureSpec (A : RustAlloc) : Spec GetSpkClosureArgs where
  pre := fun x s =>
    ⌜BitVec.ofNat 64 x.pubBytes.length ≠ 0#64 ∧
      x.pubBytes.length < 2 ^ 63 ∧
      BitVec.ofNat 64 x.privBytes.length ≠ 0#64 ∧
      x.privBytes.length < 2 ^ 63 ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp (304 + allocHookStack) ∗
    A.pool ∗
    oneKeyBox16At x.boxPtr x.storePtr x.id 0#8 ∗
    (x.pubPtr ↦ₛ x.pubBytes) ∗
    (x.privPtr ↦ₛ x.privBytes) ∗
    spkRecordSrcAt x.storePtr x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
      x.privPtr (BitVec.ofNat 64 x.privBytes.length) x.sigPtr 0#64 x.timestamp x.id ∗
    spkPollOutUninitAt x.retPtr x.u0 x.u8 x.u10 x.u18 x.u20 x.u28 x.u30 x.u38 x.u40 x.u48 x.u50
  post := fun x s0 sf =>
    ∃∗ newPubPtr : BitVec 64, ∃∗ newPrivPtr : BitVec 64, ∃∗ pad32 : BitVec 32,
      ⌜newPubPtr ≠ 0#64 ∧ newPrivPtr ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (304 + allocHookStack) ∗
      A.pool ∗
      oneKeyBox16At x.boxPtr x.storePtr x.id 1#8 ∗
      (x.pubPtr ↦ₛ x.pubBytes) ∗
      (x.privPtr ↦ₛ x.privBytes) ∗
      spkRecordSrcAt x.storePtr x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
        x.privPtr (BitVec.ofNat 64 x.privBytes.length) x.sigPtr 0#64 x.timestamp x.id ∗
      spkRecordDstAt x.retPtr (BitVec.ofNat 64 x.pubBytes.length) newPubPtr
        (BitVec.ofNat 64 x.privBytes.length) newPrivPtr 0#64 1#64 x.timestamp x.id ∗
      ((x.retPtr + 0x54#64) ↦₃₂ pad32) ∗
      (newPubPtr ↦ₛ x.pubBytes) ∗
      A.live newPubPtr x.pubBytes.length 1 ∗
      (newPrivPtr ↦ₛ x.privBytes) ∗
      A.live newPrivPtr x.privBytes.length 1
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def oneKeyGetKyberClosureSpec (A : RustAlloc) : Spec GetSpkClosureArgs where
  pre := fun x s =>
    ⌜BitVec.ofNat 64 x.pubBytes.length ≠ 0#64 ∧
      x.pubBytes.length < 2 ^ 63 ∧
      BitVec.ofNat 64 x.privBytes.length ≠ 0#64 ∧
      x.privBytes.length < 2 ^ 63 ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp (304 + allocHookStack) ∗
    A.pool ∗
    oneKeyBox16At x.boxPtr x.storePtr x.id 0#8 ∗
    (x.pubPtr ↦ₛ x.pubBytes) ∗
    (x.privPtr ↦ₛ x.privBytes) ∗
    spkRecordSrcAt (x.storePtr + 0x58#64) x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
      x.privPtr (BitVec.ofNat 64 x.privBytes.length) x.sigPtr 0#64 x.timestamp x.id ∗
    spkPollOutUninitAt x.retPtr x.u0 x.u8 x.u10 x.u18 x.u20 x.u28 x.u30 x.u38 x.u40 x.u48 x.u50
  post := fun x s0 sf =>
    ∃∗ newPubPtr : BitVec 64, ∃∗ newPrivPtr : BitVec 64, ∃∗ pad32 : BitVec 32,
      ⌜newPubPtr ≠ 0#64 ∧ newPrivPtr ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp (304 + allocHookStack) ∗
      A.pool ∗
      oneKeyBox16At x.boxPtr x.storePtr x.id 1#8 ∗
      (x.pubPtr ↦ₛ x.pubBytes) ∗
      (x.privPtr ↦ₛ x.privBytes) ∗
      spkRecordSrcAt (x.storePtr + 0x58#64) x.pubPtr (BitVec.ofNat 64 x.pubBytes.length)
        x.privPtr (BitVec.ofNat 64 x.privBytes.length) x.sigPtr 0#64 x.timestamp x.id ∗
      spkRecordDstAt x.retPtr (BitVec.ofNat 64 x.pubBytes.length) newPubPtr
        (BitVec.ofNat 64 x.privBytes.length) newPrivPtr 0#64 1#64 x.timestamp x.id ∗
      ((x.retPtr + 0x54#64) ↦₃₂ pad32) ∗
      (newPubPtr ↦ₛ x.pubBytes) ∗
      A.live newPubPtr x.pubBytes.length 1 ∗
      (newPrivPtr ↦ₛ x.privBytes) ∗
      A.live newPrivPtr x.privBytes.length 1
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.E2E.Pqxdh.ResponderStore
