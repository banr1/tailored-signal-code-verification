/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Seams
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# `SP2Ext` Seam Contracts and Composition for `consume_message_key`

Defines the `cmkStackX = 20480` checkpoint states, segment contracts `S0` through `S5` on
`SP2Ext img.base ext`, store-loop induction (`s3_of_iter_x`), and top-level composition
(`cmk_of_seams_x`).
-/
namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_CmkX_Seams : True := trivial


theorem anyHeap_sepConj_left (P : SepProp) : (anyHeap ∗ P) ⊢ anyHeap :=
  entails_anyHeap _

theorem stackAt_sub_le (sp : BitVec 64) (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ 2 ^ 64) :
    stackAt sp b = stackAt sp a ∗ memRegion (sp - BitVec.ofNat 64 b) (b - a) := by
  have h := stackAt_split_bottom sp a (b - a) (by omega)
  rw [Nat.add_sub_of_le h1] at h
  rw [h, sepConj_comm]

/-! ## Stack Splits and Checkpoint State Predicates -/

abbrev cmkName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

def cmkSpecX (F : ShaCompress) (A : RustAlloc) (img : Obj.Image) : Spec ConsumeMessageKeyGhost :=
  ({ pre := fun x s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ckA ∧
        (s.readReg64 .x3).setWidth 32 = x.counter ∧
        (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s.readReg64 .x8 = x.ret⌝ ∗
      ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ckA ↦ₛ chainKeyBytes x.ck) ∗ memRegion x.ret 88 ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp cmkStackX ∗ A.pool
     post := fun x s0 sf =>
      ⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ G' : RatchetGhost,
        ⌜x.G.AgreeExcept G' (x.touched F)⌝ ∗ ratchetAt A x.self G' (x.model F).2) ∗
      consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
      (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStackX ∗ A.pool
     onPanic := (consumeMessageKeySpec F A img).onPanic } : Spec ConsumeMessageKeyGhost).inImage img

def CmkOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr cmkName)
    (cmkSpecX C.F A img)

/-- The low 12,288 bytes `[sp0 - 20480#64 .. sp0 - 8192#64]` that extend `cmkStack` (`8192`) to
`cmkStackX` (`20480`). -/
abbrev cmkLowStack (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 20480#64) 12288

theorem stackAt_cmkStackX_eq_cmkStack_sep_low (sp0 : BitVec 64) :
    stackAt sp0 cmkStackX = stackAt sp0 cmkStack ∗ cmkLowStack sp0 :=
  stackAt_sub_le sp0 cmkStack cmkStackX (by decide) (by decide)

theorem stackAt_7712_sep_low_eq_20000 (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 7712 ∗ cmkLowStack sp0 = stackAt (sp0 - 480#64) 20000 := by
  have h := stackAt_split_bottom (sp0 - 480#64) 7712 12288 (by decide)
  have hsub : sp0 - 480#64 - 20000#64 = sp0 - 20480#64 := by bv_omega
  change stackAt (sp0 - 480#64) 20000 =
    memRegion (sp0 - 480#64 - 20000#64) 12288 ∗ stackAt (sp0 - 480#64) 7712 at h
  rw [hsub, sepConj_comm] at h
  exact h.symm

def cmkLoopHeapX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (s0 : State) : SepProp :=
  ratchetAt A x.self Gc stc ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 20000 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

theorem cmkLoopHeap_sep_low_eq (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (s0 : State) :
    cmkLoopHeap A img x Gc stc ckc s0 ∗ cmkLowStack s0.sp =
      cmkLoopHeapX A img x Gc stc ckc s0 := by
  unfold cmkLoopHeap cmkLoopHeapX
  rw [← stackAt_7712_sep_low_eq_20000 s0.sp]
  ac_rfl

theorem stackAt_20000_split_extHook (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 20000 =
      memRegion (sp0 - 20480#64) 3616 ∗ stackAt (sp0 - 480#64) extHookStack := by
  have h := stackAt_split_bottom (sp0 - 480#64) 16384 3616 (by decide)
  have hsub : sp0 - 480#64 - 20000#64 = sp0 - 20480#64 := by bv_omega
  change stackAt (sp0 - 480#64) 20000 =
    memRegion (sp0 - 480#64 - 20000#64) 3616 ∗ stackAt (sp0 - 480#64) extHookStack at h
  rwa [hsub] at h

theorem stackAt_20000_split_findIndexX (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 20000 =
      memRegion (sp0 - 20480#64) 2592 ∗ stackAt (sp0 - 480#64) findIndexStackX := by
  have h := stackAt_split_bottom (sp0 - 480#64) 17408 2592 (by decide)
  have hsub : sp0 - 480#64 - 20000#64 = sp0 - 20480#64 := by bv_omega
  change stackAt (sp0 - 480#64) 20000 =
    memRegion (sp0 - 480#64 - 20000#64) 2592 ∗ stackAt (sp0 - 480#64) findIndexStackX at h
  rwa [hsub] at h

theorem stackAt_20000_split_hmacX (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 20000 =
      memRegion (sp0 - 20480#64) 1568 ∗ stackAt (sp0 - 480#64) hmacStackX := by
  have h := stackAt_split_bottom (sp0 - 480#64) 18432 1568 (by decide)
  have hsub : sp0 - 480#64 - 20000#64 = sp0 - 20480#64 := by bv_omega
  change stackAt (sp0 - 480#64) 20000 =
    memRegion (sp0 - 480#64 - 20000#64) 1568 ∗ stackAt (sp0 - 480#64) hmacStackX at h
  rwa [hsub] at h

theorem stackAt_20000_split_growOneX (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 20000 =
      memRegion (sp0 - 20480#64) 3104 ∗ stackAt (sp0 - 480#64) Proofs.libsignal.Stage1X.growOneChainStackX := by
  have h := stackAt_split_bottom (sp0 - 480#64) 16896 3104 (by decide)
  have hsub : sp0 - 480#64 - 20000#64 = sp0 - 20480#64 := by bv_omega
  change stackAt (sp0 - 480#64) 20000 =
    memRegion (sp0 - 480#64 - 20000#64) 3104 ∗ stackAt (sp0 - 480#64) Proofs.libsignal.Stage1X.growOneChainStackX at h
  rwa [hsub] at h

def CmkTakeStateX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (R : SepProp)
    (s0 s : State) : Prop :=
  CmkTakeState A img x (cmkLowStack s0.sp ∗ R) s0 s

def CmkTooFarStateX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (R : SepProp)
    (s0 s : State) : Prop :=
  CmkTooFarState A img x (cmkLowStack s0.sp ∗ R) s0 s

def CmkLoopStateX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (R : SepProp)
    (pc : BitVec 64) (s0 s : State) : Prop :=
  CmkLoopState A img x Gc stc ckc (cmkLowStack s0.sp ∗ R) pc s0 s

theorem cmkSpecX_pre_iff {F : ShaCompress} {A : RustAlloc} {img : Obj.Image}
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State) :
    (s0.mem ⊨ (cmkSpecX F A img).pre x s0 ∗ R) ↔
      (s0.mem ⊨ (consumeMessageKeySpec F A img).pre x s0 ∗ (cmkLowStack s0.sp ∗ R)) := by
  dsimp only [cmkSpecX, consumeMessageKeySpec, Spec.inImage]
  rw [stackAt_cmkStackX_eq_cmkStack_sep_low s0.sp]
  constructor <;> (intro h; ac_nf at h ⊢)

theorem cmkSpecX_post_iff {F : ShaCompress} {A : RustAlloc} {img : Obj.Image}
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 sf : State) :
    (sf.mem ⊨ (cmkSpecX F A img).post x s0 sf ∗ R) ↔
      (sf.mem ⊨ (consumeMessageKeySpec F A img).post x s0 sf ∗ (cmkLowStack s0.sp ∗ R)) := by
  dsimp only [cmkSpecX, consumeMessageKeySpec, Spec.inImage]
  rw [stackAt_cmkStackX_eq_cmkStack_sep_low s0.sp]
  constructor <;> (intro h; ac_nf at h ⊢)

theorem cmkSpecX_onPanic_eq {F : ShaCompress} {A : RustAlloc} {img : Obj.Image}
    (x : ConsumeMessageKeyGhost) (s0 sf : State) :
    (cmkSpecX F A img).onPanic x s0 sf = (consumeMessageKeySpec F A img).onPanic x s0 sf := rfl

theorem cmkSpecX_onPanic_of_low {F : ShaCompress} {A : RustAlloc} {img : Obj.Image}
    {x : ConsumeMessageKeyGhost} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 sf ∗ (cmkLowStack s0.sp ∗ R)) :
    sf.mem ⊨ (cmkSpecX F A img).onPanic x s0 sf ∗ R := by
  dsimp only [cmkSpecX, consumeMessageKeySpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hpure, hmem⟩
  refine ⟨hpure, ?_⟩
  have hrearr : anyHeap ∗ (cmkLowStack s0.sp ∗ R) = (anyHeap ∗ cmkLowStack s0.sp) ∗ R := by ac_rfl
  rw [hrearr] at hmem
  exact Satisfies.mono (sepConj_mono_left (anyHeap_sepConj_left (cmkLowStack s0.sp))) hmem

theorem reaches_outcome_cmkSpecX_of_low {prog : Program} {F : ShaCompress} {A : RustAlloc}
    {img : Obj.Image} {x : ConsumeMessageKeyGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog (consumeMessageKeySpec F A img) x (cmkLowStack s0.sp ∗ R) s0 s) :
    reaches_outcome prog (cmkSpecX F A img) x R s0 s := by
  refine h.mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, _, hex_mem⟩ | ⟨_, hoom_mem⟩
  · exact Or.inl ⟨hret, hcc, (cmkSpecX_post_iff x R s0 sf).mpr hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, cmkSpecX_onPanic_of_low hpan_mem⟩)
  · dsimp only [consumeMessageKeySpec, Spec.inImage] at hex_mem
    rw [satisfies_pure_sepConj] at hex_mem
    exact False.elim hex_mem.1
  · dsimp only [consumeMessageKeySpec, Spec.inImage] at hoom_mem
    rw [satisfies_pure_sepConj] at hoom_mem
    exact False.elim hoom_mem.1

/-! ## Segment Contracts S0 through S5 -/

def CmkS0PastSpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
      s0.pc = cmkEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (cmkSpecX F A img).pre x s0 ∗ R) →
      x.counter < x.ck.index →
      reaches_pc (SP2Ext img.base ext) (cmkTakePC img) s0
        (CmkTakeStateX A img x R s0)

def CmkS0TooFarSpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
      s0.pc = cmkEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (cmkSpecX F A img).pre x s0 ∗ R) →
      x.ck.index ≤ x.counter →
      reaches_pc (SP2Ext img.base ext) (cmkTooFarPC img) s0
        (CmkTooFarStateX A img x R s0)

def CmkS0AdvanceEntrySpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
      s0.pc = cmkEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (cmkSpecX F A img).pre x s0 ∗ R) →
      x.ck.index ≤ x.counter →
      (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps →
      let targetPC := if x.ck.index < x.counter then cmkLoopPC img else cmkEpiloguePC img
      reaches_pc (SP2Ext img.base ext) targetPC s0
        (CmkLoopStateX A img x x.G x.st x.ck R targetPC s0)

def CmkS1SpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img → FindIndexOkX img A ext →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.counter < x.ck.index →
      CmkTakeStateX A img x R s0 s →
      reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s

def CmkS2SpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index ≤ x.counter →
      x.st.maxForwardJumps < (x.counter - x.ck.index).toNat →
      CmkTooFarStateX A img x R s0 s →
      reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s

def CmkS3IterSpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    FindIndexOkX img A ext → HmacOkX img F ext → GrowOneChainOkX img A ext →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopStateX A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (SP2Ext img.base ext).CodeLoaded s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC img else cmkEpiloguePC img
      ∃ s', Steps (SP2Ext img.base ext) s s' ∧
        ((∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopStateX A img x G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkSpecX F A img).onPanic x s0 s' ∗ R)))

def CmkS3SpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    FindIndexOkX img A ext → HmacOkX img F ext → GrowOneChainOkX img A ext →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopStateX A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (SP2Ext img.base ext).CodeLoaded s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps (SP2Ext img.base ext) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopStateX A img x G' st_end ck_end R (cmkEpiloguePC img) s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkSpecX F A img).onPanic x s0 s' ∗ R)))

def CmkS4SpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    FindIndexOkX img A ext → HmacOkX img F ext →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      x.counter ≠ BitVec.allOnes 32 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      x.G.AgreeExcept Gc (some ci) →
      (x.model F).1 = .ok (ckc.messageKeys F) →
      (x.model F).2 =
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with chainKey := some (chainStepN F 1 ckc) } } →
      x.touched F = some ci →
      CmkLoopStateX A img x Gc stc ckc R (cmkEpiloguePC img) s0 s →
      reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s

def CmkS5NoChainLoopSpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    FindIndexOkX img A ext → HmacOkX img F ext →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index < x.counter →
      x.st.findReceiverChainIndex x.their = none →
      (x.model F).1 = .error .panic →
      CmkLoopStateX A img x x.G x.st x.ck R (cmkLoopPC img) s0 s →
      reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s

def CmkS5EpiloguePanicSpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    FindIndexOkX img A ext → HmacOkX img F ext →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      (x.counter = BitVec.allOnes 32 ∨ stc.findReceiverChainIndex x.their = none) →
      (x.model F).1 = .error .panic →
      CmkLoopStateX A img x Gc stc ckc R (cmkEpiloguePC img) s0 s →
      reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s

/-! ## Store-Loop Induction and Top-Level Seam Composition -/

private theorem getElem?_set_self {α : Type} {xs : List α} {i : Nat}
    (hi : i < xs.length) (v : α) : (xs.set i v)[i]? = some v := by
  rw [List.getElem?_set_self hi]

private theorem set_set_same {α : Type} (xs : List α) (i : Nat) (u v : α) :
    (xs.set i u).set i v = xs.set i v := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem take_append_take_eq {α : Type} (xs ys : List α) (n : Nat) :
    (xs ++ ys.take n).take n = (xs ++ ys).take n := by
  rw [List.take_append, List.take_append, List.take_take, Nat.min_eq_left (Nat.sub_le n xs.length)]

private theorem s3_loop_ind_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hiter : CmkS3IterSpecX F A ext img)
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) (himg : Obj.Loads libsignalSessionImage img)
    (hfind : FindIndexOkX img A ext) (hhmac : HmacOkX img F ext) (hgrow : GrowOneChainOkX img A ext)
    (x : ConsumeMessageKeyGhost) (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopStateX A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (SP2Ext img.base ext).CodeLoaded s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps (SP2Ext img.base ext) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopStateX A img x G' st_end ck_end R (cmkEpiloguePC img) s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkSpecX F A img).onPanic x s0 s' ∗ R)))
  | 0, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC img else cmkEpiloguePC img) =
        cmkEpiloguePC img := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨G', hG', hst'⟩ | hpan⟩ :=
      hiter hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst'
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, G', hG', ?_⟩⟩
      simpa [chainStepN, skippedKeys] using hst'
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC img else cmkEpiloguePC img) =
        cmkLoopPC img := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨G1, hG1, hst1⟩ | hpan1⟩ :=
      hiter hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | hpan2⟩ :=
        s3_loop_ind_x F A ext img hiter hA himg hfind hhmac hgrow x ci R s0
          k G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1 (hsteps1.codeLoaded hL)
      · refine ⟨s2, hsteps1.trans hsteps2, Or.inl ⟨hck_end, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (Ratchet.chainHmac F ckc.key Ratchet.chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem s3_of_iter_x {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hiter : CmkS3IterSpecX F A ext img) : CmkS3SpecX F A ext img := by
  intro hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 := ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk]
  exact s3_loop_ind_x F A ext img hiter hA himg hfind hhmac hgrow x ci R s0
    k Gc stc ckc chc s hlt hk hci hchc hstate hL

private theorem findReceiverChainIndex_some_getElem? {st : RatchetState} {their : PublicKey}
    {ci : Nat} (h : st.findReceiverChainIndex their = some ci) :
    ∃ ch, st.receiverChains[ci]? = some ch := by
  unfold RatchetState.findReceiverChainIndex at h
  have hlt : ci < st.receiverChains.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
  exact ⟨st.receiverChains[ci], List.getElem?_eq_getElem hlt⟩

theorem cmkEntry_eq_sp2_fnAddr {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkEntry img = (SP2Ext img.base ext).fnAddr cmkName := by
  rw [cmkEntry_eq himg, Program.fnAddr_rebase, cmkName, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]

theorem cmk_of_seams_x {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hfind : FindIndexOkX img A ext)
    (hhmac : HmacOkX img C.F ext)
    (hgrow : GrowOneChainOkX img A ext)
    (hs0_past : CmkS0PastSpecX C.F A ext img)
    (hs0_tooFar : CmkS0TooFarSpecX C.F A ext img)
    (hs0_adv : CmkS0AdvanceEntrySpecX C.F A ext img)
    (hs1 : CmkS1SpecX C.F A ext img)
    (hs2 : CmkS2SpecX C.F A ext img)
    (hs3_iter : CmkS3IterSpecX C.F A ext img)
    (hs4 : CmkS4SpecX C.F A ext img)
    (hs5_loop : CmkS5NoChainLoopSpecX C.F A ext img)
    (hs5_ep : CmkS5EpiloguePanicSpecX C.F A ext img) :
    CmkOkX img C A ext := by
  unfold CmkOkX
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  rw [← cmkEntry_eq_sp2_fnAddr himg ext] at hpc
  have hratchet : s0.mem ⊨ ratchetAt A x.self x.G x.st ∗
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
       ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStackX ∗ A.pool ∗ R) := by
    simp only [cmkSpecX, Spec.inImage] at hpre
    exact Satisfies.of_eq hpre
  have hok : ChainsOk x.st := chainsOk_of_ratchetAt hratchet
  by_cases hlt : x.counter < x.ck.index
  · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
      hs0_past himg x R s0 hpc hrun hsp hpre hlt hL
    · exact LibsignalSession.reaches_outcome_steps hsteps1 (hs1 hA himg hfind x R s0 s1 hlt hst1)
    · exact False.elim hoom
  · have hle : x.ck.index ≤ x.counter := BitVec.not_lt.mp hlt
    by_cases hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps
    · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
        hs0_adv himg x R s0 hpc hrun hsp hpre hle hj hL
      swap; · exact False.elim hoom
      have hL1 := hsteps1.codeLoaded hL
      by_cases hck_lt : x.ck.index < x.counter
      · simp only [hck_lt, ↓reduceIte] at hst1
        cases hci : x.st.findReceiverChainIndex x.their with
        | none =>
          have hpan_model : (x.model C.F).1 = .error .panic :=
            (consumeMessageKey_panic_iff C.F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, Or.inr hci⟩
          exact LibsignalSession.reaches_outcome_steps hsteps1
            (hs5_loop hA himg hfind hhmac x R s0 s1 hck_lt hci hpan_model hst1)
        | some ci =>
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | ⟨hpan2, hq2⟩⟩ :=
            s3_of_iter_x hs3_iter hA himg hfind hhmac hgrow x x.G x.st x.ck ci ch R s0 s1
              hck_lt hci hch hst1 hL1
          · refine LibsignalSession.reaches_outcome_steps (hsteps1.trans hsteps2) ?_
            let n := (x.counter - x.ck.index).toNat
            let ckc := chainStepN C.F n x.ck
            let chc : ReceiverChain :=
              { ch with messageKeys := (skippedKeys C.F n x.ck ++ ch.messageKeys).take maxMessageKeys }
            let stc : RatchetState := { x.st with receiverChains := x.st.receiverChains.set ci chc }
            by_cases hc_max : x.counter = BitVec.allOnes 32
            · have hpan_model : (x.model C.F).1 = .error .panic :=
                (consumeMessageKey_panic_iff C.F x.st x.their x.ck x.counter x.msgType).mpr
                  ⟨hle, hj, Or.inl hc_max⟩
              exact hs5_ep himg hfind hhmac x G2 stc ckc R s0 s2 hck_end (Or.inl hc_max) hpan_model hst2
            · obtain ⟨ch', hch', hmodel⟩ :=
                consumeMessageKey_advance C.F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
              rw [hch] at hch'; cases hch'
              have hci_lt : ci < x.st.receiverChains.length := (List.getElem?_eq_some_iff.mp hch).1
              have hchc_get : stc.receiverChains[ci]? = some chc := getElem?_set_self hci_lt chc
              have hci_stc : stc.findReceiverChainIndex x.their = some ci := by
                rw [findReceiverChainIndex_set x.st x.their ci chc ⟨ch, hch, rfl⟩]
                exact hci
              have hm1 : (x.model C.F).1 = .ok (ckc.messageKeys C.F) := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
              have hm2 : (x.model C.F).2 =
                  { stc with
                    receiverChains := stc.receiverChains.set ci
                      { chc with chainKey := some (chainStepN C.F 1 ckc) } } := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
                dsimp only [stc, chc]
                rw [set_set_same]
              have htouch : x.touched C.F = some ci := by
                unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
              exact hs4 hA himg hfind hhmac x G2 stc ckc ci chc R s0 s2
                hck_end hc_max hci_stc hchc_get hG2 hm1 hm2 htouch hst2
          · exact LibsignalSession.reaches_outcome_steps (hsteps1.trans hsteps2)
              (reaches_outcome_refl_panic hpan2 hq2)
      · simp only [hck_lt, ↓reduceIte] at hst1
        have hck_eq : x.ck.index = x.counter :=
          BitVec.le_antisymm hle (BitVec.not_lt.mp hck_lt)
        by_cases hpan_cond : x.counter = BitVec.allOnes 32 ∨ x.st.findReceiverChainIndex x.their = none
        · have hpan_model : (x.model C.F).1 = .error .panic :=
            (consumeMessageKey_panic_iff C.F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, hpan_cond⟩
          exact LibsignalSession.reaches_outcome_steps hsteps1
            (hs5_ep himg hfind hhmac x x.G x.st x.ck R s0 s1 hck_eq hpan_cond hpan_model hst1)
        · rw [not_or] at hpan_cond
          rcases hpan_cond with ⟨hc_max, hci_ne⟩
          obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hci_ne
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨ch', hch', hmodel⟩ :=
            consumeMessageKey_advance C.F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
          rw [hch] at hch'; cases hch'
          have hn0 : (x.counter - x.ck.index).toNat = 0 := by rw [hck_eq, BitVec.sub_self]; rfl
          have htake : ch.messageKeys.take maxMessageKeys = ch.messageKeys :=
            List.take_of_length_le (hok ch (List.mem_of_getElem? hch)).1
          have hm1 : (x.model C.F).1 = .ok (x.ck.messageKeys C.F) := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]; simp [hn0, chainStepN]
          have hm2 : (x.model C.F).2 =
              { x.st with
                receiverChains := x.st.receiverChains.set ci
                  { ch with chainKey := some (chainStepN C.F 1 x.ck) } } := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]
            simp [hn0, chainStepN, skippedKeys, htake]
          have htouch : x.touched C.F = some ci := by
            unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
          exact LibsignalSession.reaches_outcome_steps hsteps1
            (hs4 hA himg hfind hhmac x x.G x.st x.ck ci ch R s0 s1
              hck_eq hc_max hci hch (RatchetGhost.AgreeExcept.refl x.G (some ci))
              hm1 hm2 htouch hst1)
    · have hj_gt : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat := Nat.lt_of_not_ge hj
      obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
        hs0_tooFar himg x R s0 hpc hrun hsp hpre hle hL
      · exact LibsignalSession.reaches_outcome_steps hsteps1 (hs2 hA himg x R s0 s1 hle hj_gt hst1)
      · exact False.elim hoom

/-! ## Shared Stub and Subroutine Helpers -/

theorem shim_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img) :=
  hA.shim_ok_at name k hk

theorem alloc_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack).inImage img) :=
  hA.alloc_ok_at name k hk

theorem dealloc_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hA.dealloc_ok_at name k hk

theorem session_memmove_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memmove" := by simp only [arm64_norm]) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemmoveSpec extHookStack).inImage img) :=
  hA.session_memmove_ok_at name k hk

theorem find_index_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hfind : FindIndexOkX img A ext)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = 60040) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((findIndexSpecX img A).inImage img) := by
  have haddr : (SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k =
      (SP2Ext img.base ext).fnAddr findIndexName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, findIndexName,
        (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"), BitVec.add_assoc, ← BitVec.ofNat_add, hk]
  rw [haddr]
  exact hfind

theorem hmac_ok_at_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} (hhmac : HmacOkX img F ext)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = 134024) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((hmacSpecX F).inImage img) := by
  have haddr : (SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k =
      (SP2Ext img.base ext).fnAddr hmacName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hmacName,
        (ls_lemma% fnOff "libsignal_protocol::crypto::hmac_sha256"), BitVec.add_assoc, ← BitVec.ofNat_add, hk]
  rw [haddr]
  exact hhmac

theorem grow_one_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hgrow : GrowOneChainOkX img A ext)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = 89260) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((growOneChainSpecX A).inImage img) := by
  have haddr : (SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k =
      (SP2Ext img.base ext).fnAddr growOneChainName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn,
        growOneChainName, (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"), BitVec.add_assoc, ← BitVec.ofNat_add, hk]
  rw [haddr]
  exact hgrow

theorem panic_at_handle_error_x {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "alloc::raw_vec::handle_error")) :
    (SP2Ext b ext).externAt? ((SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by simp only [arm64_norm]) (ls_hook% "alloc::raw_vec::handle_error")
    (by simp [Rust.isPanicSymbol])

theorem panic_at_expect_failed_x {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "core::option::expect_failed")) :
    (SP2Ext b ext).externAt? ((SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by simp only [arm64_norm]) (ls_hook% "core::option::expect_failed")
    (by simp [Rust.isPanicSymbol])

theorem panic_at_add_overflow_x {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow")) :
    (SP2Ext b ext).externAt? ((SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by decide)
    (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
    (by simp [Rust.isPanicSymbol])

end Proofs.libsignal.Stage1X.CmkX
