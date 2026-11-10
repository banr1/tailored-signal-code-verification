/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `ChainKey::message_keys` (Block `38`)

Defines the `messageKeysEvents` (`rustAllocEvents 32 1`) allocation envelope and verifies
`<libsignal_protocol::ratchet::keys::ChainKey>::message_keys` (Block `38`) against
`messageKeysPlacedSpec{,WithStack,X}` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝` under
`FitsEnv M lim st MessageKeysEnv`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState hmacWith keyToBytes32 sha256With toBEBytes)
open CryptoGames.LibsignalSession (ChainKey ShaCompress)
open CryptoVerification (
  LibsignalPlacement LibsignalCodeLoaded lsmpl blkPC_38 blkPl_38 lsρ
  ls_hook_ok_of_mem withLsCodeLoaded extract_withLsCodeLoaded
)
open CryptoVerification.RustHeap (
  allocHookStack memRegion_24_eq_exists_vecHeader vecHeader
)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes leBytes)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalTripleRatchet (
  ChainKeyGhost extHookStack messageKeysStack messageKeysStackX mkgAt
  lsRustNoAllocShimSym lsRustAllocSym
  noAllocShimSpec shimSpecWithStack hmacSpecWithStack
  hmacWith_one_eq_messageKeys_seed mkgAt_of_parts
  LibsignalCodeRoLoaded withLsCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  withStack subroutine_ok_withStack_of_subroutine_ok
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Allocation Envelope & Relocatable Specifications -/

/-- Deterministic `AllocEvent` list emitted by `ChainKey::message_keys` (`32`-byte seed `Vec<u8>`). -/
def messageKeysEvents : List AllocEvent :=
  rustAllocEvents 32 1

def MessageKeysEnv (evs : List AllocEvent) : Prop :=
  evs = messageKeysEvents

theorem messageKeysEnv_events : MessageKeysEnv messageKeysEvents := rfl

theorem fitsEvents_messageKeys_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (h : FitsEnv M lim st MessageKeysEnv) :
    FitsEvents M lim st messageKeysEvents :=
  h messageKeysEvents rfl

def messageKeysPlacedSpecWithStack {M : AllocCostModel} (F : ShaCompress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (totalStack : Nat) :
    Spec (ChainKeyGhost × M.σ) where
  pre := fun ((self, ck, ret), st) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret ∧ FitsEnv M lim st MessageKeysEnv⌝ ∗
      (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗
      A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun ((self, ck, ret), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ MessageKeysEnv evs⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ mkgAt A.repAlloc ret (ck.messageKeys F) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp totalStack

abbrev messageKeysPlacedSpec {M : AllocCostModel} (F : ShaCompress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (ChainKeyGhost × M.σ) :=
  messageKeysPlacedSpecWithStack F A lim messageKeysStack

abbrev messageKeysPlacedSpecX {M : AllocCostModel} (F : ShaCompress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (ChainKeyGhost × M.σ) :=
  messageKeysPlacedSpecWithStack F A lim messageKeysStackX

/-! ## 2. Private Stack & Region Framing Helpers -/

private theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

private theorem pointsToBytes_chainKeyBytes_eq (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

@[local simp] private theorem toBEBytes_length (n : Nat) (w : BitVec (8 * n)) :
    (toBEBytes n w).length = n := by
  simp [toBEBytes]

@[local simp] private theorem shaState_flatMap_length (h : ShaState) :
    (h.toList.flatMap (toBEBytes 4)).length = 32 := by
  rcases h with ⟨l, hl⟩
  simp [List.length_flatMap, hl]

private theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : (hmacWith F key msg).length = 32 := by
  unfold hmacWith sha256With
  exact shaState_flatMap_length _

private theorem length_messageKeys_seed (F : ShaState → List (BitVec 8) → ShaState)
    (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  rw [← hmacWith_one_eq_messageKeys_seed]
  exact length_hmacWith F _ _

private theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

private theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

private theorem stackAt_80_messageKeys (sp : BitVec 64) :
    stackAt sp 80 =
      memRegion (sp - 80#64) 32 ∗
      (∃∗ v : BitVec 64, (sp - 48#64) ↦₆₄ v) ∗
      (∃∗ v : BitVec 64, (sp - 40#64) ↦₆₄ v) ∗
      (∃∗ v : BitVec 64, (sp - 32#64) ↦₆₄ v) ∗
      memRegion (sp - 24#64) 4 ∗
      (∃∗ b : BitVec 8, (sp - 20#64) ↦₈ b) ∗
      memRegion (sp - 19#64) 3 ∗
      (∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v) ∗
      (∃∗ v : BitVec 64, (sp - 8#64) ↦₆₄ v) := by
  show memRegion (sp - BitVec.ofNat 64 80) 80 = _
  rw [mr_cut' sp 80 48 32 48 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 20 4 20 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 20 19 1 19 20 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 19 16 3 16 19 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64), memRegion_eight (sp - 32#64),
      memRegion_one (sp - 20#64), memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

private theorem stackAt_80_messageKeys_repack (sp : BitVec 64)
    (w0 w1 w2 w3 v29 v30 v21 v20 v19 : BitVec 64) (b0 : BitVec 8) :
    ((sp - 80#64) ↦₆₄ w0) ∗
    ((sp - 72#64) ↦₆₄ w1) ∗
    ((sp - 64#64) ↦₆₄ w2) ∗
    ((sp - 56#64) ↦₆₄ w3) ∗
    ((sp - 48#64) ↦₆₄ v29) ∗
    ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗
    memRegion (sp - 24#64) 4 ∗
    ((sp - 20#64) ↦₈ b0) ∗
    memRegion (sp - 19#64) 3 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp 80 := by
  rw [stackAt_80_messageKeys sp]
  have hw0 := pointsTo64_entails_memRegion (sp - 80#64) w0
  have hw1 := pointsTo64_entails_memRegion (sp - 72#64) w1
  have hw2 := pointsTo64_entails_memRegion (sp - 64#64) w2
  have hw3 := pointsTo64_entails_memRegion (sp - 56#64) w3
  have h72 : sp - 80#64 + 8#64 = sp - 72#64 := by bv_arith
  have h64 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_arith
  have h56 : sp - 64#64 + 8#64 = sp - 56#64 := by bv_arith
  have h32 :
      ((sp - 80#64) ↦₆₄ w0) ∗ ((sp - 72#64) ↦₆₄ w1) ∗ ((sp - 64#64) ↦₆₄ w2) ∗ ((sp - 56#64) ↦₆₄ w3) ⊢
        memRegion (sp - 80#64) 32 := by
    refine Entails.trans (sepConj_mono hw0 (sepConj_mono hw1 (sepConj_mono hw2 hw3))) ?_
    rw [← h56, ← memRegion_split (sp - 64#64) 8 8 (by decide),
        ← h64, ← memRegion_split (sp - 72#64) 8 16 (by decide),
        ← h72, ← memRegion_split (sp - 80#64) 8 24 (by decide)]
    exact Entails.refl _
  have hv29 : ((sp - 48#64) ↦₆₄ v29) ⊢ ∃∗ v : BitVec 64, (sp - 48#64) ↦₆₄ v :=
    Entails.sepExists_right v29 (Entails.refl _)
  have hv30 : ((sp - 40#64) ↦₆₄ v30) ⊢ ∃∗ v : BitVec 64, (sp - 40#64) ↦₆₄ v :=
    Entails.sepExists_right v30 (Entails.refl _)
  have hv21 : ((sp - 32#64) ↦₆₄ v21) ⊢ ∃∗ v : BitVec 64, (sp - 32#64) ↦₆₄ v :=
    Entails.sepExists_right v21 (Entails.refl _)
  have hb0 : ((sp - 20#64) ↦₈ b0) ⊢ ∃∗ b : BitVec 8, (sp - 20#64) ↦₈ b :=
    Entails.sepExists_right b0 (Entails.refl _)
  have hv20 : ((sp - 16#64) ↦₆₄ v20) ⊢ ∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v :=
    Entails.sepExists_right v20 (Entails.refl _)
  have hv19 : ((sp - 8#64) ↦₆₄ v19) ⊢ ∃∗ v : BitVec 64, (sp - 8#64) ↦₆₄ v :=
    Entails.sepExists_right v19 (Entails.refl _)
  have hpull :
      (((sp - 80#64) ↦₆₄ w0) ∗
        ((sp - 72#64) ↦₆₄ w1) ∗
        ((sp - 64#64) ↦₆₄ w2) ∗
        ((sp - 56#64) ↦₆₄ w3) ∗
        ((sp - 48#64) ↦₆₄ v29) ∗
        ((sp - 40#64) ↦₆₄ v30) ∗
        ((sp - 32#64) ↦₆₄ v21) ∗
        memRegion (sp - 24#64) 4 ∗
        ((sp - 20#64) ↦₈ b0) ∗
        memRegion (sp - 19#64) 3 ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) =
      ((((sp - 80#64) ↦₆₄ w0) ∗ ((sp - 72#64) ↦₆₄ w1) ∗
         ((sp - 64#64) ↦₆₄ w2) ∗ ((sp - 56#64) ↦₆₄ w3)) ∗
        ((sp - 48#64) ↦₆₄ v29) ∗
        ((sp - 40#64) ↦₆₄ v30) ∗
        ((sp - 32#64) ↦₆₄ v21) ∗
        memRegion (sp - 24#64) 4 ∗
        ((sp - 20#64) ↦₈ b0) ∗
        memRegion (sp - 19#64) 3 ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) := by sep_ac_rfl
  rw [hpull]
  exact sepConj_mono h32 (sepConj_mono hv29 (sepConj_mono hv30 (sepConj_mono hv21
    (sepConj_mono_right (sepConj_mono hb0 (sepConj_mono_right
      (sepConj_mono hv20 hv19)))))))

private theorem stackAt_gen_split (sp : BitVec 64) (totalStack midStack padTop : Nat)
    (htot : (80 + midStack) + padTop = totalStack) (hbound : totalStack ≤ 2 ^ 64) :
    stackAt sp totalStack =
      memRegion (sp - BitVec.ofNat 64 totalStack) padTop ∗
      stackAt (sp - 80#64) midStack ∗
      stackAt sp 80 := by
  subst htot
  rw [stackAt_split_bottom sp (80 + midStack) padTop hbound,
      stackAt_split_bottom sp 80 midStack (by omega)]
  have hsub : sp - BitVec.ofNat 64 (80 + midStack) = sp - 80#64 - BitVec.ofNat 64 midStack := by
    rw [BitVec.ofNat_add]
    bv_arith
  have hm : memRegion (sp - BitVec.ofNat 64 (80 + midStack)) midStack =
      stackAt (sp - 80#64) midStack := by
    unfold stackAt
    rw [hsub]
  rw [hm]

private theorem stackAt_sub_split (sp : BitVec 64) (subStack subPad midStack : Nat)
    (h : subStack + subPad = midStack) (hb : midStack ≤ 2 ^ 64) :
    stackAt sp midStack =
      memRegion (sp - BitVec.ofNat 64 midStack) subPad ∗ stackAt sp subStack := by
  subst h
  exact stackAt_split_bottom sp subStack subPad hb

private theorem stackAt_gen_repack (sp : BitVec 64)
    (totalStack midStack padTop allocStack allocPad : Nat)
    (htot : (80 + midStack) + padTop = totalStack)
    (ha : allocStack + allocPad = midStack)
    (hb : totalStack ≤ 2 ^ 64)
    (w0 w1 w2 w3 v29 v30 v21 v20 v19 : BitVec 64) (b0 : BitVec 8) :
    memRegion (sp - BitVec.ofNat 64 totalStack) padTop ∗
    memRegion (sp - 80#64 - BitVec.ofNat 64 midStack) allocPad ∗
    stackAt (sp - 80#64) allocStack ∗
    ((sp - 80#64) ↦₆₄ w0) ∗
    ((sp - 72#64) ↦₆₄ w1) ∗
    ((sp - 64#64) ↦₆₄ w2) ∗
    ((sp - 56#64) ↦₆₄ w3) ∗
    ((sp - 48#64) ↦₆₄ v29) ∗
    ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗
    memRegion (sp - 24#64) 4 ∗
    ((sp - 20#64) ↦₈ b0) ∗
    memRegion (sp - 19#64) 3 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp totalStack := by
  rw [stackAt_gen_split sp totalStack midStack padTop htot hb,
      stackAt_sub_split (sp - 80#64) allocStack allocPad midStack ha (by omega),
      sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (stackAt_80_messageKeys_repack sp w0 w1 w2 w3 v29 v30 v21 v20 v19 b0)))

private theorem remerge_and_split_midStack (sp : BitVec 64)
    (hmacStack hmacPad allocStack allocPad midStack : Nat)
    (hh : hmacStack + hmacPad = midStack) (ha : allocStack + allocPad = midStack)
    (hb : midStack ≤ 2 ^ 64)
    (P1 P2 P3 P4 P5 P6 P7 P8 : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ stackAt sp hmacStack ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗
        memRegion (sp - BitVec.ofNat 64 midStack) hmacPad ∗ P8 =
      memRegion (sp - BitVec.ofNat 64 midStack) allocPad ∗ stackAt sp allocStack ∗
        P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 := by
  have h1 : memRegion (sp - BitVec.ofNat 64 midStack) hmacPad ∗ stackAt sp hmacStack =
      stackAt sp midStack :=
    (stackAt_sub_split sp hmacStack hmacPad midStack hh hb).symm
  have h2 : stackAt sp midStack =
      memRegion (sp - BitVec.ofNat 64 midStack) allocPad ∗ stackAt sp allocStack :=
    stackAt_sub_split sp allocStack allocPad midStack ha hb
  calc
    _ = (memRegion (sp - BitVec.ofNat 64 midStack) hmacPad ∗ stackAt sp hmacStack) ∗
          (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8) := by sep_ac_rfl
    _ = (memRegion (sp - BitVec.ofNat 64 midStack) allocPad ∗ stackAt sp allocStack) ∗
          (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8) := by rw [h1, h2]
    _ = _ := by sep_ac_rfl

private theorem memRegion40_unpack (r : BitVec 64) :
    memRegion r 40 =
      (∃∗ t0 : BitVec 32, (r ↦₃₂ t0)) ∗
      memRegion (r + 4#64) 4 ∗
      (∃∗ c0 : BitVec 64, ((r + 8#64) ↦₆₄ c0)) ∗
      (∃∗ p0 : BitVec 64, ((r + 16#64) ↦₆₄ p0)) ∗
      (∃∗ l0 : BitVec 64, ((r + 24#64) ↦₆₄ l0)) ∗
      (∃∗ i0 : BitVec 32, ((r + 32#64) ↦₃₂ i0)) ∗
      memRegion (r + 36#64) 4 := by
  rw [show memRegion r 40 = memRegion r 4 ∗ memRegion (r + 4#64) 36 from
        memRegion_split r 4 36 (by decide),
      show memRegion (r + 4#64) 36 = memRegion (r + 4#64) 4 ∗ memRegion (r + 4#64 + 4#64) 32 from
        memRegion_split (r + 4#64) 4 32 (by decide)]
  have h8 : r + 4#64 + 4#64 = r + 8#64 := by bv_arith
  rw [h8, show memRegion (r + 8#64) 32 = memRegion (r + 8#64) 8 ∗ memRegion (r + 8#64 + 8#64) 24 from
        memRegion_split (r + 8#64) 8 24 (by decide)]
  have h16 : r + 8#64 + 8#64 = r + 16#64 := by bv_arith
  rw [h16, show memRegion (r + 16#64) 24 = memRegion (r + 16#64) 8 ∗ memRegion (r + 16#64 + 8#64) 16 from
        memRegion_split (r + 16#64) 8 16 (by decide)]
  have h24 : r + 16#64 + 8#64 = r + 24#64 := by bv_arith
  rw [h24, show memRegion (r + 24#64) 16 = memRegion (r + 24#64) 8 ∗ memRegion (r + 24#64 + 8#64) 8 from
        memRegion_split (r + 24#64) 8 8 (by decide)]
  have h32 : r + 24#64 + 8#64 = r + 32#64 := by bv_arith
  rw [h32, show memRegion (r + 32#64) 8 = memRegion (r + 32#64) 4 ∗ memRegion (r + 32#64 + 4#64) 4 from
        memRegion_split (r + 32#64) 4 4 (by decide)]
  have h36 : r + 32#64 + 4#64 = r + 36#64 := by bv_arith
  rw [h36, memRegion_four r, memRegion_eight (r + 8#64), memRegion_eight (r + 16#64),
      memRegion_eight (r + 24#64), memRegion_four (r + 32#64)]

private theorem memRegion32_eq_exists_cells4 (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) := by
  rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split a 8 24 (by decide),
      memRegion_eight a, memRegion_24_eq_exists_vecHeader (a + 8#64)]
  unfold vecHeader
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_arith
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_arith
  rw [h16, h24, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext d0
  rw [sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext d1
  rw [sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext d2
  rw [sepExists_sepConj_right]

/-! ## 3. Callee Wrappers & `SepWP` Proof (Block `38`) -/

private theorem shimVmWithStack_of_noAllocShimVm {prog : Program} {addr : BitVec 64}
    (hookStack : Nat)
    (h : subroutine_ok prog addr (withVmPreserved noAllocShimSpec)) :
    subroutine_ok prog addr (withVmPreserved (shimSpecWithStack hookStack)) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack (withVmPreserved noAllocShimSpec) hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      withVmPreserved, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine h'.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      withVmPreserved, noAllocShimSpec, shimSpecWithStack] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact Or.inr hrest

private theorem sepWP_seq_lscl {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWP prog tgt sm Pm Q)) :
    SepWP prog tgt s P Q :=
  SepWP.seq_frozen (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h

private theorem hmacVmWithStack_placed_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState} {hmacStack : Nat} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacSpecWithStack F hmacStack))))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp hmacStack
        post := (withVmPreserved (hmacSpecWithStack F hmacStack)).post } := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine hhmac.mono_outcome (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp (fun _ hout => hout)
  dsimp only [withLsCodeLoaded, withVmPreserved, hmacSpecWithStack] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

private theorem hmacVmWithStack_placed_cro_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState} {hmacStack : Nat} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpecWithStack F hmacStack))))
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp hmacStack
        post := (withVmPreserved (hmacSpecWithStack F hmacStack)).post } := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeRoLoaded, withVmPreserved, hmacSpecWithStack] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

set_option maxHeartbeats 800000 in
theorem message_keys_placed_ok_gen [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaCompress} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {totalStack midStack padTop hmacStack hmacPad allocStack allocPad : Nat}
    (htot : (80 + midStack) + padTop = totalStack := by decide)
    (htot64 : totalStack ≤ 2 ^ 64 := by decide)
    (hhmac_pad : hmacStack + hmacPad = midStack := by decide)
    (halloc_pad : allocStack + allocPad = midStack := by decide)
    (hhmac_at : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacSpecWithStack F hmacStack))))
    (hshim_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustNoAllocShimSym)
      (withVmPreserved (shimSpecWithStack allocStack)))
    (halloc_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocStack)) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeLoaded lsmpl (messageKeysPlacedSpecWithStack F A lim totalStack)) := by
  have hshim := hshim_in
  dsimp only [withVmPreserved, shimSpecWithStack] at hshim
  have halloc := halloc_in
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc
  refine subroutine_ok_of_sepWP fun ⟨⟨self, ck, ret⟩, stB⟩ R s0 hpc hrun hpre hsp0 => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [messageKeysPlacedSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hEnv⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool lim stB s0 ∗
    stackAt s0.sp totalStack, R, by simpa [sepConj_assoc] using hmem, ?_⟩
  rw [pointsToBytes_chainKeyBytes_eq self ck,
      stackAt_gen_split s0.sp totalStack midStack padTop htot htot64,
      stackAt_sub_split (s0.sp - 80#64) hmacStack hmacPad midStack hhmac_pad (by omega),
      stackAt_80_messageKeys s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun v19 => SepWP.exists_elim fun v20 =>
    SepWP.exists_elim fun b0 => SepWP.exists_elim fun v21 =>
    SepWP.exists_elim fun v30 => SepWP.exists_elim fun v29 => ?_
  apply sepWP_seq_lscl (mid := lsmpl.base 73) hcl0
  wp_steps_sync_pool (lsmpl.base 73)
  simp only [State.setMem_setMem]
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmacVmWithStack_placed_ok_at_state hhmac_at hcl1
  dsimp only [withVmPreserved, hmacSpecWithStack] at hhmac1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 20#64) 1#8]
  wp_call hhmac1 (s0.sp - 80#64, self, keyToBytes32 ck.key, s0.sp - 20#64, [1#8])
  have htr_hmac : sf.trace = s0.trace := by assumption
  have hsp_hmac : sf.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  rw [hmacWith_one_eq_messageKeys_seed F ck]
  obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
    exists_unpack64_of_length_32 (length_messageKeys_seed F ck)
  have hw_sp := hw32 (s0.sp - 80#64)
  have h72 : s0.sp - 80#64 + 8#64 = s0.sp - 72#64 := by bv_arith
  have h64 : s0.sp - 80#64 + 16#64 = s0.sp - 64#64 := by bv_arith
  have h56 : s0.sp - 80#64 + 24#64 = s0.sp - 56#64 := by bv_arith
  rw [h72, h64, h56] at hw_sp
  wp_simp_pre only [hsp_hmac]
  conv =>
    arg 4
    rw [hw_sp]
  have hmid_eq :
      A.pool lim stB sf ∗
        (((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
         ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3)) ∗
        (self ↦ₛ keyToBytes32 ck.key) ∗ ((s0.sp - 20#64) ↦₈ 1#8) ∗
        stackAt (s0.sp - 80#64) hmacStack ∗
        ((self + 32#64) ↦₃₂ ck.index) ∗ memRegion ret 40 ∗
        memRegion (s0.sp - BitVec.ofNat 64 totalStack) padTop ∗
        memRegion (s0.sp - 80#64 - BitVec.ofNat 64 midStack) hmacPad ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
         memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19)) =
      A.pool lim stB sf ∗
        memRegion (s0.sp - 80#64 - BitVec.ofNat 64 midStack) allocPad ∗
        stackAt (s0.sp - 80#64) allocStack ∗
        ((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
        ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3) ∗
        (self ↦ₛ keyToBytes32 ck.key) ∗ ((s0.sp - 20#64) ↦₈ 1#8) ∗
        ((self + 32#64) ↦₃₂ ck.index) ∗ memRegion ret 40 ∗
        memRegion (s0.sp - BitVec.ofNat 64 totalStack) padTop ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
        memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19) := by
    have hr := remerge_and_split_midStack (s0.sp - 80#64) hmacStack hmacPad allocStack allocPad
      midStack hhmac_pad halloc_pad (by omega)
      (((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
       ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3))
      (self ↦ₛ keyToBytes32 ck.key)
      ((s0.sp - 20#64) ↦₈ 1#8)
      ((self + 32#64) ↦₃₂ ck.index)
      (memRegion ret 40)
      (memRegion (s0.sp - BitVec.ofNat 64 totalStack) padTop)
      (A.pool lim stB sf)
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
       ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
       memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19))
    exact Eq.trans (by sep_ac_rfl) (Eq.trans hr (by sep_ac_rfl))
  refine SepWP.weaken_pre (Entails.of_eq hmid_eq) ?_
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_shim : sf_1.trace = sf.trace := by assumption
  have hsp_shim : sf_1.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_simp_pre only [hsp_shim]
  have hfe_alloc : FitsEvents M lim stB [.alloc 32] := by
    simpa [messageKeysEvents, rustAllocEvents] using
      fitsEvents_messageKeys_of_fitsEnv M lim stB hEnv
  rcases hfe_alloc with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (32, 1, stB)
  have hne0 : sf_2.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hbeq0 : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  have htr_alloc : sf_2.trace = sf_1.trace := by assumption
  have hsp_alloc : sf_2.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre only [hsp_alloc, memRegion40_unpack ret,
    memRegion32_eq_exists_cells4 (sf_2.readReg64 Reg.x0),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun d0 => SepWP.exists_elim fun d1 =>
    SepWP.exists_elim fun d2 => SepWP.exists_elim fun d3 =>
    SepWP.exists_elim fun t0 => SepWP.exists_elim fun c0 =>
    SepWP.exists_elim fun p0 => SepWP.exists_elim fun l0 =>
    SepWP.exists_elim fun i0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  refine SepWP.done (by simp_all) (by simp_all) ⟨fun hm => ?_, ?_, ?_⟩
  · refine Satisfies.mono (sepConj_mono_left ?_) hm
    refine Entails.sepExists_right messageKeysEvents ?_
    have htr_all : sf_2.trace = s0.trace := by rw [htr_alloc, htr_shim, htr_hmac]
    refine Entails.pure_right ⟨htr_all, rfl⟩ ?_
    rw [pointsToBytes_chainKeyBytes_eq self ck]
    have hmkg := mkgAt_of_parts A.repAlloc ret (sf_2.readReg64 Reg.x0) (ck.messageKeys F)
      (length_messageKeys_seed F ck) hne0
    rw [hw32 (sf_2.readReg64 Reg.x0), A.repAlloc_live_norm] at hmkg
    have hstk := stackAt_gen_repack s0.sp totalStack midStack padTop allocStack allocPad
      htot halloc_pad htot64 w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 1#8
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono hmkg (sepConj_mono_right hstk)))
    exact Entails.of_eq (by
      dsimp only [ChainKey.messageKeys, messageKeysEvents, Reg.x0, Reg.x19, Reg.x20, Reg.x21,
        Reg.lr, Reg.x29]
      sep_ac_rfl)
  · simp only [wp_norm, arm64_norm, *]
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem message_keys_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaCompress} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacSpec F))))
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeLoaded lsmpl (messageKeysPlacedSpec F A lim)) :=
  message_keys_placed_ok_gen
    (totalStack := messageKeysStack) (midStack := 4096) (padTop := 4016)
    (hmacStack := 2048) (hmacPad := 2048) (allocStack := allocHookStack) (allocPad := 0)
    (by decide) (by decide) (by decide) (by decide)
    hhmac
    (shimVmWithStack_of_noAllocShimVm allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem message_keys_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaCompress} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacSpec F))))
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeLoaded lsmpl (messageKeysPlacedSpecX F A lim)) :=
  message_keys_placed_ok_gen
    (totalStack := messageKeysStackX) (midStack := extHookStack) (padTop := 4016)
    (hmacStack := 2048) (hmacPad := 14336) (allocStack := extHookStack) (allocPad := 0)
    (by decide) (by decide) (by decide) (by decide)
    hhmac
    (shimVmWithStack_of_noAllocShimVm extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := extHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

set_option maxHeartbeats 800000 in
theorem message_keys_placed_cro_ok_gen [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaCompress} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {totalStack midStack padTop hmacStack hmacPad allocStack allocPad : Nat}
    (htot : (80 + midStack) + padTop = totalStack := by decide)
    (htot64 : totalStack ≤ 2 ^ 64 := by decide)
    (hhmac_pad : hmacStack + hmacPad = midStack := by decide)
    (halloc_pad : allocStack + allocPad = midStack := by decide)
    (hhmac_at : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpecWithStack F hmacStack))))
    (hshim_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustNoAllocShimSym)
      (withVmPreserved (shimSpecWithStack allocStack)))
    (halloc_in : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocStack)) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpecWithStack F A lim totalStack)) := by
  have hshim := hshim_in
  dsimp only [withVmPreserved, shimSpecWithStack] at hshim
  have halloc := halloc_in
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc
  refine subroutine_ok_of_sepWP fun ⟨⟨self, ck, ret⟩, stB⟩ R s0 hpc hrun hpre hsp0 => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [messageKeysPlacedSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hEnv⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool lim stB s0 ∗
    stackAt s0.sp totalStack, R, by simpa [sepConj_assoc] using hmem, ?_⟩
  rw [pointsToBytes_chainKeyBytes_eq self ck,
      stackAt_gen_split s0.sp totalStack midStack padTop htot htot64,
      stackAt_sub_split (s0.sp - 80#64) hmacStack hmacPad midStack hhmac_pad (by omega),
      stackAt_80_messageKeys s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun v19 => SepWP.exists_elim fun v20 =>
    SepWP.exists_elim fun b0 => SepWP.exists_elim fun v21 =>
    SepWP.exists_elim fun v30 => SepWP.exists_elim fun v29 => ?_
  apply sepWP_seq_lscro (mid := lsmpl.base 73) hcl0
  wp_steps_sync_pool (lsmpl.base 73)
  simp only [State.setMem_setMem]
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmacVmWithStack_placed_cro_ok_at_state hhmac_at hcl1
  dsimp only [withVmPreserved, hmacSpecWithStack] at hhmac1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 20#64) 1#8]
  wp_call hhmac1 (s0.sp - 80#64, self, keyToBytes32 ck.key, s0.sp - 20#64, [1#8])
  have htr_hmac : sf.trace = s0.trace := by assumption
  have hsp_hmac : sf.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  rw [hmacWith_one_eq_messageKeys_seed F ck]
  obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
    exists_unpack64_of_length_32 (length_messageKeys_seed F ck)
  have hw_sp := hw32 (s0.sp - 80#64)
  have h72 : s0.sp - 80#64 + 8#64 = s0.sp - 72#64 := by bv_arith
  have h64 : s0.sp - 80#64 + 16#64 = s0.sp - 64#64 := by bv_arith
  have h56 : s0.sp - 80#64 + 24#64 = s0.sp - 56#64 := by bv_arith
  rw [h72, h64, h56] at hw_sp
  wp_simp_pre only [hsp_hmac]
  conv =>
    arg 4
    rw [hw_sp]
  have hmid_eq :
      A.pool lim stB sf ∗
        (((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
         ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3)) ∗
        (self ↦ₛ keyToBytes32 ck.key) ∗ ((s0.sp - 20#64) ↦₈ 1#8) ∗
        stackAt (s0.sp - 80#64) hmacStack ∗
        ((self + 32#64) ↦₃₂ ck.index) ∗ memRegion ret 40 ∗
        memRegion (s0.sp - BitVec.ofNat 64 totalStack) padTop ∗
        memRegion (s0.sp - 80#64 - BitVec.ofNat 64 midStack) hmacPad ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
         memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19)) =
      A.pool lim stB sf ∗
        memRegion (s0.sp - 80#64 - BitVec.ofNat 64 midStack) allocPad ∗
        stackAt (s0.sp - 80#64) allocStack ∗
        ((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
        ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3) ∗
        (self ↦ₛ keyToBytes32 ck.key) ∗ ((s0.sp - 20#64) ↦₈ 1#8) ∗
        ((self + 32#64) ↦₃₂ ck.index) ∗ memRegion ret 40 ∗
        memRegion (s0.sp - BitVec.ofNat 64 totalStack) padTop ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
        memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19) := by
    have hr := remerge_and_split_midStack (s0.sp - 80#64) hmacStack hmacPad allocStack allocPad
      midStack hhmac_pad halloc_pad (by omega)
      (((s0.sp - 80#64) ↦₆₄ w0) ∗ ((s0.sp - 72#64) ↦₆₄ w1) ∗
       ((s0.sp - 64#64) ↦₆₄ w2) ∗ ((s0.sp - 56#64) ↦₆₄ w3))
      (self ↦ₛ keyToBytes32 ck.key)
      ((s0.sp - 20#64) ↦₈ 1#8)
      ((self + 32#64) ↦₃₂ ck.index)
      (memRegion ret 40)
      (memRegion (s0.sp - BitVec.ofNat 64 totalStack) padTop)
      (A.pool lim stB sf)
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
       ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
       memRegion (s0.sp - 24#64) 4 ∗ memRegion (s0.sp - 19#64) 3 ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19))
    exact Eq.trans (by sep_ac_rfl) (Eq.trans hr (by sep_ac_rfl))
  refine SepWP.weaken_pre (Entails.of_eq hmid_eq) ?_
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_shim : sf_1.trace = sf.trace := by assumption
  have hsp_shim : sf_1.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_simp_pre only [hsp_shim]
  have hfe_alloc : FitsEvents M lim stB [.alloc 32] := by
    simpa [messageKeysEvents, rustAllocEvents] using
      fitsEvents_messageKeys_of_fitsEnv M lim stB hEnv
  rcases hfe_alloc with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (32, 1, stB)
  have hne0 : sf_2.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hbeq0 : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  have htr_alloc : sf_2.trace = sf_1.trace := by assumption
  have hsp_alloc : sf_2.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre only [hsp_alloc, memRegion40_unpack ret,
    memRegion32_eq_exists_cells4 (sf_2.readReg64 Reg.x0),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun d0 => SepWP.exists_elim fun d1 =>
    SepWP.exists_elim fun d2 => SepWP.exists_elim fun d3 =>
    SepWP.exists_elim fun t0 => SepWP.exists_elim fun c0 =>
    SepWP.exists_elim fun p0 => SepWP.exists_elim fun l0 =>
    SepWP.exists_elim fun i0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  refine SepWP.done (by simp_all) (by simp_all) ⟨fun hm => ?_, ?_, ?_⟩
  · refine Satisfies.mono (sepConj_mono_left ?_) hm
    refine Entails.sepExists_right messageKeysEvents ?_
    have htr_all : sf_2.trace = s0.trace := by rw [htr_alloc, htr_shim, htr_hmac]
    refine Entails.pure_right ⟨htr_all, rfl⟩ ?_
    rw [pointsToBytes_chainKeyBytes_eq self ck]
    have hmkg := mkgAt_of_parts A.repAlloc ret (sf_2.readReg64 Reg.x0) (ck.messageKeys F)
      (length_messageKeys_seed F ck) hne0
    rw [hw32 (sf_2.readReg64 Reg.x0), A.repAlloc_live_norm] at hmkg
    have hstk := stackAt_gen_repack s0.sp totalStack midStack padTop allocStack allocPad
      htot halloc_pad htot64 w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 1#8
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono hmkg (sepConj_mono_right hstk)))
    exact Entails.of_eq (by
      dsimp only [ChainKey.messageKeys, messageKeysEvents, Reg.x0, Reg.x19, Reg.x20, Reg.x21,
        Reg.lr, Reg.x29]
      sep_ac_rfl)
  · simp only [wp_norm, arm64_norm, *]
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem message_keys_placed_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaCompress} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec F))))
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_38).rebase (blkPl_38).base H) (blkPl_38).base
      (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec F A lim)) :=
  message_keys_placed_cro_ok_gen
    (totalStack := messageKeysStack) (midStack := 4096) (padTop := 4016)
    (hmacStack := 2048) (hmacPad := 2048) (allocStack := allocHookStack) (allocPad := 0)
    (by decide) (by decide) (by decide) (by decide)
    hhmac
    (shimVmWithStack_of_noAllocShimVm allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

end LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget
