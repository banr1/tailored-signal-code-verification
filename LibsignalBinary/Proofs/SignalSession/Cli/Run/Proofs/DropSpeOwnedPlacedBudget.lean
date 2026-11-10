/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Drop Glue Proof for Owned `SignalProtocolError`

Proves the `RustCliAllocBudget M` contract `DropSpeOwnedOkPlaced` for
`core::ptr::drop_glue::<SignalProtocolError>` under `[LibsignalPlacement]`, together with
caller-block transfer and `.proto` specializations (`dropSpeSpecStkPlaced`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (InvalidMessageReason SignalProtocolError)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ
)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecHeader vecU8 vecU8At vecU8At_entails_dealloc)
open CryptoVerification.LibsignalTripleRatchetRepr (
  invalidMessageStrAt invalidSessionStructureStr speAt speWord strRefAt utf8
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost dropSpeStackX)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal addrCloneAt apiErrAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block sepWP_seq_lscro
  withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession.Cli.DropSpeProof.Helpers (stackAt_split_ge subroutine_ok_frame_weaken)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553 instIsLsBlockProg_553 lsProg_553)
open CryptoVerification.SignalSession.Cli.RunDrop (
  DropSpeOwnedGhost PlainSpeTag SpeOwned StrSpeTag speOwnedAt
)
open CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers (
  SatEntails SpecAt cells4_entails_stack_bottomX spe_tail_dealloc_postX stackAt_dropSpeX_split
  stack_restore_32_speX subroutine_ok_of_pure_pre subroutine_ok_pointwise subroutine_ok_specialize
  untrustedIdentity_entails_withString12 weaken_pre_sat
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget (dropSpeSpecStk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (
  dropSpeOwnedSpec dropSpeOwnedSpec_proto_post dropSpeOwnedSpec_proto_pre
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudgetAux (
  cliDropSpeOwned_plain_placed_ok_x cliDropSpeOwned_withStr_placed_ok_x
  cliSpeJumpTableSym cliSpeJumpTable_byte_placed dropSpePlainRawSpec
  dropSpeWithStrSpecXPlaced freeOnlyPool freeOnlyPool_dealloc freeOnlyPool_nil
  intro_rodata_cliSpeJumpTable_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)

/-- Budget-threaded `[LibsignalPlacement]` specification for `drop_glue::<SignalProtocolError>`. -/
def dropSpeOwnedSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropSpeOwnedGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (dropSpeOwnedSpec A lim stk)

/-- Budget-threaded `drop_glue::<SignalProtocolError>` contract on `lsProg_553`. -/
def DropSpeOwnedOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ stk, 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeOwnedSpecPlaced A lim stk)

/-- Caller-block-polymorphic budget-threaded `drop_glue::<SignalProtocolError>` contract. -/
def DropSpeOwnedOkAtBlock [LibsignalPlacement] {M : AllocCostModel}
    (callerProg : Program) (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ stk, 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok callerProg (blkPl_553).base (dropSpeOwnedSpecPlaced A lim stk)

/-- Budget-threaded `[LibsignalPlacement]` `.proto` error drop specification. -/
def dropSpeSpecStkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropSpeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (dropSpeSpecStk A lim stk)

section DropSpeOwnedPlacedBudgetSnfAndProto

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

private theorem strRefAt_entails_memRegion16_placed (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt a lit) (memRegion a 16) := by
  unfold strRefAt
  apply SatEntails.sepExists_elim
  intro p
  refine SatEntails.trans (SatEntails.sepConj_mono_right (SatEntails.drop_right _ _)) ?_
  apply SatEntails.of_entails
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a p)
    (pointsTo64_entails_memRegion (a + 8#64) _)

private theorem snf_words_entails_48_placed (a cap ptr : BitVec 64) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ⊢ memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  have h3 := sepConj_mono (pointsTo64_entails_memRegion a cap)
    (sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) ptr)
      (Q := memRegion (a + 16#64) 32))
  rw [h1, h2]
  exact h3

private theorem snf_cap0_pre_weaken_fullX_placed (a cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (snf_words_entails_48_placed a cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      pool ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem snf_tail_dealloc_pre_weakenX_placed (a cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ live1 ∗ live2 ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (snf_words_entails_48_placed a cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
  have hreord :
      pool ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ live1 ∗ live2 ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by sep_ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by sep_ac_rfl)

private theorem vecU8_at_0_exposeX_placed (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ∗ memRegion (a + 24#64) 24 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hexp : vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
         A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
    refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
    unfold vecHeader
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
    simp only [hbeq]
    rw [sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
    by_cases hc : cap = 0
    · simp only [hc, ↓reduceIte]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0))
      have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
      exact Entails.pure_right ⟨hlay, hcap_lt⟩ (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hexp) ?_
  have hm : memRegion (a + 16#64) 32 = memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide),
        show a + 16#64 + 8#64 = a + 24#64 by bv_omega]
  rw [hm]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem sessionNotFound_tail_entails_24_placed (a : BitVec 64) (dev : BitVec 8)
    (lit : List (BitVec 8)) :
    SatEntails
      (((a + 0x18#64) ↦₈ dev) ∗ memRegion (a + 0x19#64) 7 ∗ strRefAt (a + 0x20#64) lit)
      (memRegion (a + 24#64) 24) := by
  have hd : a + 0x18#64 = a + 24#64 := by bv_omega
  have hr : a + 0x19#64 = a + 25#64 := by bv_omega
  have hs : a + 0x20#64 = a + 32#64 := by bv_omega
  rw [hd, hr, hs]
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16_placed (a + 32#64) lit))) ?_
  apply SatEntails.of_entails
  have h1 : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 1 ∗ memRegion (a + 25#64) 23 := by
    rw [show (24 : Nat) = 1 + 23 from rfl, memRegion_split (a + 24#64) 1 23 (by decide),
        show a + 24#64 + 1#64 = a + 25#64 by bv_omega]
  have h2 : memRegion (a + 25#64) 23 = memRegion (a + 25#64) 7 ∗ memRegion (a + 32#64) 16 := by
    rw [show (23 : Nat) = 7 + 16 from rfl, memRegion_split (a + 25#64) 7 16 (by decide),
        show a + 25#64 + 7#64 = a + 32#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 24#64) dev) (IsBlock.memRegion (a + 24#64) 1)
      fun _ _ => trivial)

private theorem speOwnedAt_sessionNotFound_exposeX_placed (A : RustAlloc) (a : BitVec 64)
    (addr : AddrVal) (op : String) :
    SatEntails (speOwnedAt A a (.sessionNotFound addr op))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        memRegion (a + 16#64) 32 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speOwnedAt, apiErrAt, addrCloneAt]
  have hreord :
      (vecU8 A a addr.name ∗ ((a + 0x18#64) ↦₈ addr.device) ∗ memRegion (a + 0x19#64) 7) ∗
        strRefAt (a + 0x20#64) (utf8 op) =
      vecU8 A a addr.name ∗
        (((a + 0x18#64) ↦₈ addr.device) ∗ memRegion (a + 0x19#64) 7 ∗
          strRefAt (a + 0x20#64) (utf8 op)) := by
    sep_ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (sessionNotFound_tail_entails_24_placed a addr.device (utf8 op))) ?_
  exact SatEntails.of_entails (vecU8_at_0_exposeX_placed A a addr.name)

private theorem speOwned_snf_pre_weakenX_placed (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (addr : AddrVal) (op : String)
    (hbyte : SatEntails ro_tbl ro_byte)
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speOwnedAt A a (.sessionNotFound addr op) ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        memRegion (a + 16#64) 32 ∗ ro_byte ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  refine SatEntails.trans
    (SatEntails.sepConj_mono hbyte
      (SatEntails.sepConj_mono_left (speOwnedAt_sessionNotFound_exposeX_placed A a addr op))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by sep_ac_rfl)

private theorem conditionHolds_hi_addsPState64_placed (x y : BitVec 64) :
    ConditionHolds .HI (addsPState64 x y) = (BitVec.ult (x + y) x && (x + y != 0#64)) := by
  have hcs := conditionHolds_cs_addsPState64 x y
  have hne := conditionHolds_ne_addsPState64 x y
  cases h : addsPState64 x y with
  | mk n z c v =>
    rw [h] at hcs hne
    dsimp [ConditionHolds] at hcs hne ⊢
    rw [hcs, hne]

attribute [local simp] conditionHolds_hi_addsPState64_placed
attribute [local arm64_norm] conditionHolds_hi_addsPState64_placed
attribute [local wp_norm] conditionHolds_hi_addsPState64_placed

private theorem snf_xor_ult_35_eq_false_placed {cap : BitVec 64} (hcap_lt : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap ^^^ 0x8000000000000000#64) 35#64 = false := by
  have hb1 : cap.getLsbD 63 = false := by
    simp only [BitVec.getLsbD]
    exact Nat.testBit_lt_two_pow hcap_lt
  have hb2 : (0x8000000000000000#64 : BitVec 64).getLsbD 63 = true := by decide
  have hbx : (cap ^^^ 0x8000000000000000#64).getLsbD 63 = true := by
    rw [BitVec.getLsbD_xor, hb1, hb2]
    rfl
  have hge : 2 ^ 63 ≤ (cap ^^^ 0x8000000000000000#64).toNat := by
    by_contra hlt
    have hf : (cap ^^^ 0x8000000000000000#64).getLsbD 63 = false := by
      simp only [BitVec.getLsbD]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_not_le hlt)
    rw [hbx] at hf
    exact Bool.noConfusion hf
  have h35 : (35#64 : BitVec 64).toNat = 35 := rfl
  simp only [BitVec.ult, h35]
  exact decide_eq_false (by omega)

private theorem snf_cmn3_ult_eq_false_placed {cap : BitVec 64}
    (hcap : cap ≠ 0#64) (hcap_lt : cap.toNat < 2 ^ 63) :
    BitVec.ult ((cap - 1#64) + 3#64) (cap - 1#64) = false := by
  have hpos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
  simp only [BitVec.ult]
  exact decide_eq_false (by bv_omega)

private theorem snf_add2_ult_sub1_eq_false_placed {cap : BitVec 64}
    (hcap : cap ≠ 0#64) (hcap_lt : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap + 2#64) (cap - 1#64) = false := by
  have heq : cap + 2#64 = (cap - 1#64) + 3#64 := by bv_omega
  rw [heq]
  exact snf_cmn3_ult_eq_false_placed hcap hcap_lt

private def dropSpeSnfSpecXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × AddrVal × String) × M.σ) where
  pre := fun (⟨a, addr, op⟩, st) s =>
    (⌜s.readReg64 .x0 = a ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speOwnedAt A.repAlloc a (.sessionNotFound addr op) ∗
      A.pool lim st s ∗ stackAt s.sp dropSpeStackX) ∗
      ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun (⟨a, _, _⟩, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 48 ∗ freeOnlyPool A lim st sf ∗ stackAt s0.sp dropSpeStackX

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_snf_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeSnfSpecXPlaced A lim) := by
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_553 H) hA
  clear hA
  simp only [dropSpeSnfSpecXPlaced, pure_sepConj_pure_assoc]
  dsimp only [withLsCodeRoLoaded, lsProg_553, RustCliAllocBudget.live, ↓reduceIte] at hdealloc ⊢
  wp_init x s0
  obtain ⟨⟨a, addr, op⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine weaken_pre_sat
    (speOwned_snf_pre_weakenX_placed A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) addr op
      (cliSpeJumpTable_byte_placed (lsρ cliSpeJumpTableSym) 19 0x13#8 rfl rfl) _) ?_
  wp_pull_exists
  rename_i cap ptr
  by_cases hcap : cap = 0#64
  · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    wp_steps_sync_pool (s0.readReg64 .lr)
    refine weaken_pre_sat (snf_cap0_pre_weaken_fullX_placed _ _ _ s0.sp _ _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hlay, hcap_lt⟩
    have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
    have hlo_false : BitVec.ult (cap ^^^ 0x8000000000000000#64) 35#64 = false :=
      snf_xor_ult_35_eq_false_placed hcap_lt
    have hhi_ult : BitVec.ult ((cap - 1#64) + 3#64) (cap - 1#64) = false :=
      snf_cmn3_ult_eq_false_placed hcap hcap_lt
    have hhi_ult2 : BitVec.ult (cap + 2#64) (cap - 1#64) = false :=
      snf_add2_ult_sub1_eq_false_placed hcap hcap_lt
    have hhi_ult3 : BitVec.ult (cap - bv% (2 ^ 64 - 2)) (cap - 1#64) = false := by
      rw [show cap - bv% (2 ^ 64 - 2) = cap + 2#64 by bv_omega]
      exact hhi_ult2
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    refine weaken_pre_sat
      (snf_tail_dealloc_pre_weakenX_placed (s0.readReg64 (Reg.gpr 0#5)) cap ptr s0.sp
        _ _ _ _ _ _ _ _) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl_call, hro_call⟩
    wp_call hdealloc (ptr, cap.toNat, 1, st)
    apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (spe_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) _ s0.sp)) ?_
    wp_done

/-! ## Stack-parameterized liftings -/
private theorem cliDropSpeOwned_plain_placed_ok_stk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {i : Nat} (hi : PlainSpeTag i) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeOwnedSpecPlaced A lim stk) (⟨a, .plain i hi⟩, st)) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (cliDropSpeOwned_plain_placed_ok_x (A := A) (lim := lim) (H := H) hi a st)
    (fun _ s0 => ?_)
    (fun _ s0 sf => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpePlainRawSpec,
      withLsCodeRoLoaded, dropSpeOwnedSpec, speOwnedAt]
    rw [stackAt_split_ge s0.sp hstkX hstk64, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hx0, _⟩
    simp only [sepConj_assoc]
    exact Entails.pure_right hx0 (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpePlainRawSpec,
      withLsCodeRoLoaded, dropSpeOwnedSpec]
    rw [sepConj_assoc]
    apply Entails.pure_left; intro htr
    refine Entails.sepExists_right [] ?_
    rw [M.stepEvents_nil]
    refine Entails.pure_right ⟨htr, FreeOnlyEvs.nil⟩ ?_
    rw [stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpePlainRawSpec, withLsCodeRoLoaded]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_withStr_placed_ok_stk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {i : Nat} (hi : StrSpeTag i) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeOwnedSpecPlaced A lim stk) (⟨a, .withString i hi⟩, st)) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (subroutine_ok_specialize (cliDropSpeOwned_withStr_placed_ok_x hA) (⟨a, ⟨i, hi⟩⟩, st))
    (fun _ s0 => ?_)
    (fun _ s0 sf => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpeWithStrSpecXPlaced,
      withLsCodeRoLoaded, dropSpeOwnedSpec]
    rw [stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpeWithStrSpecXPlaced,
      withLsCodeRoLoaded, dropSpeOwnedSpec, freeOnlyPool]
    rw [sepConj_assoc]
    apply Entails.pure_left; intro htr
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro evs
    have hpure :
        (memRegion a 48 ∗ (⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt s0.sp dropSpeStackX) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX) =
        ⌜FreeOnlyEvs evs⌝ ∗
          (memRegion a 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp dropSpeStackX ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX)) := by sep_ac_rfl
    rw [hpure]
    apply Entails.pure_left; intro hfo
    refine Entails.sepExists_right evs (Entails.pure_right ⟨htr, hfo⟩ ?_)
    rw [stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpeWithStrSpecXPlaced, withLsCodeRoLoaded]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_snf_placed_ok_stk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (addr : AddrVal) (op : String) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeOwnedSpecPlaced A lim stk) (⟨a, .sessionNotFound addr op⟩, st)) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (subroutine_ok_specialize (cliDropSpeOwned_snf_placed_ok_x hA) (⟨a, addr, op⟩, st))
    (fun _ s0 => ?_)
    (fun _ s0 sf => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpeSnfSpecXPlaced,
      withLsCodeRoLoaded, dropSpeOwnedSpec]
    rw [stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpeSnfSpecXPlaced,
      withLsCodeRoLoaded, dropSpeOwnedSpec, freeOnlyPool]
    rw [sepConj_assoc]
    apply Entails.pure_left; intro htr
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro evs
    have hpure :
        (memRegion a 48 ∗ (⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt s0.sp dropSpeStackX) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX) =
        ⌜FreeOnlyEvs evs⌝ ∗
          (memRegion a 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp dropSpeStackX ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX)) := by sep_ac_rfl
    rw [hpure]
    apply Entails.pure_left; intro hfo
    refine Entails.sepExists_right evs (Entails.pure_right ⟨htr, hfo⟩ ?_)
    rw [stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [SpecAt, dropSpeOwnedSpecPlaced, dropSpeSnfSpecXPlaced, withLsCodeRoLoaded]
    exact Entails.pure_left nofun

private theorem subroutine_ok_weaken_speOwnedAt_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {a : BitVec 64} {k k' : SpeOwned} {st : M.σ}
    (h : subroutine_ok prog entry (SpecAt (dropSpeOwnedSpecPlaced A lim stk) (⟨a, k⟩, st)))
    (hent : SatEntails (speOwnedAt A.repAlloc a k') (speOwnedAt A.repAlloc a k)) :
    subroutine_ok prog entry (SpecAt (dropSpeOwnedSpecPlaced A lim stk) (⟨a, k'⟩, st)) := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hp => hp)
  intro _ R s0 hp
  dsimp only [SpecAt, dropSpeOwnedSpecPlaced, withLsCodeRoLoaded, dropSpeOwnedSpec] at hp ⊢
  exact SatEntails.sepConj_mono_left
    (SatEntails.sepConj_mono_right (SatEntails.sepConj_mono_left hent)) s0.mem R hp

private theorem spe_u64_at_8_entails_40_placed (a : BitVec 64) (v : BitVec 64) :
    ((a + 8#64) ↦₆₄ v) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) v)

private theorem spe_u8_at_8_entails_40_placed (a : BitVec 64) (v : BitVec 8) :
    ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 := by
    rw [show (40 : Nat) = 1 + 39 from rfl, memRegion_split (a + 8#64) 1 39 (by decide),
        show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) v) (IsBlock.memRegion (a + 8#64) 1)
      fun _ _ => trivial)

private theorem spe_u8_at_32_entails_16_placed (a : BitVec 64) (v : BitVec 8) :
    ((a + 32#64) ↦₈ v) ∗ memRegion (a + 33#64) 15 ⊢ memRegion (a + 32#64) 16 := by
  have h : memRegion (a + 32#64) 16 = memRegion (a + 32#64) 1 ∗ memRegion (a + 33#64) 15 := by
    rw [show (16 : Nat) = 1 + 15 from rfl, memRegion_split (a + 32#64) 1 15 (by decide),
        show a + 32#64 + 1#64 = a + 33#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 32#64) v) (IsBlock.memRegion (a + 32#64) 1)
      fun _ _ => trivial)

private theorem spe_u32x2_at_8_entails_40_placed (a : BitVec 64) (v1 v2 : BitVec 32) :
    ((a + 8#64) ↦₃₂ v1) ∗ ((a + 12#64) ↦₃₂ v2) ∗ memRegion (a + 16#64) 32 ⊢
      memRegion (a + 8#64) 40 := by
  have h1 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  have h2 : memRegion (a + 12#64) 36 = memRegion (a + 12#64) 4 ∗ memRegion (a + 16#64) 32 := by
    rw [show (36 : Nat) = 4 + 32 from rfl, memRegion_split (a + 12#64) 4 32 (by decide),
        show a + 12#64 + 4#64 = a + 16#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v1) (IsBlock.memRegion (a + 8#64) 4)
      fun _ _ => trivial)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (a + 12#64) v2) (IsBlock.memRegion (a + 12#64) 4)
         fun _ _ => trivial))

private theorem spe_strRef_at_8_entails_40_placed (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt (a + 8#64) lit ∗ memRegion (a + 24#64) 24) (memRegion (a + 8#64) 40) := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 16 ∗ memRegion (a + 24#64) 24 := by
    rw [show (40 : Nat) = 16 + 24 from rfl, memRegion_split (a + 8#64) 16 24 (by decide),
        show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  rw [h]
  exact SatEntails.sepConj_mono_left (strRefAt_entails_memRegion16_placed (a + 8#64) lit)

private theorem invalidMessageStrAt_entails_vecU8_placed (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right _ (Entails.refl _)
  | macFailed =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right _ (Entails.refl _)
  | pqRatchet =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | badCiphertext =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | decryptionFailed =>
    simp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_proto_placed_ok_stk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeOwnedSpecPlaced A lim stk) (⟨a, .proto fnName e⟩, st)) := by
  cases e with
  | panic =>
    refine subroutine_ok.of_codeLoaded fun _ R s0 _ _ hp _ _ => ?_
    dsimp only [SpecAt, dropSpeOwnedSpecPlaced,
      withLsCodeRoLoaded, dropSpeOwnedSpec, speOwnedAt, speAt] at hp
    have heq (P : Prop) :
        ((⌜P⌝ ∗ ⌜False⌝ ∗ A.pool lim st s0 ∗ stackAt s0.sp stk) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜False⌝ ∗ (⌜P⌝ ∗ A.pool lim st s0 ∗ stackAt s0.sp stk ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := by sep_ac_rfl
    rw [heq, satisfies_pure_sepConj] at hp
    exact hp.1.elim
  | invalidState =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 (i := 1) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16_placed (a + 32#64) fnName))
  | invalidMessage t r =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 (i := 24) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails
      (sepConj_mono_right
        (sepConj_mono (invalidMessageStrAt_entails_vecU8_placed A.repAlloc (a + 8#64) r)
          (spe_u8_at_32_entails_16_placed a _)))
  | invalidProtobufEncoding =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 2) (by decide) a st)
      (SatEntails.refl _)
  | ciphertextMessageTooShort n =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 3) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u64_at_8_entails_40_placed a _))
  | legacyCiphertextVersion v =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 4) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u8_at_8_entails_40_placed a v))
  | unrecognizedCiphertextVersion v =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 5) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u8_at_8_entails_40_placed a v))
  | noKeyTypeIdentifier =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 7) (by decide) a st)
      (SatEntails.refl _)
  | badKeyType t =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 8) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u8_at_8_entails_40_placed a t))
  | badKeyLength n =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 9) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u64_at_8_entails_40_placed a _))
  | invalidKeyAgreement =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 10) (by decide) a st)
      (SatEntails.refl _)
  | invalidSessionStructure r =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 20) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40_placed a (invalidSessionStructureStr r))
  | duplicatedMessage idx c =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 (i := 23) (by decide) a st) ?_
    dsimp only [speOwnedAt, speAt]
    have hreord :
        (a ↦₆₄ speWord 23) ∗ ((a + 8#64) ↦₃₂ idx) ∗ ((a + 12#64) ↦₃₂ c) ∗
          memRegion (a + 16#64) 32 =
        (a ↦₆₄ speWord 23) ∗
          (((a + 8#64) ↦₃₂ idx) ∗ ((a + 12#64) ↦₃₂ c) ∗ memRegion (a + 16#64) 32) := by sep_ac_rfl
    rw [hreord]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u32x2_at_8_entails_40_placed a idx c))

end DropSpeOwnedPlacedBudgetSnfAndProto

/-- Proves the budget-threaded `DropSpeOwnedOkPlaced` contract across all `SpeOwned` variants. -/
theorem cliDropSpeOwned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    DropSpeOwnedOkPlaced A lim H := by
  intro stk hstk hstk64
  refine subroutine_ok_pointwise fun ⟨⟨a, k⟩, st⟩ => ?_
  cases k with
  | proto fnName e =>
    exact cliDropSpeOwned_proto_placed_ok_stk hA stk hstk hstk64 fnName e a st
  | sessionNotFound addr op =>
    exact cliDropSpeOwned_snf_placed_ok_stk hA stk hstk hstk64 addr op a st
  | untrustedIdentity addr =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 (i := 12) (by decide) a st)
      (SatEntails.of_entails (untrustedIdentity_entails_withString12 A.repAlloc a addr))
  | badKemKeyType =>
    exact cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64
      (i := 31) (by decide) a st
  | badKemKeyLength =>
    exact cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64
      (i := 33) (by decide) a st
  | plain i hi =>
    exact cliDropSpeOwned_plain_placed_ok_stk (A := A) (lim := lim) (H := H) stk hstk hstk64 hi a st
  | withString i hi =>
    exact cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 hi a st

/-- Transfers `cliDropSpeOwned_placed_ok` to any caller block `i < 619`. -/
theorem cliDropSpeOwned_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (hi : i < 619 := by decide) :
    DropSpeOwnedOkAtBlock callerProg A lim := by
  intro stk hstk hstk64
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_553 H) i 553 H
    hcaller (instIsLsBlockProg_553 H) (blkPl_553).base _
    (cliDropSpeOwned_placed_ok hA stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- Specializes `cliDropSpeOwned_placed_ok` to `.proto` errors (`dropSpeSpecStkPlaced`). -/
theorem cliDropSpe_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeSpecStkPlaced A lim stk) := by
  refine subroutine_ok_pointwise fun ⟨⟨a, fnName, e⟩, st⟩ => ?_
  have h0 := subroutine_ok_specialize (cliDropSpeOwned_placed_ok hA stk hstk hstk64)
    (⟨a, .proto fnName e⟩, st)
  refine subroutine_ok_mono h0 ?_ ?_
  · intro _ R s0 hp
    dsimp only [SpecAt, dropSpeSpecStkPlaced, dropSpeOwnedSpecPlaced, withLsCodeRoLoaded] at hp ⊢
    rw [dropSpeOwnedSpec_proto_pre]
    exact hp
  · intro _ R s0 sf hp
    dsimp only [SpecAt, dropSpeSpecStkPlaced, dropSpeOwnedSpecPlaced, withLsCodeRoLoaded] at hp ⊢
    rw [← dropSpeOwnedSpec_proto_post]
    exact hp

/-- Transfers `cliDropSpe_placed_ok` to any caller block `i < 619`. -/
theorem cliDropSpe_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_553).base (dropSpeSpecStkPlaced A lim stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_553 H) i 553 H
    hcaller (instIsLsBlockProg_553 H) (blkPl_553).base _
    (cliDropSpe_placed_ok hA stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
