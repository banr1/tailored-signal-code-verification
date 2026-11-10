/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Drop Glue Proof for Owned `SignalProtocolError`

Proves `DropSpeOwnedOkPlaced` for `core::ptr::drop_glue::<SignalProtocolError>` under
`[LibsignalPlacement]` and transfers it to caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunDrop

open Arm64 ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed

/-- Relocatable `[LibsignalPlacement]` specification for `drop_glue::<SignalProtocolError>`. -/
def dropSpeOwnedSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec DropSpeOwnedGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeOwnedSpec A stk)

/-- Relocatable `drop_glue::<SignalProtocolError>` contract on `lsProg_553`. -/
def DropSpeOwnedOkPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  ∀ stk, 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeOwnedSpecPlaced A stk)

/-- Caller-block-polymorphic `drop_glue::<SignalProtocolError>` contract. -/
def DropSpeOwnedOkAtBlock [LibsignalPlacement] (callerProg : Program) (A : RustAlloc) : Prop :=
  ∀ stk, 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok callerProg (blkPl_553).base (dropSpeOwnedSpecPlaced A stk)

end CryptoVerification.SignalSession.Cli.RunDrop

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters (speJumpTable dropSpeStackX)
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers

abbrev dropSpeOwnedSpecPlaced [LibsignalPlacement] := RunDrop.dropSpeOwnedSpecPlaced

section DropSpeOwnedPlacedHelpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private abbrev cliSpeJumpTableSym : String :=
  "libsignal_cli:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

private theorem lsroCheck_cliSpeJumpTable :
    lsroCheck cliSpeJumpTableSym speJumpTable = true := by
  rfl_kernel

private theorem intro_rodata_cliSpeJumpTable_placed [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s
      (((lsρ cliSpeJumpTableSym) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro_intro_chk hro lsroCheck_cliSpeJumpTable hm)

private theorem cliSpeJumpTable_byte_placed (tbl : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails (tbl ↦ᵣ speJumpTable) ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h :
      (tbl ↦ᵣ speJumpTable) =
      (tbl ↦ᵣ speJumpTable.take i) ∗
        (((tbl + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         ((tbl + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem plain_tbl_weaken_placed (tbl a : BitVec 64) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (heq : speJumpTable = speJumpTable.take i ++ (0x1b#8 :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i)
    (rest : SepProp) :
    SatEntails
      ((tbl ↦ᵣ speJumpTable) ∗ ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40 ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ 0x1b#8) ∗ rest) :=
  spe_plain_tbl_pre_weakenX a i w hw (cliSpeJumpTable_byte_placed tbl i 0x1b#8 heq hlen) rest

private def dropSpePlainSpecXPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec (BitVec 64 × Nat) :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpePlainSpecX A)

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_tbl1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {i : Nat} (hi : i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10]) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainSpecXPlaced A) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre hi ?_
  unfold dropSpePlainSpecXPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [SpecAt, dropSpePlainSpecX, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ite_true]
  wp_init u s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10] := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 2 0x8000000000000002#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 3 0x8000000000000003#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 4 0x8000000000000004#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 5 0x8000000000000005#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 6 0x8000000000000006#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 7 0x8000000000000007#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 8 0x8000000000000008#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 9 0x8000000000000009#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 10 0x800000000000000a#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_tbl2_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {i : Nat} (hi : i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23]) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainSpecXPlaced A) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre hi ?_
  unfold dropSpePlainSpecXPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [SpecAt, dropSpePlainSpecX, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ite_true]
  wp_init u s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23] := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 11 0x800000000000000b#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 13 0x800000000000000d#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 14 0x800000000000000e#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 15 0x800000000000000f#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 16 0x8000000000000010#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 17 0x8000000000000011#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 20 0x8000000000000014#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 21 0x8000000000000015#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 23 0x8000000000000017#64 rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_hi_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {i : Nat} (hi : i ∈ [28, 29, 30, 31, 32, 33, 34]) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainSpecXPlaced A) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre hi ?_
  unfold dropSpePlainSpecXPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [SpecAt, dropSpePlainSpecX, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ite_true]
  wp_init u s0
  have hmem : i ∈ [28, 29, 30, 31, 32, 33, 34] := ‹_›
  subst ‹s0.readReg64 _ = a›
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show speWord 28 = 0x800000000000001c#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 29 = 0x800000000000001d#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 30 = 0x800000000000001e#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 31 = 0x800000000000001f#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 32 = 0x8000000000000020#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 33 = 0x8000000000000021#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 34 = 0x8000000000000022#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done

private theorem cliDropSpeOwned_plain_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {i : Nat} (hi : PlainSpeTag i) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainSpecXPlaced A) ⟨a, i⟩) := by
  have hsplit :
      i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10] ∨
      i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23] ∨
      i ∈ [28, 29, 30, 31, 32, 33, 34] := by
    simp only [PlainSpeTag, plainSpeTags, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rcases hsplit with h1 | h2 | h3
  · exact cliDropSpeOwned_plainTag_tbl1_placed_ok_x h1 a
  · exact cliDropSpeOwned_plainTag_tbl2_placed_ok_x h2 a
  · exact cliDropSpeOwned_plainTag_hi_placed_ok_x h3 a

/-! ## String-carrying (`withString`) error drop helpers -/
private def dropSpeWithStrRawSpecXPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec (BitVec 64 × Nat) where
  pre := fun ⟨a, i⟩ s =>
    (⌜s.readReg64 .x0 = a⌝ ∗
      ((a ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
        memRegion (a + 32#64) 16) ∗
      A.pool ∗ stackAt s.sp dropSpeStackX) ∗
      ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun ⟨a, _⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStackX

private theorem spe_str_cap0_pre_weaken_fullX_placed (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem spe_tail_dealloc_pre_weakenX_placed (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem str_tbl_weaken_placed (A : RustAlloc) (tbl a : BitVec 64) (i : Nat)
    (w : BitVec 64) (bs : List (BitVec 8))
    (hw : speWord i = w)
    (heq : speJumpTable = speJumpTable.take i ++ (0x00#8 :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i)
    (rest : SepProp) :
    SatEntails
      ((tbl ↦ᵣ speJumpTable) ∗
        ((a ↦₆₄ speWord i) ∗ vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ 0x00#8) ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  have hbyte := cliSpeJumpTable_byte_placed tbl i 0x00#8 heq hlen
  have grouped :
      (a ↦₆₄ speWord i) ∗ vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ∗ rest =
      (a ↦₆₄ speWord i) ∗ (vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16) ∗ rest := by
    ac_rfl
  rw [grouped]
  refine SatEntails.trans
    (SatEntails.sepConj_mono hbyte
      (SatEntails.sepConj_mono_right
        (SatEntails.sepConj_mono_left (SatEntails.of_entails (vecU8_at_8_exposeX A a bs))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by ac_rfl)

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_withStr1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    {i : Nat} (h4 : i ∈ [0, 1, 12, 18]) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeWithStrRawSpecXPlaced A) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre h4 ?_
  have hdealloc : subroutine_ok (lsProg_553 H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_553 H) (lsProg_617 H) 553 617 H
      (instIsLsBlockProg_553 H) (instIsLsBlockProg_617 H) (lsρ lsRustDeallocSymCli) _
      hA.dealloc _ _ _ _ (by decide) (by decide) (by decide)
  clear hA
  simp only [SpecAt, dropSpeWithStrRawSpecXPlaced, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ite_true, withLsRoCl, rustDeallocExternSpecWithStack] at hdealloc ⊢
  wp_init u s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [0, 1, 12, 18] := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 0 0x8000000000000000#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 1 0x8000000000000001#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 12 0x800000000000000c#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 18 0x8000000000000012#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_withStr2_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    {i : Nat} (h4 : i ∈ [22, 24, 25, 27]) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeWithStrRawSpecXPlaced A) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre h4 ?_
  have hdealloc : subroutine_ok (lsProg_553 H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_553 H) (lsProg_617 H) 553 617 H
      (instIsLsBlockProg_553 H) (instIsLsBlockProg_617 H) (lsρ lsRustDeallocSymCli) _
      hA.dealloc _ _ _ _ (by decide) (by decide) (by decide)
  clear hA
  simp only [SpecAt, dropSpeWithStrRawSpecXPlaced, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ite_true, withLsRoCl, rustDeallocExternSpecWithStack] at hdealloc ⊢
  wp_init u s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [22, 24, 25, 27] := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 22 0x8000000000000016#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 24 0x8000000000000018#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 25 0x8000000000000019#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A (lsρ cliSpeJumpTableSym) _ 27 0x800000000000001b#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done

private def dropSpeWithStrSpecXPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec (BitVec 64 × { i : Nat // StrSpeTag i }) :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeWithStrSpecX A)

private theorem cliDropSpeOwned_withStr_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeWithStrSpecXPlaced A) := by
  refine subroutine_ok_pointwise fun ⟨a, ⟨i, hi⟩⟩ => ?_
  have hraw : subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeWithStrRawSpecXPlaced A) ⟨a, i⟩) := by
    have hsplit : i ∈ [0, 1, 12, 18] ∨ i ∈ [22, 24, 25, 27] := by
      simp only [StrSpeTag, strSpeTags, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rcases hsplit with h1 | h2
    · exact cliDropSpeOwned_withStr1_placed_ok_x hA h1 a
    · exact cliDropSpeOwned_withStr2_placed_ok_x hA h2 a
  exact subroutine_ok_mono hraw
    (fun _ R s0 hp => by
      dsimp only [SpecAt, dropSpeWithStrSpecXPlaced, dropSpeWithStrRawSpecXPlaced,
        LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeWithStrSpecX, speOwnedAt] at hp ⊢
      exact hp)
    (fun _ R s0 sf hp => by
      dsimp only [SpecAt, dropSpeWithStrSpecXPlaced, dropSpeWithStrRawSpecXPlaced,
        LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeWithStrSpecX] at hp ⊢
      exact hp)

end DropSpeOwnedPlacedHelpers

section DropSpeOwnedPlacedSnfAndProto

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## `SessionNotFound` error drop helpers -/
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
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (snf_words_entails_48_placed a cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem snf_tail_dealloc_pre_weakenX_placed (a cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (snf_words_entails_48_placed a cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

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
  exact Entails.of_eq (by ac_rfl)

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
        strRefAt (a + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op) =
      vecU8 A a addr.name ∗
        (((a + 0x18#64) ↦₈ addr.device) ∗ memRegion (a + 0x19#64) 7 ∗
          strRefAt (a + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op)) := by
    ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (sessionNotFound_tail_entails_24_placed a addr.device
        (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op))) ?_
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
  exact SatEntails.of_eq (by ac_rfl)

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

private def dropSpeSnfSpecXPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec (BitVec 64 × AddrVal × String) :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSnfSpecX A)

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_snf_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeSnfSpecXPlaced A) := by
  unfold dropSpeSnfSpecXPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  have hdealloc : subroutine_ok (lsProg_553 H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_553 H) (lsProg_617 H) 553 617 H
      (instIsLsBlockProg_553 H) (instIsLsBlockProg_617 H) (lsρ lsRustDeallocSymCli) _
      hA.dealloc _ _ _ _ (by decide) (by decide) (by decide)
  clear hA
  simp only [dropSpeSnfSpecX, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ite_true, withLsRoCl, rustDeallocExternSpecWithStack] at hdealloc ⊢
  wp_init x s0
  obtain ⟨a, addr, op⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine weaken_pre_sat
    (speOwned_snf_pre_weakenX_placed A (s0.readReg64 (Reg.gpr 0#5)) addr op
      (cliSpeJumpTable_byte_placed (lsρ cliSpeJumpTableSym) 19 0x13#8 rfl rfl) _) ?_
  wp_pull_exists
  rename_i cap ptr
  by_cases hcap : cap = 0#64
  · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    wp_steps
    refine weaken_pre_sat (snf_cap0_pre_weaken_fullX_placed _ _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨⟨hlay1, hlay2, hlay3⟩, hcap_lt⟩
    have hlo_false : BitVec.ult (cap ^^^ 0x8000000000000000#64) 35#64 = false :=
      snf_xor_ult_35_eq_false_placed hcap_lt
    have hhi_ult : BitVec.ult ((cap - 1#64) + 3#64) (cap - 1#64) = false :=
      snf_cmn3_ult_eq_false_placed hcap hcap_lt
    have hhi_ult2 : BitVec.ult (cap + 2#64) (cap - 1#64) = false :=
      snf_add2_ult_sub1_eq_false_placed hcap hcap_lt
    have hhi_ult3 : BitVec.ult (cap - bv% (2 ^ 64 - 2)) (cap - 1#64) = false := by
      rw [show cap - bv% (2 ^ 64 - 2) = cap + 2#64 by bv_omega]
      exact hhi_ult2
    apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
    wp_steps
    refine weaken_pre_sat
      (snf_tail_dealloc_pre_weakenX_placed (s0.readReg64 (Reg.gpr 0#5)) cap ptr s0.sp
        _ _ _ _ _ _ _ _) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl_call, hro_call⟩
    wp_call hdealloc (ptr, cap.toNat, 1)
    refine SepWP.weaken_pre (spe_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
    wp_done

/-! ## Stack-parameterized liftings -/
private theorem cliDropSpeOwned_plain_placed_ok_stk [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {i : Nat} (hi : PlainSpeTag i) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (RunDrop.dropSpeOwnedSpecPlaced A stk) ⟨a, .plain i hi⟩) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (cliDropSpeOwned_plain_placed_ok_x (A := A) (H := H) hi a)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpePlainSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, speOwnedAt,
      dropSpePlainSpecX]
    rw [DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpePlainSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, dropSpePlainSpecX]
    rw [DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpePlainSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_withStr_placed_ok_stk [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {i : Nat} (hi : StrSpeTag i) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (RunDrop.dropSpeOwnedSpecPlaced A stk) ⟨a, .withString i hi⟩) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (subroutine_ok_specialize (cliDropSpeOwned_withStr_placed_ok_x hA) ⟨a, ⟨i, hi⟩⟩)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpeWithStrSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, dropSpeWithStrSpecX]
    rw [DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpeWithStrSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, dropSpeWithStrSpecX]
    rw [DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpeWithStrSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_snf_placed_ok_stk [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (addr : AddrVal) (op : String) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (RunDrop.dropSpeOwnedSpecPlaced A stk) ⟨a, .sessionNotFound addr op⟩) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (subroutine_ok_specialize (cliDropSpeOwned_snf_placed_ok_x hA) ⟨a, addr, op⟩)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpeSnfSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, dropSpeSnfSpecX]
    rw [DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpeSnfSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, dropSpeSnfSpecX]
    rw [DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced, dropSpeSnfSpecXPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    exact Entails.pure_left nofun

/-! ## Reduction of `.proto` and `.untrustedIdentity` arms -/
private theorem subroutine_ok_weaken_speOwnedAt_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc} {stk : Nat}
    {a : BitVec 64} {k k' : SpeOwned}
    (h : subroutine_ok prog entry (SpecAt (RunDrop.dropSpeOwnedSpecPlaced A stk) ⟨a, k⟩))
    (hent : SatEntails (speOwnedAt A a k') (speOwnedAt A a k)) :
    subroutine_ok prog entry (SpecAt (RunDrop.dropSpeOwnedSpecPlaced A stk) ⟨a, k'⟩) := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hp => hp)
  intro _ R s0 hp
  dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec] at hp ⊢
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
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) (a : BitVec 64) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (RunDrop.dropSpeOwnedSpecPlaced A stk) ⟨a, .proto fnName e⟩) := by
  cases e with
  | panic =>
    intro _ R s0 _ _ hp _ _
    dsimp only [SpecAt, RunDrop.dropSpeOwnedSpecPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropSpeOwnedSpec, speOwnedAt, speAt] at hp
    have heq :
        ((⌜s0.readReg64 Reg.x0 = a⌝ ∗ ⌜False⌝ ∗ A.pool ∗ stackAt s0.sp stk) ∗
          ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜False⌝ ∗ (⌜s0.readReg64 Reg.x0 = a⌝ ∗ A.pool ∗ stackAt s0.sp stk ∗
          ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := by ac_rfl
    rw [heq, satisfies_pure_sepConj] at hp
    exact hp.1.elim
  | invalidState =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 (i := 1) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16_placed (a + 32#64) fnName))
  | invalidMessage t r =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 (i := 24) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails
      (sepConj_mono_right
        (sepConj_mono (invalidMessageStrAt_entails_vecU8_placed A (a + 8#64) r)
          (spe_u8_at_32_entails_16_placed a _)))
  | invalidProtobufEncoding =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 2) (by decide) a)
      (SatEntails.refl _)
  | ciphertextMessageTooShort n =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 3) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u64_at_8_entails_40_placed a _))
  | legacyCiphertextVersion v =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 4) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u8_at_8_entails_40_placed a v))
  | unrecognizedCiphertextVersion v =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 5) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u8_at_8_entails_40_placed a v))
  | noKeyTypeIdentifier =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 7) (by decide) a)
      (SatEntails.refl _)
  | badKeyType t =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 8) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u8_at_8_entails_40_placed a t))
  | badKeyLength n =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 9) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u64_at_8_entails_40_placed a _))
  | invalidKeyAgreement =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 10) (by decide) a)
      (SatEntails.refl _)
  | invalidSessionStructure r =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 20) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40_placed a (invalidSessionStructureStr r))
  | duplicatedMessage idx c =>
    refine subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_plain_placed_ok_stk stk hstk hstk64 (i := 23) (by decide) a) ?_
    dsimp only [speOwnedAt, speAt]
    have hreord :
        (a ↦₆₄ speWord 23) ∗ ((a + 8#64) ↦₃₂ idx) ∗ ((a + 12#64) ↦₃₂ c) ∗
          memRegion (a + 16#64) 32 =
        (a ↦₆₄ speWord 23) ∗
          (((a + 8#64) ↦₃₂ idx) ∗ ((a + 12#64) ↦₃₂ c) ∗ memRegion (a + 16#64) 32) := by ac_rfl
    rw [hreord]
    exact SatEntails.of_entails (sepConj_mono_right (spe_u32x2_at_8_entails_40_placed a idx c))

end DropSpeOwnedPlacedSnfAndProto

/-- Proves `DropSpeOwnedOkPlaced` for `core::ptr::drop_glue::<SignalProtocolError>` across all `SpeOwned` variants. -/
theorem cliDropSpeOwned_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    RunDrop.DropSpeOwnedOkPlaced A H := by
  intro stk hstk hstk64
  refine subroutine_ok_pointwise fun ⟨a, k⟩ => ?_
  cases k with
  | proto fnName e =>
    exact cliDropSpeOwned_proto_placed_ok_stk hA stk hstk hstk64 fnName e a
  | sessionNotFound addr op =>
    exact cliDropSpeOwned_snf_placed_ok_stk hA stk hstk hstk64 addr op a
  | untrustedIdentity addr =>
    exact subroutine_ok_weaken_speOwnedAt_placed
      (cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 (i := 12) (by decide) a)
      (SatEntails.of_entails (untrustedIdentity_entails_withString12 A a addr))
  | badKemKeyType =>
    exact cliDropSpeOwned_plain_placed_ok_stk (A := A) (H := H) stk hstk hstk64
      (i := 31) (by decide) a
  | badKemKeyLength =>
    exact cliDropSpeOwned_plain_placed_ok_stk (A := A) (H := H) stk hstk hstk64
      (i := 33) (by decide) a
  | plain i hi =>
    exact cliDropSpeOwned_plain_placed_ok_stk (A := A) (H := H) stk hstk hstk64 hi a
  | withString i hi =>
    exact cliDropSpeOwned_withStr_placed_ok_stk hA stk hstk hstk64 hi a

/-- Transfers `cliDropSpeOwned_placed_ok` to any caller block `i < 619`. -/
theorem cliDropSpeOwned_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide) :
    RunDrop.DropSpeOwnedOkAtBlock callerProg A := by
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

end CryptoVerification.SignalSession.Cli.RunProofs

namespace CryptoVerification.SignalSession.Cli.RunDrop

open Arm64 ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops

theorem cliDropSpeOwned_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    RunDrop.DropSpeOwnedOkPlaced A H :=
  RunProofs.cliDropSpeOwned_placed_ok hA

theorem cliDropSpeOwned_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide) :
    RunDrop.DropSpeOwnedOkAtBlock callerProg A :=
  RunProofs.cliDropSpeOwned_placed_at_block hA hi

end CryptoVerification.SignalSession.Cli.RunDrop
