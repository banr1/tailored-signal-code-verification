/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegExit
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchTail
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import ProofLib.ProgramReflection -- shake: keep

/-!
# Budget-Threaded Exit Jump-Table Segment (`SegExitBudget`)

Relocatable `RustCliAllocBudget` / `SeamBudget` verification of the `errs` drop loop and buffer
deallocation (`+0x1e8c → +0x1f50`, block 197).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Record.SegExitBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto MessageType InvalidMessageReason)
open CryptoVerification (
  LibsignalPlacement lsmpl lsRustDeallocSym
)
open CryptoVerification.RustHeap (
  RustAlloc allocHookStack vecHeader vecU8At vecU8
)
open CryptoVerification.LibsignalSessionRepr (
  msgTypeByte
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost uuidTryParse utf8 speWord speAt
  protocolAddressAt signalMessageAt sessionStateAt tapeAfter
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel RecordDecryptGhost rootStack
  recordResultAt recordResultTag
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (
  RecErr recErrAt errsAt
  blkPC_197 blkPl_197 blkLib_197 blkLib_eq_197
  ls_hook_ok_226
  recJPCPlaced recExitPlaced recMetaPlaced recFramePlaced
  SatEntails_shared_lb SepWP_weaken_pre_sat_shared_lb
  exitJumpTableSym exitJumpTable_shared_lb
  rodata_exitJumpTable_placed_intro exitJumpTable_byte_placed
  strRefAt_entails_memRegion16_shared_lb
  spe_u64_at_8_entails_40_shared_lb spe_u32_at_8_entails_40_shared_lb
  spe_u8_at_8_entails_40_shared_lb spe_u8_at_32_entails_16_shared_lb
  spe_u32x2_at_8_entails_40_shared_lb spe_strRef_at_8_entails_40_shared_lb
  iscmk_entails_40_shared_lb invalidMessageStrAt_entails_vecU8_shared_lb
  spe_str_after_weaken_shared_lb spe_noop_after_weaken_shared_lb
  spe_unit_pre_weaken_shared_lb
  frame_high_entails_0x920_shared_lb
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  AllocCallPreserved FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  TryDecryptEnvArgs SeamBudget RecordDecryptEnv
  recordDecryptPlacedSpec JStatePlaced SegExitPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  protocolAddressAt_atState signalMessageAt_atState
  sessionStateAt_atState recordResultAt_atState
  errsAt_atState recFramePlaced_atState
  checkBlockNoSvc0_197
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `speAt` exposure and frame helpers -/

private theorem stackAt_root_split_alloc (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack (rootStack - allocHookStack) (by decide)

private theorem sepWP_false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private theorem frame_low_entails_0xa0 (sp : BitVec 64) (w80 w88 w90 : BitVec 64) (w9c : BitVec 32) :
    memRegion sp 0x80 ∗ ((sp + 0x80#64) ↦₆₄ w80) ∗ ((sp + 0x88#64) ↦₆₄ w88) ∗
      ((sp + 0x90#64) ↦₆₄ w90) ∗ memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ w9c) ⊢
      memRegion sp 0xa0 := by
  rw [show (0xa0 : Nat) = 0x80 + 32 from rfl, memRegion_split sp 0x80 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80) 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8) 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_right (pointsTo32_entails_memRegion _ _)))))

private theorem vecU8At_entails_dealloc (A : RustAlloc) (a : BitVec 64) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  simp only [vecU8At, vecHeader, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) _)) ?_
  refine sepConj_mono_right ?_
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, _⟩
  by_cases hcap : cap = 0#64
  · subst hcap
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Entails.refl _
  · have hcap0 : ¬ cap = 0 := hcap
    have hbeq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap0, hbeq, Bool.false_eq_true, ↓reduceIte]
    refine sepConj_mono_right ?_
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      have heq : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      exact memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [hsplit]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

private theorem vecU8_at_8_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_dealloc A (a + 8#64) cap ptr bs)) ?_
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have hm : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 := by
    rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (a + 24#64) 8 16 (by decide),
        show a + 24#64 + 8#64 = a + 32#64 by bv_omega]
  rw [h16, h24, hm]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem speAt_invalidState_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntails_shared_lb (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails_shared_lb.sepExists_elim; intro bs
  refine SatEntails_shared_lb.trans
    (SatEntails_shared_lb.sepConj_mono_right
      (SatEntails_shared_lb.sepConj_mono_right
        (strRefAt_entails_memRegion16_shared_lb (a + 32#64) fnName))) ?_
  apply SatEntails_shared_lb.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem speAt_invalidMessage_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntails_shared_lb (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntails_shared_lb.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8_shared_lb A (a + 8#64) r)
      (spe_u8_at_32_entails_16_shared_lb a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem spe_str_pre_weaken (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (r : RecErr) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails_shared_lb ro_tbl ro_byte)
    (he : SatEntails_shared_lb (recErrAt A a r)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntails_shared_lb (ro_tbl ∗ (recErrAt A a r ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntails_shared_lb.trans
    (SatEntails_shared_lb.sepConj_mono hbyte (SatEntails_shared_lb.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails_shared_lb.sepExists_elim; intro cap
  apply SatEntails_shared_lb.sepExists_elim; intro ptr
  refine SatEntails_shared_lb.sepExists_right cap (SatEntails_shared_lb.sepExists_right ptr ?_)
  exact SatEntails_shared_lb.of_eq (by sep_ac_rfl)

private def recFramePlacedRest [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost)
    (sp : BitVec 64) : SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ lsLogOff ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack)

private theorem recFramePlaced_split_rep [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (x : RecordDecryptGhost) (sp : BitVec 64) :
    recFramePlaced A.repAlloc x sp =
      recFramePlacedRest A.repAlloc x sp ∗ stackAt sp allocHookStack := by
  unfold recFramePlaced recFramePlacedRest
  rw [stackAt_root_split_alloc sp, RustCliAllocBudget.repAlloc_pool, sepConj_emp]
  sep_ac_rfl

private theorem recPostPlaced_of_frame_aux [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (st' : M.σ)
    (x : RecordDecryptGhost) (S_sess resSlot tape R : SepProp) (s0 sf : State)
    (w_cap w_ptr w_len : BitVec 64)
    (hm : sf.mem ⊨ recFramePlaced A.repAlloc x s0.sp ∗ A.pool lim st' sf ∗
      ((s0.sp + 0x5d8#64) ↦₆₄ w_cap) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ w_ptr) ∗
      ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ w_len) ∗ memRegion (s0.sp + 0xca0#64) 344 ∗
      S_sess ∗ resSlot ∗ tape ∗ R) :
    sf.mem ⊨ memRegion s0.sp 0xa0 ∗
      ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
      ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
      S_sess ∗ resSlot ∗ memRegion (s0.sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      tape ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool lim st' sf ∗ R := by
  have hm_rearr : sf.mem ⊨
      (memRegion s0.sp 0x80 ∗ ((s0.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s0.sp + 0x88#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x90#64) ↦₆₄ x.msgA) ∗ memRegion (s0.sp + 0x98#64) 4 ∗
        ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32)) ∗
      ((memRegion (s0.sp + 0x4e0#64) 0xd0 ∗ ((s0.sp + 0x5b0#64) ↦₆₄ x.remA) ∗
        memRegion (s0.sp + 0x5b8#64) 4 ∗ ((s0.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
        memRegion (s0.sp + 0x5bd#64) 3 ∗ ((s0.sp + 0x5c0#64) ↦₆₄ (s0.sp + 0x5bc#64)) ∗
        ((s0.sp + 0x5c8#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0x5d0#64) ↦₆₄ (s0.sp + 0x5b0#64)) ∗
        ((s0.sp + 0x5d8#64) ↦₆₄ w_cap) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ w_ptr) ∗
        ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ w_len) ∗ memRegion (s0.sp + 0x5f0#64) 0x6b0 ∗
        memRegion (s0.sp + 0xca0#64) 344 ∗ memRegion (s0.sp + 0xdf8#64) 8) ∗
       (((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗ S_sess ∗ resSlot ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tape ∗ lsLogOff ∗
        stackAt s0.sp rootStack ∗ A.pool lim st' sf ∗ R)) := by
    dsimp only [recFramePlaced] at hm
    rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  clear hm
  have hm_fold := Satisfies.mono
    (sepConj_mono (frame_low_entails_0xa0 s0.sp x.sret x.locA x.msgA _)
      (sepConj_mono_left (frame_high_entails_0x920_shared_lb s0.sp x.remA (msgTypeByte .whisper)
        (s0.sp + 0x5bc#64) x.msgA (s0.sp + 0x5b0#64) w_cap w_ptr w_len))) hm_rearr
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_fold

/-! ## Budget-threaded single-element drop and `segExit_placed_ok` -/

local macro "seg_exit_noop_placed_b " s0:ident r:term:max i:num w:term:max off:term:max he:term:max : tactic =>
  `(tactic| (
    refine SepWP_weaken_pre_sat_shared_lb
      (spe_unit_pre_weaken_shared_lb _ _ $r $i $w rfl
        (exitJumpTable_byte_placed _ $i $off 0x00#8 rfl (by rfl_kernel) (by rfl_kernel)) $he _) ?_
    wp_steps_sync_197 ((blkPl_197).base + 7988#64)
    refine SepWP_weaken_pre_sat_shared_lb
      (SatEntails_shared_lb.sepConj_mono_right (spe_noop_after_weaken_shared_lb _ _ _ _)) ?_
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨[], FreeOnlyEvs.nil, ?_,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    rw [show ($s0:ident).sp + 0x5d8#64 + 8#64 = ($s0:ident).sp + 1504#64 by bv_omega,
      show ($s0:ident).sp + 0x5d8#64 + 16#64 = ($s0:ident).sp + 1512#64 by bv_omega]
    exact Entails.of_eq (by sep_ac_rfl)))

local macro "seg_exit_str_placed_b " s:ident hsp:ident s0:ident _st:ident r:term:max i:num w:term:max off:term:max he:term:max : tactic =>
  `(tactic| (
    refine SepWP_weaken_pre_sat_shared_lb
      (spe_str_pre_weaken _ _ $r $i $w rfl
        (exitJumpTable_byte_placed _ $i $off 0x0d#8 rfl (by rfl_kernel) (by rfl_kernel)) $he _) ?_
    wp_pull_exists; rename_i cap ptr; by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]
      wp_steps_sync_197 ((blkPl_197).base + 7988#64)
      refine SepWP_weaken_pre_sat_shared_lb
        (SatEntails_shared_lb.sepConj_mono_right (spe_str_after_weaken_shared_lb _ _ _ _ _ _)) ?_
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨[], FreeOnlyEvs.nil, ?_,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      rw [show ($s0:ident).sp + 0x5d8#64 + 8#64 = ($s0:ident).sp + 1504#64 by bv_omega,
        show ($s0:ident).sp + 0x5d8#64 + 16#64 = ($s0:ident).sp + 1512#64 by bv_omega]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live_norm]
      wp_steps_sync_197 (lsmpl.ρ lsRustDeallocSym)
      refine SepWP_weaken_pre_sat_shared_lb
        (SatEntails_shared_lb.sepConj_mono_right (spe_str_after_weaken_shared_lb _ _ _ _ _ _)) ?_
      wp_apply
      have htr_d := (‹AllocCallPreserved $s:ident _›).2.1
      wp_steps_sync_197 ((blkPl_197).base + 7988#64)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, ?_,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      rw [$hsp:ident, show ($s0:ident).sp + 0x5d8#64 + 8#64 = ($s0:ident).sp + 1504#64 by bv_omega,
        show ($s0:ident).sp + 0x5d8#64 + 16#64 = ($s0:ident).sp + 1512#64 by bv_omega]
      exact Entails.of_eq (by sep_ac_rfl)))

private def segExitDropPost [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (p : BitVec 64) (st : M.σ) (s0 s sm : State) (Pm : SepProp) : Prop :=
  ∃ evs : List AllocEvent,
    FreeOnlyEvs evs ∧
    (Pm ⊢ memRegion p 48 ∗
      (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
        stackAt s0.sp allocHookStack ∗ A.pool lim (M.stepEvents evs st) sm)) ∧
    sm.sp = s.sp ∧ sm.trace = s.trace ∧
    sm.readReg64 .x20 = p ∧
    sm.readReg64 .x26 = s.readReg64 .x26 ∧
    sm.readReg64 .x27 = s.readReg64 .x27 ∧
    sm.readReg64 .x28 = s.readReg64 .x28 ∧
    sm.readReg64 .x29 = s.readReg64 .x29 ∧
    calleeSavedVRegs sm = calleeSavedVRegs s

private theorem segExit_drop_invalidState_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (p : BitVec 64) (st : M.σ) (s0 s : State)
    (hpc_s : s.pc = (blkPl_197).base + 7820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hsp_align : s.spAligned = true) :
    SepWP ((blkPC_197).rebase (blkPl_197).base H)
      ((blkPl_197).base + 7988#64) s
      ((lsmpl.ρ exitJumpTableSym ↦ᵣ exitJumpTable_shared_lb) ∗
        (recErrAt A.repAlloc p (.spe .invalidState) ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool lim st s)))
      (segExitDropPost A lim p st s0 s) := by
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hdealloc := ls_hook_ok_226 (by decide) hdealloc_sat
  unfold segExitDropPost
  seg_exit_str_placed_b s hsp s0 st (.spe .invalidState) 1 0x8000000000000001#64 16#64
    (by simpa only [recErrAt] using speAt_invalidState_expose A.repAlloc (utf8 "decrypt") p)

private theorem segExit_drop_invalidMessage_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (p : BitVec 64) (t : MessageType) (r : InvalidMessageReason) (st : M.σ) (s0 s : State)
    (hpc_s : s.pc = (blkPl_197).base + 7820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hsp_align : s.spAligned = true) :
    SepWP ((blkPC_197).rebase (blkPl_197).base H)
      ((blkPl_197).base + 7988#64) s
      ((lsmpl.ρ exitJumpTableSym ↦ᵣ exitJumpTable_shared_lb) ∗
        (recErrAt A.repAlloc p (.spe (.invalidMessage t r)) ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool lim st s)))
      (segExitDropPost A lim p st s0 s) := by
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hdealloc := ls_hook_ok_226 (by decide) hdealloc_sat
  unfold segExitDropPost
  seg_exit_str_placed_b s hsp s0 st (.spe (.invalidMessage t r)) 24 0x8000000000000018#64 39#64
    (by simpa only [recErrAt] using speAt_invalidMessage_expose A.repAlloc (utf8 "decrypt") p t r)

private theorem segExit_drop_one_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (p : BitVec 64) (r : RecErr) (st : M.σ) (s0 s : State)
    (hpc_s : s.pc = (blkPl_197).base + 7820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hsp_align : s.spAligned = true) :
    SepWP ((blkPC_197).rebase (blkPl_197).base H)
      ((blkPl_197).base + 7988#64) s
      ((lsmpl.ρ exitJumpTableSym ↦ᵣ exitJumpTable_shared_lb) ∗
        (recErrAt A.repAlloc p r ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool lim st s)))
      (segExitDropPost A lim p st s0 s) := by
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  unfold segExitDropPost
  cases r with
  | version v =>
    seg_exit_noop_placed_b s0 (.version v) 6 0x8000000000000006#64 21#64
      (SatEntails_shared_lb.of_entails
        (by simp only [recErrAt]; exact sepConj_mono_right (spe_u32_at_8_entails_40_shared_lb _ _)))
  | spe e =>
    cases e with
    | panic =>
      simp only [recErrAt, speAt]
      exact sepWP_false_elim
    | invalidState =>
      exact segExit_drop_invalidState_placed hdealloc_sat p st s0 s hpc_s hrun hsp hsp_align
    | invalidMessage t r =>
      exact segExit_drop_invalidMessage_placed hdealloc_sat p t r st s0 s hpc_s hrun hsp hsp_align
    | invalidProtobufEncoding =>
      seg_exit_noop_placed_b s0 (.spe .invalidProtobufEncoding) 2 0x8000000000000002#64 17#64
        (SatEntails_shared_lb.refl _)
    | ciphertextMessageTooShort n =>
      seg_exit_noop_placed_b s0 (.spe (.ciphertextMessageTooShort n)) 3 0x8000000000000003#64 18#64
        (SatEntails_shared_lb.of_entails
          (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40_shared_lb _ _)))
    | legacyCiphertextVersion v =>
      seg_exit_noop_placed_b s0 (.spe (.legacyCiphertextVersion v)) 4 0x8000000000000004#64 19#64
        (SatEntails_shared_lb.of_entails
          (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_shared_lb _ _)))
    | unrecognizedCiphertextVersion v =>
      seg_exit_noop_placed_b s0 (.spe (.unrecognizedCiphertextVersion v)) 5 0x8000000000000005#64 20#64
        (SatEntails_shared_lb.of_entails
          (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_shared_lb _ _)))
    | noKeyTypeIdentifier =>
      seg_exit_noop_placed_b s0 (.spe .noKeyTypeIdentifier) 7 0x8000000000000007#64 22#64
        (SatEntails_shared_lb.refl _)
    | badKeyType t =>
      seg_exit_noop_placed_b s0 (.spe (.badKeyType t)) 8 0x8000000000000008#64 23#64
        (SatEntails_shared_lb.of_entails
          (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_shared_lb _ _)))
    | badKeyLength n =>
      seg_exit_noop_placed_b s0 (.spe (.badKeyLength n)) 9 0x8000000000000009#64 24#64
        (SatEntails_shared_lb.of_entails
          (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40_shared_lb _ _)))
    | invalidKeyAgreement =>
      seg_exit_noop_placed_b s0 (.spe .invalidKeyAgreement) 10 0x800000000000000a#64 25#64
        (SatEntails_shared_lb.refl _)
    | invalidSessionStructure r =>
      seg_exit_noop_placed_b s0 (.spe (.invalidSessionStructure r)) 20 0x8000000000000014#64 35#64
        (by simp only [recErrAt, speAt]; exact SatEntails_shared_lb.sepConj_mono_right (spe_strRef_at_8_entails_40_shared_lb _ _))
    | duplicatedMessage idx c =>
      seg_exit_noop_placed_b s0 (.spe (.duplicatedMessage idx c)) 23 0x8000000000000017#64 38#64
        (SatEntails_shared_lb.of_entails
          (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40_shared_lb _ _ _)))
  | iscmk =>
    seg_exit_noop_placed_b s0 .iscmk 20 0x8000000000000014#64 35#64
      (iscmk_entails_40_shared_lb A.repAlloc p)

private theorem segExit_main_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : RecordDecryptGhost) (st : M.σ) (S_sess resSlot tape R : SepProp) (s0 s : State)
    (hpc_s : s.pc = recJPCPlaced)
    (hmeta : recMetaPlaced s0 s)
    (hno_pan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hx26 : s.readReg64 .x26 = s0.sp + 0xa0#64)
    (hx27 : s.readReg64 .x27 = x.sret)
    (hx28 : s.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1)
    (hmem : s.mem ⊨ recFramePlaced A.repAlloc x s0.sp ∗ A.pool lim st s ∗ S_sess ∗ resSlot ∗
      (∃∗ errs : List RecErr, errsAt A.repAlloc (s0.sp + 0x5d8#64) errs) ∗
      memRegion (s0.sp + 0xca0#64) 344 ∗ tape ∗ R)
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem) :
    ∃ sf evs_exit, Steps ((blkPC_197).rebase (blkPl_197).base H) s sf ∧
      FreeOnlyEvs evs_exit ∧
      sf.pc = recExitPlaced ∧ sf.status = .Running ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      ((x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧
        sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.readReg64 .x27 = x.sret ∧
        sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧
        sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1) ∧
      (sf.mem ⊨
        memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        S_sess ∗ resSlot ∗
        memRegion (s0.sp + 0x4e0#64) 0x920 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        tape ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool lim (M.stepEvents evs_exit st) sf ∗ R) := by
  obtain ⟨hrun, hsp, hsp_align, hx29, htrace, hfl, hvregs⟩ := hmeta
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hro := hfl.2
  have hdealloc := ls_hook_ok_226 (by decide) hdealloc_sat
  dsimp only [recJPCPlaced] at hpc_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  obtain ⟨errs, hmem⟩ := hmem
  rcases errs with _ | ⟨r_err, _ | ⟨r2, rest⟩⟩
  · have hmem_nil : s.mem ⊨
        (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
         ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64) ∗ A.pool lim st s) ∗
        (recFramePlaced A.repAlloc x s0.sp ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗
         S_sess ∗ resSlot ∗ tape ∗ R) := by
      dsimp only [errsAt] at hmem
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    clear hmem
    have hwp_nil : SepWP ((blkPC_197).rebase (blkPl_197).base H)
        ((blkPl_197).base + 8016#64) s
        (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
         ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64) ∗ A.pool lim st s)
        (fun sf Pf =>
          (Pf ⊢ ((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
            ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64) ∗ A.pool lim st sf) ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      wp_steps_sync_197 ((blkPl_197).base + 8016#64)
      exact SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨Entails.of_eq (by sep_ac_rfl),
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
    rcases hwp_nil.elim hmem_nil hL with
      ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_f, hsp_sf, htr_sf,
        hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    have hmf' := Satisfies.mono (sepConj_mono_left hent_f) hmf
    refine ⟨sf, [], hsteps, FreeOnlyEvs.nil, hpc_sf, hrun_sf, hvregs_sf,
      ⟨hno_pan, htr_sf, hsp_sf, hx29_sf, hx27_sf, hx26_sf, hx28_sf⟩, ?_⟩
    apply recPostPlaced_of_frame_aux st x S_sess resSlot tape R s0 sf 0#64 8#64 0#64
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf'
  · dsimp only [errsAt] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
    obtain ⟨p, hmem⟩ := hmem
    have hmem_ro := rodata_exitJumpTable_placed_intro hro hmem
    clear hmem
    rw [recFramePlaced_split_rep A x s0.sp, RustCliAllocBudget.repAlloc_live_norm] at hmem_ro
    have hmem_p : s.mem ⊨ ⌜p ≠ 0⌝ ∗
        ((((lsmpl.ρ exitJumpTableSym) ↦ᵣ exitJumpTable_shared_lb) ∗
          (recErrAt A.repAlloc p r_err ∗
            (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
              stackAt s0.sp allocHookStack ∗ A.pool lim st s))) ∗
         (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion (p + 48#64) 144 ∗
          recFramePlacedRest A.repAlloc x s0.sp ∗
          memRegion (s0.sp + 0xca0#64) 344 ∗
          S_sess ∗ resSlot ∗ tape ∗ R)) := by
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_ro
    clear hmem_ro
    rw [satisfies_pure_sepConj] at hmem_p
    obtain ⟨_hp, hmem_drop⟩ := hmem_p
    have hdrop := segExit_drop_one_placed hdealloc_sat p r_err st s0 s hpc_s hrun hsp hsp_align
    rcases hdrop.elim hmem_drop hL with ⟨sm, hsteps1,
      ⟨hpc_sm, hrun_sm, Pm, hmm, evs1, hevs1, hent_m, hsp_sm, htr_sm, hx20_sm,
       hx26_sm, hx27_sm, hx28_sm, hx29_sm, hvregs_sm0⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    clear hmem_drop hdrop
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := hvregs_sm0.trans hvregs
    have hmm' := Satisfies.mono (sepConj_mono_left hent_m) hmm
    clear hmm hent_m
    have h192 : memRegion p 192 = memRegion p 48 ∗ memRegion (p + 48#64) 144 := by
      simpa using memRegion_split p 48 144 (by decide)
    have hmm_dealloc : sm.mem ⊨
        (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion p 192 ∗
         stackAt s0.sp allocHookStack ∗ A.pool lim (M.stepEvents evs1 st) sm) ∗
        (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
         recFramePlacedRest A.repAlloc x s0.sp ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗
         S_sess ∗ resSlot ∗ tape ∗ R) := by
      rw [h192]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmm'
    clear hmm'
    have hsp_sm0 : sm.sp = s0.sp := hsp_sm.trans hsp
    have hwp_dealloc : SepWP ((blkPC_197).rebase (blkPl_197).base H)
        ((blkPl_197).base + 8016#64) sm
        (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion p 192 ∗
         stackAt s0.sp allocHookStack ∗ A.pool lim (M.stepEvents evs1 st) sm)
        (fun sf Pf =>
          (Pf ⊢ ((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ stackAt s0.sp allocHookStack ∗
            A.pool lim (M.stepEvents (rustDeallocEvents 192 8) (M.stepEvents evs1 st)) sf) ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      wp_steps_sync_197 (lsmpl.ρ lsRustDeallocSym)
      wp_apply
      have htr_192 := (‹AllocCallPreserved sm _›).2.1
      wp_steps_sync_197 ((blkPl_197).base + 8016#64)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨?_, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      rw [hsp_sm0]
      exact Entails.of_eq (by sep_ac_rfl)
    rcases hwp_dealloc.elim hmm_dealloc (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_f, hsp_sf, htr_sf,
        hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ | ⟨_, hoom⟩⟩
    rotate_left; · exact (not_satisfies_false_sepConj hoom).elim
    clear hmm_dealloc hwp_dealloc
    have hmf' := Satisfies.mono (sepConj_mono_left hent_f) hmf
    clear hmf hent_f
    rw [← M.stepEvents_append evs1 (rustDeallocEvents 192 8) st] at hmf'
    refine ⟨sf, evs1 ++ rustDeallocEvents 192 8, hsteps1.trans hsteps2,
      hevs1.append (FreeOnlyEvs.singleton 8 192), hpc_sf, hrun_sf, hvregs_sf,
      ⟨hno_pan, htr_sf, hsp_sf, hx29_sf, hx27_sf, hx26_sf, hx28_sf⟩, ?_⟩
    apply recPostPlaced_of_frame_aux _ x S_sess resSlot tape R s0 sf 4#64 p 1#64
    rw [recFramePlaced_split_rep A x s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf'
  · dsimp only [errsAt] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (recFramePlaced A.repAlloc x s0.sp ∗ A.pool lim st s ∗ S_sess ∗ resSlot ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗ tape ∗ R) := by
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1

theorem segExit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    SegExitPlacedSpec C A lim ctl uuidTryParse S tdEnv H := by
  intro hdealloc_sat x st_init st R s0 s hJ hL
  obtain ⟨hsb, hpc_s, hmeta, hno_pan, hx26, hx27, hx28, hmem⟩ := hJ
  conv at hmem =>
    simp only [recFramePlaced_atState, sessionStateAt_atState,
      recordResultAt_atState, errsAt_atState, RustCliAllocBudget.atState_pool, sepConj_assoc]
  obtain ⟨sf, evs_exit, hsteps, hevs_exit, hpc_sf, hrun_sf, hvregs_sf, hpure_sf, hmem_sf⟩ :=
    segExit_main_placed hdealloc_sat x st _ _ (tapeAfter ctl x.cur x.rest (x.draws C)) R
      s0 s hpc_s hmeta hno_pan hx26 hx27 hx28 hmem hL
  obtain ⟨evs_total, hst_total, henv_total⟩ := hsb.finish hevs_exit
  rw [hst_total] at hmem_sf
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hvregs_sf, ?_⟩⟩
  dsimp only [recordDecryptPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs_total, ?_⟩
  simp only [sessionStateAt_atState, recordResultAt_atState,
    protocolAddressAt_atState, signalMessageAt_atState,
    RustCliAllocBudget.atState_pool, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨henv_total, hpure_sf, by simpa only [sepConj_assoc] using hmem_sf⟩

end LibsignalBinary.Proofs.TripleRatchet.Record.SegExitBudget
