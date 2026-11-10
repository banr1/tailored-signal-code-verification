/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionRecvPrekeyClosureCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionRecvPrekeyCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Closure Entry/Exit Layout and Outcome Helpers

Separation-logic entry unpacking and exit repacking lemmas for `cliDpPollName` (stack frame
`0xcd0 = 3280` bytes, coroutine size `0x7d8 = 2008` bytes), covering stack budget splits,
`dpFutStartAt` / `dpFutDoneAt` coroutine folding, result conversion into `decResAt`, and
`SubroutineOutcome` post/panic packaging.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Symbol Identity & Stack Budget Lemmas -/

theorem cliDpPollName_eq_closureName :
    cliDpPollName = CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName :=
  rfl

theorem dpPollNeed_eq_frame_add_subStack (B : RunBudgets) :
    dpPollNeed B = 3280 + dpClosSubStack B := by
  dsimp only [dpPollNeed, dpClosSubStack]
  omega

theorem rootStack_le_subStack (B : RunBudgets) :
    rootStack ≤ dpClosSubStack B := by
  have hr : rootStack ≤ 524288 := by decide
  dsimp only [dpClosSubStack]
  omega

theorem stageP1UntrustedCallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) :
    stageP1UntrustedCallStack
      (cliPollSessKit A b F0 Scope peer (cliKitStk B))
      (cliPollIdKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  have hk := cliKitStk_add_alloc_le_subStack B
  dsimp only [DpKitStk.All] at hk
  rcases hk with ⟨h1, h2, _, _, h5, h6, _⟩
  dsimp only [stageP1UntrustedCallStack, stageP1CallStack, loadCallStack,
    MessageDecrypt.Pf.SegTrust.trustCallStack,
    untrustedErrCallStack, cliPollSessKit, cliPollIdKit, cliSessionStoreSpec, cliIdStoreSpecFull,
    cliIdentityStoreSpec]
  have hext : extHookStack = 16384 := rfl
  have hdrop : FromRecordCallees.dropSessionStructureLocal2Stack ≤ 65536 := by decide
  have halloc : allocHookStack = 4096 := rfl
  dsimp only [dpClosSubStack] at h1 h2 h5 h6 ⊢
  omega

theorem stackAt_poll_entry_split (sp0 : BitVec 64) (B : RunBudgets) (stk' : Nat)
    (hge : dpPollNeed B ≤ stk') (hle : stk' ≤ 2 ^ 63) :
    stackAt sp0 stk' =
      memRegion (sp0 - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      stackAt (sp0 - 0xcd0#64) (dpClosSubStack B) ∗
      memRegion (sp0 - 0xcd0#64) 3280 := by
  have h64 : stk' ≤ 2 ^ 64 := by omega
  have hneed64 : dpPollNeed B ≤ 2 ^ 64 := by omega
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have h1 := stackAt_sub_split sp0 stk' (dpPollNeed B) hge h64
  have h2 := stackAt_sub_split sp0 (dpPollNeed B) 3280
    (by rw [dpPollNeed_eq_frame_add_subStack]; omega) hneed64
  have h3 : memRegion (sp0 - BitVec.ofNat 64 (dpPollNeed B)) (dpPollNeed B - 3280) =
      stackAt (sp0 - 0xcd0#64) (dpClosSubStack B) := by
    have hdiff : dpPollNeed B - 3280 = dpClosSubStack B := by
      rw [dpPollNeed_eq_frame_add_subStack]; omega
    rw [hdiff]
    unfold stackAt
    have haddr : sp0 - BitVec.ofNat 64 (dpPollNeed B) =
        (sp0 - 0xcd0#64) - BitVec.ofNat 64 (dpClosSubStack B) := by
      have heq : BitVec.ofNat 64 (dpPollNeed B) =
          0xcd0#64 + BitVec.ofNat 64 (dpClosSubStack B) := by
        rw [dpPollNeed_eq_frame_add_subStack B, BitVec.ofNat_add]
      rw [heq]; bv_omega
    rw [haddr]
  have hsp3280 : stackAt sp0 3280 = memRegion (sp0 - 0xcd0#64) 3280 := rfl
  rw [h3, hsp3280] at h2
  rw [h2, ← sepConj_assoc] at h1
  rw [sepConj_assoc] at h1
  exact h1

theorem stackAt_subStack_split (sp : BitVec 64) (B : RunBudgets) (k : Nat)
    (hkle : k ≤ dpClosSubStack B) (hsub : dpClosSubStack B ≤ 2 ^ 64) :
    stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - k) ∗
      stackAt sp k :=
  stackAt_sub_split sp (dpClosSubStack B) k hkle hsub

/-! ## 2. Context & Coroutine (`0x7d8` = `2008` B) Unpacking and Folding -/

theorem dpCxAt_entails_memRegion32 (cx : BitVec 64) :
    dpCxAt cx ⊢ memRegion cx 32 := by
  unfold dpCxAt
  refine Entails.sepExists_elim fun wk => ?_
  rw [memRegion_split cx 8 24 (by decide),
      memRegion_split (cx + 8#64) 8 16 (by decide),
      memRegion_split (cx + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (Entails.refl _)))

theorem dpWords13_coins_eq_coroInit (img : Obj.Image) (x : DecPkGhost) (fut coins : BitVec 64) :
    dpWordsAt fut (dpSlotArgs img x) ∗ ((fut + 0x68#64) ↦₆₄ coins) =
      decryptPrekeyCoroInitAt fut x.msgA x.peerA x.meA
        (x.stores + 0xf0#64) (sessVt img)
        x.stores (idVt img)
        (x.stores + 0xc8#64) (oneTimeVt img)
        (x.stores + 0x50#64) (signedVt img)
        (x.stores + 0x78#64) (kyberVt img) coins := by
  dsimp only [dpSlotArgs, dpWordsAt, decryptPrekeyCoroInitAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]

/-- Untouched coroutine sub-regions outside both `stageP1_ok_kit` and `stageP1_untrusted_ok_kit`
(`0x280..0x2c0` + `0x2c1..0x2c8` + `0x391..0x398` + `0x3a8..0x428` + `0x468..0x490` +
`0x4b0..0x4f2` + `0x4f3..0x4f8` + `0x4f8..0x7d8`). -/
def coroUnusedP1At (fut : BitVec 64) : SepProp :=
  memRegion (fut + 0x280#64) 64 ∗
  memRegion (fut + 0x2c1#64) 7 ∗
  memRegion (fut + 0x391#64) 7 ∗
  memRegion (fut + 0x3a8#64) 128 ∗
  memRegion (fut + 0x468#64) 40 ∗
  memRegion (fut + 0x4b0#64) 66 ∗
  memRegion (fut + 0x4f3#64) 5 ∗
  memRegion (fut + 0x4f8#64) 736

theorem dpFutStartAt_split_for_p1 (img : Obj.Image) (x : DecPkGhost) (fut : BitVec 64) :
    dpFutStartAt fut (dpSlotArgs img x) =
      (∃∗ b_4f2 : BitVec 8, ∃∗ u_3a0 : BitVec 64,
       ∃∗ u_398 : BitVec 64, ∃∗ b_390 : BitVec 8, ∃∗ coins : BitVec 64,
        decryptPrekeyCoroInitAt fut x.msgA x.peerA x.meA
          (x.stores + 0xf0#64) (sessVt img)
          x.stores (idVt img)
          (x.stores + 0xc8#64) (oneTimeVt img)
          (x.stores + 0x50#64) (signedVt img)
          (x.stores + 0x78#64) (kyberVt img) coins ∗
        cells (fut + 0x70#64) 14 ∗
        cells (fut + 0xe0#64) 4 ∗
        memRegion (fut + 0x100#64) 336 ∗
        cells (fut + 0x250#64) 6 ∗
        ((fut + 0x2c0#64) ↦₈ 0#8) ∗
        cells (fut + 0x2c8#64) 25 ∗
        ((fut + 0x390#64) ↦₈ b_390) ∗
        ((fut + 0x398#64) ↦₆₄ u_398) ∗
        ((fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
        cells (fut + 0x428#64) 8 ∗
        cells (fut + 0x490#64) 4 ∗
        ((fut + 0x4f2#64) ↦₈ b_4f2) ∗
        coroUnusedP1At fut) := by
  unfold dpFutStartAt coroUnusedP1At
  change dpWordsAt fut (dpSlotArgs img x) ∗
    (∃∗ coins : BitVec 64, (fut + 0x68#64) ↦₆₄ coins) ∗
    memRegion (fut + 0x70#64) 592 ∗
    ((fut + 0x2c0#64) ↦₈ 0#8) ∗
    memRegion (fut + 0x2c1#64) 1303 = _
  have h592 : memRegion (fut + 0x70#64) 592 =
      cells (fut + 0x70#64) 14 ∗ cells (fut + 0xe0#64) 4 ∗
      memRegion (fut + 0x100#64) 336 ∗ cells (fut + 0x250#64) 6 ∗
      memRegion (fut + 0x280#64) 64 := by
    rw [memRegion_split (fut + 0x70#64) 112 480 (by decide),
        memRegion_split (fut + 0x70#64 + 112#64) 32 448 (by decide),
        memRegion_split (fut + 0x70#64 + 112#64 + 32#64) 336 112 (by decide),
        memRegion_split (fut + 0x70#64 + 112#64 + 32#64 + 336#64) 48 64 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [ProofLib.memRegion_cells (fut + 0x70#64) 14 (by decide),
        ProofLib.memRegion_cells (fut + 0xe0#64) 4 (by decide),
        ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide)]
  have h1303 : memRegion (fut + 0x2c1#64) 1303 =
      memRegion (fut + 0x2c1#64) 7 ∗
      memRegion ((fut - 1112#64) + 1824#64) 560 ∗
      memRegion (fut + 0x4f8#64) 736 := by
    rw [memRegion_split (fut + 0x2c1#64) 7 1296 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64) 560 736 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h2c8 : fut + 0x2c8#64 = (fut - 1112#64) + 1824#64 := by bv_omega
    rw [h2c8]
  have h560 := coro_1824_560_split_for_p1 (fut - 1112#64)
  dsimp only at h560
  have hbase : (fut - 1112#64) + 1112#64 = fut := by bv_omega
  rw [hbase] at h560
  rw [h592, h1303, h560]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  refine congrArg sepExists (funext fun b_4f2 => ?_)
  refine congrArg sepExists (funext fun u_3a0 => ?_)
  refine congrArg sepExists (funext fun u_398 => ?_)
  refine congrArg sepExists (funext fun b_390 => ?_)
  refine congrArg sepExists (funext fun coins => ?_)
  rw [dpWords13_coins_eq_coroInit img x fut coins]
  ac_rfl

/-- Untouched stack sub-regions of `memRegion sp 3280` for `stageP1_untrusted_ok_kit`. -/
def closStackUnusedUntrustedAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x8#64) 160 ∗
  memRegion (sp + 0x234#64) 316 ∗
  memRegion (sp + 0x394#64) 76 ∗
  memRegion (sp + 0x550#64) 1344 ∗
  memRegion (sp + 0xac0#64) 432

theorem clos_stack_3280_split_for_p1_untrusted (sp0 : BitVec 64) :
    let sp := sp0 - 0xcd0#64
    memRegion sp 3280 =
      (∃∗ u_a8 : BitVec 64, ∃∗ u_b0 : BitVec 64, ∃∗ u_b8 : BitVec 64,
       ∃∗ u_c0 : BitVec 64, ∃∗ u_c8 : BitVec 64, ∃∗ u_d0 : BitVec 64,
       ∃∗ v_sp0 : BitVec 64,
        (sp ↦₆₄ v_sp0) ∗
        ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
        ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
        ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
        ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
        ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0xa90#64) 6 ∗
        cells (sp0 - 0x60#64) 12 ∗
        closStackUnusedUntrustedAt sp) := by
  dsimp only
  let sp := sp0 - 0xcd0#64
  change memRegion sp 3280 = _
  rw [memRegion_split sp 8 3272 (by decide),
      memRegion_split (sp + 8#64) 160 3112 (by decide),
      memRegion_split (sp + 8#64 + 160#64) 48 3064 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64) 348 2716 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64) 316 2400 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64 + 316#64) 36 2364 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64 + 316#64 + 36#64) 76 2288 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64 + 316#64 + 36#64 + 76#64) 368 1920 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64 + 316#64 + 36#64 + 76#64 + 368#64) 1344 576 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64 + 316#64 + 36#64 + 76#64 + 368#64 + 1344#64) 48 528 (by decide),
      memRegion_split (sp + 8#64 + 160#64 + 48#64 + 348#64 + 316#64 + 36#64 + 76#64 + 368#64 + 1344#64 + 48#64) 432 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h_c70 : sp + 0xc70#64 = sp0 - 0x60#64 := by dsimp only [sp]; bv_omega
  have h1 : memRegion sp 8 = (∃∗ v_sp0 : BitVec 64, sp ↦₆₄ v_sp0) := by
    rw [ProofLib.memRegion_cells sp 1 (by decide)]
    simp only [cells, sepConj_emp]
  have h6 : memRegion (sp + 0xa8#64) 48 =
      (∃∗ u_a8 : BitVec 64, ∃∗ u_b0 : BitVec 64, ∃∗ u_b8 : BitVec 64,
       ∃∗ u_c0 : BitVec 64, ∃∗ u_c8 : BitVec 64, ∃∗ u_d0 : BitVec 64,
        ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
        ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
        ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0)) := by
    rw [ProofLib.memRegion_cells (sp + 0xa8#64) 6 (by decide)]
    simp only [cells_succ, cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_right]
  rw [h_c70, h1, h6,
      ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide),
      ProofLib.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
  unfold closStackUnusedUntrustedAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun u_a8 => ?_)
  refine congrArg sepExists (funext fun u_b0 => ?_)
  refine congrArg sepExists (funext fun u_b8 => ?_)
  refine congrArg sepExists (funext fun u_c0 => ?_)
  refine congrArg sepExists (funext fun u_c8 => ?_)
  refine congrArg sepExists (funext fun u_d0 => ?_)
  refine congrArg sepExists (funext fun v_sp0 => ?_)
  dsimp only [sp]
  ac_rfl

/-! ## 4. Coroutine & Stack Exit Folding + Sret Bridges -/

theorem savedRegs_entails_memRegion_96' (sp0 : BitVec 64) (s0 : State) :
    decryptPrekeySavedRegsAt sp0 s0 ⊢ memRegion (sp0 - 0x60#64) 96 := by
  unfold decryptPrekeySavedRegsAt
  rw [ProofLib.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_comm _ (sp0 - 0x60#64),
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
    (Entails.sepExists_right (s0.readReg64 .x28)
    (Entails.sepExists_right (s0.readReg64 .x27)
    (Entails.sepExists_right (s0.readReg64 .x26)
    (Entails.sepExists_right (s0.readReg64 .x25)
    (Entails.sepExists_right (s0.readReg64 .x24)
    (Entails.sepExists_right (s0.readReg64 .x23)
    (Entails.sepExists_right (s0.readReg64 .x22)
    (Entails.sepExists_right (s0.readReg64 .x21)
    (Entails.sepExists_right (s0.readReg64 .x20)
    (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))))

theorem clos_stack_3280_of_p1_untrusted (sp0 : BitVec 64) (s0 : State)
    (v_sp0 v_a8 v_b0 v_b8 v_c0 v_c8 v_d0 : BitVec 64) :
    let sp := sp0 - 0xcd0#64
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ v_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ v_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (sp + 0xa90#64) 6 ∗
    decryptPrekeySavedRegsAt sp0 s0 ∗
    closStackUnusedUntrustedAt sp ⊢ memRegion sp 3280 := by
  dsimp only
  have hcells12 : decryptPrekeySavedRegsAt sp0 s0 ⊢ cells (sp0 - 0x60#64) 12 := by
    rw [← ProofLib.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
    exact savedRegs_entails_memRegion_96' sp0 s0
  rw [clos_stack_3280_split_for_p1_untrusted sp0]
  refine Entails.sepExists_right v_a8 (Entails.sepExists_right v_b0
    (Entails.sepExists_right v_b8 (Entails.sepExists_right v_c0
    (Entails.sepExists_right v_c8 (Entails.sepExists_right v_d0
    (Entails.sepExists_right v_sp0 ?_))))))
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hcells12)))))))))))

theorem coroInit_entails_memRegion_112
    (fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng : BitVec 64) :
    decryptPrekeyCoroInitAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng ⊢
      memRegion fut 112 := by
  unfold decryptPrekeyCoroInitAt
  rw [ProofLib.memRegion_cells fut 14 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_right]
  exact Entails.sepExists_right msgA (Entails.sepExists_right peerA
    (Entails.sepExists_right meA (Entails.sepExists_right sPtr
    (Entails.sepExists_right sVt (Entails.sepExists_right iPtr
    (Entails.sepExists_right iVt (Entails.sepExists_right pkPtr
    (Entails.sepExists_right pkVt (Entails.sepExists_right spkPtr
    (Entails.sepExists_right spkVt (Entails.sepExists_right kPtr
    (Entails.sepExists_right kVt (Entails.sepExists_right rng (Entails.refl _))))))))))))))

theorem coroCopy_entails_memRegion_112
    (fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng : BitVec 64) :
    decryptPrekeyCoroCopyAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng ⊢
      memRegion (fut + 0x70#64) 112 := by
  unfold decryptPrekeyCoroCopyAt
  rw [ProofLib.memRegion_cells (fut + 0x70#64) 14 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_right]
  exact Entails.sepExists_right msgA (Entails.sepExists_right peerA
    (Entails.sepExists_right meA (Entails.sepExists_right sPtr
    (Entails.sepExists_right sVt (Entails.sepExists_right iPtr
    (Entails.sepExists_right iVt (Entails.sepExists_right pkPtr
    (Entails.sepExists_right pkVt (Entails.sepExists_right spkPtr
    (Entails.sepExists_right spkVt (Entails.sepExists_right kPtr
    (Entails.sepExists_right kVt (Entails.sepExists_right rng (Entails.refl _))))))))))))))

/-- Any `RunDrop.SpeOwned` error witness at `out` entails `decResAt A out (.error err)`. -/
theorem speOwnedAt_entails_decResAt_err (A : RustAlloc) (out : BitVec 64)
    (k : RunDrop.SpeOwned) (err : ApiError AddrVal Unit) :
    RunDrop.speOwnedAt A out k ⊢ decResAt A out (.error err) := by
  dsimp only [decResAt]
  exact Entails.sepExists_right k (Entails.refl _)

/-- `vecResultAt A out (.ok pt)` entails `decResAt A out (.ok pt)`. -/
theorem decResultAt_entails_decResAt_ok (A : RustAlloc) (out : BitVec 64) (pt : E2E.Bytes) :
    vecResultAt A out (.ok pt) ⊢ decResAt A out (.ok pt) :=
  Entails.refl _

/-- `apiDecResultAt A out (.error (.untrustedIdentity addr))` entails `decResAt` directly. -/
theorem apiDecResultAt_untrusted_entails_decResAt (A : RustAlloc) (out : BitVec 64)
    (addr : AddrVal) :
    apiDecResultAt A out (.error (.untrustedIdentity addr)) ⊢
      decResAt A out (.error (.untrustedIdentity addr)) :=
  speOwnedAt_entails_decResAt_err A out (.untrustedIdentity addr) (.untrustedIdentity addr)

/-- Generic `dpFutDoneAt` introduction from `[0..704)`, `[+0x2c0] = 1#8`, and `[0x2c1..2008)`. -/
theorem dpFutDoneAt_of_regions (fut : BitVec 64) :
    memRegion fut 704 ∗ ((fut + 0x2c0#64) ↦₈ 1#8) ∗ memRegion (fut + 0x2c1#64) 1303 ⊢
      dpFutDoneAt fut :=
  Entails.refl _

theorem processPrekeyInnerInitAt_entails_cells25
    (fut msgA peerA meA iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt : BitVec 64) :
    processPrekeyInnerInitAt fut msgA peerA meA iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt ⊢
      cells (fut + 0x2c8#64) 25 := by
  unfold processPrekeyInnerInitAt
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_right]
  exact Entails.sepExists_right msgA (Entails.sepExists_right peerA
    (Entails.sepExists_right meA (Entails.sepExists_right (fut + 0xe0#64)
    (Entails.sepExists_right iPtr (Entails.sepExists_right iVt
    (Entails.sepExists_right pkPtr (Entails.sepExists_right pkVt
    (Entails.sepExists_right spkPtr (Entails.sepExists_right spkVt
    (Entails.sepExists_right kPtr (Entails.sepExists_right kVt
    (Entails.sepExists_right msgA (Entails.sepExists_right peerA
    (Entails.sepExists_right meA (Entails.sepExists_right (fut + 0xe0#64)
    (Entails.sepExists_right iPtr (Entails.sepExists_right iVt
    (Entails.sepExists_right pkPtr (Entails.sepExists_right pkVt
    (Entails.sepExists_right spkPtr (Entails.sepExists_right spkVt
    (Entails.sepExists_right kPtr (Entails.sepExists_right kVt
    (Entails.sepExists_right (msgA + 0xc8#64) (Entails.refl _)))))))))))))))))))))))))

/-- Fold the coroutine postcondition of `stageP1_untrusted_ok_kit` + untouched `coroUnusedP1At`
fields back into `dpFutDoneAt fut`. -/
theorem coro_of_p1_untrusted_entails_dpFutDoneAt
    (fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng : BitVec 64)
    (b_4f2 : BitVec 8) :
    decryptPrekeyCoroInitAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng ∗
    decryptPrekeyCoroCopyAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng ∗
    memRegion (fut + 0xe0#64) 368 ∗
    cells (fut + 0x250#64) 6 ∗
    ((fut + 0x2c0#64) ↦₈ 1#8) ∗
    processPrekeyInnerInitAt fut msgA peerA meA iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗
    cells (fut + 0x398#64) 2 ∗
    cells (fut + 0x428#64) 8 ∗
    cells (fut + 0x490#64) 4 ∗
    ((fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At fut ⊢ dpFutDoneAt fut := by
  have hinit := coroInit_entails_memRegion_112 fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng
  have hcopy := coroCopy_entails_memRegion_112 fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng
  have hinner : processPrekeyInnerInitAt fut msgA peerA meA iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt ⊢
      memRegion (fut + 0x2c8#64) 200 := by
    rw [ProofLib.memRegion_cells (fut + 0x2c8#64) 25 (by decide)]
    exact processPrekeyInnerInitAt_entails_cells25 fut msgA peerA meA iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt
  have hb390 := pointsTo8_entails_memRegion (fut + 0x390#64) 1#8
  have hb4f2 := pointsTo8_entails_memRegion (fut + 0x4f2#64) b_4f2
  rw [← ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide),
      ← ProofLib.memRegion_cells (fut + 0x398#64) 2 (by decide),
      ← ProofLib.memRegion_cells (fut + 0x428#64) 8 (by decide),
      ← ProofLib.memRegion_cells (fut + 0x490#64) 4 (by decide)]
  refine Entails.trans
    (sepConj_mono hinit
      (sepConj_mono hcopy
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hinner
            (sepConj_mono hb390
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left hb4f2))))))))))) ?_
  unfold coroUnusedP1At dpFutDoneAt
  dsimp only [dpFutStateOff, dpFutSize]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  have h704 : memRegion fut 704 =
      memRegion fut 112 ∗ memRegion (fut + 0x70#64) 112 ∗ memRegion (fut + 0xe0#64) 368 ∗
      memRegion (fut + 0x250#64) 48 ∗ memRegion (fut + 0x280#64) 64 := by
    rw [memRegion_split fut 112 592 (by decide),
        memRegion_split (fut + 112#64) 112 480 (by decide),
        memRegion_split (fut + 112#64 + 112#64) 368 112 (by decide),
        memRegion_split (fut + 112#64 + 112#64 + 368#64) 48 64 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1303 : memRegion (fut + 0x2c1#64) 1303 =
      memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x2c8#64) 200 ∗
      memRegion (fut + 0x390#64) 1 ∗ memRegion (fut + 0x391#64) 7 ∗
      memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x3a8#64) 128 ∗
      memRegion (fut + 0x428#64) 64 ∗ memRegion (fut + 0x468#64) 40 ∗
      memRegion (fut + 0x490#64) 32 ∗ memRegion (fut + 0x4b0#64) 66 ∗
      memRegion (fut + 0x4f2#64) 1 ∗ memRegion (fut + 0x4f3#64) 5 ∗
      memRegion (fut + 0x4f8#64) 736 := by
    rw [memRegion_split (fut + 0x2c1#64) 7 1296 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64) 200 1096 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64) 1 1095 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64) 7 1088 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64) 16 1072 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64) 128 944 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64) 64 880 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64) 40 840 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64) 32 808 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64 + 32#64) 66 742 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64 + 32#64 + 66#64) 1 741 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64 + 32#64 + 66#64 + 1#64) 5 736 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h704, h1303]
  exact Entails.of_eq (by ac_rfl)

/-- Expose `((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList)` inside `preKeyMsgAt` for Stage P1. -/
def preKeyMsgRemIdKeyAt (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) : SepProp :=
  signalMessageAt A g.msg a m.message ∗ optU32At (a + 0x78#64) m.preKeyId ∗
    boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗ optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
    ((a + 0xa8#64) ↦ₛ m.baseKey.bytes.toList) ∗
    ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
    ((a + 0xf0#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0xf1#64) 7

theorem preKeyMsgAt_eq_idKey_sep (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) :
    preKeyMsgAt A g a m =
      ((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemIdKeyAt A g a m := by
  unfold preKeyMsgAt preKeyMsgRemIdKeyAt
  ac_rfl

/-! ## 5. `slotOutTr` & `CalleeSavedPreserved` Introduction Helpers -/

theorem slotOutTr_of_err {α : Type} {ans : SlotAns α} (g' : StoresGhost)
    {err : ApiError AddrVal Unit} (tr0 tr1 : List TraceEvent)
    (hnp : err ≠ .panic) (hns : err ≠ .store ()) (hans : ans = some none) :
    slotOutTr ans g' (.error err) tr0 tr1 :=
  ⟨fun h => hnp (Except.error.inj h), fun h => hns (Except.error.inj h), hans⟩

theorem slotOutTr_of_ok {α : Type} {ans : SlotAns α} {g' : StoresGhost} {v : α}
    (tr0 tr1 : List TraceEvent)
    (hans : ans = some (some (g', v))) (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) :
    slotOutTr ans g' (.ok v) tr0 tr1 :=
  ⟨nofun, nofun, hans, hwr⟩

theorem calleeSavedPreserved_of_closure {s0 sf : State}
    (hcs : ClosureCalleeSaved s0 sf)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, _⟩
  exact ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hvregs⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

