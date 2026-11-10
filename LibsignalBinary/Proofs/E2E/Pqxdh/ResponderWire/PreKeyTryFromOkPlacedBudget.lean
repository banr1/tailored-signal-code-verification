/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoopBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Top-Level Proof

Composes the budget-threaded post-loop segments (`+1120 → +1284`) and epilogue (`+1284 .. +1316`) to
establish top-level `RustCliAllocBudget M` correctness (`preKeyTryFrom_placed_ok` and
`preKeyTryFrom_cro_placed_ok`) for Block `111` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet hiding tryCloneFromRefSpec
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  int32MergeSpec bytesMergeRawSpec
open CryptoVerification.LibsignalTripleRatchet.Wire hiding
  TripleRatchetHooksWPlaced TryFromDepsPlaced
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  dropSpeSpec lsRustDeallocSym blkPC_5 blkPl_5
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  SepWPp SepWPp.pure_pre SepWPp.exists_pre SepWPp.mono_pre
  PreKeyDeallocOk preKeyDeallocOk_of_hookSat PreKeyDropSpeOk
  PreKeyIntoBoxOk PreKeySigTryFromOk PreKeyTryCloneOk
  preKeyIntoBoxOk_of_hooks preKeyTryCloneOk_of_hooks int32Merge_ok_at_prekey_placed
  preKeyDropSpeOk_cro_of_hookSat preKeySigTryFromOk_cro_of_deps
  post_seg4_ok_placed_wp post_seg4_after_signal_placed_wp
  post_f90_to_034_placed_wp preKeyTryFromPlacedRawSpec preKeyTryFromPlacedSpec
  epilogue_034_placed_wp preKeyTryFrom_inv_ok preKeyTryFrom_placed_ok_of_callees
  preKeyTryFrom_placed_ok preKeyTryFrom_placed_ok_at
  preKeyTryFrom_cro_placed_ok preKeyTryFrom_cro_placed_ok_at
  preKey_entry_to_f90_placed_wp
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs SeqEnv
  RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec framelessMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (int32MergeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeRawSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget (
  TripleRatchetHooksWPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget (
  TryFromPostEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget (TryFromDepsPlaced)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (
  preKeyLoopEvents PreKeyLoopEnv PreKeySeg2Env PreKeySeg4OkEnv PreKeySeg4Env
  FromSeg3Env FromSeg2Env PreKeyPostEnv PreKeyTryFromEnv
  preKeyTryFromPlacedRawEnvSpec preKeyTryFromPlacedEnvSpec
  preKeyTryFromPlacedRawSpec preKeyTryFromPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoopBudget (
  preKey_entry_to_f90_placed_wp
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  preKeyNoPanicQp
  SepWPp.of_sepWP_end_noPanic_pk SepWPp.let_state SepWPp.frame_noPanic_pk
  PreKeyDeallocOk preKeyDeallocOk_of_hookSat PreKeyDropSpeOk
  post_seg1a_f90_to_0ac_placed_wp post_seg1b_0ac_to_1b4_placed_wp
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget (
  SigTryFromEnv SigTryFromConcreteEnv
  PreKeyIntoBoxOk PreKeySigTryFromOkGen PreKeySigTryFromOk
  post_seg2_1b4_to_360_placed_wp post_seg3_360_to_3a8_placed_wp
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux (
  PreKeyTryCloneOk
  preKeyIntoBoxOk_of_hooks
  preKeyTryCloneOk_of_hooks
  int32Merge_ok_at_prekey_placed
  preKeyDropSpeOk_cro_of_hookSat
  preKeySigTryFromOk_cro_of_deps
  post_seg4_ok_placed_wp
  post_seg4_after_signal_placed_wp
)

export LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux (
  PreKeyTryCloneOk
  preKeyIntoBoxOk_of_hooks
  preKeyTryCloneOk_of_hooks
  int32Merge_ok_at_prekey_placed
  preKeyDropSpeOk_cro_of_hookSat
  preKeySigTryFromOk_cro_of_deps
  post_seg4_ok_placed_wp
  post_seg4_after_signal_placed_wp
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## `SepWPp` Bind/Frame and `FreeOnlyEvs` Helpers -/

private theorem sepWPp_strengthen_inv {prog : Program} {ret : BitVec 64}
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s0 : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s0.mem) (h : SepWPp prog ret s0 P Q Qp) :
    SepWPp prog ret s0 P (fun sf Pf => Inv sf.mem ∧ Q sf Pf) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, ⟨hkf hinv hsteps.keepsFrozen, hq⟩, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

private theorem sepWPp_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64}
    {s : State} {P F : SepProp} {Qm Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm preKeyNoPanicQp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog ret sm (Pm ∗ F) Q preKeyNoPanicQp) :
    SepWPp prog ret s (P ∗ F) Q preKeyNoPanicQp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  rcases h1 (F ∗ R) hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hqm, hvm⟩ | ⟨_, _, _, hp⟩ | ⟨_, hoom⟩⟩
  · rw [← sepConj_assoc] at hmm
    rcases h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpan⟩
    · exact ⟨sf, hsteps1.trans hsteps2, Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hvm⟩⟩
    · exact ⟨sf, hsteps1.trans hsteps2, Or.inr hpan⟩
  · exact False.elim hp
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem freeOnlyEvs_append {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) :
    FreeOnlyEvs (evs₁ ++ evs₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

/-! ## Stack Reassembly Helpers and Chained Post-Loop (`+1120 → +1284`) -/

private theorem memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗ memRegion (sp' + 16#64) 96 ∗
      memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 := by
  rw [show (296 : Nat) = 12 + (4 + (96 + (32 + (32 + (112 + 8))))) by decide,
    Prost.memRegion_split sp' 12 284 (by decide),
    Prost.memRegion_split (sp' + 12#64) 4 280 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64) 96 184 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64) 32 152 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64) 32 120 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64 + 32#64) 112 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem spills96_entails_memRegion (sp' : BitVec 64)
    (w16 w20 w24 w28 w48 w52 w56 w60 w68 : BitVec 32)
    (w32 w40 w72 w80 w88 w96 w104 : BitVec 64) :
    ((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
    ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
    ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
    ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
    ((sp' + 56#64) ↦₃₂ w56) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗
    memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
    ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
    ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
    ((sp' + 104#64) ↦₆₄ w104) ⊢
      memRegion (sp' + 16#64) 96 := by
  rw [show (96 : Nat) =
      4 + (4 + (4 + (4 + (8 + (8 + (4 + (4 +
        (4 + (4 + (4 + (4 + (8 + (8 + (8 + (8 + 8)))))))))))))))
      by decide,
    Prost.memRegion_split (sp' + 16#64) 4 92 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 4 52 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64) 4 48
      (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 44 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 40 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64) 8 32 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (sepConj_mono (pointsTo32_entails_memRegion _ _)
                      (sepConj_mono_right
                        (sepConj_mono (pointsTo32_entails_memRegion _ _)
                          (sepConj_mono (pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (pointsTo64_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                  (pointsTo64_entails_memRegion _ _))))))))))))))))

private theorem region152_repack (sp' w296 w304 w440 : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ w296) ∗ ((sp' + 304#64) ↦₆₄ w304) ∗
    memRegion (sp' + 312#64) 120 ∗ memRegion (sp' + 432#64) 8 ∗
    ((sp' + 440#64) ↦₆₄ w440) ⊢ memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 8 + (8 + (120 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 296#64) 8 144 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64) 8 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64) 120 16 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64 + 120#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))

private theorem stackAt_preKeyTryFrom_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) smallRootStack ∗
    memRegion (sp - 608#64) 296 ∗ memRegion (sp - 608#64 + 296#64) 152 ∗
    memRegion (sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

set_option maxHeartbeats 800000 in
theorem post_f90_to_034_placed_wp_gen [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {postEnv : List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdealloc : PreKeyDeallocOk Inv A lim H)
    (hDropSpe : PreKeyDropSpeOk Inv A lim H)
    (hIntoBox : PreKeyIntoBoxOk Inv A lim H)
    (hSigTryFrom : PreKeySigTryFromOkGen Inv postEnv A lim H)
    (hTryClone : PreKeyTryCloneOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {opkVal : BitVec 32}
    (hlt : x.bytes.length < 2 ^ 32)
    (hfits : FitsEnv M lim st (PreKeyPostEnv (SigTryFromEnv postEnv) x))
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hinv : Inv s.mem) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ memRegion sp' 296 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, PreKeyPostEnv (SigTryFromEnv postEnv) x evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A.repAlloc x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
          memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152 ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  have hlt_in : x.inner.length < 2 ^ 32 := (psmRem_lengths_lt x hlt).2.2.2.2.2.2.2.2.2
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk⟩ :=
    exists_pkBytesOf x.baseKey.toList (List.Vector.toList_length x.baseKey)
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.idPub)
  refine SepWPp.mono_pre
    (P' := (memRegion (sp' + 16#64) 96 ∗
        vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack) ∗
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ lsLogOff))
    (by
      rw [memRegion296_split sp']
      apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (post_seg1a_f90_to_0ac_placed_wp hkf hDropSpe hpc hrun hregs hsp hinv htr hx24) ?_
  intro s1 P1 hpc1 hrun1 ⟨evs1a, hevs1a, hst1, hky_lt, hbk_lt, hik_lt, hmsg_lt,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx24_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1,
    hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  clear hent1
  refine SepWPp.mono_pre
    (P' := (((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs1a st) s1 ∗ stackAt sp' smallRootStack) ∗
      (((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗
        ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by
      dsimp only [seg1SpillsAt]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (post_seg1b_0ac_to_1b4_placed_wp (st := M.stepEvents evs1a st) hkf hcl_of_inv hDropSpe
      hst1 hpc1 hrun1 hik_lt hmsg_lt
      hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
  intro s2 P2 hpc2 hrun2
    ⟨evs1b, hevs1b, hst2, hx29_2, hx28_2, hx27_2, hx26_2, hx25_2, hx24_2, hx23_2, hx22_2, hx21_2,
      hx20_2, hx19_2, hent2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
  clear hent2
  have hevs1 : FreeOnlyEvs (evs1a ++ evs1b) := freeOnlyEvs_append hevs1a hevs1b
  have hfits_from2 : FitsEnv M lim (M.stepEvents (evs1a ++ evs1b) st)
      (FromSeg2Env (SigTryFromEnv postEnv) x) :=
    FitsEnv.seq_right hfits hevs1
  refine SepWPp.mono_pre
    (P' := (memRegion (sp' + 12#64) 4 ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
        memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
        A.pool lim (M.stepEvents (evs1a ++ evs1b) st) s2 ∗ stackAt sp' smallRootStack) ∗
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ lsLogOff ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by
      rw [M.stepEvents_append evs1a evs1b st]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (post_seg2_1b4_to_360_placed_wp (st := M.stepEvents (evs1a ++ evs1b) st)
      hkf hIntoBox (FitsEnv.seq_left hfits_from2) hpk hst2 hpc2 hrun2 hky_lt
      hx29_2 hx28_2 hx27_2 hx26_2 hx25_2 hx23_2 hx22_2 hx21_2 hx20_2 hx19_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨evs2, hevs2, kyberBoxPtr, hst3,
    hx29_3, hx28_3, hx27_3, hx26_3, hx25_3, hx24_3, hx23_3, hx22_3, hx21_3, hx20_3, hx19_3,
    hent3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_
  clear hent3
  have hfits_from3 : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st))
      (FromSeg3Env (SigTryFromEnv postEnv) x) :=
    FitsEnv.seq_right hfits_from2 hevs2
  refine SepWPp.mono_pre
    (P' := (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st)) s3 ∗
        stackAt sp' smallRootStack) ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        memRegion (sp' + 64#64) 4 ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        memRegion (sp' + 432#64) 8 ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (post_seg3_360_to_3a8_placed_wp
      (st := M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st))
      hkf hcl_of_inv hSigTryFrom (FitsEnv.seq_left hfits_from3)
      hik hlt_in hst3 hpc3 hrun3
      hx29_3 hx28_3 hx26_3 hx25_3 hx24_3 hx23_3 hx22_3 hx21_3 hx20_3 hx19_3) ?_
  intro s4 P4 hpc4 hrun4
    ⟨evs3, hevs3, hst4, hx29_4, hx28_4, hx27_4, hx26_4, hx25_4, hx24_4, hx23_4, hx22_4, hx21_4,
      hx20_4, hx19_4, hent4⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent4) ?_
  clear hent4
  have hfits_seg4 :
      FitsEnv M lim
        (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st)))
        (PreKeySeg4Env x) :=
    FitsEnv.seq_right hfits_from3 hevs3
  refine SepWPp.mono_pre
    (P' := (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion (sp' + 176#64) 112 ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        A.pool lim
          (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st))) s4 ∗
        stackAt sp' smallRootStack) ∗
      (lsLogOff ∗ memRegion sp' 12 ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 60#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 64#64) 4 ∗
        spUnused112 sp' ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        memRegion (sp' + 432#64) 8 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.frame_noPanic_pk
    (post_seg4_after_signal_placed_wp
      (st := M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st)))
      hkf hdealloc hTryClone hlt hfits_seg4 hopk hpk hik
      hst4 hpc4 hrun4 hx29_4 hx28_4 hx26_4 hx25_4 hx24_4 hx23_4 hx22_4 hx21_4 hx20_4 hx19_4)
    fun sf Pf ⟨evs4, hevs4, hstf, hentf⟩ => ?_
  refine ⟨(evs1a ++ evs1b) ++ (evs2 ++ (evs3 ++ evs4)),
    SeqEnv.append hevs1 (SeqEnv.append hevs2 (SeqEnv.append hevs3 hevs4)),
    hstf, ?_⟩
  rw [M.stepEvents_append (evs1a ++ evs1b) (evs2 ++ (evs3 ++ evs4)) st,
      M.stepEvents_append evs2 (evs3 ++ evs4) (M.stepEvents (evs1a ++ evs1b) st),
      M.stepEvents_append evs3 evs4 (M.stepEvents evs2 (M.stepEvents (evs1a ++ evs1b) st))]
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hm12 := pointsTo32_entails_memRegion (sp' + 12#64) (b7.zeroExtend 32)
  have hm96 := spills96_entails_memRegion sp'
    x.kpkId (opkTag x) opkVal x.spkId 1#32 x.regId x.regId 0#32 (b8.zeroExtend 32)
    (BitVec.ofNat 64 x.inner.length) 1569#64 w15 bkPtr bkCap msgPtr ikPtr
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
  have hm144 :
      ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ⊢
        memRegion (sp' + 144#64) 32 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words4_entails_memRegion32 (sp' + 144#64) ik0 ik1 ik2 ik3
  have hm152 := region152_repack sp' (cur8 x) 0#64 (sp' + 296#64)
  rw [memRegion296_split sp']
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono
        (sepConj_mono_right
          (sepConj_mono hm12 (sepConj_mono hm96 (sepConj_mono hm112 (sepConj_mono_left hm144)))))
        (sepConj_mono_left hm152))))
  simp only [sepConj_assoc]
  apply entails_of_eq; sep_ac_rfl

abbrev post_f90_to_034_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m) :=
  @post_f90_to_034_placed_wp_gen _ Inv hkf hcl_of_inv TryFromPostEnv

/-! ## Epilogue (`+1284 .. +1316`) and Top-Level `preKeyTryFrom_placed_ok` -/

theorem epilogue_034_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {Env : PreKeyTryFromArgs → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st : M.σ} {evs : List AllocEvent}
    {H : LibsignalHooks}
    {x : PreKeyTryFromArgs} {s0 s : State}
    (hevs : Env x evs)
    (_hsp0 : s0.spAligned = true)
    (hst : PreKeyPostState Inv s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        preKeyResultAt A.repAlloc x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs st) s)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyTryFromPlacedRawEnvSpec Env M A lim).post (x, st) s0 sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  unfold preKeyCalleeSavedAt
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv ?_
  wp_steps_sync_111 (s0.readReg64 .x30)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun _hinv1 => ?_⟩
  refine ⟨by simp_all [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], hv⟩
  · dsimp only [preKeyTryFromPlacedRawEnvSpec]
    refine Entails.trans ?_ (Entails.sepExists_intro evs)
    rw [pure_true_emp ⟨by simp [htr, arm64_norm], hevs⟩, emp_sepConj]
    have hstk := stackAt_preKeyTryFrom_unsplit s0.sp s0
    unfold preKeyCalleeSavedAt at hstk
    simp only [bv_sub_add_lit', BitVec.reduceSub] at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq; sep_ac_rfl

/-- Generic `Inv`- and `postEnv`-parametric budget subroutine correctness for Block 111
(`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`) under `[LibsignalPlacement]`. -/
theorem preKeyTryFrom_inv_ok_gen [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {postEnv : List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim)))
    (hdealloc : PreKeyDeallocOk Inv A lim H)
    (hDropSpe : PreKeyDropSpeOk Inv A lim H)
    (hIntoBox : PreKeyIntoBoxOk Inv A lim H)
    (hSigTryFrom : PreKeySigTryFromOkGen Inv postEnv A lim H)
    (hTryClone : PreKeyTryCloneOk Inv A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (withPreKeyInv Inv (preKeyTryFromPlacedRawSpec (SigTryFromEnv postEnv) M A lim)) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hinv0, hpre0⟩ := extract_withPreKeyInv hpre
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hcl_of_inv s0.mem hinv0
  have hL : (preKeyPlacedProg H).CodeLoaded s0.mem :=
    (IsLsBlockProg.eq_blockProgram (prog := preKeyPlacedProg H) (i := 111) (H := H)).symm ▸
      hcl0 111 (by decide) (by decide) H (fun _ => none) Syscall.standard
  dsimp only [preKeyTryFromPlacedRawSpec, preKeyTryFromPlacedRawEnvSpec] at hpre0
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1_nat, hlt, hx8, hfits⟩, hmem⟩
  have hfit_loop : FitsEvents M lim st (preKeyLoopEvents x) :=
    FitsEnv.seq_left hfits (preKeyLoopEvents x) rfl
  have hfits_post : FitsEnv M lim (M.stepEvents (preKeyLoopEvents x) st)
      (PreKeyPostEnv (SigTryFromEnv postEnv) x) :=
    FitsEnv.seq_right hfits rfl
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set sp' := s0.sp - 608#64
  have hstk_top := stackAt_preKeyTryFrom_split s0.sp
  have hstk_sub := stackAt_sub_split sp' bytesMergeStack smallRootStack (by decide) (by decide)
  have hmem' : s0.mem ⊨
      (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0)) ∗ R := by
    ac_nf at hmem ⊢
  have hfull : SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyTryFromPlacedRawSpec (SigTryFromEnv postEnv) M A lim).post (x, st) s0 sf))
      preKeyNoPanicQp := by
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96 ∗
          A.pool lim st s0 ∗ stackAt sp' bytesMergeStack) ∗
        (memRegion x.sret 248 ∗ lsLogOff ∗
          memRegion sp' 296 ∗ memRegion (sp' + 448#64) 64 ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - bytesMergeStack)))
      (by
        rw [hstk_top, show preKeyTryFromSubStack = smallRootStack from rfl]
        dsimp only [sp'] at hstk_sub ⊢
        rw [hstk_sub]
        apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_bind_frame_noPanic
      (sepWPp_strengthen_inv hkf hinv0
        (preKey_entry_to_f90_placed_wp
          (subroutine_ok_withPreKeyInv_of_cl (fun _ h => h) hint32)
          (subroutine_ok_withPreKeyInv_of_cl (fun _ h => h) hbytes)
          hfit_loop rfl hlt hpc hrun hsp hcl0 hx0 hx1 hx8)) ?_
    intro s1 P1 hpc1 hrun1 ⟨hinv1, hregs1, hsp1, _hcl1, htr1, hx24_1,
      opkVal, kyberCap, kyberPtr, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopk, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    clear hent1
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ memRegion sp' 296 ∗
          ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
          vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
          vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
          vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
          vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
          ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
          ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents (preKeyLoopEvents x) st) s1 ∗
          stackAt sp' smallRootStack) ∗
        (memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0))
      (by
        rw [hstk_sub, show PreKeyTryFromLoopBudget.preKeyLoopEvents x = preKeyLoopEvents x from rfl]
        apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_bind_frame_noPanic
      (post_f90_to_034_placed_wp_gen (st := M.stepEvents (preKeyLoopEvents x) st)
        hkf hcl_of_inv hdealloc hDropSpe hIntoBox hSigTryFrom hTryClone
        hlt hfits_post hopk hpc1 hrun1 hregs1 hsp1 hinv1 htr1 hx24_1) ?_
    intro s2 P2 hpc2 hrun2 ⟨evs_post, hevs_post, hst2, hent2⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
    clear hent2
    refine SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        preKeyResultAt A.repAlloc x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents (preKeyLoopEvents x ++ evs_post) st) s2)
      (by
        rw [M.stepEvents_append (preKeyLoopEvents x) evs_post st]
        dsimp only [sp']
        apply entails_of_eq; sep_ac_rfl) ?_
    exact epilogue_034_placed_wp hkf (SeqEnv.append rfl hevs_post) hsp hst2 hpc2 hrun2
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ |
    ⟨_, _, _, hp⟩ | ⟨_, hoom⟩
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
        Satisfies.mono (sepConj_mono_left hent_f) hmf⟩))
  · exact False.elim hp
  · exact (allowPanic_not_exited hoom).elim

abbrev preKeyTryFrom_inv_ok [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m) :=
  @preKeyTryFrom_inv_ok_gen _ Inv hkf hcl_of_inv TryFromPostEnv

theorem preKeyTryFrom_placed_ok_of_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim)))
    (hdealloc : PreKeyDeallocOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hIntoBox : PreKeyIntoBoxOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hTryClone : PreKeyTryCloneOk (LibsignalCodeLoaded lsmpl) A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (preKeyTryFromPlacedSpec SigTryFromConcreteEnv M A lim) :=
  preKeyTryFrom_inv_ok keepsFrozenInv_codeLoaded (fun _ h => h)
    hint32 hbytes hdealloc hDropSpe hIntoBox hSigTryFrom hTryClone

/-- Placed budget subroutine correctness for Block 111
(`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`), discharging `int32_merge`,
`into_boxed_slice`, `try_clone_from_ref`, `deserialize`, and `IdentityKey::try_from` from
`HookSat`. -/
theorem preKeyTryFrom_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim)))
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (preKeyTryFromPlacedSpec SigTryFromConcreteEnv M A lim) :=
  preKeyTryFrom_placed_ok_of_callees
    (int32Merge_ok_at_prekey_placed hshim_s halloc)
    hbytes
    (preKeyDeallocOk_of_hookSat hdealloc)
    hDropSpe
    (preKeyIntoBoxOk_of_hooks (fun _ h => h) hdealloc hrealloc)
    hSigTryFrom
    (preKeyTryCloneOk_of_hooks (fun _ h => h) hshim halloc hmemcpy)

theorem preKeyTryFrom_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide)
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim)))
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A lim H) :
    subroutine_ok callerProg (lsmpl.base 111)
      (preKeyTryFromPlacedSpec SigTryFromConcreteEnv M A lim) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (i := i) (j := 111)
    (preKeyTryFrom_placed_ok hshim_s hshim halloc hdealloc hrealloc hmemcpy
      hbytes hDropSpe hSigTryFrom) hi (by decide) (by decide)

/-- `withLsCodeRoLoaded` variant of Block 111 budget correctness, additionally discharging
`drop_spe` (`Block 4`) and `SignalMessage::try_from` (`Block 85`). -/
theorem preKeyTryFrom_cro_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hS : TripleRatchetHooksWPlaced A lim H)
    (d : TryFromDepsPlaced A lim H)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim))) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (withLsCodeRoLoaded lsmpl
        (preKeyTryFromPlacedRawSpec SigTryFromConcreteEnv M A lim)) :=
  preKeyTryFrom_inv_ok keepsFrozenInv_codeRoLoaded (fun _ h => h.1)
    (int32Merge_ok_at_prekey_placed hshim_s halloc)
    hbytes
    (preKeyDeallocOk_of_hookSat hdealloc)
    (preKeyDropSpeOk_cro_of_hookSat hdealloc)
    (preKeyIntoBoxOk_of_hooks (fun _ h => h.1) hdealloc hrealloc)
    (preKeySigTryFromOk_cro_of_deps hS d)
    (preKeyTryCloneOk_of_hooks (fun _ h => h.1) hshim halloc hmemcpy)

theorem preKeyTryFrom_cro_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide)
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hS : TripleRatchetHooksWPlaced A lim H)
    (d : TryFromDepsPlaced A lim H)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim))) :
    subroutine_ok callerProg (lsmpl.base 111)
      (withLsCodeRoLoaded lsmpl
        (preKeyTryFromPlacedRawSpec SigTryFromConcreteEnv M A lim)) :=
  ls_subroutine_ok_cro_of_block (callerProg := callerProg) (i := i) (j := 111)
    (preKeyTryFrom_cro_placed_ok hshim_s hshim halloc hdealloc hrealloc hmemcpy
      hS d hbytes) hi (by decide) (by decide)

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
