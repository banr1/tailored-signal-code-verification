/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Top-Level Stage P2 Matched-Session Contract

Budget-threaded `[LibsignalPlacement]` counterpart of `Matched.M2TopPlaced` on Block `518`
(`lsProg_518 (Rust.withPanics ext)`), defining `StageP2MatchedMismatchEnv`, `StageP2MatchedEnv`, and
`StageP2MatchedTopEnv` and proving `stageP2_matched_ok_placed` (`+0x0868 → +0x1778` / `x30`) with
zero allocator panic/OOM residue.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget

noncomputable section

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsBlackBoxU8Sym lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (remoteIdentityOkAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost apiDecResultAt sessionRecordAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt processPrekeyActive10At
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  SepWPp.weaken_frame entails_replace_sub eq_of_sep_emp
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  chunks32At coro_2a0_split32_placed memRegion_32_eq_chunks32 memRegion_34_split_24_10
  memRegion_920_6_join memRegion_920_6_split memRegion_a90_48_join_10_38
  memRegion_a90_48_split_10_38 mismatchRemoteIkStrPlaced prevSessionsEmptyAt
  processPrekeyActive10At_eq_placed publicKey_beq_false_of_ne_placed
  rem34_bytes_entails_memRegion34 remoteIdentityOkAt_none_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
  fitsEvents_append rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  PublicKeySerializeEnv publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv fitsEnv_publicKeySerialize_of_bridge fitsEnv_stageP2MatchedBridge_iff
  stageP2MatchedBridgeEvents stageP2_matched_0868_to_094c_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudget (
  bind_sepWPp_nopanic_state p2_seg_094c_ok_placed_wp p2_seg_1064_none_placed_wp
  p2_seg_10cc_mismatch_placed_wp sepWPp_lift_qp stageP2_matched_094c_match_placed
  stageP2_matched_094c_some_to_10cc_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget (
  bind_sepWP_lscro_steps_m2_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget (
  strToOwnedEvents strToOwnedLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget (
  StageP2MismatchTailEnv fitsEvents_of_fitsEnv_stageP2MismatchTail
  stageP2MismatchTailPostAtPlaced stageP2MismatchTailPrePlaced
  stageP2_matched_mismatch_tail_exists_placed
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  publicKey_beq_false_of_ne_placed coro_2a0_split32_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## Stage P2 matched-session allocator envelopes -/

/-- Exact allocator event envelope for the Stage P2 remote-identity mismatch exit path
(`+0x0868 → s0.readReg64 .x30` when `sess.state.remoteIdentity ≠ some remIdKey`):
`StageP2MatchedBridgeEnv` (`[.alloc 33, .free 1 33]`) followed by `StageP2MismatchTailEnv`
(`[.alloc 70] ++ FreeOnlyEvs`). -/
def StageP2MatchedMismatchEnv : List AllocEvent → Prop :=
  SeqEnv StageP2MatchedBridgeEnv StageP2MismatchTailEnv

/-- Branch-exact Stage P2 matched-session allocator event envelope at `+0x0868`:
- when `sess.state.remoteIdentity = some remIdKey`: `StageP2MatchedBridgeEnv` (`+0x0868 → +0x1778`);
- when `sess.state.remoteIdentity ≠ some remIdKey`: `StageP2MatchedMismatchEnv` (`+0x0868 → x30`). -/
def StageP2MatchedEnv (sess : Session (List (BitVec 8))) (remIdKey : IdentityKey)
    (evs : List AllocEvent) : Prop :=
  if sess.state.remoteIdentity = some remIdKey then
    StageP2MatchedBridgeEnv evs
  else
    StageP2MatchedMismatchEnv evs

/-- Branch-agnostic disjunction envelope covering both Stage P2 matched-session outcomes. -/
def StageP2MatchedTopEnv (evs : List AllocEvent) : Prop :=
  StageP2MatchedBridgeEnv evs ∨ StageP2MatchedMismatchEnv evs

theorem stageP2MatchedMismatchEnv_of_tail {evs_tail : List AllocEvent}
    (htail : StageP2MismatchTailEnv evs_tail) :
    StageP2MatchedMismatchEnv (stageP2MatchedBridgeEvents ++ evs_tail) :=
  Or.inr ⟨stageP2MatchedBridgeEvents, evs_tail, rfl, rfl, htail⟩

theorem stageP2MatchedEnv_match {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey}
    (heq : sess.state.remoteIdentity = some remIdKey) :
    StageP2MatchedEnv sess remIdKey stageP2MatchedBridgeEvents := by
  simp [StageP2MatchedEnv, heq, StageP2MatchedBridgeEnv]

theorem stageP2MatchedEnv_mismatch_of_tail {sess : Session (List (BitVec 8))}
    {remIdKey : IdentityKey} {evs_tail : List AllocEvent}
    (hne : sess.state.remoteIdentity ≠ some remIdKey)
    (htail : StageP2MismatchTailEnv evs_tail) :
    StageP2MatchedEnv sess remIdKey (stageP2MatchedBridgeEvents ++ evs_tail) := by
  simp [StageP2MatchedEnv, hne]
  exact stageP2MatchedMismatchEnv_of_tail htail

theorem fitsEnv_bridge_and_mismatchTail_of_mismatchEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEnv M lim st StageP2MatchedMismatchEnv) :
    FitsEnv M lim st PublicKeySerializeEnv ∧
      FitsEvents M lim (M.stepEvents stageP2MatchedBridgeEvents st)
        (strToOwnedEvents mismatchRemoteIkStrPlaced) := by
  have hmem :
      StageP2MatchedMismatchEnv
        (stageP2MatchedBridgeEvents ++ strToOwnedEvents mismatchRemoteIkStrPlaced) :=
    Or.inr ⟨stageP2MatchedBridgeEvents, strToOwnedEvents mismatchRemoteIkStrPlaced, rfl, rfl,
      ⟨strToOwnedEvents mismatchRemoteIkStrPlaced, [], rfl, FreeOnlyEvs.nil,
        (List.append_nil _).symm⟩⟩
  have hboth :=
    (fitsEvents_append M lim stageP2MatchedBridgeEvents
      (strToOwnedEvents mismatchRemoteIkStrPlaced) st).mp (h _ hmem)
  exact ⟨fitsEnv_publicKeySerialize_of_bridge (fitsEnv_stageP2MatchedBridge_iff.mpr hboth.1),
    hboth.2⟩

theorem fitsEnv_publicKeySerialize_of_matchedEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey}
    (h : FitsEnv M lim st (StageP2MatchedEnv sess remIdKey)) :
    FitsEnv M lim st PublicKeySerializeEnv := by
  by_cases hrem : sess.state.remoteIdentity = some remIdKey
  · apply fitsEnv_publicKeySerialize_of_bridge
    intro evs hevs
    apply h evs
    simpa [StageP2MatchedEnv, hrem] using hevs
  · refine (fitsEnv_bridge_and_mismatchTail_of_mismatchEnv ?_).1
    intro evs hevs
    apply h evs
    simpa [StageP2MatchedEnv, hrem] using hevs

theorem fitsEvents_mismatchTail_of_matchedEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey}
    (hne : sess.state.remoteIdentity ≠ some remIdKey)
    (h : FitsEnv M lim st (StageP2MatchedEnv sess remIdKey)) :
    FitsEvents M lim (M.stepEvents stageP2MatchedBridgeEvents st)
      (strToOwnedEvents mismatchRemoteIkStrPlaced) := by
  refine (fitsEnv_bridge_and_mismatchTail_of_mismatchEnv ?_).2
  intro evs hevs
  apply h evs
  simpa [StageP2MatchedEnv, hne] using hevs

theorem fitsEnv_matchedEnv_of_topEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (sess : Session (List (BitVec 8))) (remIdKey : IdentityKey)
    (h : FitsEnv M lim st StageP2MatchedTopEnv) :
    FitsEnv M lim st (StageP2MatchedEnv sess remIdKey) := by
  intro evs hevs
  apply h evs
  by_cases hrem : sess.state.remoteIdentity = some remIdKey
  · simp only [StageP2MatchedEnv, hrem, ↓reduceIte] at hevs
    exact Or.inl hevs
  · simp only [StageP2MatchedEnv, hrem, ↓reduceIte] at hevs
    exact Or.inr hevs

/-! ## Budget-threaded spatial bundles -/

abbrev stageP2MatchedMismatchPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_b0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey) (F : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMismatchPostPlaced
    (A.atState lim st sf) s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt
    v_330 v_388 u_80 u_88 u_90 u_b0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F

abbrev stageP2MatchedMatchPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s2 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt
      v_330 v_388 v_d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outerVerByte innerVerByte b_2c0 : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (F : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMatchPrePlaced
    (A.atState lim st s2) s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt
    v_330 v_388 v_d0 opkHi kyberPreKeyId signedPreKeyId
    outerVerByte innerVerByte b_2c0 baseKey remIdKey g recG recSt F

abbrev stageP2MatchedPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (F : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedPrePlaced
    (A.atState lim st s) s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
    baseKey remIdKey g r F

private theorem sepWPp_ret_frame_nopanic {prog : Program} {ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_stage Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage Q_stage (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hret : ∀ sf P_f, Steps prog s sf → sf.pc = ret → sf.status = .Running →
      Q_stage sf P_f → Q sf (P_f ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hqf⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f ∗ F, hmf, hret sf P_f hsteps hpcf hrunf hqf⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Remote-identity mismatch branch (`+0x094c → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` Stage P2 remote-identity mismatch branch
(`(blkPl_518).base + 0x094c → s0.readReg64 .x30` when `recSt.remoteIdentity ≠ some remIdKey`)
producing a `StageP2MismatchTailEnv` witness. -/
theorem stageP2_matched_094c_mismatch_exists_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_ne : recSt.remoteIdentity ≠ some remIdKey)
    (hfits : FitsEvents M lim st (strToOwnedEvents mismatchRemoteIkStrPlaced))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP2MismatchTailEnv evs ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 34 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x920#64) 6 ∗
            memRegion (sp + 0xa90#64) 48 ∗
            apiDecResultAt A.repAlloc outPtr
              (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp rootStack)) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  apply sepWPp_lift_qp
  cases hrem : recSt.remoteIdentity with
  | none =>
    conv =>
      arg 4
      rw [remoteIdentityOkAt_none_eq sp, memRegion_32_eq_chunks32 (sp + 0x3e2#64),
          memRegion_920_6_split sp, memRegion_a90_48_split_10_38 sp]
    dsimp only [chunks32At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    sep_norm
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun h1 =>
      SepWPp.exists_elim fun q2 => SepWPp.exists_elim fun q3 =>
      SepWPp.exists_elim fun q4 => SepWPp.exists_elim fun h5 =>
      SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
      SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
    have h094c := p2_seg_094c_ok_placed_wp (A := A) (lim := lim) ext st s coroPtr outPtr
      hpc hrun hsp_align hx19
    rw [hsp_eq] at h094c
    refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
      fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, _, _⟩
    have hsp1 : s1.sp = sp := hsp1_s
    have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
    have h1064 := p2_seg_1064_none_placed_wp (A := A) (lim := lim) ext st s1 coroPtr q2 q3 q4 u_a90
      w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 (by rw [hsp1, ← hsp_eq]; exact hsp_align) hx19_1 hx21_1'
    rw [hsp1] at h1064
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans (hx25_1.trans hx25)
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans (hx28_1.trans hx28)
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      congrArg VRegFile.calleeSaved (hvregs2.trans hvregs1)
    have hrem34 := rem34_bytes_entails_memRegion34 sp 0#8 0#8 w0 h1 q2 q3 q4 h5
    dsimp only [chunks32At] at hrem34
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrem34
    refine SepWPp.weaken_frame hrem34 (by sep_focus) ?_
    refine SepWPp.weaken_frame (memRegion_920_6_join sp w0 h1) (by sep_focus) ?_
    refine SepWPp.weaken_frame (memRegion_a90_48_join_10_38 sp q4 h5) (by sep_focus) ?_
    conv => arg 4; rw [memRegion_34_split_24_10 sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_exists_placed (Qp := fun _ _ => False)
      hto hdealloc hdrop_ss st s0 s2 sp coroPtr outPtr u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt
      hfits hcro2 hsp2 hsp_root hpc2 hrun2 hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine sepWPp_ret_frame_nopanic htail
      (by unfold stageP2MismatchTailPrePlaced; sep_focus)
      fun sf P_tail _ _ _ ⟨⟨evs, henv, hent_tail⟩, hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine ⟨⟨evs, henv, ?_⟩, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    unfold stageP2MismatchTailPostAtPlaced at hent_tail
    refine Entails.trans (sepConj_mono_left hent_tail) ?_
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10 sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (by sep_ac_rfl)
  | some ik =>
    have hne_ik : some ik ≠ some remIdKey := by rw [← hrem]; exact hrem_ne
    have hchk := stageP2_matched_094c_some_to_10cc_placed (A := A) (lim := lim)
      (Qp := fun _ _ => False)
      h_bb st s sp coroPtr outPtr msgPtr remIdKey ik hcro hsp_eq hsp_root hpc hrun hsp_align
      hx19 hx21 hx25 hx28
    refine bind_sepWPp_nopanic_state hchk (by sep_focus)
      fun s1 _ hpc1 hrun1 ⟨hsp1, htr1_s, hx0_1, hx19_1, hx25_1, hx26_1, hx28_1, _, hvregs1, hcro1⟩ => ?_
    have hx0_zero : s1.readReg64 .x0 = 0#64 := by
      simpa [publicKey_beq_false_of_ne_placed hne_ik] using hx0_1
    have h10cc := p2_seg_10cc_mismatch_placed_wp (A := A) (lim := lim) ext st s1 coroPtr
      hpc1 hrun1 hx0_zero hx19_1
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h10cc (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans hx25_1
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans hx28_1
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      (congrArg VRegFile.calleeSaved hvregs2).trans hvregs1
    conv => arg 4; rw [memRegion_34_split_24_10 sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_exists_placed (Qp := fun _ _ => False)
      hto hdealloc hdrop_ss st s0 s2 sp coroPtr outPtr u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt
      hfits hcro2 hsp2 hsp_root hpc2 hrun2 hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine sepWPp_ret_frame_nopanic htail
      (by unfold stageP2MismatchTailPrePlaced; sep_focus)
      fun sf P_tail _ _ _ ⟨⟨evs, henv, hent_tail⟩, hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine ⟨⟨evs, henv, ?_⟩, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    unfold stageP2MismatchTailPostAtPlaced at hent_tail
    refine Entails.trans (sepConj_mono_left hent_tail) ?_
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10 sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (by sep_ac_rfl)

/-- Corollary of `stageP2_matched_094c_mismatch_exists_placed` accepting
`FitsEnv M lim st StageP2MismatchTailEnv`. -/
theorem stageP2_matched_094c_mismatch_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_ne : recSt.remoteIdentity ≠ some remIdKey)
    (hfits : FitsEnv M lim st StageP2MismatchTailEnv)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP2MismatchTailEnv evs ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 34 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x920#64) 6 ∗
            memRegion (sp + 0xa90#64) 48 ∗
            apiDecResultAt A.repAlloc outPtr
              (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp rootStack)) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp :=
  stageP2_matched_094c_mismatch_exists_placed hto hdealloc h_bb hdrop_ss st s0 s
    sp coroPtr outPtr msgPtr u_a8 u_d0 b_4f2 b_390 b_2c0 remIdKey g recG recSt
    hrem_ne (fitsEvents_of_fitsEnv_stageP2MismatchTail hfits)
    hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx21 hx25 hx28

/-! ## Top-level budget-threaded Stage P2 matched-session contract -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` top-level Stage P2 matched-session contract
(`(blkPl_518).base + 0x0868 → +0x1778` / `s0.readReg64 .x30`) under
`FitsEnv M lim st (StageP2MatchedEnv sess remIdKey)`. -/
theorem stageP2_matched_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (F : SepProp)
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = outerVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st (StageP2MatchedEnv sess remIdKey))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64)
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedMismatchEnv evs →
        ∀ (sf : State) (Pf : SepProp),
          sf.pc = s0.readReg64 .x30 →
          sf.status = .Running →
          Steps (lsProg_518 (Rust.withPanics ext)) s sf →
          sf.sp = sp + 0xcd0#64 →
          sf.trace = s.trace →
          ClosureCalleeSaved s0 sf →
          calleeSavedVRegs sf = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl sf.mem →
          (Pf ⊢ stageP2MatchedMismatchPostPlaced A lim (M.stepEvents evs st) s0 sf sp coroPtr outPtr
            msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
            u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
            u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
          Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedBridgeEnv evs →
        ∀ (s2 : State) (recG : SessionGhost) (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
          g.cur = some recG →
          SessionExtraRel recG sess →
          Steps (lsProg_518 (Rust.withPanics ext)) s s2 →
          s2.pc = (blkPl_518).base + 0x1778#64 →
          s2.status = .Running →
          s2.sp = sp →
          (s2.sp &&& 15#64 == 0#64) = true →
          s2.trace = s.trace →
          s2.readReg64 .x19 = coroPtr →
          s2.readReg64 .x27 = sp + 0x370#64 →
          s2.readReg64 .x29 = sp + 0xc70#64 →
          calleeSavedVRegs s2 = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl s2.mem →
          SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
            (stageP2MatchedMatchPrePlaced A lim (M.stepEvents evs st) s0 s2 sp coroPtr outPtr msgPtr
              remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt v_330 v_388 v_d0
              opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
              baseKey remIdKey g recG sess.state F)
            Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A lim st s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp := by
  dsimp only [stageP2MatchedPrePlaced, stageP2MatchedMismatchPostPlaced,
    stageP2MatchedMatchPrePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedPrePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMismatchPostPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMatchPrePlaced]
    at hmismatch hmatch ⊢
  have hpre_eq :
      sessionRecordAt (A.atState lim st s) (coroPtr + 0xe0#64) g r =
        sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r := rfl
  have hpool_s : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpre_eq, hpool_s]
  have hpre := stageP2_matched_0868_to_094c_placed (Qp := fun _ _ => False)
    hser hdealloc h_bb st s sp coroPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt outerVerByte b_4f1 baseKey
    g r sess hcur hver halice (fitsEnv_publicKeySerialize_of_matchedEnv hfits)
    hcro hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine bind_sepWPp_nopanic_state hpre (by sep_focus)
    fun sm hsteps01 hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hspm, htrm, hx19m, hx21m, hx25m, hx28m, hx29m, hvregsm, hcrom⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm, ← hsp_eq]; exact hsp_align
  let st_br := M.stepEvents stageP2MatchedBridgeEvents st
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun ⟨hgc, hextra⟩ => ?_
  by_cases hrem : sess.state.remoteIdentity = some remIdKey
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    have hm := stageP2_matched_094c_match_placed (A := A) (lim := lim) (Qp := fun _ _ => False)
      h_bb st_br sm sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0 u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
      u_2a8 u_b8 innerVerByte b_4f2 b_390 b_3ac remIdKey recG sess.state hrem
      hcrom hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine bind_sepWPp_nopanic_state hm (by sep_focus)
      fun s2 hsteps12 hpc2 hrun2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx27_2, hx29_2, hvregs2, hcro2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    sep_norm
    refine SepWPp.exists_elim fun opkHi => SepWPp.exists_elim fun kyberPacked => ?_
    have hgoal := hmatch hrem stageP2MatchedBridgeEvents rfl s2 recG opkHi
      (kyberPacked.extractLsb' 0 32) (kyberPacked.extractLsb' 32 32)
      hgc hextra (hsteps01.trans hsteps12) hpc2 hrun2 hsp2 hsp2_align
      (htr2.trans htrm) hx19_2 hx27_2 (hx29_2.trans hx29m) (hvregs2.trans hvregsm) hcro2
    refine fun R hmR hL => hgoal R (Arm64.Satisfies.mono (sepConj_mono_left ?_) hmR) hL
    have hprev2 :
        prevSessionsEmptyAt (A.atState lim st_br s2) coroPtr g =
          prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
    have hss2 :
        sessionStateAt (A.atState lim st_br s2) (coroPtr + 0xf8#64) recG sess.state =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG sess.state := rfl
    have hpool2 : (A.atState lim st_br s2).pool = A.pool lim st_br s2 := rfl
    rw [hprev2, hss2, hpool2, coro_2a0_split32_placed coroPtr kyberPacked,
      processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    have hmm := stageP2_matched_094c_mismatch_exists_placed (A := A) (lim := lim)
      (Qp := fun _ _ => False) hto hdealloc h_bb hdrop_ss st_br s0 sm
      sp coroPtr outPtr msgPtr u_a8 v_d0 b_4f2 b_390 b_2c0 remIdKey g recG sess.state
      hrem (fitsEvents_mismatchTail_of_matchedEnv hrem hfits)
      hcrom hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine sepWPp_ret_frame_nopanic hmm (by sep_focus)
      fun sf P_mis hsteps1f hpcf hrunf ⟨⟨evs_tail, htail, hent_mis⟩, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine hmismatch hrem (stageP2MatchedBridgeEvents ++ evs_tail)
      (stageP2MatchedMismatchEnv_of_tail htail) sf _ hpcf hrunf
      (hsteps01.trans hsteps1f) hspf (htrf.trans htrm) hcsf (hvregsf.trans hvregsm) hcrof ?_
    refine Entails.trans (sepConj_mono_left hent_mis) ?_
    let st_exit := M.stepEvents (stageP2MatchedBridgeEvents ++ evs_tail) st
    have hstep_eq : M.stepEvents evs_tail st_br = st_exit :=
      (M.stepEvents_append stageP2MatchedBridgeEvents evs_tail st).symm
    have hdec_eq :
        apiDecResultAt (A.atState lim st_exit sf) outPtr
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) =
          apiDecResultAt A.repAlloc outPtr
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := rfl
    have hpoolf : (A.atState lim st_exit sf).pool = A.pool lim st_exit sf := rfl
    rw [hstep_eq, hdec_eq, hpoolf, processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev stageP2_matched_ok_framed_placed := @stageP2_matched_ok_placed

/-- Specialization of `stageP2_matched_ok_placed` substituting the singleton bridge witness
`evs = stageP2MatchedBridgeEvents` directly in `hmatch`. -/
theorem stageP2_matched_ok_fixedBridge_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (F : SepProp)
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = outerVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st (StageP2MatchedEnv sess remIdKey))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64)
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedMismatchEnv evs →
        ∀ (sf : State) (Pf : SepProp),
          sf.pc = s0.readReg64 .x30 →
          sf.status = .Running →
          Steps (lsProg_518 (Rust.withPanics ext)) s sf →
          sf.sp = sp + 0xcd0#64 →
          sf.trace = s.trace →
          ClosureCalleeSaved s0 sf →
          calleeSavedVRegs sf = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl sf.mem →
          (Pf ⊢ stageP2MatchedMismatchPostPlaced A lim (M.stepEvents evs st) s0 sf sp coroPtr outPtr
            msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
            u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
            u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
          Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
      ∀ (s2 : State) (recG : SessionGhost) (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        g.cur = some recG →
        SessionExtraRel recG sess →
        Steps (lsProg_518 (Rust.withPanics ext)) s s2 →
        s2.pc = (blkPl_518).base + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s.trace →
        s2.readReg64 .x19 = coroPtr →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = sp + 0xc70#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s →
        LibsignalCodeRoLoaded lsmpl s2.mem →
        SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
          (stageP2MatchedMatchPrePlaced A lim (M.stepEvents stageP2MatchedBridgeEvents st) s0 s2
            sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt v_330 v_388 v_d0
            opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
            baseKey remIdKey g recG sess.state F)
          Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A lim st s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp :=
  stageP2_matched_ok_placed hser hto hdealloc h_bb hdrop_ss st s0 s sp coroPtr outPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 u_2a8 u_b8
    outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac baseKey remIdKey g r sess F
    hcur hver halice hfits hcro hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
    hmismatch (fun heq evs hevs => by subst hevs; exact hmatch heq)

/-- Branch-agnostic `StageP2MatchedTopEnv` corollary of `stageP2_matched_ok_placed`. -/
theorem stageP2_matched_ok_topEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (F : SepProp)
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = outerVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st StageP2MatchedTopEnv)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64)
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedMismatchEnv evs →
        ∀ (sf : State) (Pf : SepProp),
          sf.pc = s0.readReg64 .x30 →
          sf.status = .Running →
          Steps (lsProg_518 (Rust.withPanics ext)) s sf →
          sf.sp = sp + 0xcd0#64 →
          sf.trace = s.trace →
          ClosureCalleeSaved s0 sf →
          calleeSavedVRegs sf = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl sf.mem →
          (Pf ⊢ stageP2MatchedMismatchPostPlaced A lim (M.stepEvents evs st) s0 sf sp coroPtr outPtr
            msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
            u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
            u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
          Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedBridgeEnv evs →
        ∀ (s2 : State) (recG : SessionGhost) (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
          g.cur = some recG →
          SessionExtraRel recG sess →
          Steps (lsProg_518 (Rust.withPanics ext)) s s2 →
          s2.pc = (blkPl_518).base + 0x1778#64 →
          s2.status = .Running →
          s2.sp = sp →
          (s2.sp &&& 15#64 == 0#64) = true →
          s2.trace = s.trace →
          s2.readReg64 .x19 = coroPtr →
          s2.readReg64 .x27 = sp + 0x370#64 →
          s2.readReg64 .x29 = sp + 0xc70#64 →
          calleeSavedVRegs s2 = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl s2.mem →
          SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
            (stageP2MatchedMatchPrePlaced A lim (M.stepEvents evs st) s0 s2 sp coroPtr outPtr msgPtr
              remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt v_330 v_388 v_d0
              opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
              baseKey remIdKey g recG sess.state F)
            Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A lim st s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp :=
  stageP2_matched_ok_placed hser hto hdealloc h_bb hdrop_ss st s0 s sp coroPtr outPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 u_2a8 u_b8
    outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac baseKey remIdKey g r sess F
    hcur hver halice (fitsEnv_matchedEnv_of_topEnv sess remIdKey hfits)
    hcro hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
    hmismatch hmatch

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
