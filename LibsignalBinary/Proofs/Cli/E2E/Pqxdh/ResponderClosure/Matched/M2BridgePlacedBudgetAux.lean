/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Envelopes, Spatial Bundles, and Segments for `Matched.M2BridgePlacedBudget`

Defines the exact allocator event trace `stageP2MatchedBridgeEvents` / `StageP2MatchedBridgeEnv`,
spatial bundles (`stageP2Matched0868PrePlaced`, `stageP2Matched094cPostPlaced`), stack/state split
helpers, and pool-threaded Block-`518` basic-block segment lemmas for `Matched.M2BridgePlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux

noncomputable section

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsLogFilterAddr lsmpl lsρ
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecAt vecHeader vecU8At)
open CryptoVerification.LibsignalSessionRepr (chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  remoteIdentityKeyStack remoteIdentityOkAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost optSenderChainAt optTailVecAt sessionStateAt
)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost sessionRecordAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  processPrekeyActive10At
)
open CryptoVerification.CliHandshake.RespClosurePlaced (
  blkLib_eq_518 blkPl_518 lsProg_518
)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel stackAt_split_of_le
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  prevSessionsEmptyAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
  fitsEvents_append rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  PublicKeySerializeEnv boxU8Buf fitsEnv_publicKeySerialize_iff publicKeySerializeEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

@[local simp, local wp_norm] private theorem vregs_advancePC (s : State) :
    s.advancePC.vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_setMem (s : State) (m : Memory) :
    (s.setMem m).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_setPState (s : State) (ps : PState) :
    (s.setPState ps).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_writeReg64 (s : State) (r : Reg) (val : BitVec 64) :
    (s.writeReg64 r val).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_writeReg32 (s : State) (r : Reg) (val : BitVec 32) :
    (s.writeReg32 r val).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_writeReg (s : State) (w : Width) (r : Reg) (val : BitVec 64) :
    (s.writeReg w r val).vregs = s.vregs := by cases s; rfl
@[local simp, local wp_norm] private theorem vregs_applyWriteback
    (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).vregs = s.vregs := by cases wb <;> cases s <;> rfl

local macro "wp_steps_sync_518 " h:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $h))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Allocator event list, envelope, and spatial bundles -/

/-- Exact allocator event trace across `+0x0868 → +0x094c`:
`<PublicKey>::serialize` (`__rust_alloc(33, 1)`) followed by `__rust_dealloc(serPtr, 33, 1)`. -/
def stageP2MatchedBridgeEvents : List AllocEvent :=
  publicKeySerializeEvents ++ rustDeallocEvents 33 1

/-- Exact allocator event envelope of `+0x0868 → +0x094c` (`evs = [.alloc 33, .free 1 33]`). -/
def StageP2MatchedBridgeEnv (evs : List AllocEvent) : Prop :=
  evs = stageP2MatchedBridgeEvents

theorem fitsEnv_stageP2MatchedBridge_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st StageP2MatchedBridgeEnv ↔ FitsEvents M lim st stageP2MatchedBridgeEvents :=
  FitsEnv.eq_iff

theorem fitsEnv_publicKeySerialize_of_bridge {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st StageP2MatchedBridgeEnv) :
    FitsEnv M lim st PublicKeySerializeEnv := by
  rw [fitsEnv_publicKeySerialize_iff]
  exact ((fitsEvents_append M lim publicKeySerializeEvents (rustDeallocEvents 33 1) st).mp
    (fitsEnv_stageP2MatchedBridge_iff.mp h)).1

def stageP2Matched0868PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp coroPtr msgPtr : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
  sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s ∗
  stackAt sp rootStack

def stageP2Matched094cPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st' : M.σ) (sf : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ∃∗ recG : SessionGhost,
    ⌜g.cur = some recG ∧ SessionExtraRel recG sess⌝ ∗
    processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt ∗
    ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
    ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
    ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
    prevSessionsEmptyAt A.repAlloc coroPtr g ∗
    sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG sess.state ∗
    remoteIdentityOkAt (sp + 0x3e0#64) sess.state.remoteIdentity ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    A.pool lim st' sf ∗
    stackAt sp rootStack

/-! ## Stack, buffer, and `sessionStateAt` framing helpers -/

theorem stack_root_to_pkSerialize_m2_placed (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - (allocHookStack + 32)) ∗
        stackAt sp (allocHookStack + 32) :=
  stackAt_split_of_le sp rootStack (allocHookStack + 32) (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

theorem stack_root_to_remoteIk_m2_placed (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - remoteIdentityKeyStack) ∗
        stackAt sp remoteIdentityKeyStack :=
  stackAt_split_of_le sp rootStack remoteIdentityKeyStack (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

theorem boxU8Buf_pk_serialize_entails_placed (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  unfold boxU8Buf CryptoVerification.LibsignalTripleRatchet.boxU8Buf
  simp only [hne, ↓reduceIte, hlen]
  exact Entails.pure_left fun _ => Entails.refl _

theorem sessionStateAt_split_remoteIk_placed (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    ∃ R_ss : SepProp,
      (sessionStateAt A ss G st ⊢
        ⌜G.localIk.cap.toNat < 2 ^ 63 ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        R_ss) ∧
      ((ss ↦₆₄ G.localIk.cap) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_ss ⊢
        sessionStateAt A ss G st) := by
  have hloc :
      ∃ R_loc : SepProp,
        (vecGhostAt A G.localIk ss ⊢
          ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ (ss ↦₆₄ G.localIk.cap) ∗ R_loc) ∧
        ((ss ↦₆₄ G.localIk.cap) ∗ R_loc ⊢ vecGhostAt A G.localIk ss) := by
    unfold vecGhostAt vecU8At vecHeader
    refine ⟨((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
            ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
            ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧
              G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0#64⌝ ∗
            (if G.localIk.cap = 0#64 then emp
             else A.live G.localIk.ptr G.localIk.cap.toNat 1 ∗
               (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
               memRegion (G.localIk.ptr + BitVec.ofNat 64 G.localIk.bytes.length)
                 (G.localIk.cap.toNat - G.localIk.bytes.length)), ?_, ?_⟩
    · simp only [sepConj_assoc]
      refine Entails.trans (Entails.of_eq (by sep_focus : _ =
        ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧
          G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0#64⌝ ∗ _)) ?_
      refine Entails.pure_left fun hp => Entails.pure_right hp.2.1
        (Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (Entails.of_eq (by simp only [pure_sepConj_of_true hp, sepConj_assoc]; sep_ac_rfl)))
    · simp only [sepConj_assoc]
      exact Entails.of_eq (by sep_ac_rfl)
  obtain ⟨R_loc, hloc_f, hloc_b⟩ := hloc
  let P_pure : Prop :=
    PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)
  let R_rest : SepProp :=
    vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
      G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + asm64% ssAliceBaseKeyOff) ∗
    vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
    optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
    optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber ∗
    ((ss + asm64% ssSessionVersionOff) ↦₃₂ st.sessionVersion) ∗
    ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
    ((ss + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)
  have hss_eq : sessionStateAt A ss G st =
      ⌜P_pure⌝ ∗ vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_rest := by
    unfold sessionStateAt P_pure R_rest
    rfl
  refine ⟨⌜P_pure⌝ ∗ R_loc ∗ R_rest, ?_, ?_⟩
  · rw [hss_eq]
    refine Entails.pure_left fun hp => ?_
    refine Entails.trans (sepConj_mono_left hloc_f) ?_
    simp only [sepConj_assoc]
    refine Entails.pure_left fun hcap => Entails.pure_right ⟨hcap, hp.2.1⟩ ?_
    simp only [pure_sepConj_of_true hp, sepConj_assoc]
    exact Entails.of_eq (by sep_ac_rfl)
  · rw [hss_eq]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ (⌜P_pure⌝ ∗ R_loc ∗ R_rest) =
      ⌜P_pure⌝ ∗ ((ss ↦₆₄ G.localIk.cap) ∗ R_loc) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_rest)) ?_
    exact sepConj_mono_right (sepConj_mono_left hloc_b)

theorem memRegion_3e0_34_split_16_18_placed (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 16 ∗ memRegion (sp + 0x3f0#64) 18 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 16 18 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_3e0_34_restore_placed (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
    memRegion (sp + 0x3e9#64) 7 ∗ memRegion (sp + 0x3f0#64) 18 ⊢
      memRegion (sp + 0x3e0#64) 34 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 26 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 1 25 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 1#64) 7 18 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))

private theorem cond_eq_adds_1_false_m2_placed {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

/-! ## Pool-threaded Block-`518` basic-block segments -/

/-- Pool-threaded `[LibsignalPlacement]` segment `(blkPl_518).base + 0x0868 → lsmpl.base 205`
(`<PublicKey>::serialize`). -/
theorem p2_seg1a_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
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
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205) s
      ((cells (coroPtr + 0x3f8#64) 6 ∗
        cells (coroPtr + 0x468#64) 4 ∗
        ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
        ((msgPtr + 0xf0#64) ↦₈ msgVerByte)) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          (processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ msgVerByte)) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x8a0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx8' : s.readReg64 (Reg.gpr 8#5) = kyberStorePtr := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = kyberStoreVt := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = preKeyStorePtr := hx11
  have hx12' : s.readReg64 (Reg.gpr 12#5) = remoteAddrPtr := hx12
  have hx13' : s.readReg64 (Reg.gpr 13#5) = preKeyStoreVt := hx13
  have hx14' : s.readReg64 (Reg.gpr 14#5) = localAddrPtr := hx14
  have hx15' : s.readReg64 (Reg.gpr 15#5) = idStorePtr := hx15
  have hx16' : s.readReg64 (Reg.gpr 16#5) = idStoreVt := hx16
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_518 (Rust.withPanics ext) (lsmpl.base 205)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by dsimp only [processPrekeyActive10At]; sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-- Pool-threaded `[LibsignalPlacement]` segment `(blkPl_518).base + 0x08a0 → lsmpl.base 50`
(`<SessionRecord>::promote_matching_session`). -/
theorem p2_seg1b_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (msgVerByte : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = msgVerByte.zeroExtend 64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 50) s
      (A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x8c0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = msgVerByte.zeroExtend 64 := hx25
  wp_steps_sync_518 (Rust.withPanics ext) (lsmpl.base 50)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-- Pool-threaded `[LibsignalPlacement]` segment `(blkPl_518).base + 0x08c0 → __rust_dealloc`
on the `Ok(true)` branch of `promote_matching_session`. -/
theorem p2_matched_to_dealloc_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr serPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") s
      ((((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8)) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8)) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = serPtr ∧
        s1.readReg64 .x1 = 33#64 ∧
        s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x930#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps_sync_518 (Rust.withPanics ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-- Pool-threaded `[LibsignalPlacement]` segment `(blkPl_518).base + 0x0930 → lsmpl.base 29`
(`<SessionState>::remote_identity_key`). -/
theorem p2_matched_to_remote_ik_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr locCap : BitVec 64)
    (hcap : locCap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x930#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 29) s
      ((((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        ((coroPtr + 0xf8#64) ↦₆₄ locCap)) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ (((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((coroPtr + 0xf8#64) ↦₆₄ locCap)) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x94c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcmn := cond_eq_adds_1_false_m2_placed hcap
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 (Rust.withPanics ext) (lsmpl.base 29)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux
