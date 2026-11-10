/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P2 Over-Path Substages P2.1–P2.4

Defines bounded allocation event envelopes for Over-path Substages P2.1–P2.4 (`P2OverSub1To4Arm3Env`,
`P2OverSub1To4OkEnv`, `P2OverSub1To4Env`) and proves the budget-threaded `[LibsignalPlacement]`
composition `stageP2_over_sub1_to_4_kits_ext_placed_ofEnv` (`+0x0868 → +0x36ac` or Arms 1–3).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (dropSessionStructureLocal2Stack)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionStateReprAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt IdentitySelfStoreSpec IdentitySelfVtablesPlacedOk IdentityStoreSpec
  KyberPreKeyStoreSpec KyberPreKeyVtablesPlacedOk LibsignalCodeRoLoaded NoFsEv
  PreKeyStoreSpec PreKeyVtablesPlacedOk
  SignedPreKeyStoreSpec SignedPreKeyVtablesPlacedOk speErrAt
)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List clampBv8List_length)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved bytes7At decryptPrekeySavedRegsAt eq_of_sep_emp
  processPrekeyActive10At sessionRecordEmptyHeaderAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  OpkOkWitness opkOkEvs opkOkKeyBytes opkOkRel opkOkUpdate opkOptTag8 opkOptTag32
  p2_ac0_join_16_1 p2_bytes7_1_to_memRegion8 p2_cells8_930_split_56_8
  p2_drop_frame_mid p2_envOk_pk p2_fsAt_step_pk p2_intro_pk_vt_placed
  p2_keyPair64UnalignedAt_eq_bytes32_pair p2_keyPair64UnalignedAt_to_memRegion
  p2_kpShim_le_stageP2 p2_memRegion64_to_bytes32_pair
  p2_memRegion64_to_keyPair64UnalignedAt p2_memRegion8_to_bytes7_1
  p2_memRegion_3e0_split_88_280 p2_pair64_4f8_to_cells2
  p2_pkPoll_le_stageP2 p2_pkShim_le_stageP2 p2_pointsToBytes_entails_memRegion
  p2_processPrekeyActive10At_eq p2_pure_le_stageP2 p2_sepWPp_weaken_eq
  p2_stackAt_split_of_le stageP1EntryPlaced stageP1ProgPlaced
  stageP2CallStack stageP2EnvOk stageP2Quiet
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_baseCall_le_callStack p2_over_dropSS3_le_overPure
  p2_over_pure_le_callStack sessionAt_entails_sessionStateAt
  stageP2OverCallStack stageP2OverCallStack4K stageP2OverCallStack4K_eq
  stageP2OverPureAndErrStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env StageP2ClosureHooksPlaced StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K StageP2PureCalleesPlaced4KOfEnv StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEnv_iff_eq boxAllocEvents p2Sub1Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget (
  p2OpkRecFreeEvents_freeOnly p2Sub4NoneEnv_iff_boxAllocEnv p2Sub4SomeTailEvents
  stageP2_sub4_none_kits_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudget (
  p2Sub4SomeOkEvents p2Sub4SomePollEvents stageP2_sub4_some_kits_seqEnv_ext_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget (
  p2_over_arm3_err_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env P2OverSub1To3Env
  stageP2_over_sub1_to_3_kits_ext_placed_ofEnv
)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

private theorem p2_sepWPp_frame_eq {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P' Q Qp) (hP : P = P') :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem sepWPp_exists_elim {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {F : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (F x) Q Qp) :
    SepWPp prog ret s (∃∗ x : α, F x) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hmx⟩ := hm
  exact h x R hmx hL

private theorem sepWPp_pure_elim {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem p2_finish_err_arm_evs_drop {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre Rest Drop : SepProp} {ArmOut Keep : List AllocEvent → State → SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : List AllocEvent → State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧ (P_f ⊢ ArmOut evs sf) ∧ Φ evs sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ∀ evs sf, ArmOut evs sf ∗ Rest ⊢ Drop ∗ Keep evs sf)
    (hQ : ∀ (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      FreeOnlyEvs evs → sf.trace = s.trace → (P_f ⊢ Keep evs sf) → Φ evs sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, evs, hfree, htrf, hentf, hΦ⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hArm (Rest ∗ R) hm hL
  · have hmf1 : sf.mem ⊨ ((ArmOut evs sf ∗ Rest) ∗ R) := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hentf) hmf
    have hmf2 : sf.mem ⊨ ((Drop ∗ Keep evs sf) ∗ R) :=
      Satisfies.mono (sepConj_mono_left (hSplit evs sf)) hmf1
    rw [sepConj_assoc] at hmf2
    have hmf3 : sf.mem ⊨ Keep evs sf ∗ R := Satisfies.of_sep_right hmf2
    exact ⟨sf, hsteps,
      Or.inl ⟨hpcf, hrunf, Keep evs sf, hmf3,
        hQ evs sf (Keep evs sf) hsteps hpcf hrunf hfree htrf (Entails.refl _) hΦ⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Bounded Event Envelopes -/

/-- Over-path Arm 3 (`get_pre_key` error and `SessionRecord` drop) event envelope. -/
abbrev P2OverSub1To4Arm3Env (spkBoxSize : Nat) (spkPollEnv : List AllocEvent → Prop)
    (kpkBoxSize : Nat) (kpkPollEnv : List AllocEvent → Prop)
    (pkBoxSize : Nat) (pkPollEnv : BitVec 32 → List AllocEvent → Prop)
    (opkId? : Option (BitVec 32)) : List AllocEvent → Prop :=
  P2Sub1To4Arm3Env spkBoxSize spkPollEnv kpkBoxSize kpkPollEnv pkBoxSize pkPollEnv opkId?

example : P2OverSub1To4Arm3Env 64 (· = []) 64 (· = []) 64 (fun _ => (· = []))
    (some 1#32) (p2Sub1Events 64) :=
  Or.inl (Or.inl rfl)

/-- Over-path normal `+0x36ac` exit event envelope across Substages P2.1–P2.4. -/
abbrev P2OverSub1To4OkEnv (spkBoxSize : Nat) (spkPollEnv : List AllocEvent → Prop)
    (kpkBoxSize : Nat) (kpkPollEnv : List AllocEvent → Prop)
    (pkBoxSize : Nat) (pkPollEnv : BitVec 32 → List AllocEvent → Prop)
    (kpBoxSize : Nat) (opkId? : Option (BitVec 32)) : List AllocEvent → Prop :=
  P2Sub1To4OkEnv spkBoxSize spkPollEnv kpkBoxSize kpkPollEnv pkBoxSize pkPollEnv kpBoxSize opkId?

example : P2OverSub1To4OkEnv 64 (· = []) 64 (· = []) 64 (fun _ => (· = [])) 64
    none (p2Sub1Events 64) :=
  Or.inl (Or.inl rfl)

/-- Combined Over-path Substages P2.1–P2.4 event envelope covering Arms 1–3 and `+0x36ac`. -/
abbrev P2OverSub1To4Env (spkBoxSize : Nat) (spkPollEnv : List AllocEvent → Prop)
    (kpkBoxSize : Nat) (kpkPollEnv : List AllocEvent → Prop)
    (pkBoxSize : Nat) (pkPollEnv : BitVec 32 → List AllocEvent → Prop)
    (kpBoxSize : Nat) (opkId? : Option (BitVec 32)) : List AllocEvent → Prop :=
  P2Sub1To4Env spkBoxSize spkPollEnv kpkBoxSize kpkPollEnv pkBoxSize pkPollEnv kpBoxSize opkId?

example : P2OverSub1To4Env 64 (· = []) 64 (· = []) 64 (fun _ => (· = [])) 64
    (some 1#32) (p2Sub1Events 64) :=
  Or.inl (Or.inl rfl)

/-! ## Budget-Threaded Placed Substages P2.1–P2.4 (`+0x0868 → +0x36ac` or Arms 1–3) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed Over-path Stage P2 Substages P2.1–P2.4 (`+0x0868 → +0x36ac` or error
exit to `s0.readReg64 .x30` via Arms 1–3), unifying both OPK branches at `+0x36ac`. -/
theorem stageP2_over_sub1_to_4_kits_ext_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat)
    (hstk_p2 : stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤ stk)
    (st : M.σ)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 u_488 : BitVec 64)
    (hstk_sp : stk ≤ sp.toNat)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId opkIdWord : BitVec 32)
    (opkId? : Option (BitVec 32))
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState)
    (b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (hfits : FitsEnv M lim st
      (P2OverSub1To4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize opkId?))
    (hPromMiss : PromoteMatchingMissAtPlacedProp A.repAlloc ext coroPtr g recG sess 4#8 baseKey.serialize)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopk_word : ∀ id : BitVec 32, opkId? = some id → opkIdWord = id)
    (hid_pk : ∀ id : BitVec 32, opkId? = some id → pkKit.getIdOk id)
    (hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), opkId? = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = ikit.id_vt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt)
    (hErrSpk : ∀ (e : spkKit.GetErr) (spkFutPtr : BitVec 64)
      (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      P2OverSub1To3Arm1Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (coroPtr + 0x4b1#64) 64 ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
        ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (e : kpkKit.GetErr) (kyberFutPtr : BitVec 64)
      (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      P2OverSub1To3Arm2Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
        cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (coroPtr + 0x4b1#64) 64 ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
        ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hErrPk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (opkId : BitVec 32) (e : pkKit.GetErr)
      (pkBuf skBuf opkFutPtr v90 : BitVec 64)
      (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkId? = some opkId → pkKit.getRel stPk opkId (.error e) →
      P2OverSub1To4Arm3Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) opkId? evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
        ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
        ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (coroPtr + 0x4b1#64) 64 ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
        ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (wOpk : OpkOkWitness opkId?) (opkPkBytes opkSkBytes : List (BitVec 8))
      (pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' : BitVec 64)
      (evs : List AllocEvent) (s4 : State),
      Steps (stageP1ProgPlaced ext) s s4 →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s4 →
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk opkId? wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes opkId? wOpk opkPkBytes opkSkBytes →
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize opkId? evs →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 → idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      s4.pc = stageP1EntryPlaced + 0x36ac#64 →
      s4.status = .Running → s4.sp = sp →
      s4.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit opkId? wOpk →
      s4.readReg64 .x0 = idKpFutPtr → s4.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      s4.readReg64 .x19 = coroPtr → s4.readReg64 .x21 = v_b0 →
      s4.readReg64 .x23 = coroPtr + 0x4f2#64 → s4.readReg64 .x24 = sp + 0x370#64 →
      s4.readReg64 .x25 = sp + 0x210#64 → s4.readReg64 .x26 = coroPtr + 0x398#64 →
      s4.readReg64 .x27 = ctxPtr → s4.readReg64 .x28 = sp + 0xa90#64 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s4.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s4
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
         pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk opkId? wOpk) ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         prevSessionsEmptyAt A.repAlloc coroPtr g ∗
         sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
           idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkOptTag8 opkId?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
         ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8') ∗
         ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8') ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
         decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
         memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents evs st) s4 ∗ stackAt sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (spkKit.storeAt spkStorePtr stSpk ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗
       pkKit.storeAt preKeyStorePtr stPk ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
       cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       memRegion (coroPtr + 0x4b1#64) 64 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim st s ∗ stackAt sp stk ∗ Frame)
      Q Qp := by
  have hstk_lt : stk ≤ 2 ^ 64 := Nat.le_trans hstk_sp (Nat.le_of_lt sp.isLt)
  have hstk_p2' : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk :=
    (stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit) ▸ hstk_p2
  have hstk_base : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans (p2_over_baseCall_le_callStack spkKit kpkKit pkKit skit) hstk_p2'
  have hstk_overPure : stageP2OverPureAndErrStack ≤ stk :=
    Nat.le_trans (p2_over_pure_le_callStack spkKit kpkKit pkKit skit) hstk_p2'
  have hstk_dss : dropSessionStructureLocal2Stack ≤ stk :=
    Nat.le_trans p2_over_dropSS3_le_overPure hstk_overPure
  have hsp_dss : dropSessionStructureLocal2Stack ≤ sp.toNat :=
    Nat.le_trans hstk_dss hstk_sp
  have hstk_dss_split :=
    p2_stackAt_split_of_le sp stk dropSessionStructureLocal2Stack hstk_dss hstk_lt
  have hfits13 : FitsEnv M lim st
      (P2OverSub1To3Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)) :=
    FitsEnv.mono
      (fun _ h =>
        match h with
        | Or.inl h1 => Or.inl h1
        | Or.inr (Or.inl h2) => Or.inr (Or.inl h2)
        | Or.inr (Or.inr h3) => Or.inr (Or.inr (Or.inr (SeqEnv.inl h3))))
      hfits
  have hfits_ok14 : FitsEnv M lim st
      (P2Sub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize opkId?) :=
    FitsEnv.mono (fun _ h => Or.inr (Or.inr (Or.inr h))) hfits
  refine p2_sepWPp_frame_eq
    (stageP2_over_sub1_to_3_kits_ext_placed_ofEnv
      (P := P) (A := A) (lim := lim) (F := F) ext hH hPure
      skit spkKit spkEnv hspkVt hspkOk kpkKit kpkEnv hkpkVt hkpkOk pkKit stk hstk_p2
      st s0 s _ Q (Qp := Qp)
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 hstk_sp
      g recG sess baseKey signedPreKeyId kyberPreKeyId stSpk stKpk
      b_2c0 b_390 b_4f1 b_4f2
      hfits13 hPromMiss hkyber_nz hCode hfs hid_spk hspk_wf hid_kpk hkpk_wf
      hpc hrun hsp_eq hsp_align htr hvregs
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 ?_ ?_ ?_)
    (by (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
  · intro e spkFutPtr evs sf P_f hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hCodef hent
    exact hErrSpk e spkFutPtr evs sf P_f hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hCodef
      (Entails.trans hent (Entails.of_eq (eq_of_sep_emp (by sep_focus))))
  · intro spkRec spkPubBytes spkPrivBytes e kyberFutPtr evs sf P_f
      hrel_spk hrec_spk hpub_len hpriv_len hpub_eq hpriv_eq hrel_kpk hevs
      hpcf hrunf htrf hspf hcsf hvregsf hCodef hent
    exact hErrKpk spkRec spkPubBytes spkPrivBytes e kyberFutPtr evs sf P_f
      hrel_spk hrec_spk hpub_len hpriv_len hpub_eq hpriv_eq hrel_kpk hevs
      hpcf hrunf htrf hspf hcsf hvregsf hCodef
      (Entails.trans hent (Entails.of_eq (eq_of_sep_emp (by sep_focus))))
  · intro spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
      pkBuf skBuf kyberFutPtr v90_3 privCap_3 privPtr_3 evs13 s3
      hst03 hfs3 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
      hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
      hevs13 hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3 htr3
      hx19_3 hx21_3 _ hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
      hvregs3 hCode3
    have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hsp_align
    have hfits4_ok := hfits_ok14.seq_right hevs13
    refine weaken_frame
      (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt))
      (by sep_focus) ?_
    cases opkId? with
    | none =>
      dsimp only [opkOptTag32]
      have hfits_none : FitsEnv M lim (M.stepEvents evs13 st) (BoxAllocEnv skit.kpBoxSize) :=
        FitsEnv.mono
          (fun evs h => (p2Sub4NoneEnv_iff_boxAllocEnv skit.kpBoxSize evs).mpr h)
          hfits4_ok
      refine p2_sepWPp_frame_eq
        (stageP2_sub4_none_kits_placed ext ikit skit senv hskitVt hskitOk
          stk (Nat.le_trans (p2_kpShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_base) hstk_lt
          (s0.readReg64 .x30) (M.stepEvents evs13 st) s0 s3 _ Q (Qp := Qp)
          coroPtr msgPtr ctxPtr idStorePtr (msgPtr + 0x90#64) v_b0 u_488 opkIdWord b_4b0
          hfits_none hCode3 hpc3 hrun3 hsp3_align hvregs3 hx19_3 hx21_3 ?_)
        (by rw [hsp3]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
      intro idKpFutPtr s4 hst34 hpc4 hrun4 hsp4 htr4_3 hx0_4 hx1_4 hidKp_nz hidKp_al
        hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
        hvregs4 hCode4
      try rw [hsp3] at hsp4
      try rw [hsp3] at hx23_4
      try rw [hsp3] at hx24_4
      try rw [hsp3] at hx28_4
      try rw [hsp3]
      have hst04 : Steps (stageP1ProgPlaced ext) s s4 := hst03.trans hst34
      have hfs4 := hfs3.of_steps hst34 (evs := []) (by rw [htr4_3, List.append_nil])
        (fun _ => NoFsEv.nil)
      have hevs_none : P2OverSub1To4OkEnv
          spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
          kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
          pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize none
          (evs13 ++ boxAllocEvents skit.kpBoxSize) :=
        SeqEnv.append hevs13
          ((p2Sub4NoneEnv_iff_boxAllocEnv skit.kpBoxSize _).mpr
            ((boxAllocEnv_iff_eq skit.kpBoxSize _).mpr rfl))
      have hpool_none :
          M.stepEvents (boxAllocEvents skit.kpBoxSize) (M.stepEvents evs13 st) =
            M.stepEvents (evs13 ++ boxAllocEvents skit.kpBoxSize) st :=
        (M.stepEvents_append evs13 (boxAllocEvents skit.kpBoxSize) st).symm
      rw [hpool_none]
      refine weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      refine weaken_frame
        (p2_pair64_4f8_to_cells2 coroPtr kyberFutPtr (0#64 + kpkKit.getFutVtOff))
        (by sep_focus) ?_
      refine weaken_frame
        (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp).symm) (by sep_focus) ?_
      refine weaken_frame
        (p2_memRegion64_to_bytes32_pair (coroPtr + 0x4b1#64)) (by sep_focus) ?_
      sep_norm
      refine sepWPp_exists_elim fun opkPkBytes => sepWPp_exists_elim fun opkSkBytes =>
        sepWPp_pure_elim fun ⟨hopkPk_len, hopkSk_len⟩ => ?_
      have hok := hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        (() : OpkOkWitness none) opkPkBytes opkSkBytes
        pkBuf skBuf idKpFutPtr v90_3 3169#64 privCap_3 privPtr_3
        (evs13 ++ boxAllocEvents skit.kpBoxSize) s4
        hst04 hfs4 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
        hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        True.intro hopkPk_len hopkSk_len True.intro hevs_none
        hpkBuf_nz hskBuf_nz hidKp_nz hidKp_al hpc4 hrun4 hsp4
        (by dsimp only [opkOkEvs]; rw [htr4_3, htr3, List.append_nil])
        hx0_4 hx1_4 hx19_4 hx21_4
        (hx23_4.trans hx23_3) hx24_4 (hx25_4.trans hx25_3) (hx26_4.trans hx26_3)
        hx27_4 (hx28_4.trans hx28_3) (hx29_4.trans hx29_3)
        hvregs4 hCode4
      dsimp only [opkOkUpdate, opkOptTag8, opkOptTag32] at hok
      exact p2_sepWPp_weaken_eq hok (by sep_focus)
    | some opkId =>
      have hopk_eq : opkIdWord = opkId := hopk_word opkId rfl
      dsimp only [P2Sub4OkEnv] at hfits4_ok
      dsimp only [opkOptTag32]
      rw [hopk_eq]
      refine p2_intro_pk_vt_placed (A := A.repAlloc) hpkVt hCode3 ?_
      let Drop_pk : SepProp :=
        ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
        ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
        ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
        ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff))
      refine weaken_frame (p2_memRegion8_to_bytes7_1 (sp + 0x3b0#64)) (by sep_focus) ?_
      sep_norm
      refine sepWPp_exists_elim fun s0_b => sepWPp_exists_elim fun s1_b =>
        sepWPp_exists_elim fun s2_b => sepWPp_exists_elim fun s3_b =>
        sepWPp_exists_elim fun s4_b => sepWPp_exists_elim fun s5_b =>
        sepWPp_exists_elim fun s6_b => ?_
      refine weaken_frame (Entails.of_eq (p2_cells8_930_split_56_8 sp)) (by sep_focus) ?_
      refine weaken_frame (p2_memRegion64_to_keyPair64UnalignedAt (coroPtr + 0x4b1#64))
        (by sep_focus) ?_
      sep_norm
      refine sepWPp_exists_elim fun c0_i => sepWPp_exists_elim fun c1_i =>
        sepWPp_exists_elim fun c2_i => sepWPp_exists_elim fun c3_i =>
        sepWPp_exists_elim fun c4_i => sepWPp_exists_elim fun c5_i =>
        sepWPp_exists_elim fun c6_i => sepWPp_exists_elim fun c63_i =>
        sepWPp_exists_elim fun cw0_i => sepWPp_exists_elim fun cw1_i =>
        sepWPp_exists_elim fun cw2_i => sepWPp_exists_elim fun cw3_i =>
        sepWPp_exists_elim fun cw4_i => sepWPp_exists_elim fun cw5_i =>
        sepWPp_exists_elim fun cw6_i => ?_
      refine p2_sepWPp_frame_eq
        (stageP2_sub4_some_kits_seqEnv_ext_placed
          (P := P) (A := A) (lim := lim) (F := F) ext hH hPure
          pkKit pkEnv hpkOk ikit skit senv hskitVt hskitOk
          stk (Nat.le_trans (p2_pure_le_stageP2 spkKit kpkKit pkKit skit) hstk_base)
          (Nat.le_trans (p2_pkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_base)
          (Nat.le_trans (p2_pkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_base)
          (Nat.le_trans (p2_kpShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_base) hstk_lt
          (s0.readReg64 .x30) (M.stepEvents evs13 st) s0 s3 _ Q (Qp := Qp)
          coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr (msgPtr + 0x90#64)
          (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 3169#64 privCap_3 privPtr_3
          u_488 kyberFutPtr (0#64 + kpkKit.getFutVtOff)
          opkId stPk b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
          c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i
          hfits4_ok hCode3 (fun sm hst htrm => p2_envOk_pk hfs3 hst htrm)
          (hid_pk opkId rfl) (fun r hrel hrec => hpk_wf opkId r rfl hrel hrec)
          hpc3 hrun3 hsp3_align hvregs3 hx19_3 hx21_3 hx23_3 hx26_3 (hsp3.symm ▸ hx28_3)
          ?_ ?_)
        (by rw [hsp3]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
      ·
        intro opkFutPtr e evs_poll s4 _ hrel_pk hevs_poll hpc4 hrun4 hsp4 htr4_3
          hx19_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 _
          hvregs4 hCode4
        try rw [hsp3] at hsp4
        try rw [hsp3] at hx28_4
        try rw [hsp3]
        have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hsp_align
        rw [← hopk_eq]
        have h3b0_err :
            bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
              memRegion (sp + 0x3b7#64) 1 ⊢ memRegion (sp + 0x3b0#64) 8 := by
          have ha : (sp + 0x3b0#64) + 7#64 = sp + 0x3b7#64 := by bv_omega
          simpa only [ha] using
            p2_bytes7_1_to_memRegion8 (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b
        refine weaken_frame
          (sessionAt_entails_sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG sess)
          (by sep_focus) ?_
        refine weaken_frame (Entails.of_eq hstk_dss_split) (by sep_focus) ?_
        refine weaken_frame
          (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyber_pub_len)
          (by sep_focus) ?_
        refine weaken_frame
          (p2_pointsToBytes_entails_memRegion skBuf kyberPrivBytes 3168 hkyber_priv_len)
          (by sep_focus) ?_
        refine weaken_frame h3b0_err (by sep_focus) ?_
        refine weaken_frame
          (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp).symm) (by sep_focus) ?_
        refine weaken_frame
          (Entails.of_eq (p2_cells8_930_split_56_8 sp).symm) (by sep_focus) ?_
        refine weaken_frame
          (p2_keyPair64UnalignedAt_to_memRegion (coroPtr + 0x4b1#64)
            c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i)
          (by sep_focus) ?_
        refine weaken_frame
          (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
          (by sep_focus) ?_
        have harm3 := p2_over_arm3_err_hooks_placed_ok
          (st := M.stepEvents (p2Sub4SomePollEvents pkKit.getBoxSize evs_poll)
            (M.stepEvents evs13 st))
          (Qp := fun _ _ => False)
          hH hPure.dropSessionStructure3 hpkOk s0 s4
          sp coroPtr outPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
          v_b0 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) 3169#64 v_b0 privCap_3 ctxPtr privPtr_3
          opkId b_2c0 b_390 b_4f2 e
          g recG sess.state hCode4 hsp4 hsp_dss
          hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx23_4 (hx25_4.trans hx25_3) hx26_4 hx27_4 hx28_4
          hvregs4
        refine p2_finish_err_arm_evs_drop (Drop := Drop_pk) harm3 (by sep_focus) ?_
          (fun evs_arm sf P_f _ hpcf hrunf hfree_arm htrf hent ⟨hspf, hcsf, hvregsf, hCodef, _⟩ =>
            hErrPk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              opkId e pkBuf skBuf opkFutPtr v90_3
              (evs13 ++ (boxAllocEvents pkKit.getBoxSize ++ (evs_poll ++ evs_arm))) sf P_f
              hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
              hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
              rfl hrel_pk
              (SeqEnv.append hevs13
                (SeqEnv.append ((boxAllocEnv_iff_eq pkKit.getBoxSize _).mpr rfl)
                  (SeqEnv.append hevs_poll hfree_arm)))
              hpcf hrunf (by rw [htrf, htr4_3, htr3])
              hspf hcsf hvregsf hCodef hent)
        intro evs_arm sf
        have hpool_eq :
            M.stepEvents evs_arm
              (M.stepEvents (p2Sub4SomePollEvents pkKit.getBoxSize evs_poll)
                (M.stepEvents evs13 st)) =
            M.stepEvents
              (evs13 ++ (boxAllocEvents pkKit.getBoxSize ++ (evs_poll ++ evs_arm))) st := by
          dsimp only [p2Sub4SomePollEvents]
          simp only [← M.stepEvents_append, List.append_assoc]
        dsimp only [Drop_pk, opkOptTag32]
        rw [hpool_eq, hstk_dss_split, ← p2_ac0_join_16_1 sp]
        exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
      ·
        intro opkRec opkPubBytes opkPrivBytes evs_poll opkFutPtr idKpFutPtr
          pubCap_4 privCap_4 privPtr_4
          b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b63_4 c0_4 c1_4 c2_4 c3_4 c4_4 c5_4 c6_4
          w0_4 w1_4 w2_4 w3_4 w4_4 w5_4 w6_4 u0_o u1_o u2_o u3_o u4_o u5_o u6_o u7_o
          s4 hst34 hrel_pk hrec_pk hevs_poll _hpub_cap _hpriv_cap
          hopk_pub_len hopk_priv_len hopk_pub_eq hopk_priv_eq
          hopk_pub_w hopk_priv_w hopk_lo hopk_hi
          hpc4 hrun4 hsp4 htr4_3 hx0_4 hx1_4 hidKp_nz hidKp_al
          hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
          hvregs4 hCode4
        try rw [hsp3] at hsp4
        try rw [hsp3] at hx24_4
        try rw [hsp3] at hx28_4
        try rw [hsp3]
        have hst04 : Steps (stageP1ProgPlaced ext) s s4 := hst03.trans hst34
        have hfs4 := p2_fsAt_step_pk opkId (.ok opkRec) hfs3 hst34 htr4_3
        have hevs4_ok : P2Sub4OkEnv pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize
            (some opkId)
            (p2Sub4SomeOkEvents pkKit.getBoxSize evs_poll
              pubCap_4.toNat privCap_4.toNat skit.kpBoxSize) := by
          dsimp only [P2Sub4OkEnv, p2Sub4SomeOkEvents, p2Sub4SomeTailEvents]
          rw [List.append_assoc]
          exact SeqEnv.append ((boxAllocEnv_iff_eq pkKit.getBoxSize _).mpr rfl)
            (SeqEnv.append hevs_poll
              (SeqEnv.append
                (p2OpkRecFreeEvents_freeOnly pkKit.getBoxSize pubCap_4.toNat privCap_4.toNat)
                ((boxAllocEnv_iff_eq skit.kpBoxSize _).mpr rfl)))
        have hpool_ok :
            M.stepEvents
              (p2Sub4SomeOkEvents pkKit.getBoxSize evs_poll
                pubCap_4.toNat privCap_4.toNat skit.kpBoxSize)
              (M.stepEvents evs13 st) =
            M.stepEvents
              (evs13 ++ p2Sub4SomeOkEvents pkKit.getBoxSize evs_poll
                pubCap_4.toNat privCap_4.toNat skit.kpBoxSize) st :=
          (M.stepEvents_append _ _ _).symm
        rw [hpool_ok, ← hopk_eq]
        refine weaken_frame
          (Entails.of_eq (p2_keyPair64UnalignedAt_eq_bytes32_pair (coroPtr + 0x4b1#64)
            opkPubBytes opkPrivBytes
            b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b63_4 c0_4 c1_4 c2_4 c3_4 c4_4 c5_4 c6_4
            w0_4 w1_4 w2_4 w3_4 w4_4 w5_4 w6_4 u0_o u1_o u2_o u3_o u4_o u5_o u6_o u7_o
            hopk_pub_w hopk_priv_w hopk_lo hopk_hi))
          (by sep_focus) ?_
        sep_norm
        have h3b0_ok :
            bytes7At (sp + 0x3b0#64) b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 ∗
              memRegion (sp + 0x3b7#64) 1 ⊢ memRegion (sp + 0x3b0#64) 8 := by
          have ha : (sp + 0x3b0#64) + 7#64 = sp + 0x3b7#64 := by bv_omega
          simpa only [ha] using
            p2_bytes7_1_to_memRegion8 (sp + 0x3b0#64) b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4
        refine weaken_frame h3b0_ok (by sep_focus) ?_
        refine weaken_frame
          (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp).symm) (by sep_focus) ?_
        refine weaken_frame
          (Entails.of_eq (p2_cells8_930_split_56_8 sp).symm) (by sep_focus) ?_
        refine weaken_frame
          (p2_pair64_4f8_to_cells2 coroPtr opkFutPtr (0#64 + pkKit.getFutVtOff))
          (by sep_focus) ?_
        refine weaken_frame
          (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
          (by sep_focus) ?_
        refine p2_drop_frame_mid (Drop := Drop_pk) (by dsimp only [Drop_pk]; sep_focus) ?_
        have hok := hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          (opkRec : OpkOkWitness (some opkId)) opkPubBytes (clampBv8List opkPrivBytes)
          pkBuf skBuf idKpFutPtr v90_3 32#64 privCap_4 privPtr_4
          (evs13 ++ p2Sub4SomeOkEvents pkKit.getBoxSize evs_poll
            pubCap_4.toNat privCap_4.toNat skit.kpBoxSize) s4
          hst04 hfs4 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
          hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
          ⟨hrel_pk, hrec_pk⟩ hopk_pub_len (clampBv8List_length hopk_priv_len)
          ⟨opkPrivBytes, hopk_priv_len, hopk_pub_eq, hopk_priv_eq, rfl⟩
          (SeqEnv.append hevs13 hevs4_ok)
          hpkBuf_nz hskBuf_nz hidKp_nz hidKp_al hpc4 hrun4 hsp4
          (by dsimp only [opkOkEvs]; rw [htr4_3, htr3])
          hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4
          (hx25_4.trans hx25_3) hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29_3)
          hvregs4 hCode4
        dsimp only [opkOkUpdate, opkOptTag8, opkOptTag32] at hok
        exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_over_sub1_to_4_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_sub1_to_4_kits_ext_placed_ofEnv _ M P A lim F (InitializeBobV1Env F) AcceptErrEnv

abbrev stageP2_over_sub1_to_4_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_over_sub1_to_4_kits_ext_placed

abbrev stageP2_over_sub1_to_4_kits_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat)
    (hstk_p2 : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_over_sub1_to_4_kits_ext_placed_ofEnv ext hH hPure.to_4K
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    stk ((stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).symm ▸ hstk_p2)

abbrev stageP2_over_sub1_to_4_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat)
    (hstk_p2 : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_over_sub1_to_4_kits_placed_ofEnv ext hH hPure
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    stk hstk_p2

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget
