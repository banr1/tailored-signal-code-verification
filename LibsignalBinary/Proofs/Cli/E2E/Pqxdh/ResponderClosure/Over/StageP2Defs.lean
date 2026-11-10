/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage P2 Over-Path Spatial Predicates, Stack Budgets, and Callee Contracts

Defines `OverP2`-scoped `previous_sessions` (`Vec<Vec<u8>>`) predicates and `clearPending` helpers,
unified Stage P2 stack budgets, and instance-specialized and universal contracts for
`SessionRecord::promote_matching_session` (miss) and `SessionRecord::promote_state` (archive-and-promote).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr

/-- Element predicate for `previous_sessions` (`Vec<Vec<u8>>` entries). -/
abbrev prevElem (A : RustAlloc) : List (BitVec 8) → BitVec 64 → SepProp :=
  fun bs a => vecU8 A a bs

/-- Three-word `Vec` header `{cap, ptr, len}` at `r`. -/
abbrev HdrP (r cap ptr len : BitVec 64) : SepProp :=
  vecHeader r cap ptr len

/-- `Vec<Vec<u8>>` representation at `r` (`elemSize = 24`, `align = 8`). -/
abbrev prevVecAt (A : RustAlloc) (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (prevElem A) r cap ptr ps

/-- Capacity-4 1-element `previous_sessions` backing buffer. -/
def Prev1 (A : RustAlloc) (q : BitVec 64) (enc : List (BitVec 8)) : SepProp :=
  vecBuf A 24 8 (prevElem A) 4#64 q [enc]

/-- `SessionGhost` after `clear_unacknowledged_pre_key_message()`. -/
def clearPendingGhost (G : SessionGhost) : SessionGhost :=
  { G with pending := none, kyber := none }

/-- Model `Session` after `clear_unacknowledged_pre_key_message()`. -/
def clearPending (s : Session (List (BitVec 8))) : Session (List (BitVec 8)) :=
  { s with
    state := { s.state with pendingPreKey := false }
    pendingPreKey := none
    pendingKyberPreKey := none }

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Record and `SepWPp` Helpers -/

/-- Framed sequential composition for a panic-free `SepWPp` stage (`Qp := fun _ _ => False`). -/
theorem p2_bind_sepWPp_nopanic_frame {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p2_hdrP4_prev1_entails_prevVecAt (A : RustAlloc) (r q : BitVec 64) (enc : List (BitVec 8)) :
    OverP2.HdrP r 4#64 q 1#64 ∗ OverP2.Prev1 A q enc ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗ OverP2.prevVecAt A r prevCap' prevPtr' [enc] := by
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right q ?_)
  have hc4 : (4#64 : BitVec 64) ≠ 0#64 := by decide
  exact Entails.pure_right hc4 (Entails.refl _)

theorem prevEmpty_sessionAt_eq_sessionRecordAt (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess =
      sessionRecordAt A (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some recG⟩ ⟨some sess⟩ := by
  simp only [sessionRecordAt, prevSessionsEmptyAt, BitVec.add_assoc, BitVec.reduceAdd]

theorem sessionAt_entails_sessionStateAt (A : RustAlloc) (p : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionStateReprAt A p recG sess ⊢ sessionStateAt A p recG sess.state := by
  unfold sessionStateReprAt
  exact Entails.pure_left fun _ => Entails.refl _

/-! ## Stack Budgets -/

/-- Stack budget of `SessionRecord::archive_current_state_inner`. -/
abbrev p2ArchiveStackX : Nat := 464 + serializeSubStackX

/-- Stack budget of `SessionRecord::promote_state` (`32 + p2ArchiveStackX`). -/
abbrev p2PromoteStackX : Nat := 32 + p2ArchiveStackX

/-- Stack budget of `<SessionRecord>::promote_matching_session` on any miss path (`1248` B). -/
abbrev p2PromoteMissStack : Nat := 1248

/-- Stack floor across Over-path Substages P2.1–P2.6 pure callees and error exits. -/
def stageP2OverPureAndErrStack : Nat :=
  max stageP2PureAndErrStack (max p2PromoteMissStack p2PromoteStackX)

/-- Unified stack budget for Over-path Stage P2 at `stageP2CallStack`. -/
def stageP2OverCallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2CallStack spkKit kpkKit pkKit skit) stageP2OverPureAndErrStack

/-- Unified stack budget for Over-path Stage P2 with concrete SPQR-V1 Substage P2.5. -/
def stageP2OverV1CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2V1CallStack spkKit kpkKit pkKit skit) stageP2OverPureAndErrStack

theorem p2_over_basePure_le_overPure :
    stageP2PureAndErrStack ≤ stageP2OverPureAndErrStack :=
  Nat.le_max_left _ _

theorem p2_over_promoteMiss_le_overPure :
    p2PromoteMissStack ≤ stageP2OverPureAndErrStack :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_over_promoteOver_le_overPure :
    p2PromoteStackX ≤ stageP2OverPureAndErrStack :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem p2_over_dropSS3_le_overPure :
    dropSessionStructureLocal2Stack ≤ stageP2OverPureAndErrStack :=
  Nat.le_trans p2_dropSS3_le_pure p2_over_basePure_le_overPure

theorem p2_over_pure_le_callStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverCallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_right _ _

theorem p2_over_pure_le_v1CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_right _ _

theorem p2_over_baseCall_le_callStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2CallStack spkKit kpkKit pkKit skit ≤ stageP2OverCallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_left _ _

theorem p2_over_baseV1Call_le_v1CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_left _ _

theorem p2_over_callStack_le_v1CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack spkKit kpkKit pkKit skit ≤
      stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  Nat.max_le.mpr
    ⟨Nat.le_trans (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit) (Nat.le_max_left _ _),
     Nat.le_max_right _ _⟩

theorem p2_over_pure_lt_32 : stageP2OverPureAndErrStack < 2 ^ 32 := by decide

theorem p2_over_callStack_lt_32 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit)
    (hcall_lt : stageP2CallStack spkKit kpkKit pkKit skit < 2 ^ 32) :
    stageP2OverCallStack spkKit kpkKit pkKit skit < 2 ^ 32 :=
  Nat.max_lt.mpr ⟨hcall_lt, p2_over_pure_lt_32⟩

theorem p2_over_v1CallStack_lt_32 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit)
    (hcall_lt : stageP2V1CallStack spkKit kpkKit pkKit skit < 2 ^ 32) :
    stageP2OverV1CallStack spkKit kpkKit pkKit skit < 2 ^ 32 :=
  Nat.max_lt.mpr ⟨hcall_lt, p2_over_pure_lt_32⟩

/-- Stack budget of `<SessionRecord>::promote_matching_session` on any miss path under
`CliExt.blackBoxSpec` (`1248 + extHookStack = 17632` B). -/
abbrev p2OverPromoteMissStackExt : Nat := p2PromoteMissStack + extHookStack

def stageP2OverCallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2CallStack4K spkKit kpkKit pkKit skit) stageP2OverPureAndErrStack

def stageP2OverV1CallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2V1CallStack4K spkKit kpkKit pkKit skit) stageP2OverPureAndErrStack

theorem p2_over_pure4K_le_overPure :
    stageP2PureAndErrStack4K ≤ stageP2OverPureAndErrStack := by decide

theorem p2_over_bobExt_le_overPure :
    768 + Initiator.pqxdhEntryStackExt ≤ stageP2OverPureAndErrStack :=
  Nat.le_trans p2_bobExt_le_pure4K p2_over_pure4K_le_overPure

theorem p2_over_promoteMissExt_le_overPure :
    p2OverPromoteMissStackExt ≤ stageP2OverPureAndErrStack := by decide

private theorem p2_over_cells48_le_overPure :
    48 ≤ stageP2OverPureAndErrStack := by decide

theorem p2_over_strToOwnedX_le_overPure :
    Matched.strToOwnedLocal2StackWith extHookStack ≤ stageP2OverPureAndErrStack := by decide

theorem p2_over_allocHook_le_overPure :
    allocHookStack ≤ stageP2OverPureAndErrStack := by decide

private theorem p2_max3_le {a b c c' t : Nat}
    (h12 : max a (max b c') ≤ t) (h3 : c ≤ t) :
    max a (max b c) ≤ t :=
  Nat.max_le.mpr
    ⟨Nat.le_trans (Nat.le_max_left _ _) h12,
     Nat.max_le.mpr
       ⟨Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) h12, h3⟩⟩

theorem stageP2OverCallStack4K_eq {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack4K spkKit kpkKit pkKit skit =
      stageP2OverCallStack spkKit kpkKit pkKit skit := by
  have hle1 :
      stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤
        stageP2OverCallStack spkKit kpkKit pkKit skit := by
    have hcall : stageP2CallStack spkKit kpkKit pkKit skit ≤
        stageP2OverCallStack spkKit kpkKit pkKit skit := Nat.le_max_left _ _
    have hpure : stageP2PureAndErrStack4K ≤
        stageP2OverCallStack spkKit kpkKit pkKit skit :=
      Nat.le_trans p2_over_pure4K_le_overPure (Nat.le_max_right _ _)
    have hs14 : stageP2Sub1To4Stack spkKit kpkKit pkKit ≤
        stageP2OverCallStack spkKit kpkKit pkKit skit :=
      Nat.le_trans (Nat.le_max_left _ _) hcall
    have hs56 : stageP2Sub56Stack skit ≤
        stageP2OverCallStack spkKit kpkKit pkKit skit :=
      Nat.le_trans (Nat.le_max_right _ _) hcall
    refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨?_, Nat.max_le.mpr ⟨?_, ?_⟩⟩,
      Nat.max_le.mpr ⟨?_, ?_⟩⟩, Nat.le_max_right _ _⟩
    · exact p2_max3_le (Nat.le_trans (Nat.le_max_left _ _) hs14) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hs14) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hs14) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_max_left _ _) hs56) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_max_right _ _) hs56) hpure
  have hle2 :
      stageP2OverCallStack spkKit kpkKit pkKit skit ≤
        stageP2OverCallStack4K spkKit kpkKit pkKit skit := by
    have hcall : stageP2CallStack4K spkKit kpkKit pkKit skit ≤
        stageP2OverCallStack4K spkKit kpkKit pkKit skit := Nat.le_max_left _ _
    have hpure : stageP2PureAndErrStack ≤
        stageP2OverCallStack4K spkKit kpkKit pkKit skit :=
      Nat.le_trans p2_over_basePure_le_overPure (Nat.le_max_right _ _)
    have hs14 : stageP2Sub1To4Stack4K spkKit kpkKit pkKit ≤
        stageP2OverCallStack4K spkKit kpkKit pkKit skit :=
      Nat.le_trans (Nat.le_max_left _ _) hcall
    have hs56 : stageP2Sub56Stack4K skit ≤
        stageP2OverCallStack4K spkKit kpkKit pkKit skit :=
      Nat.le_trans (Nat.le_max_right _ _) hcall
    refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨?_, Nat.max_le.mpr ⟨?_, ?_⟩⟩,
      Nat.max_le.mpr ⟨?_, ?_⟩⟩, Nat.le_max_right _ _⟩
    · exact p2_max3_le (Nat.le_trans (Nat.le_max_left _ _) hs14) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hs14) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hs14) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_max_left _ _) hs56) hpure
    · exact p2_max3_le (Nat.le_trans (Nat.le_max_right _ _) hs56) hpure
  exact Nat.le_antisymm hle1 hle2

theorem stageP2OverV1CallStack4K_eq {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverV1CallStack4K spkKit kpkKit pkKit skit =
      stageP2OverV1CallStack spkKit kpkKit pkKit skit := by
  have hv4k :
      stageP2OverV1CallStack4K spkKit kpkKit pkKit skit =
        stageP2OverCallStack4K spkKit kpkKit pkKit skit :=
    Nat.le_antisymm
      (Nat.max_le.mpr
        ⟨Nat.max_le.mpr
           ⟨Nat.le_max_left _ _, Nat.le_trans p2_over_bobExt_le_overPure (Nat.le_max_right _ _)⟩,
         Nat.le_max_right _ _⟩)
      (Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
  have hbob1 : stageP2bStack + 0x700 ≤ stageP2OverPureAndErrStack := by decide
  have hv0 :
      stageP2OverV1CallStack spkKit kpkKit pkKit skit =
        stageP2OverCallStack spkKit kpkKit pkKit skit :=
    Nat.le_antisymm
      (Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hbob1 (Nat.le_max_right _ _)⟩,
         Nat.le_max_right _ _⟩)
      (Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
  exact hv4k.trans ((stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).trans hv0.symm)

/-! ## Callee Contracts: `promote_matching_session` and `promote_state` -/

abbrev p2PromoteStateName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_state"

/-- Predicate stating that `Session` `s` matches `(msgVer, serBytes)` in
`SessionRecord::promote_matching_session`. -/
def P2SessMatchesMsg (s : Session (List (BitVec 8))) (msgVer : BitVec 8)
    (serBytes : List (BitVec 8)) : Prop :=
  s.state.version = msgVer.zeroExtend 32 ∧ s.aliceBaseKey = serBytes

structure P2PromoteMatchingMissCallGhost where
  serPtr : BitVec 64
  outPtr : BitVec 64

/-- Instance-specialized specification of `<SessionRecord>::promote_matching_session` returning
`Ok(false)` without modifying the populated `SessionRecord` at `coroPtr + 0xe0`. -/
def p2PromoteMatchingMissAtSpec (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Spec P2PromoteMatchingMissCallGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = coroPtr + 0xe0#64 ∧
     st.readReg64 .x1 = msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr⌝ ∗
    prevSessionsEmptyAt A coroPtr g ∗
    sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
    (x.serPtr ↦ₛ serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp p2PromoteMissStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    prevSessionsEmptyAt A coroPtr g ∗
    sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
    (x.serPtr ↦ₛ serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp p2PromoteMissStack

def PromoteMatchingMissAtProp (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteMatchingSessionName)
    (p2PromoteMatchingMissAtSpec A coroPtr g recG sess msgVer serBytes)

structure P2PromoteMissGhost where
  recPtr : BitVec 64
  msgVer : BitVec 8
  serPtr : BitVec 64
  serBytes : List (BitVec 8)
  outPtr : BitVec 64
  g : RecordGhost
  r : SessionRecord (List (BitVec 8))
  s : Session (List (BitVec 8))

/-- Universal specification for a `<SessionRecord>::promote_matching_session` miss. -/
def p2PromoteMatchingMissGenSpec (A : RustAlloc) : Spec P2PromoteMissGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     ¬ P2SessMatchesMsg x.s x.msgVer x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp p2PromoteMissStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp p2PromoteMissStack

def PromoteMatchingMissGenProp (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteMatchingSessionName)
    (p2PromoteMatchingMissGenSpec A)

theorem promoteMatchingMissAt_of_gen {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenProp A img ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtProp A img ext coroPtr g recG sess msgVer serBytes := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ (p2PromoteMatchingMissGenSpec A).pre xg s0 ∗ R := by
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, xg, g']
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem p2_subroutine_ok_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal fun _ hout => hout

/-- Specification of `<SessionRecord>::promote_matching_session` returning `Ok(false)` at the
extended hook stack budget `p2OverPromoteMissStackExt`. -/
def p2PromoteMatchingMissAtSpecExt (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Spec P2PromoteMatchingMissCallGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = coroPtr + 0xe0#64 ∧
     st.readReg64 .x1 = msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr⌝ ∗
    prevSessionsEmptyAt A coroPtr g ∗
    sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
    (x.serPtr ↦ₛ serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp p2OverPromoteMissStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    prevSessionsEmptyAt A coroPtr g ∗
    sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
    (x.serPtr ↦ₛ serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp p2OverPromoteMissStackExt

def PromoteMatchingMissAtPropExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteMatchingSessionName)
    ((p2PromoteMatchingMissAtSpecExt A coroPtr g recG sess msgVer serBytes).inImage img)

def p2PromoteMatchingMissGenSpecExt (A : RustAlloc) : Spec P2PromoteMissGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     ¬ P2SessMatchesMsg x.s x.msgVer x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp p2OverPromoteMissStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp p2OverPromoteMissStackExt

def PromoteMatchingMissGenPropExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteMatchingSessionName)
    ((p2PromoteMatchingMissGenSpecExt A).inImage img)

theorem promoteMatchingMissGen_ext_of_plain {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr promoteMatchingSessionName)
      (p2PromoteMatchingMissGenSpecExt A)) :
    PromoteMatchingMissGenPropExt A img ext :=
  p2_subroutine_ok_inImage img h

theorem promoteMatchingMissAt_of_gen_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenPropExt A img ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtPropExt A img ext coroPtr g recG sess msgVer serBytes := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ ((p2PromoteMatchingMissGenSpecExt A).inImage img).pre xg s0 ∗ R := by
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [Spec.inImage, p2PromoteMatchingMissAtSpecExt, p2PromoteMatchingMissGenSpecExt, xg, g']
    refine Entails.pure_left fun hinv => Entails.pure_right hinv ?_
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2OverPromoteMissStackExt))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2OverPromoteMissStackExt)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [Spec.inImage, p2PromoteMatchingMissAtSpecExt, p2PromoteMatchingMissGenSpecExt, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteMatchingMissAt_to_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))} {msgVer : BitVec 8} {serBytes : List (BitVec 8)}
    (h : PromoteMatchingMissAtProp A img ext coroPtr g recG sess msgVer serBytes) :
    PromoteMatchingMissAtPropExt A img ext coroPtr g recG sess msgVer serBytes := by
  refine p2_subroutine_ok_inImage img (subroutine_ok_map h ?_)
  intro x R s0 hpre
  dsimp only [p2PromoteMatchingMissAtSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp p2OverPromoteMissStackExt p2PromoteMissStack
    (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨x,
    memRegion (s0.sp - BitVec.ofNat 64 p2OverPromoteMissStackExt)
      (p2OverPromoteMissStackExt - p2PromoteMissStack) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [p2PromoteMatchingMissAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Arm64.Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissAtSpecExt] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp p2OverPromoteMissStackExt p2PromoteMissStack
      (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Arm64.Satisfies.of_eq hpost.2 (by ac_rfl)⟩

structure P2PromoteOverCallGhost where
  src : BitVec 64
  newBs : List (BitVec 8)

/-- Instance-specialized specification of `<SessionRecord>::promote_state(coroPtr + 0xe0, src)`,
archiving `sess` into `previous_sessions` and copying the 344-byte `newBs` into `coroPtr + 0xf8`. -/
def p2PromoteOverAtSpec (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    Spec P2PromoteOverCallGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = coroPtr + 0xe0#64 ∧
     st.readReg64 .x1 = x.src ∧
     x.newBs.length = 344⌝ ∗
    prevSessionsEmptyAt A coroPtr g ∗
    sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
    A.pool ∗
    (x.src ↦ₛ x.newBs) ∗
    stackAt st.sp p2PromoteStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
      ⌜prevCap' ≠ 0#64⌝ ∗
      OverP2.prevVecAt A (coroPtr + 0xe0#64) prevCap' prevPtr'
        [encSessionMem (OverP2.clearPendingGhost recG) (OverP2.clearPending sess)]) ∗
    ((coroPtr + 0xf8#64) ↦ₛ x.newBs) ∗
    (x.src ↦ₛ x.newBs) ∗
    A.pool ∗
    stackAt s0.sp p2PromoteStackX
  onPanic := allocPanic

def PromoteOverAtProp (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr p2PromoteStateName)
    ((p2PromoteOverAtSpec A coroPtr g recG sess).inImage img)

structure P2PromoteOverGenGhost where
  recPtr : BitVec 64
  src : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  newBs : List (BitVec 8)

/-- Universal specification of `<SessionRecord>::promote_state` on empty `previous_sessions`. -/
def p2PromoteOverGenSpec (A : RustAlloc) : Spec P2PromoteOverGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.src ∧
     x.newBs.length = 344 ∧
     (encSessionMem (OverP2.clearPendingGhost x.G) (OverP2.clearPending x.sess)).length < 2 ^ 32⌝ ∗
    vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
    sessionStateReprAt A (x.recPtr + 0x18#64) x.G x.sess ∗
    A.pool ∗
    (x.src ↦ₛ x.newBs) ∗
    stackAt s.sp p2PromoteStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
      ⌜prevCap' ≠ 0#64⌝ ∗
      OverP2.prevVecAt A x.recPtr prevCap' prevPtr'
        [encSessionMem (OverP2.clearPendingGhost x.G) (OverP2.clearPending x.sess)]) ∗
    ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗
    (x.src ↦ₛ x.newBs) ∗
    A.pool ∗
    stackAt s0.sp p2PromoteStackX
  onPanic := allocPanic

def PromoteOverGenProp (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr p2PromoteStateName)
    ((p2PromoteOverGenSpec A).inImage img)

theorem promoteOverAt_of_gen {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenProp A img ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (OverP2.clearPendingGhost recG) (OverP2.clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtProp A img ext coroPtr g recG sess := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let xg : P2PromoteOverGenGhost := ⟨coroPtr + 0xe0#64, x.src, g.prevCap, g.prevPtr, recG, sess, x.newBs⟩
  have hrec_eq :
      prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess =
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr [] ∗
      sessionStateReprAt A (coroPtr + 0xe0#64 + 0x18#64) recG sess := by
    rw [prevEmpty_sessionAt_eq_sessionRecordAt]
    rfl
  have hpre' : s0.mem ⊨ ((p2PromoteOverGenSpec A).inImage img).pre xg s0 ∗ R := by
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [Spec.inImage, p2PromoteOverAtSpec, p2PromoteOverGenSpec, xg]
    refine Entails.pure_left fun hinv => Entails.pure_right hinv ?_
    refine Entails.pure_left fun ⟨h0, h1, hnb⟩ => ?_
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          (A.pool ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          (A.pool ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX)) := by
      ac_rfl
    rw [hre, hrec_eq]
    exact Entails.pure_right ⟨h0, h1, hnb, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [Spec.inImage, p2PromoteOverAtSpec, p2PromoteOverGenSpec, xg]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
