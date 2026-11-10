/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKit
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCallees
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize

/-!
# Stage P2 Shared Definitions and Callee Bundles

Defines Stage P2 stack budgets, prefix-generalized `SepWPp` / `AllocContracts` combinators,
4 KiB-stacked `StageP2ClosureHooks`, generic-capacity `vecU8` and 48-byte `SignalProtocolError`
layout lemmas, SPQR V1 Bob session byte layouts, and `StageP2PureCallees{,4K}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateStack initialStateValue InitialStateOkX)

set_option maxRecDepth 200000

/-! ## 1. Stack Budgets & Splitting Lemmas (`stageP2_*`) -/

/-- Pure/unwind callee stack floor across Substages P2.1–P2.6 and error exits:
covers `stageP2aStack` (`4400`), `stageP2bStack + 0x700` (V1 `initialize_bob_session`),
`allocHookStack`, and `dropSessionStructureLocal2Stack` (`futDropSpec` uses `0` stack). -/
def stageP2PureAndErrStack : Nat :=
  max (stageP2bStack + 0x700)
    (max stageP2aStack
      (max allocHookStack dropSessionStructureLocal2Stack))

/-- Callee stack budget for Substage P2.2 (`get_signed_pre_key` shim, poll, drop, keypair serde). -/
def spkGetCallStack {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b) : Nat :=
  max spkKit.getShimStack (max spkKit.getPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.3 (`get_kyber_pre_key` shim, poll, drop, kem serde). -/
def kpkGetCallStack {A : RustAlloc} {b : BitVec 64} (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max kpkKit.getShimStack (max kpkKit.getPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.4 (`get_pre_key` shim, poll, drop, prekey serde). -/
def pkGetCallStack {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) : Nat :=
  max pkKit.getShimStack (max pkKit.getPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.5 (`get_identity_key_pair` shim/poll/drop + V1 Bob init). -/
def selfKpCallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.kpShimStack (max skit.kpPollStack stageP2PureAndErrStack)

/-- Callee stack budget for Substage P2.6 (`get_local_registration_id` shim/poll/drop + promote). -/
def selfRegIdCallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.regIdShimStack (max skit.regIdPollStack stageP2PureAndErrStack)

/-- Combined stack budget for Substages P2.1–P2.4 (`spkKit`, `kpkKit`, `pkKit`, and unwinds). -/
def stageP2Sub1To4Stack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) : Nat :=
  max (spkGetCallStack spkKit) (max (kpkGetCallStack kpkKit) (pkGetCallStack pkKit))

/-- Combined stack budget for Substages P2.5–P2.6 (`skit` self-identity methods, V1 Bob init,
promote, and unwinds). -/
def stageP2Sub56Stack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (selfKpCallStack skit) (selfRegIdCallStack skit)

/-- Unified stack budget for full Stage P2 (`+0x868 -> +0x1778` and all 6 error exits). -/
def stageP2CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2Sub1To4Stack spkKit kpkKit pkKit) (stageP2Sub56Stack skit)

theorem p2_stackAt_split_of_le (sp : BitVec 64) (big small : Nat)
    (hle : small ≤ big) (hbig : big ≤ 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

theorem p2_stageP2bV1_le_pure : stageP2bStack + 0x700 ≤ stageP2PureAndErrStack :=
  Nat.le_max_left _ _

theorem p2_stageP2b_le_pure : stageP2bStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_add_right _ _) p2_stageP2bV1_le_pure

theorem p2_stageP2a_le_pure : stageP2aStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_alloc_le_pure : allocHookStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem p2_dropSS3_le_pure : dropSessionStructureLocal2Stack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem p2_pure_le_sub1To4 {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) :
    stageP2PureAndErrStack ≤ stageP2Sub1To4Stack spkKit kpkKit pkKit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)

theorem p2_pure_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (Nat.le_max_left _ _)

theorem p2_sub1To4_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub1To4Stack spkKit kpkKit pkKit ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_left _ _

theorem p2_sub56_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub56Stack skit ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_right _ _

theorem p2_pure_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_pure_le_sub1To4 spkKit kpkKit pkKit)
    (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit)

/-! ### 1b. 4K / `Ext` Stack Budgets (`stageP2PureAndErrStack4K = 33536`) -/

def stageP2PureAndErrStack4K : Nat := max (768 + Initiator.pqxdhEntryStackExt) stageP2PureAndErrStack
def spkGetCallStack4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b) : Nat :=
  max spkKit.getShimStack (max spkKit.getPollStack stageP2PureAndErrStack4K)
def kpkGetCallStack4K {A : RustAlloc} {b : BitVec 64} (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max kpkKit.getShimStack (max kpkKit.getPollStack stageP2PureAndErrStack4K)
def pkGetCallStack4K {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) : Nat :=
  max pkKit.getShimStack (max pkKit.getPollStack stageP2PureAndErrStack4K)
def selfKpCallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.kpShimStack (max skit.kpPollStack stageP2PureAndErrStack4K)
def selfRegIdCallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max skit.regIdShimStack (max skit.regIdPollStack stageP2PureAndErrStack4K)
def stageP2Sub1To4Stack4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b) (pkKit : PreKeyStoreSpec A b) : Nat :=
  max (spkGetCallStack4K spkKit) (max (kpkGetCallStack4K kpkKit) (pkGetCallStack4K pkKit))
def stageP2Sub56Stack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (selfKpCallStack4K skit) (selfRegIdCallStack4K skit)
def stageP2CallStack4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2Sub1To4Stack4K spkKit kpkKit pkKit) (stageP2Sub56Stack4K skit)

theorem p2_pure_le_pure4K : stageP2PureAndErrStack ≤ stageP2PureAndErrStack4K := Nat.le_max_right _ _
theorem p2_bobExt_le_pure4K : 768 + Initiator.pqxdhEntryStackExt ≤ stageP2PureAndErrStack4K := Nat.le_max_left _ _
theorem p2_pure4K_le_sub1To4_4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b) (pkKit : PreKeyStoreSpec A b) :
    stageP2PureAndErrStack4K ≤ stageP2Sub1To4Stack4K spkKit kpkKit pkKit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
theorem p2_pure4K_le_sub56_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : stageP2PureAndErrStack4K ≤ stageP2Sub56Stack4K skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
theorem p2_sub1To4_4K_le_stageP2_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub1To4Stack4K spkKit kpkKit pkKit ≤ stageP2CallStack4K spkKit kpkKit pkKit skit := Nat.le_max_left _ _
theorem p2_sub56_4K_le_stageP2_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub56Stack4K skit ≤ stageP2CallStack4K spkKit kpkKit pkKit skit := Nat.le_max_right _ _
theorem p2_pure4K_le_stageP2_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack4K ≤ stageP2CallStack4K spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_pure4K_le_sub1To4_4K spkKit kpkKit pkKit) (p2_sub1To4_4K_le_stageP2_4K spkKit kpkKit pkKit skit)
private theorem p2_max3_mono_right {a b c c' : Nat} (h : c ≤ c') :
    max a (max b c) ≤ max a (max b c') :=
  Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
      Nat.le_trans h (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩⟩

theorem p2_sub1To4_le_4K {A : RustAlloc} {b : BitVec 64} (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b) (pkKit : PreKeyStoreSpec A b) :
    stageP2Sub1To4Stack spkKit kpkKit pkKit ≤ stageP2Sub1To4Stack4K spkKit kpkKit pkKit :=
  Nat.max_le.mpr ⟨Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K) (Nat.le_max_left _ _),
    Nat.max_le.mpr ⟨Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
      Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩⟩
theorem p2_sub56_le_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : stageP2Sub56Stack skit ≤ stageP2Sub56Stack4K skit :=
  Nat.max_le.mpr ⟨Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K) (Nat.le_max_left _ _),
    Nat.le_trans (p2_max3_mono_right p2_pure_le_pure4K) (Nat.le_max_right _ _)⟩
theorem p2_callStack_le_4K {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2CallStack spkKit kpkKit pkKit skit ≤ stageP2CallStack4K spkKit kpkKit pkKit skit :=
  Nat.max_le.mpr ⟨Nat.le_trans (p2_sub1To4_le_4K spkKit kpkKit pkKit)
      (p2_sub1To4_4K_le_stageP2_4K spkKit kpkKit pkKit skit),
    Nat.le_trans (p2_sub56_le_4K skit) (p2_sub56_4K_le_stageP2_4K spkKit kpkKit pkKit skit)⟩

/-! ## 2. Prefix-Generalized `SepWPp` & `AllocContracts` Combinators (`p2_*`) -/

theorem p2_allocFailedIn_of_trace_prefix {s0 s sf : State}
    (htr : s0.trace <+: s.trace) (ha : allocFailedIn s sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢
  obtain ⟨d, hd⟩ := htr
  rw [← hd, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

theorem p2_allowPanic_oom_of_trace_prefix {s0 s sf : State} {F : SepProp}
    (htr : s0.trace <+: s.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    exact ⟨p2_allocFailedIn_of_trace_prefix htr ha, htr.trans hp⟩
  exact allowPanic_frame himp hm

@[simp, arm64_norm ↓, wp_norm ↓]
theorem p2_calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) : calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl
@[simp, arm64_norm ↓, wp_norm ↓]
theorem p2_calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) : calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) : calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg64_0 (s : State) (v : BitVec 64) : calleeSavedVRegs (s.writeVReg64 0#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem p2_calleeSavedVRegs_writeVReg64_1 (s : State) (v : BitVec 64) : calleeSavedVRegs (s.writeVReg64 1#5 v) = calleeSavedVRegs s := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

theorem p2_bobPanic_to_panicOom_prefix {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (htr : s0.trace <+: s.trace)
    (h : SepWPp prog ret s P Q (BobPanicOom s)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hq⟩ | ⟨hoom, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P_f, hmf, hq⟩⟩
  · refine ⟨sf, hst, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun R' hm' => ?_⟩)⟩
    have h' := hq R' hm'
    have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
        allocFailedIn s0 sf ∧ s0.trace <+: sf.trace :=
      fun ⟨ha, hp⟩ => ⟨p2_allocFailedIn_of_trace_prefix htr ha, htr.trans hp⟩
    exact Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono himp))) h'
  · exact ⟨sf, hst, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem p2_bind_sepWP_steps_frame {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s0 s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_seg_post ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  rcases hseg.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hmo⟩⟩
  · have hmm' : sm.mem ⊨ (P_seg_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hmo).elim

theorem p2_bind_sepWPp_exists_frame {α : Type} {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : α → SepProp}
    {Q_regs : α → State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => ∃ a : α, Q_regs a sm ∧ (P_m ⊢ P_stage_post a))
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ (a : α) (sm : State), Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs a sm →
      SepWPp prog ret sm (P_stage_post a ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, a, hregs, hent⟩ | ⟨hpan, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post a ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext a sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p2_call_frame_frozen_oom_prefix {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) hsteps
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, p2_allowPanic_oom_of_trace_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem fnOff_decryptPrekeyClosureName :
    libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      num% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
  rw [show CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
    "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" by decide]
  exact (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

theorem p2_shim_at_closure_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      noAllocShimSpec :=
  shim_ok_at2_ext hA
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (k := num% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem p2_alloc_at_closure_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (rustAllocSpec A) :=
  alloc_ok_at_norm_ext hA
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (k := num% ((2^64 + ls_off% "__rustc::__rust_alloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem p2_dealloc_at_closure_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext hA
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (k := num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem p2_memcpy_at_closure_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "memcpy" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      framelessMemcpySpec :=
  memcpy_ok_at2_ext hA
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (k := num% ((2^64 + ls_off% "memcpy" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem p2_panic_at_handle_error_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (k := num% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

/-! ### 2b. Stack-Bounded `StageP2ClosureHooks` and `memcpy` Callees -/

/-- 4 KiB-stacked `memcpy` contract (`rfl`-compatible with `CliExt.memcpySpec`). -/
def p2Memcpy4KSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (libcMemcpySpec allocHookStack).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

theorem p2_framelessMemcpy_to_4K {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry framelessMemcpySpec) :
    subroutine_ok prog entry p2Memcpy4KSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [p2Memcpy4KSpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(dst, src, bs), stackAt s0.sp allocHookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [framelessMemcpySpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [framelessMemcpySpec, p2Memcpy4KSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

theorem p2_shim_at_closure_of_hookSat {b : BitVec 64} {ext : String → Option (State → State)}
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      noAllocShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (stub := libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl
    (k := num% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol]) hShim

theorem p2_alloc_at_closure_of_allocHooks {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAlloc : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (rustAllocSpec A) :=
  alloc_ok_at_ext b A ext hAlloc CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_alloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem p2_dealloc_at_closure_of_allocHooks {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAlloc : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      (rustDeallocSpec A) :=
  dealloc_ok_at_ext b A ext hAlloc CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])

theorem p2_memcpy_at_closure_4k_of_hookSat {b : BitVec 64} {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "memcpy" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
      p2Memcpy4KSpec :=
  hook_ok_at (hname := "memcpy") (stub := libsignalSessionCode.fnOff "memcpy") rfl
    (k := num% ((2^64 + ls_off% "memcpy" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol]) hMemcpy

/-- Unified closure-level extern callee bundle for Stage P2 basic blocks (`shim` at 0 B,
`alloc`/`dealloc`/`memcpy` at `allocHookStack = 4096` B). -/
structure StageP2ClosureHooks (A : RustAlloc) (b : BitVec 64)
    (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    noAllocShimSpec
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (rustAllocSpec A)
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    (rustDeallocSpec A)
  memcpy4K : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "memcpy" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64))
    p2Memcpy4KSpec

theorem StageP2ClosureHooks.of_allocContracts {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    StageP2ClosureHooks A b ext :=
  ⟨p2_shim_at_closure_ext hA, p2_alloc_at_closure_ext hA, p2_dealloc_at_closure_ext hA,
   p2_framelessMemcpy_to_4K (p2_memcpy_at_closure_ext hA)⟩

theorem StageP2ClosureHooks.of_hooks {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec)
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec) : StageP2ClosureHooks A b ext :=
  ⟨p2_shim_at_closure_of_hookSat hShim, p2_alloc_at_closure_of_allocHooks hAlloc,
   p2_dealloc_at_closure_of_allocHooks hAlloc, p2_memcpy_at_closure_4k_of_hookSat hMemcpy⟩

theorem p2_publicKeySerialize_of_hooks {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName) (publicKeySerializeSpec A) := by
  have hshim0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_core::curve::PublicKey>::serialize"))) noAllocShimSpec :=
    hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (stub := libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<libsignal_core::curve::PublicKey>::serialize"))
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol]) hShim
  have hshim4K : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_core::curve::PublicKey>::serialize")))
      (specWithOptInv none (shimSpecWithStack allocHookStack)) := by
    apply subroutine_ok_to_optNone
    refine subroutine_ok_map hshim0 ?_
    intro x R s0 hpre; dsimp only [shimSpecWithStack] at hpre
    refine ⟨x, stackAt s0.sp allocHookStack ∗ R, ?_, fun sf hpost => ?_⟩
    · dsimp only [noAllocShimSpec]; simpa only [emp_sepConj, sepConj_assoc] using hpre
    · dsimp only [noAllocShimSpec, shimSpecWithStack] at hpost ⊢; simpa only [sepConj_assoc] using hpost
  have halloc4K : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_core::curve::PublicKey>::serialize")))
      (specWithOptInv none (rustAllocSpecWithStack A allocHookStack)) :=
    subroutine_ok_to_optNone
      (alloc_ok_at_ext b A ext hAlloc publicKeySerializeName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_core::curve::PublicKey>::serialize")) (by simp only [arm64_norm]))
  exact subroutine_ok_of_optNone
    (public_key_serialize_ok_of_hooks_opt (by decide) hshim4K halloc4K)

/-! ## 3. Pure Condition, 48-Byte SPE Realignment, & Generic-Capacity `vecU8` Helpers -/

theorem p2_cond_ne_adds64_of_ne_neg3 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 w 3#64) = true := by
  have hne : w + 3#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem p2_cond_ne_adds64_of_ne_neg2 {w : BitVec 64} (h : w ≠ 0xfffffffffffffffe#64) :
    ConditionHolds CondCode.NE (addsPState64 w 2#64) = true := by
  have hne : w + 2#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_ne_addsPState64]
  exact bne_iff_ne.mpr hne

theorem p2_cond_eq_adds64_of_ne_neg1 {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  have hne : w + 1#64 ≠ 0#64 := by bv_omega
  rw [conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

theorem p2_zext64_trunc32_id (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 32 = w := by
  bv_omega

/-- Unaligned 48-byte poll/sret cell layout `(w0, o1, o2, o3, o4, o5, o6)` matching the closure's
quadword reads from `sp + 0xa98` / `sp + 0x3e8` and writes to `outPtr`. -/
def p2PollCellsAt (p w0 : BitVec 64) (o1 : BitVec 32)
    (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) : SepProp :=
  (p ↦₆₄ w0) ∗
  ((p + 0x8#64) ↦₃₂ o1) ∗
  ((p + 0xc#64) ↦₆₄ o2) ∗
  ((p + 0x14#64) ↦₆₄ o3) ∗
  ((p + 0x1c#64) ↦₆₄ o4) ∗
  ((p + 0x24#64) ↦₆₄ o5) ∗
  ((p + 0x2c#64) ↦₃₂ o6)

/-- Exact 40-byte realignment at arbitrary base `a + 8`. -/
theorem p2_words5_repack (a w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 0x08#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) ∗ ((a + 0x18#64) ↦₆₄ w3) ∗
        ((a + 0x20#64) ↦₆₄ w4) ∗ ((a + 0x28#64) ↦₆₄ w5) =
      ((a + 0x08#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((a + 0x0c#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((a + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((a + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((a + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((a + 0x2c#64) ↦₃₂ w5.extractLsb' 32 32) := by
  rw [← pointsTo32_pair (a + 0x0c#64), ← pointsTo32_pair (a + 0x14#64),
      ← pointsTo32_pair (a + 0x1c#64), ← pointsTo32_pair (a + 0x24#64)]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Exact 48-byte cell bijection between `speWordsAt p w0 w1 w2 w3 w4 w5` and `p2PollCellsAt`. -/
theorem p2_speWordsAt_eq_pollCellsAt (p w0 w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt p w0 w1 w2 w3 w4 w5 =
      p2PollCellsAt p w0
        (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) := by
  unfold speWordsAt p2PollCellsAt
  have hrep :
      ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
          ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) =
        ((p + 0x08#64) ↦₃₂ w1.extractLsb' 0 32) ∗
          ((p + 0x0c#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
          ((p + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
          ((p + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
          ((p + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
          ((p + 0x2c#64) ↦₃₂ w5.extractLsb' 32 32) :=
    p2_words5_repack p w1 w2 w3 w4 w5
  exact congrArg ((p ↦₆₄ w0) ∗ ·) hrep

/-- Done-state coroutine layout at error/return (`0x7d8` bytes with discriminant `1#8` at `+0x2c0`),
`rfl`-equal to `dpFutDoneAt coroPtr`. -/
def p2CoroDoneAt (coroPtr : BitVec 64) : SepProp :=
  memRegion coroPtr 0x2c0 ∗
    ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    memRegion (coroPtr + 0x2c1#64) (0x7d8 - 0x2c1)

/-- Rejoin a non-empty `vecU8` buffer `(ptr ↦ₛ xs) ∗ memRegion (ptr + len) (cap - len)` into
`A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat` for `__rust_dealloc`. -/
theorem p2_vecBuf_dealloc_nonzero (A : RustAlloc) (cap ptr : BitVec 64) (xs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) (hxs_le : xs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ xs) ∗
       memRegion (ptr + BitVec.ofNat 64 xs.length) (cap.toNat - xs.length)) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hcap_ne' : cap ≠ 0 := hcap_ne
  simp only [hcap_ne', ↓reduceIte]
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr xs.length ∗
        memRegion (ptr + BitVec.ofNat 64 xs.length) (cap.toNat - xs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := xs.length) (k := cap.toNat - xs.length)
      (b' := ptr + BitVec.ofNat 64 xs.length) (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptr xs))

/-! ## 4. SPQR V1 Bob Session Byte Layouts (`rfl`-compatible with `BobTailV1`) -/

/-- `Params` Bob passes to `spqr::initial_state` (`rfl`-equal to `BobTailV1.bobSpqrParams`). -/
def p2BobSpqrParams (pqrKey : SignalPqxdh.Bytes) : CryptoVerification.LibsignalSpqrV1.Params :=
  { direction := .b2a, version := .v1, minVersion := .v1, authKey := bytesToBv8 pqrKey }

/-- Heap part of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs`
(`rfl`-equal to `BobTailV1.bobSpqrVecBuf`). -/
def p2BobSpqrVecBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- First 144 bytes of Bob's V1 `SessionState` (`rfl`-equal to `BobTailV1.bobHead144Bv8V1`). -/
def p2BobHead144Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen

/-- Full 344-byte `SessionState` built by `initialize_bob_session` at V1
(`rfl`-equal to `BobTailV1.bobSession344Bv8V1`). -/
def p2BobSession344Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  p2BobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32 pad_f4 ++
  bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2

/-- First 56 bytes of Bob's `SessionState` (`+0x00..+0x38`). -/
def p2BobSessHead56Bv8 (localIkBoxPtr remoteIkBoxPtr : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64

/-- Middle 280 bytes (`+0x38..+0x150`) of Bob's V1 `SessionState`. -/
def p2BobSessMid280V1 (rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++
  unpack32 pad_f4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 c0 ++ unpack64 c1 ++ unpack64 c2 ++ unpack64 c3 ++ unpack64 c4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 d0 ++ unpack64 d1 ++ unpack64 d2 ++
  unpack64 4#64

/-- Bob's 344-byte V1 `SessionState` with `remoteRegId` and `localRegId` written at `+0x150..0x158`. -/
def p2BobSessRegIdsV1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) : List (BitVec 8) :=
  p2BobSessHead56Bv8 localIkBoxPtr remoteIkBoxPtr ++
    (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
      (unpack32 remoteRegId ++ unpack32 localRegId))

theorem p2BobSessHead56Bv8_length (p1 p2 : BitVec 64) :
    (p2BobSessHead56Bv8 p1 p2).length = 56 := by
  simp [p2BobSessHead56Bv8]

theorem p2BobSessMid280V1_length (p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length = 280 := by
  unfold p2BobSessMid280V1 senderChainBytes100
  simp only [List.length_append, unpack64_length, unpack32_length]

attribute [local irreducible] unpack64 unpack32 senderChainBytes100 in
theorem p2BobSession344Bv8V1_eq_head56_mid280V1 (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    p2BobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      p2BobSessHead56Bv8 p1 p2 ++
        (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
          unpack64 0#64) := by
  unfold p2BobSession344Bv8V1 p2BobHead144Bv8V1 p2BobSessHead56Bv8 p2BobSessMid280V1 bobTail96Bv8
  simp only [List.append_assoc]

/-! ## 5. Ext-Generic Pure Callee Bundle (`StageP2PureCallees`) -/

/-- Stack-parameterized SPQR V1 `initialize_bob_session` success contract (`bobV1Stk = stageP2bStack + 0x700`
for 0-stack, `bobV1Stk = 768 + Initiator.pqxdhEntryStackExt` for 4K/`Ext`). -/
def InitializeBobV1OkAtExt (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (img : Obj.Image) (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  ∀ (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp),
    img.FrozenLoaded s0 → s0.symtab = img.symtab → s0.status = ExecStatus.Running →
    s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym →
    s0.spAligned = true → s0.sp - 576#64 ≠ 0#64 →
    s0.readReg64 (.gpr 0#5) = argPtr → s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr →
    s0.readReg64 (.gpr 8#5) = outPtr →
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp → ikBPk.length = 32 → spkBPk.length = 32 →
    Model.acceptKeys P inp = some drKey →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp bobV1Stk ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (p2BobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            p2BobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (logFilterAddr img ↦₆₄ 0#64) ∗
            stackAt s0.sp bobV1Stk ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0)

/-- Ext-generic contract for `initialize_bob_session` on `Model.acceptKeys P inp = some drKey` at
SPQR V1, `rfl`-compatible with `BobTailV1.initializeBobSession_ok_v1`. -/
def InitializeBobV1OkExt (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtExt P A F img ext (stageP2bStack + 0x700)

/-- Pure internal callees of `message_decrypt_prekey::<Coins>::{closure#0}` Stage P2 at
`tripleRatchetProgAtExt img.base ext`. -/
structure StageP2PureCallees (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "<libsignal_core::curve::PublicKey>::serialize")
      (publicKeySerializeSpec A)
  promoteMatchingSessionEmpty :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
      promoteMatchingSessionEmptySpec
  curveKeyPairSerde :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
      curveKeyPairSerdeOkSpec
  kemKeyPairSerde :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
      (kemKeyPairFromPubPrivOkSpec A)
  preKeyRecordKeyPair :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair")
      preKeyRecordKeyPairOkSpec
  dropSpe2 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")
      ((dropSpeSpec A).inImage img)
  isSameAccount :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.isSameAccountName)
      (isSameAccountDistinctSpec A uuidTryParse)
  initializeBobErr :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img)
  initializeBobV1 :
    InitializeBobV1OkExt P A F img ext
  promoteStateEmpty :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr promoteStateName)
      promoteStateEmptySpec
  dropProcessPrekeyImplState1 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName)
      dropProcessPrekeyImplState1Spec
  dropSessionStructure3 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A)

/-! ### 5b. 4K / `Ext` Pure Callee Contracts (`StageP2PureCallees4K`) -/

/-- 4 KiB-stacked `SessionRecord::promote_state` (empty-record fast path). -/
def promoteStateEmpty4KSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, srcPtr, bs) s =>
    ⌜s.readReg64 .x0 = recPtr ∧ s.readReg64 .x1 = srcPtr ∧ bs.length = 344⌝ ∗
    ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun (recPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

theorem promoteStateEmptySpec_to_4K {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry promoteStateEmptySpec) :
    subroutine_ok prog entry promoteStateEmpty4KSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨recPtr, srcPtr, bs⟩ R s0 hpre
  dsimp only [promoteStateEmpty4KSpec] at hpre
  rw [stackAt_promote_state_eq s0.sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(recPtr, srcPtr, bs), stackAt (s0.sp - 96#64) (allocHookStack - 96) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [promoteStateEmptySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [promoteStateEmptySpec, promoteStateEmpty4KSpec] at hpost ⊢
    rw [stackAt_promote_state_eq s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

/-- Stack-parameterized `<IdentityKey>::is_same_account` contract under `DistinctSid`. -/
def isSameAccountDistinctAtSpec (A : RustAlloc) (parse : UuidParser) (stk : Nat) :
    Spec (BitVec 64 × IdentityKey × BitVec 64 × AddrGhost ×
      BitVec 64 × IdentityKey × BitVec 64 × AddrGhost) where
  pre := fun (lIkA, lIk, locA, loc, rIkA, rIk, remA, rem) s =>
    ⌜s.readReg64 .x0 = lIkA ∧ s.readReg64 .x1 = locA ∧ s.readReg64 .x2 = rIkA ∧
      s.readReg64 .x3 = remA ∧ (lIk ≠ rIk ∨ DistinctSid parse loc.name.bytes rem.name.bytes)⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ protocolAddressAt A loc locA ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ protocolAddressAt A rem remA ∗ stackAt s.sp stk
  post := fun (lIkA, lIk, locA, loc, rIkA, rIk, remA, rem) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ protocolAddressAt A loc locA ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ protocolAddressAt A rem remA ∗ stackAt s0.sp stk

theorem isSameAccountDistinctSpec_to_ext {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry (isSameAccountDistinctSpec A parse)) :
    subroutine_ok prog entry
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A parse) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
    isSameAccountDistinctStack (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
            IsSameAccountDistinctGhost),
    memRegion (s0.sp - BitVec.ofNat 64
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt -
        isSameAccountDistinctStack) ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [isSameAccountDistinctSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [isSameAccountDistinctSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
      isSameAccountDistinctStack (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

/-- 4K/`Ext` variant of `initializeBobSessionErrInnerSpec` at `768 + Initiator.pqxdhEntryStackExt`. -/
def initializeBobSessionErr4KInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost where
  pre := fun (g : InitBobCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧ g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧ g.spkBPk.length = 32 ∧ Model.acceptKeys P g.inp = none⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobErrAt g.outPtr ∗ anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool
  onPanic := rustPanicOnOom img

def initializeBobSessionErr4KSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  (initializeBobSessionErr4KInnerSpec P A img).inImage img

abbrev initializeBobSessionErrExtSpec := initializeBobSessionErr4KSpec

theorem initializeBobSessionErrSpec_to_4K {prog : Program} {entry : BitVec 64}
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    (h : subroutine_ok prog entry (initializeBobSessionErrSpec P A img)) :
    subroutine_ok prog entry (initializeBobSessionErr4KSpec P A img) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionErrSpec, initializeBobSessionErrInnerSpec,
        Spec.inImage] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionErrSpec, initializeBobSessionErrInnerSpec,
        Spec.inImage] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt))
      ((768 + Initiator.pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [initializeBobSessionErr4KSpec, initializeBobSessionErr4KInnerSpec,
    Spec.inImage] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpure, hmem⟩
  have hnone : Model.acceptKeys P g.inp = none := hpure.2.2.2.2.2.2.2.2.2
  refine ⟨g, F_stk ∗ R, ?_, fun sf hpost => ?_, fun sf hpan => ?_⟩
  · dsimp only [initializeBobSessionErrSpec, initializeBobSessionErrInnerSpec, Spec.inImage, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrSpec, initializeBobSessionErrInnerSpec,
      initializeBobSessionInnerSpec, initializeBobSessionErr4KSpec,
      initializeBobSessionErr4KInnerSpec, Spec.inImage, F_stk] at hpost ⊢
    rw [hnone] at hpost
    rw [p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrSpec, initializeBobSessionErrInnerSpec,
      initializeBobSessionErr4KSpec, initializeBobSessionErr4KInnerSpec,
      Spec.inImage, rustPanicOnOom, F_stk] at hpan ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨hp, hmem_pan⟩
    exact ⟨hp, Arm64.Satisfies.mono (Entails.trans
      (Entails.of_eq (show anyHeap ∗ (memRegion _ _ ∗ R) =
        (anyHeap ∗ memRegion _ _) ∗ R by ac_rfl))
      (sepConj_mono_left (entails_anyHeap _))) hmem_pan⟩

/-- 4K/`Ext` SPQR V1 `initialize_bob_session` success contract (`768 + Initiator.pqxdhEntryStackExt = 33536` B). -/
def InitializeBobV1OkExt4K (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtExt P A F img ext (768 + Initiator.pqxdhEntryStackExt)

abbrev InitializeBobV1Ok4K := InitializeBobV1OkExt4K

theorem InitializeBobV1OkExt.to_4K {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (h : InitializeBobV1OkExt P A F img ext) :
    InitializeBobV1OkExt4K P A F img ext := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hF hsym hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt))
      ((768 + Initiator.pqxdhEntryStackExt) - (stageP2bStack + 0x700))
  have hsplit := p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
    (stageP2bStack + 0x700) (by decide) (by decide)
  have hcall := h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey (F_stk ∗ Frame) hF hsym hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  intro R hm hL
  have hm' : s0.mem ⊨
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
        memRegion outPtr 344 ∗ logFilterAddr img ↦₆₄ 0#64 ∗
        stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ (F_stk ∗ Frame)) ∗ R := by
    refine Satisfies.of_eq hm ?_; dsimp only [F_stk]; rw [hsplit]; ac_rfl
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
    baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := hcall R hm' hL
  · refine ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
      baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7,
      Entails.trans hPf (Entails.of_eq ?_), hst'⟩⟩
    dsimp only [F_stk]; rw [hsplit]; ac_rfl
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- 4K/`Ext` pure internal callee bundle for Stage P2 at `tripleRatchetProgAtExt img.base ext`. -/
structure StageP2PureCallees4K (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  publicKeySerialize : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr "<libsignal_core::curve::PublicKey>::serialize")
    (publicKeySerializeSpec A)
  promoteMatchingSessionEmpty : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
    promoteMatchingSessionEmptySpec
  curveKeyPairSerde : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
    curveKeyPairSerdeOkSpec
  kemKeyPairSerde : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
    (kemKeyPairFromPubPrivOkSpec A)
  preKeyRecordKeyPair : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair") preKeyRecordKeyPairOkSpec
  dropSpe2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")
    ((dropSpeSpec A).inImage img)
  isSameAccount : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.isSameAccountName)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A uuidTryParse)
  initializeBobErr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
    (initializeBobSessionErr4KSpec P A img)
  initializeBobV1 : InitializeBobV1OkExt4K P A F img ext
  promoteStateEmpty : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr promoteStateName) promoteStateEmpty4KSpec
  dropProcessPrekeyImplState1 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName)
    dropProcessPrekeyImplState1Spec
  dropSessionStructure3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
    (dropSessionStructureLocal2Spec A)

abbrev StageP2PureCalleesExt := StageP2PureCallees4K

theorem StageP2PureCallees.to_4K {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (h : StageP2PureCallees P A F img ext) :
    StageP2PureCallees4K P A F img ext where
  publicKeySerialize := h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := h.dropSpe2
  isSameAccount := isSameAccountDistinctSpec_to_ext h.isSameAccount
  initializeBobErr := initializeBobSessionErrSpec_to_4K h.initializeBobErr
  initializeBobV1 := h.initializeBobV1.to_4K
  promoteStateEmpty := promoteStateEmptySpec_to_4K h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 := h.dropSessionStructure3

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
