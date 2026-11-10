/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2

/-!
# Stage P2 Substages 1–4 Shared Helpers

Region-splitting, stack-bound, `FsAt`, and `.Quiet` (`stageP2EnvOk`, `stageP2Quiet`) helpers shared
across Stage P2 Substages P2.1–P2.4.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option linter.unusedSimpArgs false

/-! ## 1. Region & `.Quiet` Helpers for Substages 1–4 -/

theorem p2_memRegion_3e0_split_9_79 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 88 =
      memRegion (sp + 0x3e0#64) 9 ∗ memRegion (sp + 0x3e9#64) 79 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 9) (k := 79)
    (b' := sp + 0x3e9#64) rfl (by bv_omega) (by decide)

theorem p2_memRegion_3e0_split_88_280 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x438#64) 280 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 88) (k := 280)
    (b' := sp + 0x438#64) rfl (by bv_omega) (by decide)

theorem p2_memRegion_a90_65_to_cells6 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 65 =
      cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 48) (k := 17)
        (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide)]

theorem p2_memRegion_a90_288_split_65_223 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 288 =
      memRegion (sp + 0xa90#64) 65 ∗ memRegion (sp + 0xad1#64) 223 :=
  ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 65) (k := 223)
    (b' := sp + 0xad1#64) rfl (by bv_omega) (by decide)

theorem p2_memRegion_3e0_split_9_359 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 9 ∗ memRegion (sp + 0x3e9#64) 359 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 9) (k := 359)
    (b' := sp + 0x3e9#64) rfl (by bv_omega) (by decide)

theorem p2_memRegion_3e0_split_64_304 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 64 ∗ memRegion (sp + 0x420#64) 304 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 64) (k := 304)
    (b' := sp + 0x420#64) rfl (by bv_omega) (by decide)

theorem p2_cells8_930_split_7_57 (sp : BitVec 64) :
    cells (sp + 0x930#64) 8 =
      memRegion (sp + 0x930#64) 7 ∗ memRegion (sp + 0x937#64) 57 := by
  rw [← ProofLib.memRegion_cells (sp + 0x930#64) 8 (by decide)]
  exact ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 7) (k := 57)
    (b' := sp + 0x937#64) rfl (by bv_omega) (by decide)

theorem p2_memRegion_a90_65_eq_cells8_1 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 65 =
      cells (sp + 0xa90#64) 8 ∗ memRegion (sp + 0xad0#64) 1 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 64) (k := 1)
        (b' := sp + 0xad0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp + 0xa90#64) 8 (by decide)]

theorem p2_memRegion_3e0_split_344_24 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 344 ∗ memRegion (sp + 0x538#64) 24 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 344) (k := 24)
    (b' := sp + 0x538#64) rfl (by bv_omega) (by decide)

theorem p2_memRegion_a90_288_split_cells8_224 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 288 =
      cells (sp + 0xa90#64) 8 ∗ memRegion (sp + 0xad0#64) 224 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 64) (k := 224)
        (b' := sp + 0xad0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp + 0xa90#64) 8 (by decide)]

theorem p2_cells2_4f8_eq (coroPtr : BitVec 64) :
    cells (coroPtr + 0x4f8#64) 2 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1) := by
  dsimp only [cells]
  sep_norm

theorem p2_sessionRecordEmptyHeaderAt_eq (coroPtr : BitVec 64) :
    ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) := by
  unfold ResponderClosure.sessionRecordEmptyHeaderAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem p2_processPrekeyActive10At_eq
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr preKeyVt kyberStorePtr kyberVt : BitVec 64) :
    processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr preKeyVt kyberStorePtr kyberVt =
      ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberVt) ∗
      ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ preKeyVt) ∗
      ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ idVt) ∗
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
      ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) := by
  unfold processPrekeyActive10At
  ac_rfl

theorem p2_cells2_398_join_48 (coroPtr : BitVec 64) :
    cells (coroPtr + 0x398#64) 2 ∗ memRegion (coroPtr + 0x3a8#64) 48 =
      memRegion (coroPtr + 0x398#64) 64 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x398#64) 2 (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x398#64) (n := 16) (k := 48)
        (b' := coroPtr + 0x3a8#64) rfl (by bv_omega) (by decide)]

theorem p2_spkShim_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    spkKit.getShimStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_left _ _) (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_spkPoll_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    spkKit.getPollStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_trans (Nat.le_max_left _ _) (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_kpkShim_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    kpkKit.getShimStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_kpkPoll_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    kpkKit.getPollStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_pkShim_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    pkKit.getShimStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_pkPoll_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    pkKit.getPollStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (p2_sub1To4_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_kpShim_le_stageP2 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    skit.kpShimStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_left _ _) (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit))

theorem p2_cells4_3d8_eq (coroPtr : BitVec 64) :
    cells (coroPtr + 0x3d8#64) 4 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((coroPtr + 0x3d8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x3e8#64) ↦₆₄ u2) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u3) := by
  dsimp only [cells]
  sep_norm

theorem p2_fsAt_envOk_of_trace_eq {envOk : FsFiles → Prop} {Q : Prop} {P : Program}
    {s s' : State} (hfs : FsAt envOk Q P s) (hst : Steps P s s') (htr : s'.trace = s.trace) :
    envOk s'.fs.files :=
  (hfs.of_steps hst (evs := []) (by rw [htr, List.append_nil]) (fun _ => NoFsEv.nil)).envOk_here

theorem p2_sessionRecordEmptyHeaderAt_errArm {A : RustAlloc} (coroPtr : BitVec 64) :
    ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if (0#64 : BitVec 64) = 0 then emp
       else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
            memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) ∗
      ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) := by
  have hif : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  rw [hif, p2_sessionRecordEmptyHeaderAt_eq coroPtr]
  sep_norm

theorem p2_cells8_398_to_keyPair64UnalignedAt (coroPtr : BitVec 64) :
    cells (coroPtr + 0x398#64) 8 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8, ∃∗ c63 : BitVec 8,
      ∃∗ cw0 : BitVec 64, ∃∗ cw1 : BitVec 64, ∃∗ cw2 : BitVec 64, ∃∗ cw3 : BitVec 64,
      ∃∗ cw4 : BitVec 64, ∃∗ cw5 : BitVec 64, ∃∗ cw6 : BitVec 64,
        keyPair64UnalignedAt (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6
          cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x398#64) 8 (by decide)]
  exact memRegion64_entails_exists_keyPair64UnalignedAt_std3 (coroPtr + 0x398#64)

theorem p2_memRegion64_to_bytes32_pair (base : BitVec 64) :
    memRegion base 64 ⊢
      ∃∗ pkBytes : List (BitVec 8), ∃∗ skBytes : List (BitVec 8),
        ⌜pkBytes.length = 32 ∧ skBytes.length = 32⌝ ∗
        (base ↦ₛ pkBytes) ∗ ((base + 0x20#64) ↦ₛ skBytes) := by
  rw [ProofLib.memRegion_split' (b := base) (n := 32) (k := 32)
        (b' := base + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eq_exists_bytes base 32 (by decide),
      ProofLib.memRegion_eq_exists_bytes (base + 0x20#64) 32 (by decide)]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun pkBytes => ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun skBytes => ?_
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hpk => ?_
  rw [← sepConj_assoc, sepConj_comm (base ↦ₛ pkBytes), sepConj_assoc]
  refine Entails.pure_left fun hsk => ?_
  refine Entails.sepExists_right pkBytes (Entails.sepExists_right skBytes ?_)
  exact Entails.pure_right ⟨hpk, hsk⟩ (Entails.refl _)

/-- Combined file-system environment predicate for the 4 Stage P2 stores. -/
def stageP2EnvOk {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (ikit : IdentityStoreSpec A b) (F : FsFiles) : Prop :=
  spkKit.envOk F ∧ kpkKit.envOk F ∧ pkKit.envOk F ∧ ikit.envOk F

theorem p2_envOk_spk {A : RustAlloc} {b : BitVec 64}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {ikit : IdentityStoreSpec A b} {Q : Prop}
    {P : Program} {s s' : State}
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) Q P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace) :
    spkKit.envOk s'.fs.files :=
  (p2_fsAt_envOk_of_trace_eq hfs hst htr).1

theorem p2_envOk_kpk {A : RustAlloc} {b : BitVec 64}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {ikit : IdentityStoreSpec A b} {Q : Prop}
    {P : Program} {s s' : State}
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) Q P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace) :
    kpkKit.envOk s'.fs.files :=
  (p2_fsAt_envOk_of_trace_eq hfs hst htr).2.1

theorem p2_envOk_pk {A : RustAlloc} {b : BitVec 64}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {ikit : IdentityStoreSpec A b} {Q : Prop}
    {P : Program} {s s' : State}
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) Q P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace) :
    pkKit.envOk s'.fs.files :=
  (p2_fsAt_envOk_of_trace_eq hfs hst htr).2.2.1

theorem p2_envOk_id {A : RustAlloc} {b : BitVec 64}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {ikit : IdentityStoreSpec A b} {Q : Prop}
    {P : Program} {s s' : State}
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) Q P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace) :
    ikit.envOk s'.fs.files :=
  (p2_fsAt_envOk_of_trace_eq hfs hst htr).2.2.2

theorem p2_allocHookStack_le_stageP2 {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    allocHookStack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (by decide : allocHookStack ≤ stageP2PureAndErrStack)
    (p2_pure_le_stageP2 spkKit kpkKit pkKit skit)

theorem p2_dropSs3Stack_le_stageP2 {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    dropSessionStructureLocal2Stack ≤ stageP2CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (by decide : dropSessionStructureLocal2Stack ≤ stageP2PureAndErrStack)
    (p2_pure_le_stageP2 spkKit kpkKit pkKit skit)

theorem p2_pointsToBytes_entails_memRegion (base : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hlen : bs.length = n) :
    (base ↦ₛ bs) ⊢ memRegion base n := by
  rw [← hlen]
  exact ProofLib.pointsToBytes_entails_memRegion base bs

theorem p2_memRegion9_fp80_unpack (fp : BitVec 64) :
    memRegion (fp + 0xffffffffffffff80#64) 9 ⊢
      ∃∗ u_fp80 : BitVec 64, ∃∗ b_fp78 : BitVec 8,
        ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗
        ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) := by
  rw [ProofLib.memRegion_split' (b := fp + 0xffffffffffffff80#64) (n := 8) (k := 1)
        (b' := fp + 0xffffffffffffff88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_one]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u_fp80 => ?_
  rw [sepExists_sepConj_right]
  exact Entails.sepExists_right u_fp80 (Entails.refl _)

theorem p2_memRegion_ac8_join_1_223 (sp : BitVec 64) :
    memRegion (sp + 0xac8#64) 8 ∗ memRegion (sp + 0xad0#64) 1 ∗ memRegion (sp + 0xad1#64) 223 =
      memRegion (sp + 0xac8#64) 8 ∗ memRegion (sp + 0xad0#64) 224 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xad0#64) (n := 1) (k := 223)
        (b' := sp + 0xad1#64) rfl (by bv_omega) (by decide)]

/-- Combined `.Quiet` predicate for the 4 Stage P2 stores (`NoFsEv` on store events). -/
def stageP2Quiet {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) : Prop :=
  spkKit.Quiet ∧ kpkKit.Quiet ∧ pkKit.Quiet ∧ skit.Quiet

theorem p2_fsAt_step_spk {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {P : Program} {s s' : State} (id : BitVec 32) (ans : Except spkKit.GetErr SignedPreKeyRecord)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace ++ spkKit.getEvs id ans) :
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s' :=
  hfs.of_steps hst htr (fun hq => hq.1 id ans)

theorem p2_fsAt_step_kpk {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {P : Program} {s s' : State} (id : BitVec 32) (ans : Except kpkKit.GetErr KyberPreKeyRecord)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace ++ kpkKit.getEvs id ans) :
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s' :=
  hfs.of_steps hst htr (fun hq => hq.2.1.1 id ans)

theorem p2_fsAt_step_pk {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {P : Program} {s s' : State} (id : BitVec 32) (ans : Except pkKit.GetErr PreKeyRecord)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace ++ pkKit.getEvs id ans) :
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s' :=
  hfs.of_steps hst htr (fun hq => hq.2.2.1.1 id ans)

theorem p2_fsAt_step_kp {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {spkKit : SignedPreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {P : Program} {s s' : State} (ans : Except skit.KpErr IdentityKeyPair)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s)
    (hst : Steps P s s') (htr : s'.trace = s.trace ++ skit.kpEvs ans) :
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) P s' :=
  hfs.of_steps hst htr (fun hq => hq.2.2.2.1 ans)

theorem p2_keyPair64UnalignedAt_eq_bytes32_pair (a : BitVec 64)
    (pubBytes privBytes : List (BitVec 8))
    (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    (hpub : ∀ p : BitVec 64, (p ↦ₛ pubBytes) =
      (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₆₄ u3))
    (hpriv : ∀ p : BitVec 64, (p ↦ₛ clampBv8List privBytes) =
      (p ↦₆₄ u4) ∗ ((p + 8#64) ↦₆₄ u5) ∗ ((p + 16#64) ↦₆₄ u6) ∗ ((p + 24#64) ↦₆₄ u7))
    (hlo : ∀ p : BitVec 64,
      bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗
      ((p + 7#64) ↦₆₄ w0) ∗ ((p + 15#64) ↦₆₄ w1) ∗ ((p + 23#64) ↦₆₄ w2) ∗ ((p + 31#64) ↦₆₄ w3) =
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₆₄ u3) ∗
          bytes7At (p + 32#64) c0 c1 c2 c3 c4 c5 c6)
    (hhi : ∀ p : BitVec 64,
      bytes7At p c0 c1 c2 c3 c4 c5 c6 ∗
      ((p + 7#64) ↦₆₄ w4) ∗ ((p + 15#64) ↦₆₄ w5) ∗ ((p + 23#64) ↦₆₄ w6) ∗ ((p + 31#64) ↦₈ b63) =
        (p ↦₆₄ u4) ∗ ((p + 8#64) ↦₆₄ u5) ∗ ((p + 16#64) ↦₆₄ u6) ∗ ((p + 24#64) ↦₆₄ u7)) :
    keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 =
      (a ↦ₛ pubBytes) ∗ ((a + 0x20#64) ↦ₛ clampBv8List privBytes) := by
  dsimp only [keyPair64UnalignedAt]
  have h1 := hlo a
  have h2 := hhi (a + 0x20#64)
  have hpriv' := hpriv (a + 0x20#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h1 h2 hpriv' ⊢
  rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  have hlo' :
      ((((bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗ ((a + 7#64) ↦₆₄ w0)) ∗ ((a + 15#64) ↦₆₄ w1)) ∗
        ((a + 23#64) ↦₆₄ w2)) ∗ ((a + 31#64) ↦₆₄ w3)) =
      (a ↦ₛ pubBytes) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6 := by
    rw [hpub a]
    simpa only [sepConj_assoc] using h1
  rw [hlo']
  simp only [sepConj_assoc]
  rw [h2, ← hpriv']

theorem p2_cells8_930_split_56_8 (sp : BitVec 64) :
    cells (sp + 0x930#64) 8 = memRegion (sp + 0x930#64) 56 ∗ memRegion (sp + 0x968#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp + 0x930#64) 8 (by decide),
      ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 56) (k := 8)
        (b' := sp + 0x968#64) rfl (by bv_omega) (by decide)]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
