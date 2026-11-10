/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Common
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne

/-!
# Helpers for `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`)
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin
open Arm64 ProofLib

namespace LoadSingle

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_writeReg64_sp (s : Arm64.State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem calleeSavedVRegs_rebuild_d8_d9 (s : Arm64.State) :
    (BitVec.setWidth 64 (s.readVReg128 8#5), BitVec.setWidth 64 (s.readVReg128 9#5),
      (calleeSavedVRegs s).2.2.1, (calleeSavedVRegs s).2.2.2.1, (calleeSavedVRegs s).2.2.2.2.1,
      (calleeSavedVRegs s).2.2.2.2.2.1, (calleeSavedVRegs s).2.2.2.2.2.2.1,
      (calleeSavedVRegs s).2.2.2.2.2.2.2) = calleeSavedVRegs s := rfl

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post :=
  HashOne.sepWP_exists_elim h

theorem sepWP_pure_left_elim {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q : SepProp} {post : Arm64.State → SepProp → Prop}
    (h : P → SepWP prog pc s Q post) :
    SepWP prog pc s (⌜P⌝ ∗ Q) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hp, hm⟩ := hm
  exact h hp R hm

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWP prog pc s F post) :
    SepWP prog pc s Q post := by
  rw [heq]
  exact sepWP_pure_left_elim h

theorem entails_sepExists_intro {α : Sort _} {P : SepProp} {Q : α → SepProp} (a : α)
    (h : P ⊢ Q a) : P ⊢ (∃∗ x, Q x) :=
  Entails.trans h (Entails.sepExists_intro a)

theorem sret368_split_eq (sret : BitVec 64) :
    memRegion sret 368 =
      (∃∗ c0 : BitVec 64, (sret ↦₆₄ c0)) ∗ memRegion (sret + 8#64) 360 := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 8) (k := 360)
        (b' := sret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight]

theorem stackAt_load_sub_eq (sp : BitVec 64) (k : Nat) (hk : k ≤ 18256) :
    stackAt sp (loadSessionClosureStack - 1200) =
      memRegion (sp - 18256#64) (18256 - k) ∗ stackAt sp k := by
  have h1 : loadSessionClosureStack - 1200 = k + (18256 - k) := by
    change 2 ^ 14 + 3072 - 1200 = k + (18256 - k); omega
  have h2 : BitVec.ofNat 64 (k + (18256 - k)) = 18256#64 := by
    have : k + (18256 - k) = 18256 := by omega
    rw [this]
  rw [h1, ProofLib.stackAt_split_bottom sp k (18256 - k) (by omega), h2]

theorem stackAt_load_eq (sp : BitVec 64) :
    stackAt sp loadSessionClosureStack =
      stackAt (sp - 1200#64) (loadSessionClosureStack - 1200) ∗
      (∃∗ c_sp0 : BitVec 64, ∃∗ c_sp8 : BitVec 64,
        ((sp - 1200#64) ↦₆₄ c_sp0) ∗ ((sp - 1192#64) ↦₆₄ c_sp8)) ∗
      memRegion (sp - 1184#64) 360 ∗
      memRegion (sp - 824#64) 344 ∗
      memRegion (sp - 480#64) 24 ∗
      memRegion (sp - 456#64) 336 ∗
      memRegion (sp - 120#64) 8 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64,
        ((sp - 0x70#64) ↦₆₄ c0) ∗ ((sp - 0x68#64) ↦₆₄ c1) ∗
        ((sp - 0x60#64) ↦₆₄ c2) ∗ ((sp - 0x58#64) ↦₆₄ c3) ∗
        ((sp - 0x50#64) ↦₆₄ c4) ∗ ((sp - 0x48#64) ↦₆₄ c5) ∗
        ((sp - 0x40#64) ↦₆₄ c6) ∗ ((sp - 0x38#64) ↦₆₄ c7) ∗
        ((sp - 0x30#64) ↦₆₄ c8) ∗ ((sp - 0x28#64) ↦₆₄ c9) ∗
        ((sp - 0x20#64) ↦₆₄ c10) ∗ ((sp - 0x18#64) ↦₆₄ c11) ∗
        ((sp - 0x10#64) ↦₆₄ c12) ∗ ((sp - 0x08#64) ↦₆₄ c13)) := by
  simp only [stackAt, loadSessionClosureStack, HashbrownBin.extHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 3072))
        (n := 2 ^ 14 + 3072 - 1200) (k := 1200)
        (b' := sp - 1200#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1200#64) (n := 16) (k := 1184)
        (b' := sp - 1184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1184#64) (n := 360) (k := 824)
        (b' := sp - 824#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 824#64) (n := 344) (k := 480)
        (b' := sp - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 24) (k := 456)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 456#64) (n := 336) (k := 120)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112)
        (b' := sp - 0x70#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - 19456#64) 18256 ∗
    (memRegion (sp - 1200#64) (8 * 2) ∗
      (memRegion (sp - 1184#64) 360 ∗
        (memRegion (sp - 824#64) 344 ∗
          (memRegion (sp - 480#64) 24 ∗
            (memRegion (sp - 456#64) 336 ∗
              (memRegion (sp - 120#64) 8 ∗
                memRegion (sp - 0x70#64) (8 * 14))))))) =
    memRegion (sp - 1200#64 - 18256#64) 18256 ∗ _
  rw [ProofLib.memRegion_cells (sp - 1200#64) 2 (by decide),
      ProofLib.memRegion_cells (sp - 0x70#64) 14 (by decide)]
  have hc2 : cells (sp - 1200#64) 2 =
      (∃∗ c_sp0 : BitVec 64, ∃∗ c_sp8 : BitVec 64,
        ((sp - 1200#64) ↦₆₄ c_sp0) ∗ ((sp - 1192#64) ↦₆₄ c_sp8)) := by
    cells_unfold
  have hc14 : cells (sp - 0x70#64) 14 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64,
        ((sp - 0x70#64) ↦₆₄ c0) ∗ ((sp - 0x68#64) ↦₆₄ c1) ∗
        ((sp - 0x60#64) ↦₆₄ c2) ∗ ((sp - 0x58#64) ↦₆₄ c3) ∗
        ((sp - 0x50#64) ↦₆₄ c4) ∗ ((sp - 0x48#64) ↦₆₄ c5) ∗
        ((sp - 0x40#64) ↦₆₄ c6) ∗ ((sp - 0x38#64) ↦₆₄ c7) ∗
        ((sp - 0x30#64) ↦₆₄ c8) ∗ ((sp - 0x28#64) ↦₆₄ c9) ∗
        ((sp - 0x20#64) ↦₆₄ c10) ∗ ((sp - 0x18#64) ↦₆₄ c11) ∗
        ((sp - 0x10#64) ↦₆₄ c12) ∗ ((sp - 0x08#64) ↦₆₄ c13)) := by
    cells_unfold
  have hsub : sp - 19456#64 = sp - 1200#64 - 18256#64 := by bv_omega
  rw [hc2, hc14, hsub]

theorem stackAt_load_of_parts (sp : BitVec 64)
    (c_sp0 c_sp8 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : BitVec 64) :
    (stackAt (sp - 1200#64) (loadSessionClosureStack - 1200) ∗
      ((sp - 1200#64) ↦₆₄ c_sp0) ∗
      ((sp - 1192#64) ↦₆₄ c_sp8) ∗
      memRegion (sp - 1184#64) 360 ∗
      memRegion (sp - 824#64) 344 ∗
      memRegion (sp - 480#64) 24 ∗
      memRegion (sp - 456#64) 336 ∗
      memRegion (sp - 120#64) 8 ∗
      ((sp - 0x70#64) ↦₆₄ c0) ∗ ((sp - 0x68#64) ↦₆₄ c1) ∗
      ((sp - 0x60#64) ↦₆₄ c2) ∗ ((sp - 0x58#64) ↦₆₄ c3) ∗
      ((sp - 0x50#64) ↦₆₄ c4) ∗ ((sp - 0x48#64) ↦₆₄ c5) ∗
      ((sp - 0x40#64) ↦₆₄ c6) ∗ ((sp - 0x38#64) ↦₆₄ c7) ∗
      ((sp - 0x30#64) ↦₆₄ c8) ∗ ((sp - 0x28#64) ↦₆₄ c9) ∗
      ((sp - 0x20#64) ↦₆₄ c10) ∗ ((sp - 0x18#64) ↦₆₄ c11) ∗
      ((sp - 0x10#64) ↦₆₄ c12) ∗ ((sp - 0x08#64) ↦₆₄ c13)) ⊢
    stackAt sp loadSessionClosureStack := by
  rw [stackAt_load_eq sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact entails_sepExists_intro c0 (entails_sepExists_intro c1 (entails_sepExists_intro c2
    (entails_sepExists_intro c3 (entails_sepExists_intro c4 (entails_sepExists_intro c5
    (entails_sepExists_intro c6 (entails_sepExists_intro c7 (entails_sepExists_intro c8
    (entails_sepExists_intro c9 (entails_sepExists_intro c10 (entails_sepExists_intro c11
    (entails_sepExists_intro c12 (entails_sepExists_intro c13 (entails_sepExists_intro c_sp0
    (entails_sepExists_intro c_sp8 (Entails.of_eq (by ac_rfl)))))))))))))))))

theorem slot376_to_vec_and_tail (sp cap : BitVec 64) (bs336 : List (BitVec 8))
    (hbs : bs336.length = 336) :
    (((sp - 824#64) ↦₆₄ cap) ∗ ((sp - 816#64) ↦ₛ bs336) ∗ memRegion (sp - 480#64) 24) ⊢
      memRegion (sp - 824#64) 24 ∗
      (∃∗ c400 : BitVec 64, ((sp - 800#64) ↦₆₄ c400)) ∗
      memRegion (sp - 792#64) 336 := by
  have h1 := pointsTo64_entails_memRegion (sp - 824#64) cap
  have h2 : ((sp - 816#64) ↦ₛ bs336) ⊢ memRegion (sp - 816#64) 336 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp - 816#64) bs336
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))) ?_
  have hmerge1 :
      memRegion (sp - 824#64) 8 ∗ memRegion (sp - 816#64) 336 =
      memRegion (sp - 824#64) 344 := by
    exact (ProofLib.memRegion_split' (b := sp - 824#64) (n := 8) (k := 336)
      (b' := sp - 816#64) rfl (by bv_omega) (by decide)).symm
  have hmerge2 :
      memRegion (sp - 824#64) 344 ∗ memRegion (sp - 480#64) 24 =
      memRegion (sp - 824#64) 368 := by
    exact (ProofLib.memRegion_split' (b := sp - 824#64) (n := 344) (k := 24)
      (b' := sp - 480#64) rfl (by bv_omega) (by decide)).symm
  rw [← sepConj_assoc, hmerge1, hmerge2,
      ProofLib.memRegion_split' (b := sp - 824#64) (n := 24) (k := 344)
        (b' := sp - 800#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 800#64) (n := 8) (k := 336)
        (b' := sp - 792#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 800#64)]
  exact Entails.refl _

theorem slot376_restore_regions (sp : BitVec 64) (bs360 : List (BitVec 8))
    (h360 : bs360.length = 360) :
    (((sp - 824#64) ↦₆₄ 0#64) ∗ ((sp - 816#64) ↦ₛ bs360)) ⊢
      memRegion (sp - 824#64) 344 ∗ memRegion (sp - 480#64) 24 := by
  have h1 := pointsTo64_entails_memRegion (sp - 824#64) 0#64
  have h2 : ((sp - 816#64) ↦ₛ bs360) ⊢ memRegion (sp - 816#64) 360 := by
    rw [← h360]; exact pointsToBytes_entails_memRegion (sp - 816#64) bs360
  refine Entails.trans (sepConj_mono h1 h2) ?_
  have hmerge :
      memRegion (sp - 824#64) 8 ∗ memRegion (sp - 816#64) 360 =
      memRegion (sp - 824#64) 368 := by
    exact (ProofLib.memRegion_split' (b := sp - 824#64) (n := 8) (k := 360)
      (b' := sp - 816#64) rfl (by bv_omega) (by decide)).symm
  rw [hmerge,
      ProofLib.memRegion_split' (b := sp - 824#64) (n := 344) (k := 24)
        (b' := sp - 480#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem pollOptSessionRecordResultAt_some_of_parts (A : RustAlloc) (sret : BitVec 64)
    (G' : SessionGhost) (ss : Session (List (BitVec 8)))
    (hCanon : CanonSession G' ss)
    (bs336 : List (BitVec 8))
    (hbs : bs336.length = 336 ∧ G'.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline G' ss.state (unpack64 G'.localIk.cap ++ bs336)) :
    ((sret ↦₆₄ 0#64) ∗
      ((sret + 8#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 G'.localIk.cap ++ bs336)) ∗
      sessionAtHeap A G' ss) ⊢
    pollOptSessionRecordResultAt A sret (some ss) := by
  unfold pollOptSessionRecordResultAt
  refine entails_sepExists_intro G' ?_
  apply Entails.pure_right hCanon
  rw [sessionRecordAt_some_eq, sessionAt_eq_head_tail]
  simp only [sepExists_sepConj_right]
  refine entails_sepExists_intro bs336 ?_
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_right hbs
  have htail := (sessionRecord_tail360_eq_bytes sret G'.localIk.cap bs336).symm
  have h1 : sret + 24#64 + 8#64 = sret + 32#64 := by bv_omega
  rw [htail, h1]
  exact Entails.of_eq (by ac_rfl)

theorem table4SingleAt_of_parts (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) (ctrl : BitVec 64)
    (hctrl : ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
      ([k].length = 4 → 2#64 = 0#64) ∧
      CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
      FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]) :
    ((mp ↦₆₄ ctrl) ∗
      ((mp + 8#64) ↦₆₄ 3#64) ∗
      ((mp + 16#64) ↦₆₄ 2#64) ∗
      ((mp + 24#64) ↦₆₄ 1#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗
      ((mp + 40#64) ↦₆₄ k1) ∗
      A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
      (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
      arrayAt
        (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
        (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse) ⊢
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt := by
  rw [table4SingleAt_eq]
  apply Entails.pure_right hk
  refine entails_sepExists_intro ctrl ?_
  apply Entails.pure_right hctrl
  exact Entails.refl _

theorem pollOptSessionRecordResultAt_none_of_parts (A : RustAlloc) (sret : BitVec 64) :
    ((sret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (sret + 8#64) 360) ⊢
    pollOptSessionRecordResultAt A sret none :=
  Entails.refl _

theorem laneBit_laneOfBucket4_beq_zero (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (laneBit (laneOfBucket4 pos k) == 0#64) = false := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide

theorem readVReg128_of_vregs_eq {s1 s2 : Arm64.State} (h : s1.vregs = s2.vregs) (r : BitVec 5) :
    s1.readVReg128 r = s2.readVReg128 r := by
  simp [Arm64.State.readVReg128, h]

theorem bucket_rec_off_eqs (ctrl : BitVec 64) (k : Nat) :
    bucketAddr ctrl 400 k + 32#64 + 8#64 = bucketAddr ctrl 400 k + 40#64 ∧
    bucketAddr ctrl 400 k + 32#64 + 16#64 = bucketAddr ctrl 400 k + 48#64 ∧
    bucketAddr ctrl 400 k + 32#64 + 24#64 = bucketAddr ctrl 400 k + 56#64 ∧
    bucketAddr ctrl 400 k + 56#64 + 8#64 = bucketAddr ctrl 400 k + 64#64 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem allocPanic_frame_of_trace_eq {α : Type} (x : α)
    (s0 sm sf : Arm64.State) (F : SepProp) (htr : sm.trace = s0.trace) :
    allocPanic x sm sf ∗ F ⊢ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocPanic allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem wpp_call_sessionClone {prog : Program} {entry ret_pc ret : BitVec 64}
    {A : RustAlloc} {s0 s : Arm64.State} {P F : SepProp}
    {Q : Arm64.State → SepProp → Prop} {Fr : SepProp}
    (dst src sp' : BitVec 64) (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hcall : subroutine_ok prog entry (Serialization.sessionCloneSpec A))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hsp_eq : s.sp = sp') (htr : s.trace = s0.trace)
    (hP : P = (sessionStateReprAt A src G ss ∗ memRegion dst 344 ∗ A.pool ∗ stackAt sp' sessionCloneStack) ∗ F)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp' → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp prog ret sf
        ((sessionStateReprAt A src G ss ∗
          (∃∗ G', ⌜encSessionMem G' ss = encSessionMem G ss⌝ ∗ sessionStateReprAt A dst G' ss) ∗
          A.pool ∗ stackAt sp' sessionCloneStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.call_frame (x := ⟨dst, src, G, ss⟩)
    (φ := s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src)
    (T := sessionStateReprAt A src G ss ∗ memRegion dst 344 ∗ A.pool ∗ stackAt sp' sessionCloneStack)
    hcall hpc hrun hsp hlr
    (by dsimp only [Serialization.sessionCloneSpec]; rw [hsp_eq])
    ⟨hx0, hx1⟩ hP
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ h => Satisfies.mono (sepConj_mono_left
      (allocPanic_frame_of_trace_eq (⟨dst, src, G, ss⟩ : SessionCloneGhost) s0 s sf F htr)) h)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [Serialization.sessionCloneSpec]
  rw [hsp_eq, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  simp only [sepConj_assoc] at hnext ⊢
  exact hnext sf hpcf hrunf (hspf.trans hsp_eq) hcsf (htr_f.trans htr)

theorem slot376_tail360_eq_bytes (sp cap : BitVec 64) (bs336 : List (BitVec 8)) :
    (((sp - 816#64) ↦₆₄ 8#64) ∗ ((sp - 808#64) ↦₆₄ 0#64) ∗
      ((sp - 800#64) ↦₆₄ cap) ∗ ((sp - 792#64) ↦ₛ bs336)) =
    ((sp - 816#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 cap ++ bs336)) := by
  have h := sessionRecord_tail360_eq_bytes (sp - 824#64) cap bs336
  have e1 : sp - 824#64 + 8#64 = sp - 816#64 := by bv_omega
  have e2 : sp - 824#64 + 16#64 = sp - 808#64 := by bv_omega
  have e3 : sp - 824#64 + 24#64 = sp - 800#64 := by bv_omega
  have e4 : sp - 824#64 + 32#64 = sp - 792#64 := by bv_omega
  rwa [e1, e2, e3, e4] at h

theorem bucket_entry_of_parts (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (peerG : AddrGhost) (recG : SessionGhost) (ss : Session (List (BitVec 8)))
    (hcanon : CanonSession recG ss) :
    (protocolAddressAt A peerG (bucketAddr ctrl 400 k) ∗
      ((bucketAddr ctrl 400 k + 32#64) ↦₆₄ 0#64) ∗
      ((bucketAddr ctrl 400 k + 40#64) ↦₆₄ 8#64) ∗
      ((bucketAddr ctrl 400 k + 48#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (bucketAddr ctrl 400 k + 56#64) recG ss) ⊢
    sessionBucketEntryAt A peerG recG ss (bucketAddr ctrl 400 k) := by
  obtain ⟨hoff40, hoff48, hoff56, _⟩ := bucket_rec_off_eqs ctrl k
  dsimp only [sessionBucketEntryAt, sessionBucketValueOff]
  apply Entails.pure_right hcanon
  rw [sessionRecordAt_some_eq A (bucketAddr ctrl 400 k + 32#64) recG ss,
      hoff40, hoff48, hoff56]
  exact Entails.of_eq (by ac_rfl)


end LoadSingle

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
