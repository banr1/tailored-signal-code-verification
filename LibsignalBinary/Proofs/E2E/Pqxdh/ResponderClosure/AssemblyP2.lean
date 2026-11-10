/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OneKeyVtables

/-!
# Stage P2.1–P2.3 Composition and `KeyPair` Layout Helpers for `message_decrypt_prekey::{closure#0}`

Provides `keyPair64UnalignedAt` simplification helpers, clean substage wrappers, and the combined
Substages P2.1–P2.3 composition (`+0x0868#64 -> +0x0d5c#64`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  bobSession344WithRegIdsBv8 bobSession280MidBv8 bobSession344Bv8 initBobErrAt protocolAddressAt

/-! ## 1. Layout & `keyPair64UnalignedAt` Simplification Helpers -/

theorem SepWPp.post_entails {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {P_post P_post' : State → SepProp} {Q_regs : State →
      Prop} (hstage : SepWPp prog ret s P
      (fun sf P_m => (P_m ⊢ P_post sf) ∧ Q_regs sf) (PanicOomProp s0))
    (hent : ∀ sf, P_post sf ⊢ P_post' sf) :
    SepWPp prog ret s P
      (fun sf P_m => (P_m ⊢ P_post' sf) ∧ Q_regs sf) (PanicOomProp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_m, hmf, hPm, hregs⟩ | hpan⟩ := hstage R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_m, hmf, Entails.trans hPm (hent sf), hregs⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem SepWPp.ret_sepWPp_frame' {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop} {Q : State →
      SepProp → Prop} (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => (P_m ⊢ P_stage_post sf) ∧ Q_regs sf) (PanicOomProp s0))
    (hP : P = P_stage ∗ F) (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running → Q_regs sf →
      Q sf (P_stage_post sf ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  SepWPp.bind_sepWPp_frame' hstage hP fun sf hpc hrun hregs => SepWPp.done hpc hrun (hret sf hpc
    hrun hregs)

theorem keyPair64UnalignedAt_eq_of_parts (a : BitVec 64) (pk sk : List (BitVec 8))
    (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) (h_pk_words : ∀ a : BitVec 64,
      (a ↦ₛ pk) = (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3))
    (h_sk_words : ∀ a : BitVec 64, (a ↦ₛ sk) = (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u5) ∗
      ((a + 16#64) ↦₆₄ u6) ∗ ((a + 24#64) ↦₆₄ u7))
    (h_part1 : ∀ a : BitVec 64, bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
      ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
          bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6)
    (h_part2 : ∀ a : BitVec 64, bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
      ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
        (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u5) ∗ ((a + 16#64) ↦₆₄ u6) ∗ ((a + 24#64) ↦₆₄ u7)) :
    keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 =
      (a ↦ₛ pk) ∗ ((a + 32#64) ↦ₛ sk) := by
  symm
  unfold keyPair64UnalignedAt
  have hp1 := h_part1 a; have hp2 := h_part2 (a + 32#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2
  rw [h_pk_words a, h_sk_words (a + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [← hp2]
  have hassoc1 :
      (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
        (bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6 ∗
       ((a + 39#64) ↦₆₄ w4) ∗ ((a + 47#64) ↦₆₄ w5) ∗ ((a + 55#64) ↦₆₄ w6) ∗ ((a + 63#64) ↦₈ b63)) =
      ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
        bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) ∗
      (((a + 39#64) ↦₆₄ w4) ∗ ((a + 47#64) ↦₆₄ w5) ∗ ((a + 55#64) ↦₆₄ w6) ∗
        ((a + 63#64) ↦₈ b63)) := by ac_rfl
  rw [hassoc1, ← hp1]
  ac_rfl

theorem memRegion64_entails_exists_keyPair64UnalignedAt (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ b4 : BitVec 8,
        ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8, ∃∗ b63 : BitVec 8,
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
  have hcells : memRegion a 64 = cells a 8 :=
    ProofLib.memRegion_cells a 8 (by decide)
  rw [hcells]
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim
    fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u6
      => Entails.sepExists_elim fun u7 => ?_
  rw [words8_eq_keyPair64UnalignedAt a u0 u1 u2 u3 u4 u5 u6 u7]
  refine Entails.sepExists_right (u0.extractLsb' 0 8)
    (Entails.sepExists_right (u0.extractLsb' 8 8) (Entails.sepExists_right (u0.extractLsb' 16 8)
    (Entails.sepExists_right (u0.extractLsb' 24 8) (Entails.sepExists_right (u0.extractLsb' 32 8)
    (Entails.sepExists_right (u0.extractLsb' 40 8) (Entails.sepExists_right (u0.extractLsb' 48 8)
    (Entails.sepExists_right (u7.extractLsb' 56 8) (Entails.sepExists_right _
      (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.refl _)))))))))))))))

theorem memRegion64_4b1_entails_exists_opkBytes (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x4b1#64) 64 ⊢
      ∃∗ opkPkBytes : List (BitVec 8), ∃∗ opkSkBytes : List (BitVec 8),
        ⌜opkPkBytes.length = 32 ∧ opkSkBytes.length = 32⌝ ∗
          ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) := by
  rw [ProofLib.memRegion_cells (coroPtr + 0x4b1#64) 8 (by decide)]
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim
    fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u6
      => Entails.sepExists_elim fun u7 => ?_
  let pk := unpack64 u0 ++ unpack64 u1 ++ unpack64 u2 ++ unpack64 u3
  let sk := unpack64 u4 ++ unpack64 u5 ++ unpack64 u6 ++ unpack64 u7
  have hpk_len : pk.length = 32 := by
    dsimp only [pk]; simp only [List.length_append, unpack64_length]
  have hsk_len : sk.length = 32 := by
    dsimp only [sk]; simp only [List.length_append, unpack64_length]
  have hpk_pts := pointsToBytes_of_eq_unpack64_4 (bs := pk) rfl (coroPtr + 0x4b1#64)
  have hsk_pts := pointsToBytes_of_eq_unpack64_4 (bs := sk) rfl (coroPtr + 0x4d1#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hpk_pts hsk_pts
  refine Entails.sepExists_right pk (Entails.sepExists_right sk ?_)
  refine Entails.pure_right ⟨hpk_len, hsk_len⟩ ?_
  rw [hpk_pts, hsk_pts]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Clean Substage Wrappers (`stageP2_sub2_clean_ok`, `stageP2_sub4_none_clean_ok`,
  `stageP2_sub4_some_clean_ok`) -/

theorem memRegion_88_split_9_79 (a : BitVec 64) :
    memRegion a 88 = memRegion a 9 ∗ memRegion (a + 9#64) 79 := by
  rw [show (88 : Nat) = 9 + 79 from rfl, memRegion_split a 9 79 (by decide)]

theorem cells_2_eq_pair (a : BitVec 64) :
    cells a 2 = ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]

theorem cells_4_eq_quad (a : BitVec 64) :
    cells a 4 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]

/-! ## 3. Combined Substage P2.1–P2.3 (`stageP2_sub1_to_3_ok`, `+0x0868#64 -> +0x0d5c#64`) -/

theorem pointsToBytes_split_head_of_pos (a : BitVec 64) (bs : List (BitVec 8))
    (h : 0 < bs.length) :
    (a ↦ₛ bs) = (a ↦₈ bs.getD 0 0#8) ∗ ((a + 1#64) ↦ₛ bs.drop 1) := by
  cases bs with
  | nil => simp at h
  | cons b0 rest => exact pointsToBytes_cons a b0 rest

theorem memRegion_344_split_88_256 (a : BitVec 64) :
    memRegion a 344 = memRegion a 88 ∗ memRegion (a + 88#64) 256 := by
  rw [show (344 : Nat) = 88 + 256 from rfl, memRegion_split a 88 256 (by decide)]

theorem memRegion_56_split_7_49 (a : BitVec 64) :
    memRegion a 56 = memRegion a 7 ∗ memRegion (a + 7#64) 49 := by
  rw [show (56 : Nat) = 7 + 49 from rfl, memRegion_split a 7 49 (by decide)]

theorem cells_8_eq_memRegion_56_8 (a : BitVec 64) :
    cells a 8 = memRegion a 56 ∗ memRegion (a + 56#64) 8 := by
  rw [← ProofLib.memRegion_cells a 8 (by decide), show 8 * 8 = 56 + 8 from rfl,
    memRegion_split a 56 8 (by decide)]

theorem memRegion_65_eq_cells_8_1 (a : BitVec 64) :
    memRegion a 65 = cells a 8 ∗ memRegion (a + 64#64) 1 := by
  rw [show (65 : Nat) = 64 + 1 from rfl, memRegion_split a 64 1 (by decide),
    ProofLib.memRegion_cells a 8 (by decide)]

theorem pair_entails_cells_2 (a u0 u1 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ⊢ cells a 2 := by
  rw [cells_2_eq_pair a]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.refl _))

def opkIdIsSomeWord (opkBSk? : Option Bytes) : BitVec 32 :=
  match opkBSk? with
  | none => 0#32
  | some _ => 1#32

theorem memRegion_288_split_65_223 (a : BitVec 64) :
    memRegion a 288 = memRegion a 65 ∗ memRegion (a + 65#64) 223 := by
  rw [show (288 : Nat) = 65 + 223 from rfl, memRegion_split a 65 223 (by decide)]

theorem memRegion_65_eq_cells_6_17 (a : BitVec 64) :
    memRegion a 65 = cells a 6 ∗ memRegion (a + 48#64) 17 := by
  rw [show (65 : Nat) = 48 + 17 from rfl, memRegion_split a 48 17 (by decide),
    show (48 : Nat) = 6 * 8 from rfl, ProofLib.memRegion_cells a 6 (by decide)]

theorem memRegion_7_1_eq_pointsTo64 (a : BitVec 64) :
    memRegion a 7 ∗ memRegion (a + 7#64) 1 = (∃∗ u : BitVec 64, a ↦₆₄ u) := by
  rw [← memRegion_split a 7 1 (by decide), show 7 + 1 = 1 * 8 from rfl,
    ProofLib.memRegion_cells a 1 (by decide)]
  simp only [cells, Nat.add_zero, sepConj_emp]

theorem pointsToBytes_1568_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 1568) :
    (a ↦ₛ bs) ⊢ memRegion a 1568 := by
  rw [← h]; exact pointsToBytes_entails_memRegion a bs

theorem SepWPp.ret_sepWPp_frame_err {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_err : BitVec 64 → SepProp} {Q_regs : State → Prop} {Q : State →
      SepProp → Prop} (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => (∃ errTag : BitVec 64, errTag ≠ 0xfffffffffffffffe#64 ∧
        (P_m ⊢ P_err errTag)) ∧ Q_regs sf)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F) (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running → Q_regs sf →
      ∀ errTag : BitVec 64, errTag ≠ 0xfffffffffffffffe#64 → Q sf (P_err errTag ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_m, hmm, ⟨errTag, hne, hent⟩, hregs⟩ | ⟨hpan, P_m, hmm,
    hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sf.mem ⊨ (P_err errTag ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_err errTag ∗
      F, hmm', hret sf hpc hrun hregs errTag hne⟩⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem memRegion_65_a90_eq (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 65 =
      cells (sp + 2704#64) 8 ∗ memRegion (sp + 2768#64) 1 := by
  rw [show (2704#64 : BitVec 64) = 0xa90#64 from rfl,
    show sp + 2768#64 = (sp + 0xa90#64) + 0x40#64 by bv_omega]
  exact memRegion_65_eq_cells_8_1 (sp + 0xa90#64)

theorem memRegion_a90_65_ad1_223_eq (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 65 ∗ memRegion (sp + 0xad1#64) 223 =
      memRegion (sp + 0xa90#64) 288 := by
  rw [show sp + 0xad1#64 = (sp + 0xa90#64) + 65#64 by bv_omega]
  exact (memRegion_288_split_65_223 (sp + 0xa90#64)).symm

theorem cells_2_4f8_eq (coroPtr : BitVec 64) :
    cells (coroPtr + 0x4f8#64) 2 =
      (∃∗ u_4f8 : BitVec 64, ∃∗ u_500 : BitVec 64, ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
        ((coroPtr + 0x500#64) ↦₆₄ u_500)) := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]

theorem processPrekeyActive10At_eq (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr preKeyVt kyberStorePtr kyberVt : BitVec 64) :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr preKeyVt kyberStorePtr kyberVt =
    ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ idVt) ∗
    ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
    ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberVt) ∗
    ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ preKeyVt) ∗
    ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) := by
  unfold processPrekeyActive10At; ac_rfl

theorem memRegion_3b0_7_1_eq (sp : BitVec 64) :
    memRegion (sp + 0x3b0#64) 7 ∗ memRegion (sp + 0x3b7#64) 1 =
      ∃∗ u_3b0 : BitVec 64, (sp + 0x3b0#64) ↦₆₄ u_3b0 := by
  rw [show sp + 0x3b7#64 = (sp + 0x3b0#64) + 7#64 by bv_omega]
  exact memRegion_7_1_eq_pointsTo64 (sp + 0x3b0#64)

theorem memRegion_3c8_7_1_eq (sp : BitVec 64) :
    memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3cf#64) 1 =
      ∃∗ u_3c8 : BitVec 64, (sp + 0x3c8#64) ↦₆₄ u_3c8 := by
  rw [show sp + 0x3cf#64 = (sp + 0x3c8#64) + 7#64 by bv_omega]
  exact memRegion_7_1_eq_pointsTo64 (sp + 0x3c8#64)

set_option allowUnsafeReducibility true in
attribute [local irreducible]
  futVtableAtP spkRecordSrcAt sessionRecordEmptyHeaderAt
  opkOptFieldAt opkUnusedFieldAt bobParamsFieldsAt inMemId16BoxAt decryptPrekeySavedRegsAt

end CryptoVerification.E2E.Pqxdh.ResponderClosure
