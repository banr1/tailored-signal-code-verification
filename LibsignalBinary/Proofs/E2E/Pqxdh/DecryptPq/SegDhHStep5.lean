/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHEvict
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHPack
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHStep12
import ProofLib.SepLogic.WPp

/-!
# Sender-Chain Commit and `S4State` Staging Helpers for `S3CommitSpec`

Byte-packing, `memRegion` elimination, `vecAt` alignment, and `ReachesOrPanic` monotonicity lemmas
for committing `sender_chain` and staging `S4State` at the end of `S3CommitSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace BS10

abbrev packLE64 := pack64
abbrev packLE32 := pack32

abbrev sckWord0 (ck : ChainKey) : BitVec 64 := pack64 ((chainKeyBytes ck).take 8)
abbrev sckWord8 (ck : ChainKey) : BitVec 64 := pack64 (((chainKeyBytes ck).drop 8).take 8)
abbrev sckWord16 (ck : ChainKey) : BitVec 32 := pack32 (((chainKeyBytes ck).drop 16).take 4)
abbrev sckWord20 (ck : ChainKey) : BitVec 64 := pack64 (((chainKeyBytes ck).drop 20).take 8)
abbrev sckWord28 (ck : ChainKey) : BitVec 64 := pack64 ((chainKeyBytes ck).drop 28)

theorem pointsToBytes_len4_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 4) : (a ↦ₛ bs) = (a ↦₃₂ pack32 bs) :=
  pointsToBytes_4_eq_pointsTo32 a h

theorem pointsToBytes_len16_to_cells (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 (bs.take 8)) ∗ ((a + 8#64) ↦₆₄ pack64 (bs.drop 8)) :=
  pointsToBytes_16_eq_pointsTo64 a h

theorem pointsToBytes_len32_to_cells (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ pack64 (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ pack64 (bs.drop 24)) :=
  pointsToBytes_32_eq_pointsTo64 a h

theorem elim_memRegion_64 {m : Memory} {base : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion base 64 ∗ R) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64,
      m ⊨ (((base ↦₆₄ v0) ∗
            ((base + 8#64) ↦₆₄ v1) ∗
            ((base + 16#64) ↦₆₄ v2) ∗
            ((base + 24#64) ↦₆₄ v3) ∗
            ((base + 32#64) ↦₆₄ v4) ∗
            ((base + 40#64) ↦₆₄ v5) ∗
            ((base + 48#64) ↦₆₄ v6) ∗
            ((base + 56#64) ↦₆₄ v7)) ∗ R) := by
  have h1 := memRegion_split base 32 32 (by decide)
  rw [show (32 + 32 : Nat) = 64 from rfl] at h1
  rw [h1, sepConj_assoc] at h
  obtain ⟨v0, v1, v2, v3, h⟩ := elim_memRegion_32 h
  have h' : m ⊨ memRegion (base + 32#64) 32 ∗
      (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗
        ((base + 24#64) ↦₆₄ v3)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v4, v5, v6, v7, h'⟩ := elim_memRegion_32 h'
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, ?_⟩
  rw [show base + 32#64 + 8#64 = base + 40#64 from add_assoc_const _ _ _ _,
      show base + 32#64 + 16#64 = base + 48#64 from add_assoc_const _ _ _ _,
      show base + 32#64 + 24#64 = base + 56#64 from add_assoc_const _ _ _ _] at h'
  refine Satisfies.mono (Entails.of_eq ?_) h'
  ac_rfl

theorem elim_memRegion_80 {m : Memory} {base : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion base 80 ∗ R) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64,
      m ⊨ (((base ↦₆₄ v0) ∗
            ((base + 8#64) ↦₆₄ v1) ∗
            ((base + 16#64) ↦₆₄ v2) ∗
            ((base + 24#64) ↦₆₄ v3) ∗
            ((base + 32#64) ↦₆₄ v4) ∗
            ((base + 40#64) ↦₆₄ v5) ∗
            ((base + 48#64) ↦₆₄ v6) ∗
            ((base + 56#64) ↦₆₄ v7) ∗
            ((base + 64#64) ↦₆₄ v8) ∗
            ((base + 72#64) ↦₆₄ v9)) ∗ R) := by
  have h1 := memRegion_split base 64 16 (by decide)
  rw [show (64 + 16 : Nat) = 80 from rfl] at h1
  rw [h1, sepConj_assoc] at h
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, h⟩ := elim_memRegion_64 h
  have h' : m ⊨ memRegion (base + 64#64) 16 ∗
      (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗
        ((base + 24#64) ↦₆₄ v3) ∗ ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗
        ((base + 48#64) ↦₆₄ v6) ∗ ((base + 56#64) ↦₆₄ v7)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v8, v9, h'⟩ := elim_memRegion_16 h'
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, ?_⟩
  rw [show base + 64#64 + 8#64 = base + 72#64 from add_assoc_const _ _ _ _] at h'
  refine Satisfies.mono (Entails.of_eq ?_) h'
  ac_rfl

theorem elim_memRegion_20 {m : Memory} {base : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion base 20 ∗ R) :
    ∃ (v0 v1 : BitVec 64) (v2 : BitVec 32),
      m ⊨ (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₃₂ v2)) ∗ R) := by
  have h1 := memRegion_split base 16 4 (by decide)
  rw [show (16 + 4 : Nat) = 20 from rfl] at h1
  rw [h1, sepConj_assoc] at h
  obtain ⟨v0, v1, h⟩ := elim_memRegion_16 h
  have h' : m ⊨ memRegion (base + 16#64) 4 ∗ (((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v2, h'⟩ := elim_memRegion_4 h'
  refine ⟨v0, v1, v2, ?_⟩
  refine Satisfies.mono (Entails.of_eq ?_) h'
  ac_rfl

theorem pointsTo64_2_entails_memRegion (base : BitVec 64) (v0 v1 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1)) ⊢ memRegion base 16 := by
  have h := memRegion_split base 8 8 (by decide)
  rw [show (8 + 8 : Nat) = 16 from rfl] at h
  rw [h]
  exact sepConj_mono (pointsTo64_entails_memRegion base v0)
    (pointsTo64_entails_memRegion (base + 8#64) v1)

theorem pointsTo64_4_entails_memRegion (base : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3)) ⊢
      memRegion base 32 := by
  have h := memRegion_split base 16 16 (by decide)
  rw [show (16 + 16 : Nat) = 32 from rfl] at h
  have h01 := pointsTo64_2_entails_memRegion base v0 v1
  have h23 := pointsTo64_2_entails_memRegion (base + 16#64) v2 v3
  rw [show base + 16#64 + 8#64 = base + 24#64 from add_assoc_const _ _ _ _] at h23
  refine Entails.trans (Entails.of_eq ?_) (Entails.trans (sepConj_mono h01 h23) (Entails.of_eq
      h.symm))
  ac_rfl

theorem pointsTo64_10_entails_memRegion (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗ ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
     ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗ ((base + 48#64) ↦₆₄ v6) ∗
     ((base + 56#64) ↦₆₄ v7) ∗ ((base + 64#64) ↦₆₄ v8) ∗ ((base + 72#64) ↦₆₄ v9)) ⊢
      memRegion base 80 := by
  have h := memRegion_split base 32 48 (by decide)
  rw [show (32 + 48 : Nat) = 80 from rfl] at h
  have h2 := memRegion_split (base + 32#64) 32 16 (by decide)
  rw [show (32 + 16 : Nat) = 48 from rfl,
      show base + 32#64 + 32#64 = base + 64#64 from add_assoc_const _ _ _ _] at h2
  have h03 := pointsTo64_4_entails_memRegion base v0 v1 v2 v3
  have h47 := pointsTo64_4_entails_memRegion (base + 32#64) v4 v5 v6 v7
  rw [show base + 32#64 + 8#64 = base + 40#64 from add_assoc_const _ _ _ _,
      show base + 32#64 + 16#64 = base + 48#64 from add_assoc_const _ _ _ _,
      show base + 32#64 + 24#64 = base + 56#64 from add_assoc_const _ _ _ _] at h47
  have h89 := pointsTo64_2_entails_memRegion (base + 64#64) v8 v9
  rw [show base + 64#64 + 8#64 = base + 72#64 from add_assoc_const _ _ _ _] at h89
  have h49 :
      (((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗ ((base + 48#64) ↦₆₄ v6) ∗
       ((base + 56#64) ↦₆₄ v7)) ∗ (((base + 64#64) ↦₆₄ v8) ∗ ((base + 72#64) ↦₆₄ v9)) ⊢
      memRegion (base + 32#64) 48 :=
    Entails.trans (sepConj_mono h47 h89) (Entails.of_eq h2.symm)
  refine Entails.trans (Entails.of_eq ?_) (Entails.trans (sepConj_mono h03 h49) (Entails.of_eq
      h.symm))
  ac_rfl

theorem pointsToBytes_rck_take20 (base : BitVec 64) (ck : ChainKey) :
    (((base ↦ₛ (chainKeyBytes ck).take 16) ∗
      ((base + 16#64) ↦ₛ ((chainKeyBytes ck).drop 16).take 4)) =
     (base ↦ₛ (chainKeyBytes ck).take 20)) :=
  (pointsToBytes_chainKey_take20 base ck).symm

theorem zip_map_fst_snd {α β : Type} (xs : List (α × β)) :
    (xs.map Prod.fst).zip (xs.map Prod.snd) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, b⟩
    simp [ih]

abbrev evictGcs (gcs : List (ChainGhost × ReceiverChain)) :
    List (ChainGhost × ReceiverChain) :=
  evictList gcs

theorem map_snd_evictGcs (gcs : List (ChainGhost × ReceiverChain)) :
    (evictGcs gcs).map Prod.snd = RatchetState.evictReceiverChains (gcs.map Prod.snd) := by
  simp [evictGcs, evictList, RatchetState.evictReceiverChains]

theorem map_snd_zip_append (gs : List ChainGhost) (cs : List ReceiverChain)
    (g : ChainGhost) (c : ReceiverChain) (h : gs.length = cs.length) :
    (gs.zip cs ++ [(g, c)]).map Prod.snd = cs ++ [c] := by
  rw [List.map_append, List.map_snd_zip (by omega)]
  rfl

theorem vecAt_chains_eq (A : RustAlloc) (sp cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    vecAt A 104 8 (chainAt A) (sp + 0x38#64) cap ptr gcs =
      ((sp + 0x38#64) ↦₆₄ cap) ∗
      ((sp + 0x40#64) ↦₆₄ ptr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
      vecBuf A 104 8 (chainAt A) cap ptr gcs := by
  unfold vecAt vecHeader
  rw [show sp + 0x38#64 + 8#64 = sp + 0x40#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 16#64 = sp + 0x48#64 from add_assoc_const _ _ _ _]
  ac_rfl

theorem reachesOrPanic_mono {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ sf, s.mem.KeepsFrozen sf.mem → sf.symtab = s.symtab → P sf → Q sf) :
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q :=
  ReachesOrPanic.seq h1 (fun sf hkf hsym hP => ReachesOrPanic.done (h2 sf hkf hsym hP))

end BS10

open BS10

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
