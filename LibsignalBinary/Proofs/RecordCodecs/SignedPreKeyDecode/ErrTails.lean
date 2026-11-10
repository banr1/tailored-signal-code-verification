/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::decode` SIMD Packing and Shared Error Exits

128-bit SIMD lane extraction helpers and shared loop-exit stubs (`+392`, `+372`, `+608`, `+648` →
`+656`) for `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` (Block `562`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## SIMD 128-bit lane extraction & memory packing helpers -/

@[arm64_norm] theorem spk_extractLsb_lo_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[arm64_norm] theorem spk_extractLsb_hi_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem spk_vecU8Buf_zero_elim (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  have hle := h.1
  have hbs : bs = [] := by simp at hle; exact hle
  subst hbs
  exact Entails.refl _

theorem spk_emp_entails_three_vecU8Buf_zero (A : RustAlloc) :
    emp ⊢ vecU8Buf A 0#64 1#64 [] ∗ vecU8Buf A 0#64 1#64 [] ∗ vecU8Buf A 0#64 1#64 [] := by
  have hz : emp ⊢ vecU8Buf A 0#64 1#64 [] := by
    unfold vecU8Buf
    rw [pure_true_emp ⟨by decide, by decide, by decide⟩, emp_sepConj]
    exact Entails.refl _
  have hz2 : emp ⊢ vecU8Buf A 0#64 1#64 [] ∗ vecU8Buf A 0#64 1#64 [] := by
    rw [← emp_sepConj emp]; exact sepConj_mono hz hz
  rw [← emp_sepConj emp]
  exact sepConj_mono hz hz2

theorem spkSpAligned_sub224 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

theorem spkFrame64_pack (sp' : BitVec 64) (s0 : State) :
    spkCalleeSavedAt sp' s0 ⊢ memRegion (sp' + 160#64) 64 := by
  unfold spkCalleeSavedAt
  rw [ProofLib.memRegion_split (sp' + 160#64) 8 56 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))))

theorem spkCfg_subStack_lt (cfg : SpkCfg) : cfg.subStack < 2 ^ 64 := by
  have := cfg.h_total_lt; dsimp [SpkCfg.subStack]; omega

theorem spkCfg_subStack_le (cfg : SpkCfg) : cfg.subStack ≤ 2 ^ 64 := by
  have := spkCfg_subStack_lt cfg; omega

theorem spkCfg_total_lt (cfg : SpkCfg) : 224 + cfg.subStack < 2 ^ 64 :=
  cfg.h_total_lt

theorem spkCfg_total_le (cfg : SpkCfg) : 224 + cfg.subStack ≤ 2 ^ 64 := by
  have := spkCfg_total_lt cfg; omega

theorem spkCfg_split_err (cfg : SpkCfg) : (cfg.subStack - cfg.errStk) + cfg.errStk = cfg.subStack := by
  have := cfg.h_err; dsimp [SpkCfg.subStack]; omega

theorem spkCfg_split_dealloc (cfg : SpkCfg) :
    (cfg.subStack - cfg.deallocStk) + cfg.deallocStk = cfg.subStack := by
  have := cfg.h_dealloc; dsimp [SpkCfg.subStack]; omega

theorem spkCfg_split_varint (cfg : SpkCfg) :
    (cfg.subStack - cfg.varintStk) + cfg.varintStk = cfg.subStack := by
  have := cfg.h_varint; dsimp [SpkCfg.subStack]; omega

theorem spkCfg_split_merge (cfg : SpkCfg) :
    (cfg.subStack - cfg.mergeStk) + cfg.mergeStk = cfg.subStack := by
  have := cfg.h_merge; dsimp [SpkCfg.subStack]; omega

theorem spkStack_split (cfg : SpkCfg) (sp : BitVec 64) :
    stackAt sp (224 + cfg.subStack) =
      stackAt (sp - 224#64) cfg.subStack ∗
        memRegion (sp - 224#64) 160 ∗
        memRegion (sp - 224#64 + 160#64) 64 := by
  have htot : 224 + cfg.subStack < 2 ^ 64 := spkCfg_total_lt cfg
  have hsub_lt : cfg.subStack < 2 ^ 64 := spkCfg_subStack_lt cfg
  have h1 := stackAt_sub_split sp 224 (224 + cfg.subStack) (by omega) (spkCfg_total_le cfg)
  have h2 : memRegion (sp - BitVec.ofNat 64 (224 + cfg.subStack)) ((224 + cfg.subStack) - 224) =
      stackAt (sp - 224#64) cfg.subStack := by
    unfold stackAt
    have hsub : (224 + cfg.subStack) - 224 = cfg.subStack := by omega
    have ha : sp - BitVec.ofNat 64 (224 + cfg.subStack) =
        sp - 224#64 - BitVec.ofNat 64 cfg.subStack := by
      have hb : BitVec.ofNat 64 (224 + cfg.subStack) = 224#64 + BitVec.ofNat 64 cfg.subStack := by
        apply BitVec.eq_of_toNat_eq
        simp [Nat.mod_eq_of_lt htot, Nat.mod_eq_of_lt hsub_lt]
      rw [hb]
      bv_omega
    rw [hsub, ha]
  have h3 : stackAt sp 224 =
      memRegion (sp - 224#64) 160 ∗ memRegion (sp - 224#64 + 160#64) 64 := by
    unfold stackAt
    exact ProofLib.memRegion_split (sp - 224#64) 160 64 (by decide)
  rw [h1, h2, h3]

theorem spkMemRegion160_pack (sp' : BitVec 64) :
    memRegion sp' 16 ∗ memRegion (sp' + 16#64) 88 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ⊢
      memRegion sp' 160 := by
  rw [show (160 : Nat) = 16 + (88 + (8 + 48)) by decide,
    ProofLib.memRegion_split sp' 16 144 (by decide),
    ProofLib.memRegion_split (sp' + 16#64) 88 56 (by decide),
    ProofLib.memRegion_split (sp' + 16#64 + 88#64) 8 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) sp')))

theorem spkStack_unsplit (cfg : SpkCfg) (sp : BitVec 64) (s0 : State) :
    memRegion (sp - 224#64) 16 ∗
      memRegion (sp - 224#64 + 16#64) 88 ∗
      ((sp - 224#64 + 104#64) ↦₆₄ (sp - 224#64)) ∗
      memRegion (sp - 224#64 + 112#64) 48 ∗
      spkCalleeSavedAt (sp - 224#64) s0 ∗
      stackAt (sp - 224#64) cfg.subStack ⊢
      stackAt sp (224 + cfg.subStack) := by
  rw [spkStack_split cfg sp]
  have h160 := spkMemRegion160_pack (sp - 224#64)
  have h64 := spkFrame64_pack (sp - 224#64) s0
  have h160' :
      memRegion (sp - 224#64) 16 ∗
        (memRegion (sp - 224#64 + 16#64) 88 ∗
          (((sp - 224#64 + 104#64) ↦₆₄ (sp - 224#64)) ∗
            memRegion (sp - 224#64 + 112#64) 48)) ⊢
      memRegion (sp - 224#64) 160 := by
    simpa [sepConj_assoc] using h160
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono h160' h64))
  apply entails_of_eq; ac_rfl

theorem spkStruct88_pack (sp' pubCap pubPtr pubLen privCap privPtr privLen sigCap sigPtr sigLen ts : BitVec 64)
    (idVal padVal : BitVec 32) :
    vecHeader (sp' + 16#64) pubCap pubPtr pubLen ∗
      vecHeader (sp' + 40#64) privCap privPtr privLen ∗
      vecHeader (sp' + 64#64) sigCap sigPtr sigLen ∗
      ((sp' + 88#64) ↦₆₄ ts) ∗
      ((sp' + 96#64) ↦₃₂ idVal) ∗ ((sp' + 100#64) ↦₃₂ padVal) ⊢
      memRegion (sp' + 16#64) 88 := by
  have hp8 : ((sp' + 96#64) ↦₃₂ idVal) ∗ ((sp' + 100#64) ↦₃₂ padVal) ⊢
      memRegion (sp' + 96#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_pair_entails_memRegion8 (sp' + 96#64) idVal padVal
  rw [show (88 : Nat) = 24 + (24 + (24 + (8 + 8))) by decide,
    ProofLib.memRegion_split (sp' + 16#64) 24 64 (by decide),
    ProofLib.memRegion_split (sp' + 16#64 + 24#64) 24 40 (by decide),
    ProofLib.memRegion_split (sp' + 16#64 + 24#64 + 24#64) 24 16 (by decide),
    ProofLib.memRegion_split (sp' + 16#64 + 24#64 + 24#64 + 24#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (vecHeader_entails_memRegion24 (sp' + 16#64) pubCap pubPtr pubLen)
    (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 40#64) privCap privPtr privLen)
      (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 64#64) sigCap sigPtr sigLen)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 88#64) ts) hp8)))

theorem spkMemRegion88_err_unpack (a : BitVec 64) :
    memRegion a 88 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ memRegion (a + 16#64) 72 := by
  rw [ProofLib.memRegion_split a 8 80 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 72 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r1 => Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  exact Entails.refl _

theorem spkMemRegion88_unpack (a : BitVec 64) :
    memRegion a 88 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
      ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64, ∃∗ r7 : BitVec 64,
      ∃∗ r8 : BitVec 64, ∃∗ r9 : BitVec 64, ∃∗ r10 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗
        ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₆₄ r4) ∗ ((a + 40#64) ↦₆₄ r5) ∗
        ((a + 48#64) ↦₆₄ r6) ∗ ((a + 56#64) ↦₆₄ r7) ∗ ((a + 64#64) ↦₆₄ r8) ∗
        ((a + 72#64) ↦₆₄ r9) ∗ ((a + 80#64) ↦₆₄ r10) := by
  rw [ProofLib.memRegion_split a 8 80 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 72 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 64 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r10 => Entails.sepExists_elim fun r9 =>
    Entails.sepExists_elim fun r8 => Entails.sepExists_elim fun r7 =>
    Entails.sepExists_elim fun r6 => Entails.sepExists_elim fun r5 =>
    Entails.sepExists_elim fun r4 => Entails.sepExists_elim fun r3 =>
    Entails.sepExists_elim fun r2 => Entails.sepExists_elim fun r1 =>
    Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  refine Entails.trans ?_ (Entails.sepExists_intro r2)
  refine Entails.trans ?_ (Entails.sepExists_intro r3)
  refine Entails.trans ?_ (Entails.sepExists_intro r4)
  refine Entails.trans ?_ (Entails.sepExists_intro r5)
  refine Entails.trans ?_ (Entails.sepExists_intro r6)
  refine Entails.trans ?_ (Entails.sepExists_intro r7)
  refine Entails.trans ?_ (Entails.sepExists_intro r8)
  refine Entails.trans ?_ (Entails.sepExists_intro r9)
  refine Entails.trans ?_ (Entails.sepExists_intro r10)
  exact Entails.refl _

theorem spkErr88_intro (A : RustAlloc) (x19 err : BitVec 64)
    {out : Option SignedPreKeyRecordStructure} (herr : out = none) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ err) ∗ decodeErrorAt A err ∗
      memRegion (x19 + 16#64) 72 ⊢
      signedDecodeResultAt A x19 out := by
  rw [herr]
  dsimp only [signedDecodeResultAt]
  have hex : ((x19 + 8#64) ↦₆₄ err) ∗ decodeErrorAt A err ⊢
      ∃∗ e : BitVec 64, ((x19 + 8#64) ↦₆₄ e) ∗ decodeErrorAt A e :=
    Entails.sepExists_intro (P := fun e => ((x19 + 8#64) ↦₆₄ e) ∗ decodeErrorAt A e) err
  rw [← sepConj_assoc ((x19 + 8#64) ↦₆₄ err) (decodeErrorAt A err)]
  exact sepConj_mono_right (sepConj_mono_left hex)

theorem spkOk88_intro (A : RustAlloc) (g : SpkGhost) (x19 : BitVec 64)
    (m : SignedPreKeyRecordStructure) (pad32 : BitVec 32)
    {out : Option SignedPreKeyRecordStructure} (hok : out = some m) :
    (x19 ↦₆₄ g.pub.cap) ∗ ((x19 + 8#64) ↦₆₄ g.pub.ptr) ∗
      ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((x19 + 24#64) ↦₆₄ g.priv.cap) ∗ ((x19 + 32#64) ↦₆₄ g.priv.ptr) ∗
      ((x19 + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((x19 + 48#64) ↦₆₄ g.sig.cap) ∗ ((x19 + 56#64) ↦₆₄ g.sig.ptr) ∗
      ((x19 + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
      ((x19 + 72#64) ↦₆₄ m.timestamp) ∗
      ((x19 + 80#64) ↦₆₄ (pad32 ++ m.id)) ∗
      vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗
      vecU8Buf A g.sig.cap g.sig.ptr m.signature ⊢
      signedDecodeResultAt A x19 out := by
  rw [hok]
  dsimp only [signedDecodeResultAt, signedPreKeyStructAt]
  have hv1 := Entails.trans
    (by rw [vecU8At_eq_header_buf]; exact Entails.refl _)
    (vecU8At_entails_vecU8 A x19 g.pub.cap g.pub.ptr m.publicKey)
  have hv2 := Entails.trans
    (by rw [vecU8At_eq_header_buf]; exact Entails.refl _)
    (vecU8At_entails_vecU8 A (x19 + 0x18#64) g.priv.cap g.priv.ptr m.privateKey)
  have hv3 := Entails.trans
    (by rw [vecU8At_eq_header_buf]; exact Entails.refl _)
    (vecU8At_entails_vecU8 A (x19 + 0x30#64) g.sig.cap g.sig.ptr m.signature)
  have hp80 : ((x19 + 80#64) ↦₆₄ (pad32 ++ m.id)) ⊢
      ((x19 + 0x50#64) ↦₃₂ m.id) ∗ memRegion (x19 + 0x54#64) 4 := by
    have hs := (pointsTo32_pair (x19 + 80#64) m.id pad32).symm
    have hs' : ((x19 + 80#64) ↦₆₄ (pad32 ++ m.id)) =
        ((x19 + 0x50#64) ↦₃₂ m.id) ∗ ((x19 + 0x54#64) ↦₃₂ pad32) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using hs
    rw [hs']
    exact sepConj_mono_right (pointsTo32_entails_memRegion (x19 + 0x54#64) pad32)
  dsimp only [vecHeader] at hv1 hv2 hv3
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hv1 hv2 hv3 hp80 ⊢
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono hv3 (sepConj_mono_right hp80))))
  apply entails_of_eq; ac_rfl

theorem spkPointsTo112_memRegion40_entails_48 (sp' v : BitVec 64) :
    ((sp' + 112#64) ↦₆₄ v) ∗ memRegion (sp' + 120#64) 40 ⊢ memRegion (sp' + 112#64) 48 := by
  rw [ProofLib.memRegion_split (sp' + 112#64) 8 40 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 112#64) v)

theorem spkMemRegion48_unpack16 (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 48 ⊢
      ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64,
        ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗ memRegion (sp' + 128#64) 32 := by
  rw [ProofLib.memRegion_split (sp' + 112#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun e1 => Entails.sepExists_elim fun e0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro e0)
  refine Entails.trans ?_ (Entails.sepExists_intro e1)
  exact Entails.refl _

theorem spkErr16_pack40 (sp' e1 : BitVec 64) :
    ((sp' + 120#64) ↦₆₄ e1) ∗ memRegion (sp' + 128#64) 32 ⊢ memRegion (sp' + 120#64) 40 := by
  rw [ProofLib.memRegion_split (sp' + 120#64) 8 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 120#64) e1)

theorem spkErrBytes_pack40 (sp' : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗ memRegion (sp' + 122#64) 6 ∗
      memRegion (sp' + 128#64) 32 ⊢ memRegion (sp' + 120#64) 40 := by
  rw [show (40 : Nat) = 1 + (1 + (6 + 32)) by decide,
    ProofLib.memRegion_split (sp' + 120#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp' + 120#64 + 1#64) 1 38 (by decide),
    ProofLib.memRegion_split (sp' + 120#64 + 1#64 + 1#64) 6 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))

theorem spkMemRegion8_bytes2 (sp' : BitVec 64) :
    memRegion (sp' + 120#64) 8 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗ memRegion (sp' + 122#64) 6 := by
  rw [ProofLib.memRegion_split (sp' + 120#64) 1 7 (by decide),
    ProofLib.memRegion_split (sp' + 120#64 + 1#64) 1 6 (by decide),
    ProofLib.memRegion_one, ProofLib.memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b1 => Entails.sepExists_elim fun b0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro b0)
  refine Entails.trans ?_ (Entails.sepExists_intro b1)
  exact Entails.refl _

theorem spkMemRegion48_unpackBytes (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 48 ⊢
      ∃∗ e0 : BitVec 64, ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
          memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32 := by
  rw [ProofLib.memRegion_split (sp' + 112#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun e0 => ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (spkMemRegion8_bytes2 sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun b0 => Entails.sepExists_elim fun b1 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro e0)
  refine Entails.trans ?_ (Entails.sepExists_intro b0)
  refine Entails.trans ?_ (Entails.sepExists_intro b1)
  exact Entails.refl _

/-! ## Shared loop exits targeting `spkOff_converge` (`+656`) -/

theorem spkConvergeMem_none_intro (subStack : Nat) (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (n : ℕ) (mErr : SignedPreKeyRecordStructure) (bs : List (BitVec 8))
    {out : Option SignedPreKeyRecordStructure} (herr : out = none) (hnz : err ≠ 0#64) :
    spkStructOf A sp' mErr ∗
      decodeErrorAtStackLen A err n ∗
      memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗
      memRegion x19 88 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' subStack ⊢
      spkConvergeMemAt subStack A sp' x19 ptr bs out err := by
  rw [herr]
  dsimp only [spkConvergeMemAt]
  rw [pure_true_emp hnz, emp_sepConj]
  exact sepConj_mono (Entails.sepExists_intro mErr)
    (sepConj_mono_left (decodeErrorWith_entails_at A err n))

/-- Empty slice exit `+392..+396` → `+656` (`x1 := 0#64`). -/
theorem okEmpty_392_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (hok : out = some m)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_okEmpty)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkStructOf A sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗ memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 392 8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simpa [arm64_norm] using hregs.sp,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hF1, hsym1, by simp [htr, arm64_norm],
    by simpa [arm64_norm] using hregs.x24,
    by simpa [arm64_norm] using hregs.x19_eq,
    ⟨by simpa [arm64_norm] using hregs.saved.x25,
     by simpa [arm64_norm] using hregs.saved.x26,
     by simpa [arm64_norm] using hregs.saved.x27,
     by simpa [arm64_norm] using hregs.saved.x28⟩⟩, ?_⟩
  rw [hok]
  dsimp only [spkConvergeMemAt]
  rw [pure_true_emp (by simp [arm64_norm]), emp_sepConj]
  exact Entails.refl _

/-- Key `DecodeError::from` exit `+372..+388` → `+656` (`x1 := err ≠ 0#64`). -/
theorem fromCommon_372_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr kind e0 : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_fromCommon)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = kind)
    (hkind : KindNoHeap kind)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ e0) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := B.decodeErrorFrom
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 372 20
  dsimp only [tripleRatchetProgAtExt] at hcall hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = kind := hx8
  have hstack := stackAt_sub_split sp' cfg.errStk cfg.subStack
    (spkCfg_split_err cfg) (spkCfg_subStack_le cfg)
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
      ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (sp' + 112#64, kind) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + spkOff_fromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool ∗ stackAt sp' cfg.errStk)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind)
    (by simp [decodeErrorFromSpecWithStack, hsp_eq, h29, h8, arm64_norm])
    ⟨rfl, hkind⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simp [htr2, htr, arm64_norm],
    by simp [hx24_2, arm64_norm],
    by simp [hx19_2, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (spkConvergeMem_none_intro cfg.subStack A sp' x19 ptr (s2.readReg64 .x0) 0 mErr bs herr herr_nz)
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  ac_rfl

/-- Shared `DecodeError::push` call `+648..+652` → `+656` (`x1 := err' ≠ 0#64`). -/
theorem pushCall_648_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_pushCall)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = sp' + 112#64)
    (hnz : err ≠ 0#64)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ err) ∗ memRegion (sp' + 120#64) 40 ∗
        decodeErrorAtStackLen A err 0 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := B.decodeErrorPush
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 648 8
  dsimp only [tripleRatchetProgAtExt] at hcall hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = sp' + 112#64 := hx0
  have hstack := stackAt_sub_split sp' cfg.errStk cfg.subStack
    (spkCfg_split_err cfg) (spkCfg_subStack_le cfg)
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError>::push") -
      ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (sp' + 112#64, err, 0) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + spkOff_pushRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
      A.pool ∗ stackAt sp' cfg.errStk)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ err ≠ 0#64 ∧ (0 : Nat) < 2 ^ 32)
    (by simp [decodeErrorPushExternSpecWithStack, hsp_eq, h0, arm64_norm])
    ⟨rfl, hnz, by decide⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [decodeErrorPushExternSpecWithStack]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun err' => ?_
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  refine Wire.SepWPp.pure_pre fun herr'_nz => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simp [htr2, htr, arm64_norm],
    by simp [hx24_2, arm64_norm],
    by simp [hx19_2, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (spkConvergeMem_none_intro cfg.subStack A sp' x19 ptr err' 1 mErr bs herr herr'_nz)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkPointsTo112_memRegion40_entails_48 sp' err'))))))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  ac_rfl

/-- Shared Tag 5 `DecodeError::from` + `DecodeError::push` tail (`+608..+644` → `+648` → `+656`). -/
theorem tag5FromPush_608_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr kind : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag5FromCommon)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hkind : KindNoHeap kind)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := B.decodeErrorFrom
  have hpush := @pushCall_648_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 608 40
  dsimp only [tripleRatchetProgAtExt] at hcall hpush hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' cfg.errStk cfg.subStack
    (spkCfg_split_err cfg) (spkCfg_subStack_le cfg)
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
      ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (sp' + 112#64, kind) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + spkOff_tag5FromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool ∗ stackAt sp' cfg.errStk)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind)
    (by simp [decodeErrorFromSpecWithStack, hsp_eq, h29, arm64_norm])
    ⟨rfl, hkind⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (spkMemRegion48_unpack16 sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_pushCall) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine Wire.SepWPp.mono_pre ?_
    (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := s2.readReg64 .x0)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      ⟨by simp [hsp2_eq, arm64_norm],
       by simp [hx29_2, arm64_norm],
       by simp [hx24_2, arm64_norm],
       by simp [hx19_2, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved2.x25,
        by simpa [arm64_norm] using hsaved2.x26,
        by simpa [arm64_norm] using hsaved2.x27,
        by simpa [arm64_norm] using hsaved2.x28⟩⟩
      (by simp [hx29_2, arm64_norm]) herr_nz
      (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
      hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
  have h40 := spkErr16_pack40 sp' e1
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left h40))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
  ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Shared Loop Exits (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem okEmpty_392_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (hok : out = some m)
    (hpc : s.pc = (blkPl_562).base + spkOff_okEmpty)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (spkStructOf A sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗ memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine ⟨⟨by simpa [arm64_norm] using hregs.sp,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcrl1, by simp [htr, arm64_norm],
    by simpa [arm64_norm] using hregs.x24,
    by simpa [arm64_norm] using hregs.x19_eq,
    ⟨by simpa [arm64_norm] using hregs.saved.x25,
     by simpa [arm64_norm] using hregs.saved.x26,
     by simpa [arm64_norm] using hregs.saved.x27,
     by simpa [arm64_norm] using hregs.saved.x28⟩⟩, ?_⟩
  rw [hok]
  dsimp only [spkConvergeMem]
  rw [pure_true_emp (by simp [arm64_norm]), emp_sepConj]
  exact Entails.refl _

theorem fromCommon_372_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr kind e0 : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_fromCommon)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = kind)
    (hkind : KindNoHeap kind)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ e0) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := spk_decodeErrorFrom_placed_ok hH
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = kind := hx8
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_lscro (sp' + 112#64, kind) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_fromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind)
    (by simp [decodeErrorFromSpec, hsp_eq, h29, h8, arm64_norm])
    ⟨rfl, hkind⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorFromSpec]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine sepWPp_of_sepWP_end_lscro hcrl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcrl3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcrl3, by simp [htr2, htr, arm64_norm],
    by simp [hx24_2, arm64_norm],
    by simp [hx19_2, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (spkConvergeMem_none_intro (SpqrV1.Varint.skipField3Stack 100) A sp' x19 ptr (s2.readReg64 .x0) 0 mErr bs herr herr_nz)
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  ac_rfl

theorem pushCall_648_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_pushCall)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = sp' + 112#64)
    (hnz : err ≠ 0#64)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ err) ∗ memRegion (sp' + 120#64) 40 ∗
        decodeErrorAtStackLen A err 0 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := spk_decodeErrorPush_placed_ok hH
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = sp' + 112#64 := hx0
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 257) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_lscro (sp' + 112#64, err, 0) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_pushRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
      A.pool ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ (0 : Nat) < 2 ^ 32)
    (by simp [decodeErrorPushSpec, hsp_eq, h0, arm64_norm])
    ⟨rfl, by decide⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorPushSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine sepWPp_of_sepWP_end_lscro hcrl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcrl3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcrl3, by simp [htr2, htr, arm64_norm],
    by simp [hx24_2, arm64_norm],
    by simp [hx19_2, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (spkConvergeMem_none_intro (SpqrV1.Varint.skipField3Stack 100) A sp' x19 ptr err 1 mErr bs herr hnz)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkPointsTo112_memRegion40_entails_48 sp' err))))))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  ac_rfl

theorem tag5FromPush_608_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr kind : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5FromCommon)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hkind : KindNoHeap kind)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := spk_decodeErrorFrom_placed_ok hH
  have hpush := @pushCall_648_placed_wp _ A H hH s0
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_lscro (sp' + 112#64, kind) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_tag5FromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind)
    (by simp [decodeErrorFromSpec, hsp_eq, h29, arm64_norm])
    ⟨rfl, hkind⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorFromSpec]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (spkMemRegion48_unpack16 sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushCall) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcrl3
  refine Wire.SepWPp.mono_pre ?_
    (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := s2.readReg64 .x0)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      ⟨by simp [hsp2_eq, arm64_norm],
       by simp [hx29_2, arm64_norm],
       by simp [hx24_2, arm64_norm],
       by simp [hx19_2, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved2.x25,
        by simpa [arm64_norm] using hsaved2.x26,
        by simpa [arm64_norm] using hsaved2.x27,
        by simpa [arm64_norm] using hsaved2.x28⟩⟩
      (by simp [hx29_2, arm64_norm]) herr_nz
      (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
      hcrl3 (by simp [htr2, htr, arm64_norm]))
  have h40 := spkErr16_pack40 sp' e1
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left h40))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
  ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
