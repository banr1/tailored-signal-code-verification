/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart1
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::clone`: Optional Sub-Struct Clone Relations and `encSessionMem` Preservation
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [scoped arm64_norm, scoped wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

theorem memRegion_344_entails_scDstSlotsAt (dst : BitVec 64) :
    memRegion dst 344 ⊢ ∃∗ dv : DstVals, scDstSlotsAt dst dv := by
  have h := memRegion_344_entails_dstSlotsAt (dst - 0xca0#64)
  have h0 : dst - 0xca0#64 + 0xca0#64 = dst := by bv_omega
  have hd : ∀ dv : DstVals, dstSlotsAt (dst - 0xca0#64) dv = scDstSlotsAt dst dv := by
    intro dv
    unfold dstSlotsAt scDstSlotsAt
    have hsub : ∀ k : BitVec 64, dst - 0xca0#64 + k = dst + (k - 0xca0#64) := by
      intro k; bv_omega
    simp only [h0, hsub, BitVec.reduceSub]
  rw [h0] at h
  refine Entails.trans h ?_
  apply Entails.sepExists_elim; intro dv
  rw [hd dv]
  exact Entails.sepExists_right dv (Entails.refl _)

def scDstSlotsWrittenAt (dst : BitVec 64)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32)
    (sessVer prevCnt w288 w28c : BitVec 32) : SepProp :=
  (dst ↦₆₄ localIk'.cap) ∗ ((dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗ ((dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
  ((dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗ ((dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
  ((dst + 0x30#64) ↦₆₄ 32#64) ∗ ((dst + 0x38#64) ↦₆₄ rootPtr') ∗ ((dst + 0x40#64) ↦₆₄ 32#64) ∗
  ((dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((dst + 0x50#64) ↦₆₄ chainsPtr') ∗ ((dst + 0x58#64) ↦₆₄ chainsCap') ∗
  ((dst + 0x60#64) ↦₆₄ alice'.cap) ∗ ((dst + 0x68#64) ↦₆₄ alice'.ptr) ∗ ((dst + 0x70#64) ↦₆₄ alice'.cap) ∗
  ((dst + 0x78#64) ↦₆₄ pqCap') ∗ ((dst + 0x80#64) ↦₆₄ pqPtr') ∗ ((dst + 0x88#64) ↦₆₄ pqCap') ∗
  ((dst + 0x90#64) ↦₆₄ scCap') ∗
  chunks96_6QAt (dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
  ((dst + 0xf8#64) ↦₆₄ pendCap') ∗ ((dst + 0x100#64) ↦₆₄ pendPtr') ∗ ((dst + 0x108#64) ↦₆₄ pendCap') ∗
  ((dst + 0x110#64) ↦₃₂ w23) ∗ ((dst + 0x114#64) ↦₃₂ w24) ∗ ((dst + 0x118#64) ↦₆₄ v18) ∗
  ((dst + 0x120#64) ↦₃₂ v2c) ∗ memRegion (dst + 0x124#64) 4 ∗
  ((dst + 0x128#64) ↦₆₄ kybCap') ∗ ((dst + 0x130#64) ↦₆₄ kybPtr') ∗ ((dst + 0x138#64) ↦₆₄ kybCap') ∗
  ((dst + 0x140#64) ↦₃₂ v28) ∗ memRegion (dst + 0x144#64) 4 ∗
  ((dst + 0x148#64) ↦₃₂ sessVer) ∗ ((dst + 0x14c#64) ↦₃₂ prevCnt) ∗
  ((dst + 0x150#64) ↦₃₂ w288) ∗ ((dst + 0x154#64) ↦₃₂ w28c)

theorem sc_chunks96_6QAt_dst_0x98 (dst : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt (dst + 0x98#64) q0 q1 q2 q3 q4 q5 =
      ((dst + 0x98#64) ↦₁₂₈ q0) ∗ ((dst + 0xa8#64) ↦₁₂₈ q1) ∗
      ((dst + 0xb8#64) ↦₁₂₈ q2) ∗ ((dst + 0xc8#64) ↦₁₂₈ q3) ∗
      ((dst + 0xd8#64) ↦₁₂₈ q4) ∗ ((dst + 0xe8#64) ↦₁₂₈ q5) := by
  unfold chunks96_6QAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## 5. Enhanced `ScOptPendClone` / `ScOptKybClone` and `sessionStateReprAt` + `encSessionMem` Preservation -/

def ScOptPendClone (A : RustAlloc) (orig : Option TailVecGhost)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32) : SepProp :=
  match orig with
  | none => ⌜pendCap' = noneCap⌝
  | some gp =>
    ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
      ∃ tw4 : BitVec 32,
        gp.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4⌝ ∗
      vecU8Buf A pendCap' pendPtr' gp.vec.bytes

def ScOptKybClone (A : RustAlloc) (orig : Option TailVecGhost)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32) : SepProp :=
  match orig with
  | none => ⌜kybCap' = noneCap⌝
  | some gk =>
    ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
      ∃ kw1 : BitVec 32, gk.tail = unpack32 v28 ++ unpack32 kw1⌝ ∗
      vecU8Buf A kybCap' kybPtr' gk.vec.bytes

theorem PendingRel_of_tail_eq (g g' : TailVecGhost) {p}
    (hvec : g'.vec.bytes = g.vec.bytes)
    (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c tw4 w4' : BitVec 32)
    (hg : g.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4)
    (hg' : g'.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 w4')
    (hrel : PendingRel (some g) p) :
    PendingRel (some g') p := by
  cases p with
  | none => exact hrel
  | some pp =>
    dsimp only [PendingRel] at hrel ⊢
    have ht4 : g'.tail.take 4 = g.tail.take 4 := by
      rw [hg, hg']; simp [unpack32]
    have hd4 : (g'.tail.drop 4).take 4 = (g.tail.drop 4).take 4 := by
      rw [hg, hg']; simp [unpack32]
    have hd8 : (g'.tail.drop 8).take 8 = (g.tail.drop 8).take 8 := by
      rw [hg, hg']; simp [unpack32, unpack64]
    have hd16 : (g'.tail.drop 16).take 4 = (g.tail.drop 16).take 4 := by
      rw [hg, hg']; simp [unpack32, unpack64]
    have hopt : OptU32Rel g'.tail pp.preKeyId := by
      cases hpk : pp.preKeyId <;> simp only [OptU32Rel, ht4, hd4]
      · simpa [OptU32Rel, hpk] using hrel.2.1
      · simpa [OptU32Rel, hpk] using hrel.2.1
    rw [hvec, hd8, hd16]
    exact ⟨hrel.1, hopt, hrel.2.2.1, hrel.2.2.2⟩

theorem KyberRel_of_tail_eq (g g' : TailVecGhost) {k}
    (hvec : g'.vec.bytes = g.vec.bytes)
    (v28 kw1 kw1' : BitVec 32)
    (hg : g.tail = unpack32 v28 ++ unpack32 kw1)
    (hg' : g'.tail = unpack32 v28 ++ unpack32 kw1')
    (hrel : KyberRel (some g) k) :
    KyberRel (some g') k := by
  cases k with
  | none => exact hrel
  | some kk =>
    dsimp only [KyberRel] at hrel ⊢
    have ht4 : g'.tail.take 4 = g.tail.take 4 := by
      rw [hg, hg']; simp [unpack32]
    rw [hvec, ht4]
    exact hrel

theorem optTailVecAt_48_of_scOptPendClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost) (p)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32)
    (hrel : PendingRel orig p) :
    ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
      ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
      ((a + 40#64) ↦₃₂ v2c) ∗ memRegion (a + 44#64) 4 ∗
      ScOptPendClone A orig pendCap' pendPtr' w23 w24 v18 v2c) ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = orig.isSome ∧ PendingRel pend' p ∧
          encPendingFieldMem pend' p = encPendingFieldMem orig p⌝ ∗
          optTailVecAt A 48 a pend' := by
  cases orig with
  | none =>
    dsimp only [ScOptPendClone]
    rw [show ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
          ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
          ((a + 40#64) ↦₃₂ v2c) ∗ memRegion (a + 44#64) 4 ∗ ⌜pendCap' = noneCap⌝) =
        (⌜pendCap' = noneCap⌝ ∗ (a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗
          ((a + 16#64) ↦₆₄ pendCap') ∗ ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗
          ((a + 32#64) ↦₆₄ v18) ∗ ((a + 40#64) ↦₃₂ v2c) ∗ memRegion (a + 44#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    refine Entails.sepExists_right none ?_
    apply Entails.pure_right ⟨rfl, hrel, rfl⟩
    unfold optTailVecAt
    apply sepConj_mono_right
    rw [memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 24#64) (b' := a + 28#64) (n := 4) (k := 20) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 28#64) (b' := a + 32#64) (n := 4) (k := 16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 40#64) (b' := a + 44#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)
  | some gp =>
    dsimp only [ScOptPendClone]
    rw [memRegion_four (a + 44#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w4'
    rw [show ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
          ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
          ((a + 40#64) ↦₃₂ v2c) ∗ ((a + 44#64) ↦₃₂ w4') ∗
          ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
            ∃ tw4 : BitVec 32,
              gp.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4⌝ ∗
          vecU8Buf A pendCap' pendPtr' gp.vec.bytes) =
        (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
            ∃ tw4 : BitVec 32,
              gp.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4⌝ ∗
          (((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap')) ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          (((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
            ((a + 40#64) ↦₃₂ v2c) ∗ ((a + 44#64) ↦₃₂ w4'))) by ac_rfl]
    apply Entails.pure_left; rintro ⟨rfl, tw4, hgp_tail⟩
    set tail := unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 w4'
    have htail_len : tail.length = 24 := by simp [tail]
    have htail_eq :
        ((a + 24#64) ↦ₛ tail) =
          ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
          ((a + 40#64) ↦₃₂ v2c) ∗ ((a + 44#64) ↦₃₂ w4') := by
      unfold tail
      simp only [List.append_assoc, pointsToBytes_append, unpack32_length, unpack64_length,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
      have h28 : a + 24#64 + BitVec.ofNat 64 4 = a + 28#64 := by bv_arith
      have h32 : a + 28#64 + BitVec.ofNat 64 4 = a + 32#64 := by bv_arith
      have h40 : a + 32#64 + BitVec.ofNat 64 8 = a + 40#64 := by bv_arith
      have h44 : a + 40#64 + BitVec.ofNat 64 4 = a + 44#64 := by bv_arith
      rw [h28, h32, h40, h44]
    rw [← htail_eq]
    set g' : TailVecGhost := ⟨⟨BitVec.ofNat 64 gp.vec.bytes.length, pendPtr', gp.vec.bytes⟩, tail⟩
    refine Entails.sepExists_right (some g') ?_
    have hrel' : PendingRel (some g') p :=
      PendingRel_of_tail_eq gp g' rfl w23 w24 v18 v2c tw4 w4' hgp_tail rfl hrel
    have henc' : encPendingFieldMem (some g') p = encPendingFieldMem (some gp) p := by
      cases p <;> rfl
    apply Entails.pure_right ⟨rfl, hrel', henc'⟩
    unfold optTailVecAt
    apply Entails.pure_right htail_len
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

theorem optTailVecAt_32_of_scOptKybClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost) (k)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32)
    (hrel : KyberRel orig k) :
    ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
      ((a + 24#64) ↦₃₂ v28) ∗ memRegion (a + 28#64) 4 ∗
      ScOptKybClone A orig kybCap' kybPtr' v28) ⊢
      ∃∗ kyb' : Option TailVecGhost,
        ⌜KyberRel kyb' k⌝ ∗ optTailVecAt A 32 a kyb' := by
  cases orig with
  | none =>
    dsimp only [ScOptKybClone]
    rw [show ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
          ((a + 24#64) ↦₃₂ v28) ∗ memRegion (a + 28#64) 4 ∗ ⌜kybCap' = noneCap⌝) =
        (⌜kybCap' = noneCap⌝ ∗ (a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗
          ((a + 16#64) ↦₆₄ kybCap') ∗ ((a + 24#64) ↦₃₂ v28) ∗ memRegion (a + 28#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    refine Entails.sepExists_right none ?_
    apply Entails.pure_right hrel
    unfold optTailVecAt
    apply sepConj_mono_right
    rw [memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 24#64) (b' := a + 28#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)
  | some gk =>
    dsimp only [ScOptKybClone]
    rw [memRegion_four (a + 28#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro kw1'
    rw [show ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
          ((a + 24#64) ↦₃₂ v28) ∗ ((a + 28#64) ↦₃₂ kw1') ∗
          ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
            ∃ kw1 : BitVec 32, gk.tail = unpack32 v28 ++ unpack32 kw1⌝ ∗
          vecU8Buf A kybCap' kybPtr' gk.vec.bytes) =
        (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
            ∃ kw1 : BitVec 32, gk.tail = unpack32 v28 ++ unpack32 kw1⌝ ∗
          (((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap')) ∗
            vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          (((a + 24#64) ↦₃₂ v28) ∗ ((a + 28#64) ↦₃₂ kw1'))) by ac_rfl]
    apply Entails.pure_left; rintro ⟨rfl, kw1, hgk_tail⟩
    set tail := unpack32 v28 ++ unpack32 kw1'
    have htail_len : tail.length = 8 := by simp [tail]
    have htail_eq :
        ((a + 24#64) ↦ₛ tail) =
          ((a + 24#64) ↦₃₂ v28) ∗ ((a + 28#64) ↦₃₂ kw1') := by
      unfold tail
      rw [pointsToBytes_append, unpack32_length,
          ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
      have h28 : a + 24#64 + BitVec.ofNat 64 4 = a + 28#64 := by bv_arith
      rw [h28]
    rw [← htail_eq]
    set g' : TailVecGhost := ⟨⟨BitVec.ofNat 64 gk.vec.bytes.length, kybPtr', gk.vec.bytes⟩, tail⟩
    refine Entails.sepExists_right (some g') ?_
    have hrel' : KyberRel (some g') k :=
      KyberRel_of_tail_eq gk g' rfl v28 kw1 kw1' hgk_tail rfl hrel
    apply Entails.pure_right hrel'
    unfold optTailVecAt
    apply Entails.pure_right htail_len
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

theorem sc_srcSessionAt_reassemble (A : RustAlloc) (x : SessionCloneGhost)
    (w288 w28c : BitVec 32)
    (h_pend_rel : PendingRel x.G.pending x.s.pendingPreKey)
    (h_kyb_rel : KyberRel x.G.kyber x.s.pendingKyberPreKey)
    (h_alice_eq : x.G.alice.bytes = x.s.aliceBaseKey)
    (h_rem_reg : x.G.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat)
    (h_loc_reg : (x.G.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.s.state.localIdentity.publicKey)
    (h_rem_deser : match x.s.state.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_chains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (h_pend_some : x.G.pending.isSome = x.s.state.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.s.state.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c)) :
    (vecGhostAt A x.G.localIk x.src ∗
      vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
      vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
      vecAt A 104 8 (chainAt A) (x.src + 0x48#64) x.G.chainsCap x.G.chainsPtr
        (x.G.chains.zip x.s.state.receiverChains) ∗
      vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
      vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
      optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
      optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
      optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
      ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
      ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
      ((x.src + 0x150#64) ↦₃₂ w288) ∗
      ((x.src + 0x154#64) ↦₃₂ w28c)) ⊢
      sessionStateReprAt A x.src x.G x.s := by
  unfold sessionStateReprAt
  apply Entails.pure_right ⟨h_pend_rel, h_kyb_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩
  rw [sc_sessionStateAt_eq]
  apply Entails.pure_right ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  have h154 : x.src + 0x150#64 + 4#64 = x.src + 0x154#64 := by bv_arith
  rw [h_reg_pts (x.src + 0x150#64), h154]
  exact Entails.of_eq (by ac_rfl)

theorem scDstSlotsWrittenAt_entails_sessionAt
    (A : RustAlloc) (x : SessionCloneGhost)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
    (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64)
    (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32)
    (w288 w28c : BitVec 32)
    (h_pend_rel : PendingRel x.G.pending x.s.pendingPreKey)
    (h_kyb_rel : KyberRel x.G.kyber x.s.pendingKyberPreKey)
    (h_alice_eq : x.G.alice.bytes = x.s.aliceBaseKey)
    (h_rem_reg : x.G.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat)
    (h_loc_reg : (x.G.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.s.state.localIdentity.publicKey)
    (h_rem_deser : match x.s.state.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : x.G.pending.isSome = x.s.state.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.s.state.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c))
    (hloc_bytes : localIk'.bytes = x.G.localIk.bytes)
    (hloc_cap : localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hrem_bytes : remoteIk'.bytes = x.G.remoteIk.bytes)
    (hrem_cap : remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hchains_len : chains'.length = x.s.state.receiverChains.length)
    (hchains_cap : chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hchains_enc : ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
      ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)))
    (halice_bytes : alice'.bytes = x.G.alice.bytes)
    (halice_cap : alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length)
    (hpq_cap : pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length)
    (hsc_inl : OptSenderChainInline sender' x.s.state.senderChain
      (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5))
    (hsc_enc : encSenderFieldMem sender' x.s.state.senderChain =
      encSenderFieldMem x.G.sender x.s.state.senderChain) :
    (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
        pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23 w24 v18 v2c
        kybCap' kybPtr' v28 x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
      vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
      vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
      vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
      vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
      vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
      vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
      optSenderChainHeap A sender' x.s.state.senderChain ∗
      ScOptPendClone A x.G.pending pendCap' pendPtr' w23 w24 v18 v2c ∗
      ScOptKybClone A x.G.kyber kybCap' kybPtr' v28) ⊢
      ∃∗ G' : SessionGhost,
        ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s := by
  have hloc_hdr :
      (x.dst ↦₆₄ localIk'.cap) ∗ ((x.dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗
        ((x.dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes =
      vecGhostAt A localIk' x.dst := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h3 : BitVec.ofNat 64 localIk'.bytes.length = localIk'.cap := by
      rw [hloc_bytes, ← hloc_cap]
    rw [h3]; ac_rfl
  have hrem_hdr :
      ((x.dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((x.dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗
        ((x.dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
        vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes =
      vecGhostAt A remoteIk' (x.dst + 0x18#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x18#64 + 8#64 = x.dst + 0x20#64 := by bv_arith
    have h2 : x.dst + 0x18#64 + 16#64 = x.dst + 0x28#64 := by bv_arith
    have h3 : BitVec.ofNat 64 remoteIk'.bytes.length = remoteIk'.cap := by
      rw [hrem_bytes, ← hrem_cap]
    rw [h1, h2, h3]; ac_rfl
  have hroot_hdr :
      ((x.dst + 0x30#64) ↦₆₄ 32#64) ∗ ((x.dst + 0x38#64) ↦₆₄ rootPtr') ∗
        ((x.dst + 0x40#64) ↦₆₄ 32#64) ∗
        vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) =
      vecU8At A (x.dst + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x30#64 + 8#64 = x.dst + 0x38#64 := by bv_arith
    have h2 : x.dst + 0x30#64 + 16#64 = x.dst + 0x40#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (keyToBytes32 x.s.state.rootKey).length = 32#64 := by
      simp [keyToBytes32]
    rw [h1, h2, h3]; ac_rfl
  have hchains_hdr :
      ((x.dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((x.dst + 0x50#64) ↦₆₄ chainsPtr') ∗
        ((x.dst + 0x58#64) ↦₆₄ chainsCap') ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) =
      vecAt A 104 8 (chainAt A) (x.dst + 0x48#64) chainsCap' chainsPtr'
        (chains'.zip x.s.state.receiverChains) := by
    unfold vecAt vecHeader
    have h1 : x.dst + 0x48#64 + 8#64 = x.dst + 0x50#64 := by bv_arith
    have h2 : x.dst + 0x48#64 + 16#64 = x.dst + 0x58#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (chains'.zip x.s.state.receiverChains).length = chainsCap' := by
      simp [hchains_len, hchains_cap]
    rw [h1, h2, h3]; ac_rfl
  have halice_hdr :
      ((x.dst + 0x60#64) ↦₆₄ alice'.cap) ∗ ((x.dst + 0x68#64) ↦₆₄ alice'.ptr) ∗
        ((x.dst + 0x70#64) ↦₆₄ alice'.cap) ∗
        vecU8Buf A alice'.cap alice'.ptr alice'.bytes =
      vecGhostAt A alice' (x.dst + 0x60#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x60#64 + 8#64 = x.dst + 0x68#64 := by bv_arith
    have h2 : x.dst + 0x60#64 + 16#64 = x.dst + 0x70#64 := by bv_arith
    have h3 : BitVec.ofNat 64 alice'.bytes.length = alice'.cap := by
      rw [halice_bytes, ← halice_cap]
    rw [h1, h2, h3]; ac_rfl
  have hpq_hdr :
      ((x.dst + 0x78#64) ↦₆₄ pqCap') ∗ ((x.dst + 0x80#64) ↦₆₄ pqPtr') ∗
        ((x.dst + 0x88#64) ↦₆₄ pqCap') ∗
        vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState =
      vecU8At A (x.dst + 0x78#64) pqCap' pqPtr' x.s.state.pqRatchetState := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x78#64 + 8#64 = x.dst + 0x80#64 := by bv_arith
    have h2 : x.dst + 0x78#64 + 16#64 = x.dst + 0x88#64 := by bv_arith
    rw [h1, h2, ← hpq_cap]; ac_rfl
  have hsc_reasm :
      (((x.dst + 0x90#64) ↦₆₄ scCap') ∗
        chunks96_6QAt (x.dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        optSenderChainHeap A sender' x.s.state.senderChain) ⊢
      optSenderChainAt A (x.dst + 0x90#64) sender' x.s.state.senderChain := by
    have h8 : x.dst + 0x90#64 + 0x8#64 = x.dst + 0x98#64 := by bv_arith
    rw [← h8, ← sepConj_assoc, ← chunks104W6QAt_eq_word_sep_chunks96]
    exact optSenderChainAt_of_chunks104W6Q A (x.dst + 0x90#64) sender' x.s.state.senderChain hsc_inl
  have hpend_reasm :
      (((x.dst + 0xf8#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x100#64) ↦₆₄ pendPtr') ∗
        ((x.dst + 0x108#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x110#64) ↦₃₂ w23) ∗
        ((x.dst + 0x114#64) ↦₃₂ w24) ∗ ((x.dst + 0x118#64) ↦₆₄ v18) ∗
        ((x.dst + 0x120#64) ↦₃₂ v2c) ∗ memRegion (x.dst + 0x124#64) 4 ∗
        ScOptPendClone A x.G.pending pendCap' pendPtr' w23 w24 v18 v2c) ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = x.G.pending.isSome ∧ PendingRel pend' x.s.pendingPreKey ∧
          encPendingFieldMem pend' x.s.pendingPreKey = encPendingFieldMem x.G.pending x.s.pendingPreKey⌝ ∗
          optTailVecAt A 48 (x.dst + 0xf8#64) pend' := by
    have h8 : x.dst + 0xf8#64 + 8#64 = x.dst + 0x100#64 := by bv_arith
    have h16 : x.dst + 0xf8#64 + 16#64 = x.dst + 0x108#64 := by bv_arith
    have h24 : x.dst + 0xf8#64 + 24#64 = x.dst + 0x110#64 := by bv_arith
    have h28 : x.dst + 0xf8#64 + 28#64 = x.dst + 0x114#64 := by bv_arith
    have h32 : x.dst + 0xf8#64 + 32#64 = x.dst + 0x118#64 := by bv_arith
    have h40 : x.dst + 0xf8#64 + 40#64 = x.dst + 0x120#64 := by bv_arith
    have h44 : x.dst + 0xf8#64 + 44#64 = x.dst + 0x124#64 := by bv_arith
    rw [← h8, ← h16, ← h24, ← h28, ← h32, ← h40, ← h44]
    exact optTailVecAt_48_of_scOptPendClone A (x.dst + 0xf8#64) x.G.pending x.s.pendingPreKey
      pendCap' pendPtr' w23 w24 v18 v2c h_pend_rel
  have hkyb_reasm :
      (((x.dst + 0x128#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x130#64) ↦₆₄ kybPtr') ∗
        ((x.dst + 0x138#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x140#64) ↦₃₂ v28) ∗
        memRegion (x.dst + 0x144#64) 4 ∗
        ScOptKybClone A x.G.kyber kybCap' kybPtr' v28) ⊢
      ∃∗ kyb' : Option TailVecGhost,
        ⌜KyberRel kyb' x.s.pendingKyberPreKey⌝ ∗
          optTailVecAt A 32 (x.dst + 0x128#64) kyb' := by
    have h8 : x.dst + 0x128#64 + 8#64 = x.dst + 0x130#64 := by bv_arith
    have h16 : x.dst + 0x128#64 + 16#64 = x.dst + 0x138#64 := by bv_arith
    have h24 : x.dst + 0x128#64 + 24#64 = x.dst + 0x140#64 := by bv_arith
    have h28 : x.dst + 0x128#64 + 28#64 = x.dst + 0x144#64 := by bv_arith
    rw [← h8, ← h16, ← h24, ← h28]
    exact optTailVecAt_32_of_scOptKybClone A (x.dst + 0x128#64) x.G.kyber x.s.pendingKyberPreKey
      kybCap' kybPtr' v28 h_kyb_rel
  have htail_eq :
      ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦₃₂ w288) ∗ ((x.dst + 0x154#64) ↦₃₂ w28c) =
      ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦ₛ x.G.regIds) := by
    have h154 : x.dst + 0x150#64 + 4#64 = x.dst + 0x154#64 := by bv_arith
    rw [h_reg_pts (x.dst + 0x150#64), h154]
  unfold scDstSlotsWrittenAt
  refine Entails.trans
    (Q := (((x.dst + 0xf8#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x100#64) ↦₆₄ pendPtr') ∗
            ((x.dst + 0x108#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x110#64) ↦₃₂ w23) ∗
            ((x.dst + 0x114#64) ↦₃₂ w24) ∗ ((x.dst + 0x118#64) ↦₆₄ v18) ∗
            ((x.dst + 0x120#64) ↦₃₂ v2c) ∗ memRegion (x.dst + 0x124#64) 4 ∗
            ScOptPendClone A x.G.pending pendCap' pendPtr' w23 w24 v18 v2c) ∗
          (((x.dst + 0x128#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x130#64) ↦₆₄ kybPtr') ∗
            ((x.dst + 0x138#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x140#64) ↦₃₂ v28) ∗
            memRegion (x.dst + 0x144#64) 4 ∗
            ScOptKybClone A x.G.kyber kybCap' kybPtr' v28) ∗
          (((x.dst + 0x90#64) ↦₆₄ scCap') ∗
            chunks96_6QAt (x.dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            optSenderChainHeap A sender' x.s.state.senderChain) ∗
          ((x.dst ↦₆₄ localIk'.cap) ∗ ((x.dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗
            ((x.dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes) ∗
          (((x.dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((x.dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗
            ((x.dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes) ∗
          (((x.dst + 0x30#64) ↦₆₄ 32#64) ∗ ((x.dst + 0x38#64) ↦₆₄ rootPtr') ∗
            ((x.dst + 0x40#64) ↦₆₄ 32#64) ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey)) ∗
          (((x.dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((x.dst + 0x50#64) ↦₆₄ chainsPtr') ∗
            ((x.dst + 0x58#64) ↦₆₄ chainsCap') ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains)) ∗
          (((x.dst + 0x60#64) ↦₆₄ alice'.cap) ∗ ((x.dst + 0x68#64) ↦₆₄ alice'.ptr) ∗
            ((x.dst + 0x70#64) ↦₆₄ alice'.cap) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes) ∗
          (((x.dst + 0x78#64) ↦₆₄ pqCap') ∗ ((x.dst + 0x80#64) ↦₆₄ pqPtr') ∗
            ((x.dst + 0x88#64) ↦₆₄ pqCap') ∗
            vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState) ∗
          (((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((x.dst + 0x150#64) ↦₃₂ w288) ∗ ((x.dst + 0x154#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hloc_hdr, hrem_hdr, hroot_hdr, hchains_hdr, halice_hdr, hpq_hdr, htail_eq]
  refine Entails.trans
    (sepConj_mono hpend_reasm (sepConj_mono hkyb_reasm (sepConj_mono_left hsc_reasm))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kyb'
  apply Entails.sepExists_elim; intro pend'
  rw [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hpend'_some, hpend'_rel, hpend'_enc⟩
  rw [show (optTailVecAt A 48 (x.dst + 0xf8#64) pend' ∗
        (⌜KyberRel kyb' x.s.pendingKyberPreKey⌝ ∗
          optTailVecAt A 32 (x.dst + 0x128#64) kyb') ∗
        optSenderChainAt A (x.dst + 0x90#64) sender' x.s.state.senderChain ∗
        vecGhostAt A localIk' x.dst ∗
        vecGhostAt A remoteIk' (x.dst + 0x18#64) ∗
        vecU8At A (x.dst + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.dst + 0x48#64) chainsCap' chainsPtr'
          (chains'.zip x.s.state.receiverChains) ∗
        vecGhostAt A alice' (x.dst + 0x60#64) ∗
        vecU8At A (x.dst + 0x78#64) pqCap' pqPtr' x.s.state.pqRatchetState ∗
        ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦ₛ x.G.regIds)) =
      (⌜KyberRel kyb' x.s.pendingKyberPreKey⌝ ∗
        optTailVecAt A 48 (x.dst + 0xf8#64) pend' ∗
        optTailVecAt A 32 (x.dst + 0x128#64) kyb' ∗
        optSenderChainAt A (x.dst + 0x90#64) sender' x.s.state.senderChain ∗
        vecGhostAt A localIk' x.dst ∗
        vecGhostAt A remoteIk' (x.dst + 0x18#64) ∗
        vecU8At A (x.dst + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.dst + 0x48#64) chainsCap' chainsPtr'
          (chains'.zip x.s.state.receiverChains) ∗
        vecGhostAt A alice' (x.dst + 0x60#64) ∗
        vecU8At A (x.dst + 0x78#64) pqCap' pqPtr' x.s.state.pqRatchetState ∗
        ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦ₛ x.G.regIds)) by ac_rfl]
  apply Entails.pure_left; intro hkyb'_rel
  let G' : SessionGhost :=
    { localIk := localIk'
      remoteIk := remoteIk'
      root := ⟨32#64, rootPtr'⟩
      chainsCap := chainsCap'
      chainsPtr := chainsPtr'
      chains := chains'
      alice := alice'
      pq := ⟨pqCap', pqPtr'⟩
      sender := sender'
      pending := pend'
      kyber := kyb'
      regIds := x.G.regIds }
  refine Entails.sepExists_right G' ?_
  have henc : encSessionMem G' x.s = encSessionMem x.G x.s := by
    unfold encSessionMem
    dsimp only [G']
    rw [hloc_bytes, hrem_bytes, hsc_enc, hchains_enc, hpend'_enc]
  apply Entails.pure_right henc
  unfold sessionStateReprAt
  have hpure_s :
      PendingRel G'.pending x.s.pendingPreKey ∧
      KyberRel G'.kyber x.s.pendingKyberPreKey ∧
      G'.alice.bytes = x.s.aliceBaseKey ∧
      G'.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat ∧
      (G'.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat := by
    dsimp [G']
    rw [halice_bytes]
    exact ⟨hpend'_rel, hkyb'_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩
  apply Entails.pure_right hpure_s
  unfold sessionStateAt
  have hpure_st :
      PublicKey.deserialize G'.localIk.bytes = .ok x.s.state.localIdentity.publicKey ∧
      (match x.s.state.remoteIdentity with
       | none => G'.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G'.remoteIk.bytes = .ok ik.publicKey) ∧
      G'.chains.length = x.s.state.receiverChains.length ∧
      G'.pending.isSome = x.s.state.pendingPreKey ∧ G'.regIds.length = 8 ∧
      G'.localIk.bytes.length = 33 ∧
      (x.s.state.remoteIdentity.isSome → G'.remoteIk.bytes.length = 33) := by
    dsimp [G']
    rw [hloc_bytes, hrem_bytes, hpend'_some]
    exact ⟨h_loc_deser, h_rem_deser, hchains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  apply Entails.pure_right hpure_st
  dsimp only [G']
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
