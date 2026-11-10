/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>` Phase 1a: `spqr::decode_state` Result Handling (`+80..+156`)

Proves `32 + 320`B relocation helpers for `protoPqRatchetStateAt`, the `decode_state = .error e`
return path (`spqr_send_decode_state_err_step`), and the `Ok(pq)` relocation step
(`spqr_send_decode_state_ok_to_156`, `0x308ac..0x308f8`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
  CryptoVerification.SpqrV1.Top.DecodeState.none3Cap_add_three_beq_zero

@[local arm64_norm, local wp_norm]
theorem bv_add_add_lit1 (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem bv_add_add_lit2 (x : BitVec 64) (a b : Nat) :
    x + (BitVec.ofNat 64 a + BitVec.ofNat 64 b) = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## `32 + 320`B Relocation Helpers for `protoPqRatchetStateAt` -/

theorem pointsToBytes_16_eq_two_cells (a : BitVec 64) :
    ∀ {bs : List (BitVec 8)}, bs.length = 16 →
      (a ↦ₛ bs) ⊢ ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜bs = unpack64 w2 ++ unpack64 w3⌝ ∗
        (a ↦₆₄ w2) ∗ ((a + 8#64) ↦₆₄ w3) := by
  intro bs hlen
  have h16 : (a ↦ₛ bs) = (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) := by
    have hbs : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
    have hl1 : (bs.take 8).length = 8 := by simp [hlen]
    conv_lhs => rw [hbs]
    rw [ProofLib.pointsToBytes_append, hl1]
  have hl2 : (bs.drop 8).length = 8 := by simp [hlen]
  have h8_1 : (a ↦ₛ bs.take 8) ⊢ ∃∗ w2 : BitVec 64, ⌜bs.take 8 = unpack64 w2⌝ ∗ (a ↦₆₄ w2) := by
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, tail⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals try (simp only [List.length] at hlen; omega)
    dsimp only [List.take]
    refine Entails.sepExists_right (pack64 b0 b1 b2 b3 b4 b5 b6 b7) ?_
    have hpack : unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
      dsimp only [pack64]
      exact ProofLib.unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
    rw [hpack]
    apply Entails.pure_right rfl
    rw [ProofLib.pointsTo64_eq_pointsToBytes, hpack]
    exact Entails.refl _
  have h8_2 : ((a + 8#64) ↦ₛ bs.drop 8) ⊢
      ∃∗ w3 : BitVec 64, ⌜bs.drop 8 = unpack64 w3⌝ ∗ ((a + 8#64) ↦₆₄ w3) := by
    rcases hdrop : bs.drop 8 with
      _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals try (rw [hdrop] at hl2; simp only [List.length] at hl2; omega)
    refine Entails.sepExists_right (pack64 b0 b1 b2 b3 b4 b5 b6 b7) ?_
    have hpack : unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
      dsimp only [pack64]
      exact ProofLib.unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
    rw [hpack]
    apply Entails.pure_right rfl
    rw [ProofLib.pointsTo64_eq_pointsToBytes, hpack]
    exact Entails.refl _
  rw [h16]
  refine Entails.trans (sepConj_mono h8_1 h8_2) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  have hpull :
      ((⌜bs.take 8 = unpack64 w2⌝ ∗ (a ↦₆₄ w2)) ∗
       ⌜bs.drop 8 = unpack64 w3⌝ ∗ ((a + 8#64) ↦₆₄ w3)) =
      ⌜bs.take 8 = unpack64 w2⌝ ∗ ⌜bs.drop 8 = unpack64 w3⌝ ∗
        ((a ↦₆₄ w2) ∗ ((a + 8#64) ↦₆₄ w3)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hw2
  apply Entails.pure_left; intro hw3
  refine Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)
  have hbs : bs = unpack64 w2 ++ unpack64 w3 := by
    rw [← hw2, ← hw3, List.take_append_drop 8 bs]
  apply Entails.pure_right hbs
  exact Entails.of_eq (by ac_rfl)

theorem two_cells_eq_pointsToBytes_16 (a w2 w3 : BitVec 64) :
    (a ↦₆₄ w2) ∗ ((a + 8#64) ↦₆₄ w3) =
      (a ↦ₛ (unpack64 w2 ++ unpack64 w3)) := by
  rw [ProofLib.pointsToBytes_append a (unpack64 w2) (unpack64 w3)]
  have hl : (unpack64 w2).length = 8 := rfl
  rw [hl, ← ProofLib.pointsTo64_eq_pointsToBytes, ← ProofLib.pointsTo64_eq_pointsToBytes]

/-- `Relocatable` for the 304-byte `chain` (`80`B) + `inner` (`224`B) portion of `PqRatchetState`. -/
def relocChainAndInnerAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (st : PqRatchetState) :
    Σ' H, Relocatable
      (fun a48 => ProtoRepr.optChainPBAt A a48 st.chain ∗
        optProtoPqRatchetInnerAt H_inner A (a48 + 80#64) st.inner)
      304 H :=
  ⟨_, reloc_append 304 80#64
    (relocOptChainPBAt A st.chain).2
    (relocOptProtoPqRatchetInnerAt H_inner A st.inner).2 rfl rfl⟩

/-- Split `DecodeState.protoPqRatchetStateAt H_inner A a st` into:
    - `w0` (`a ↦₆₄ w0`, `w0 ≠ DecodeState.none2Cap`),
    - `q0 = w2 ++ w1` (`(a + 8#64) ↦₁₂₈ (w2 ++ w1)`),
    - `w3` (`(a + 24#64) ↦₆₄ w3`),
    - `bs16 ++ bs304` (`(a + 32#64) ↦ₛ (bs16 ++ bs304)`, `bs16.length = 16`, `bs304.length = 304`),
    - `H_vn` (`(relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).1 ((unpack64 w2 ++ unpack64 w3) ++ bs16)`),
    - `H_ci` (`(relocChainAndInnerAt H_inner A st).1 bs304`). -/
theorem protoPqRatchetStateAt_entails_split32_16_304 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (st : PqRatchetState) :
    DecodeState.protoPqRatchetStateAt H_inner A a st ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ bs16 : List (BitVec 8), ∃∗ bs304 : List (BitVec 8),
        ⌜w0 ≠ DecodeState.none2Cap ∧ bs16.length = 16 ∧ bs304.length = 304⌝ ∗
        (a ↦₆₄ w0) ∗
        ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦ₛ (bs16 ++ bs304)) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        (relocChainAndInnerAt H_inner A st).1 bs304 := by
  unfold DecodeState.protoPqRatchetStateAt
  refine Entails.trans
    (sepConj_mono_left (optVersionNegotiationPBAt_entails_head16_tail32 A a st.versionNegotiation)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  have hpull0 :
      ((⌜w0 ≠ DecodeState.none2Cap⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation) ∗
       ProtoRepr.optChainPBAt A (a + 48#64) st.chain ∗
       optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner) =
      ⌜w0 ≠ DecodeState.none2Cap⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation ∗
        (ProtoRepr.optChainPBAt A (a + 48#64) st.chain ∗
         optProtoPqRatchetInnerAt H_inner A ((a + 48#64) + 80#64) st.inner) := by
    have ha128 : (a + 48#64) + 80#64 = a + 128#64 := by bv_omega
    rw [ha128]; ac_rfl
  rw [hpull0]
  apply Entails.pure_left; intro hw0
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono
        ((relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).2.to_bytes (a + 16#64))
        ((relocChainAndInnerAt H_inner A st).2.to_bytes (a + 48#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs304
  apply Entails.sepExists_elim; intro bs32
  have hpull1 :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       (⌜bs32.length = 32⌝ ∗ ((a + 16#64) ↦ₛ bs32) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).1 bs32) ∗
       ⌜bs304.length = 304⌝ ∗ ((a + 48#64) ↦ₛ bs304) ∗
       (relocChainAndInnerAt H_inner A st).1 bs304) =
      ⌜bs32.length = 32⌝ ∗ ⌜bs304.length = 304⌝ ∗
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs32) ∗ ((a + 48#64) ↦ₛ bs304) ∗
         (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).1 bs32 ∗
         (relocChainAndInnerAt H_inner A st).1 bs304) := by ac_rfl
  rw [hpull1]
  apply Entails.pure_left; intro hlen32
  apply Entails.pure_left; intro hlen304
  have hsplit32 : bs32 = bs32.take 16 ++ bs32.drop 16 := (List.take_append_drop 16 bs32).symm
  have hl16 : (bs32.take 16).length = 16 := by simp [hlen32]
  have hl16_drop : (bs32.drop 16).length = 16 := by simp [hlen32]
  have hpts32 : ((a + 16#64) ↦ₛ bs32) =
      ((a + 16#64) ↦ₛ bs32.take 16) ∗ ((a + 32#64) ↦ₛ bs32.drop 16) := by
    conv_lhs => rw [hsplit32]
    rw [ProofLib.pointsToBytes_append (a + 16#64) (bs32.take 16) (bs32.drop 16), hl16]
    have ha32 : (a + 16#64) + 16#64 = a + 32#64 := by bv_omega
    rw [ha32]
  rw [hpts32]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_left (pointsToBytes_16_eq_two_cells (a + 16#64) hl16))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  have hpull2 :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       ((⌜bs32.take 16 = unpack64 w2 ++ unpack64 w3⌝ ∗
         ((a + 16#64) ↦₆₄ w2) ∗ (((a + 16#64) + 8#64) ↦₆₄ w3)) ∗
        ((a + 32#64) ↦ₛ bs32.drop 16)) ∗
       ((a + 48#64) ↦ₛ bs304) ∗
       (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).1 bs32 ∗
       (relocChainAndInnerAt H_inner A st).1 bs304) =
      ⌜bs32.take 16 = unpack64 w2 ++ unpack64 w3⌝ ∗
        (((a + 32#64) ↦ₛ bs32.drop 16) ∗ ((a + 48#64) ↦ₛ bs304)) ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ (((a + 16#64) + 8#64) ↦₆₄ w3) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).1 bs32 ∗
        (relocChainAndInnerAt H_inner A st).1 bs304 := by ac_rfl
  rw [hpull2]
  apply Entails.pure_left; intro htake16
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  have ha48 : (a + 32#64) + 16#64 = a + 48#64 := by bv_omega
  have h320 : ((a + 32#64) ↦ₛ bs32.drop 16) ∗ ((a + 48#64) ↦ₛ bs304) =
      ((a + 32#64) ↦ₛ (bs32.drop 16 ++ bs304)) := by
    rw [ProofLib.pointsToBytes_append (a + 32#64) (bs32.drop 16) bs304, hl16_drop, ha48]
  have hbs32_eq : bs32 = (unpack64 w2 ++ unpack64 w3) ++ bs32.drop 16 := by
    rw [← htake16, ← hsplit32]
  rw [h320, ha24]
  refine Entails.sepExists_right w0
    (Entails.sepExists_right w1
      (Entails.sepExists_right w2
        (Entails.sepExists_right w3
          (Entails.sepExists_right (bs32.drop 16)
            (Entails.sepExists_right bs304 ?_)))))
  rw [← hbs32_eq]
  apply Entails.pure_right ⟨hw0, hl16_drop, hlen304⟩
  exact Entails.of_eq (by ac_rfl)

/-- After `memcpy(a + 32#64, ..., 320)`, split `((a + 32#64) ↦ₛ (bs16 ++ bs304))` and reassemble
    `ProtoRepr.optChainPBAt A (a + 48#64) st.chain ∗ optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner`. -/
theorem reassemble_chain_and_inner_after_memcpy (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (bs16 bs304 : List (BitVec 8)) (st : PqRatchetState)
    (hl16 : bs16.length = 16) (hl304 : bs304.length = 304) :
    ((a + 32#64) ↦ₛ (bs16 ++ bs304)) ∗ (relocChainAndInnerAt H_inner A st).1 bs304 ⊢
      ((a + 32#64) ↦ₛ bs16) ∗
      ProtoRepr.optChainPBAt A (a + 48#64) st.chain ∗
      optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner := by
  have ha48 : (a + 32#64) + 16#64 = a + 48#64 := by bv_omega
  have ha128 : (a + 48#64) + 80#64 = a + 128#64 := by bv_omega
  rw [ProofLib.pointsToBytes_append (a + 32#64) bs16 bs304, hl16, ha48, sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [← ha128]
  exact (relocChainAndInnerAt H_inner A st).2.of_bytes (a + 48#64) bs304 hl304

/-- Reassemble `((a + 8#64) ↦₆₄ w1) ∗ optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) optVn`
    from `((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs16)` and `H_vn`. -/
theorem reassemble_optVersionNegotiationPBTail (A : RustAlloc)
    (a w0 w1 w2 w3 : BitVec 64) (bs16 : List (BitVec 8)) (optVn : Option VersionNegotiationPB)
    (hl16 : bs16.length = 16) :
    ((a + 8#64) ↦₆₄ w1) ∗
      ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦ₛ bs16) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 optVn).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ⊢
      ((a + 8#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) optVn := by
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  have ha32 : (a + 16#64) + 16#64 = a + 32#64 := by bv_omega
  have h16 := two_cells_eq_pointsToBytes_16 (a + 16#64) w2 w3
  rw [ha24] at h16
  have hl_w23 : (unpack64 w2 ++ unpack64 w3).length = 16 := rfl
  have h32 :
      ((a + 16#64) ↦ₛ (unpack64 w2 ++ unpack64 w3)) ∗ ((a + 32#64) ↦ₛ bs16) =
      ((a + 16#64) ↦ₛ ((unpack64 w2 ++ unpack64 w3) ++ bs16)) := by
    rw [ProofLib.pointsToBytes_append (a + 16#64) (unpack64 w2 ++ unpack64 w3) bs16, hl_w23, ha32]
  have hlen32 : ((unpack64 w2 ++ unpack64 w3) ++ bs16).length = 32 := by
    rw [List.length_append, hl_w23, hl16]
  have hgroup :
      (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs16) ∗
       (relocOptVersionNegotiationPBTailAt A w0 w1 optVn).1
         ((unpack64 w2 ++ unpack64 w3) ++ bs16)) =
      ((a + 8#64) ↦₆₄ w1) ∗
        (((a + 16#64) ↦ₛ ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
         (relocOptVersionNegotiationPBTailAt A w0 w1 optVn).1
           ((unpack64 w2 ++ unpack64 w3) ++ bs16)) := by
    rw [← h32, ← h16]
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_right
    ((relocOptVersionNegotiationPBTailAt A w0 w1 optVn).2.of_bytes
      (a + 16#64) ((unpack64 w2 ++ unpack64 w3) ++ bs16) hlen32)

/-! ## `spqr::decode_state` Error Return Path (`+80 -> s0.lr`) -/

theorem ne_none2Cap_add_two_beq_zero_false {w0 : BitVec 64} (h : w0 ≠ DecodeState.none2Cap) :
    (w0 + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  unfold DecodeState.none2Cap
  bv_omega

theorem ne_none3Cap_add_three_beq_zero_false {w0 : BitVec 64} (h : w0 ≠ DecodeState.none3Cap) :
    (w0 + 3#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  unfold DecodeState.none3Cap
  bv_omega

theorem decodeStateResultAt_err_entails_head32_320 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (e : Error) :
    decodeStateResultAt H_inner A a (.error e) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ DecodeState.none2Cap) ∗
        ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 320 := by
  unfold decodeStateResultAt
  have hm8 : ((a + 8#64) ↦₈ DecodeState.spqrErrorTag e) ∗ memRegion (a + 9#64) 343 ⊢
      memRegion (a + 8#64) 344 := by
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 343) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 8#64) (DecodeState.spqrErrorTag e))
  refine Entails.trans (sepConj_mono_right hm8) ?_
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 336) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 328) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 320) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_ret_72_split_err (ret : BitVec 64) :
    memRegion ret 72 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ rw8 : BitVec 64, ∃∗ rw16 : BitVec 64, ∃∗ rw24 : BitVec 64,
        (ret ↦₆₄ r0) ∗
        ((ret + 8#64) ↦₆₄ rw8) ∗
        ((ret + 16#64) ↦₆₄ rw16) ∗
        ((ret + 24#64) ↦₆₄ rw24) ∗
        memRegion (ret + 32#64) 40 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 64) (b' := ret + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 56) (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48) (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40) (b' := ret + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret,
      ProofLib.memRegion_eight (ret + 8#64),
      ProofLib.memRegion_eight (ret + 16#64),
      ProofLib.memRegion_eight (ret + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro rw24
  apply Entails.sepExists_elim; intro rw16
  apply Entails.sepExists_elim; intro rw8
  apply Entails.sepExists_elim; intro r0
  refine Entails.sepExists_right r0
    (Entails.sepExists_right rw8 (Entails.sepExists_right rw16 (Entails.sepExists_right rw24 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem err_ret_entails_sendResultAt_none (A : RustAlloc) (ret : BitVec 64)
    (w1 w2 w3 : BitVec 64) :
    (ret ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
      ((ret + 8#64) ↦₆₄ w1) ∗
      ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗
      memRegion (ret + 32#64) 40 ⊢
      spqrSendResultAt A ret none := by
  unfold spqrSendResultAt
  have herr : LibsignalTripleRatchetRepr.noneCap = errTag := rfl
  rw [herr,
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 56) (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48) (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40) (b' := ret + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (ret + 8#64) w1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (ret + 16#64) w2)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (ret + 24#64) w3))))

theorem memRegion_1f20_split_decode_state (fsp : BitVec 64) :
    memRegion fsp 0x1f20 =
      memRegion fsp 0x1260 ∗
      memRegion (fsp + 0x1260#64) 352 ∗
      memRegion (fsp + 0x13c0#64) (0x1f20 - 0x13c0) := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1260) (k := 0x1f20 - 0x1260)
        (b' := fsp + 0x1260#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 352) (k := 0x1f20 - 0x13c0)
        (b' := fsp + 0x13c0#64) rfl (by bv_omega) (by decide)]

theorem memRegion_1260_split_190 (fsp : BitVec 64) :
    memRegion fsp 0x1260 ⊢
      ∃∗ w190 : BitVec 64, ∃∗ w198 : BitVec 64, ∃∗ w1a0 : BitVec 64,
        memRegion fsp 0x190 ∗
        ((fsp + 0x190#64) ↦₆₄ w190) ∗
        ((fsp + 0x198#64) ↦₆₄ w198) ∗
        ((fsp + 0x1a0#64) ↦₆₄ w1a0) ∗
        memRegion (fsp + 0x1a8#64) (0x1260 - 0x1a8) := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 0x190) (k := 0x1260 - 0x190)
        (b' := fsp + 0x190#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 8) (k := 0x1260 - 0x198)
        (b' := fsp + 0x198#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x198#64) (n := 8) (k := 0x1260 - 0x1a0)
        (b' := fsp + 0x1a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1a0#64) (n := 8) (k := 0x1260 - 0x1a8)
        (b' := fsp + 0x1a8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 0x190#64),
      ProofLib.memRegion_eight (fsp + 0x198#64),
      ProofLib.memRegion_eight (fsp + 0x1a0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1a0
  apply Entails.sepExists_elim; intro w198
  apply Entails.sepExists_elim; intro w190
  refine Entails.sepExists_right w190 (Entails.sepExists_right w198 (Entails.sepExists_right w1a0 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem decode_state_err_frame_rejoin (fsp : BitVec 64) (w1 w2 w3 : BitVec 64) :
    memRegion fsp 0x190 ∗
      ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1260 - 0x1a8) ∗
      ((fsp + 0x1260#64) ↦₆₄ DecodeState.none2Cap) ∗
      ((fsp + 0x1268#64) ↦₆₄ w1) ∗
      ((fsp + 0x1270#64) ↦₆₄ w2) ∗
      ((fsp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1280#64) 320 ∗
      memRegion (fsp + 0x13c0#64) (0x1f20 - 0x13c0) ⊢
      memRegion fsp 0x1f20 := by
  have h1260 :
      memRegion fsp 0x190 ∗ ((fsp + 0x190#64) ↦₆₄ w1) ∗ ((fsp + 0x198#64) ↦₆₄ w2) ∗
        ((fsp + 0x1a0#64) ↦₆₄ w3) ∗ memRegion (fsp + 0x1a8#64) (0x1260 - 0x1a8) ⊢
      memRegion fsp 0x1260 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x190) (k := 0x1260 - 0x190)
          (b' := fsp + 0x190#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 8) (k := 0x1260 - 0x198)
          (b' := fsp + 0x198#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x198#64) (n := 8) (k := 0x1260 - 0x1a0)
          (b' := fsp + 0x1a0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1a0#64) (n := 8) (k := 0x1260 - 0x1a8)
          (b' := fsp + 0x1a8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x190#64) w1)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x198#64) w2)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1a0#64) w3))))
  have h352 :
      ((fsp + 0x1260#64) ↦₆₄ DecodeState.none2Cap) ∗ ((fsp + 0x1268#64) ↦₆₄ w1) ∗
        ((fsp + 0x1270#64) ↦₆₄ w2) ∗ ((fsp + 0x1278#64) ↦₆₄ w3) ∗ memRegion (fsp + 0x1280#64) 320 ⊢
      memRegion (fsp + 0x1260#64) 352 := by
    rw [ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 8) (k := 344)
          (b' := fsp + 0x1268#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1268#64) (n := 8) (k := 336)
          (b' := fsp + 0x1270#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1270#64) (n := 8) (k := 328)
          (b' := fsp + 0x1278#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1278#64) (n := 8) (k := 320)
          (b' := fsp + 0x1280#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1260#64) DecodeState.none2Cap)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1268#64) w1)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1270#64) w2)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1278#64) w3))))
  rw [memRegion_1f20_split_decode_state fsp]
  refine Entails.trans
    (Entails.of_eq (show _ =
      (memRegion fsp 0x190 ∗ ((fsp + 0x190#64) ↦₆₄ w1) ∗ ((fsp + 0x198#64) ↦₆₄ w2) ∗
       ((fsp + 0x1a0#64) ↦₆₄ w3) ∗ memRegion (fsp + 0x1a8#64) (0x1260 - 0x1a8)) ∗
      (((fsp + 0x1260#64) ↦₆₄ DecodeState.none2Cap) ∗ ((fsp + 0x1268#64) ↦₆₄ w1) ∗
       ((fsp + 0x1270#64) ↦₆₄ w2) ∗ ((fsp + 0x1278#64) ↦₆₄ w3) ∗ memRegion (fsp + 0x1280#64) 320) ∗
      memRegion (fsp + 0x13c0#64) (0x1f20 - 0x13c0) by ac_rfl)) ?_
  exact sepConj_mono h1260 (sepConj_mono_left h352)

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_1260_add_8 (fsp : BitVec 64) :
    (fsp + 0x1260#64) + 8#64 = fsp + 0x1268#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_1268_add_8 (fsp : BitVec 64) :
    (fsp + 0x1268#64) + 8#64 = fsp + 0x1270#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_190_add_8 (fsp : BitVec 64) :
    (fsp + 0x190#64) + 8#64 = fsp + 0x198#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_38_add_8 (fsp : BitVec 64) :
    (fsp + 0x38#64) + 8#64 = fsp + 0x40#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem ret_8_add_8 (ret : BitVec 64) :
    (ret + 8#64) + 8#64 = ret + 16#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_1260_add_18 (fsp : BitVec 64) :
    (fsp + 0x1260#64) + 0x18#64 = fsp + 0x1278#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_1260_add_20 (fsp : BitVec 64) :
    (fsp + 0x1260#64) + 0x20#64 = fsp + 0x1280#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_30_add_20 (fsp : BitVec 64) :
    (fsp + 0x30#64) + 0x20#64 = fsp + 0x50#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_30_add_80 (fsp : BitVec 64) :
    (fsp + 0x30#64) + 0x80#64 = fsp + 0xb0#64 := by bv_omega

/-- `Err(e)` return path after `spqr::decode_state` (`+80 -> s0.lr`, `0x308ac..0x308e0 -> 0x31a74`):
    writes `spqrSendResultAt A ret none`, rejoins the stack frame, and executes `spqr_send_epilogue_4632`. -/
theorem spqr_send_decode_state_err_step {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (ret : BitVec 64) (e : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        memRegion ret 72 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ spqrSendResultAt A ret none ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine EncoderFromPb.seq_clean
    (mid := spqrSendEntry b + 4632#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (spqrSendResultAt A ret none ∗ Rest))
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
    spqr_send_fetches_range b (Rust.withPanics ext) 80 56
    dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_session::HookRng>" = entry
    examples_hide_fetches
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_right
        (sepConj_mono (memRegion_1260_split_190 fsp)
          (sepConj_mono (decodeStateResultAt_err_entails_head32_320 H_inner A (fsp + 4704#64) e)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion_ret_72_split_err ret))))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro r0
    apply ProofLib.SepWP.exists_left; intro rw8
    apply ProofLib.SepWP.exists_left; intro rw16
    apply ProofLib.SepWP.exists_left; intro rw24
    apply ProofLib.SepWP.exists_left; intro w1
    apply ProofLib.SepWP.exists_left; intro w2
    apply ProofLib.SepWP.exists_left; intro w3
    apply ProofLib.SepWP.exists_left; intro w190
    apply ProofLib.SepWP.exists_left; intro w198
    apply ProofLib.SepWP.exists_left; intro w1a0
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hframe := decode_state_err_frame_rejoin fsp w1 w2 w3
      have hret := err_ret_entails_sendResultAt_none A ret w1 w2 w3
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 400 ∗
           ((fsp + 400#64) ↦₆₄ w1) ∗
           ((fsp + 408#64) ↦₆₄ w2) ∗
           ((fsp + 416#64) ↦₆₄ w3) ∗
           memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
           ((fsp + 4704#64) ↦₆₄ DecodeState.none2Cap) ∗
           ((fsp + 4712#64) ↦₆₄ w1) ∗
           ((fsp + 4720#64) ↦₆₄ w2) ∗
           ((fsp + 4728#64) ↦₆₄ w3) ∗
           memRegion (fsp + 4736#64) 320 ∗
           memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
          ((ret ↦₆₄ 18446744073709551615#64) ∗
           ((ret + 8#64) ↦₆₄ w1) ∗
           ((ret + 16#64) ↦₆₄ w2) ∗
           ((ret + 24#64) ↦₆₄ w3) ∗
           memRegion (ret + 32#64) 40) ∗
          (stackAt fsp spqrSendCalleeStack ∗
           spqrSendSavedRegs fsp s0 ∗
           Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hframe (sepConj_mono_left hret)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
    have hep := spqr_send_epilogue_4632 (ext := ext) s0 s2 (spqrSendResultAt A ret none ∗ Rest) hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

/-! ## `Ok(pq)` Relocation (`+80 -> +156`, `0x308ac..0x308f8`) -/

theorem memRegion_190_split_30_50 (fsp : BitVec 64) :
    memRegion fsp 0x190 ⊢
      ∃∗ w30 : BitVec 64, ∃∗ w38 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        memRegion fsp 0x30 ∗
        ((fsp + 0x30#64) ↦₆₄ w30) ∗
        ((fsp + 0x38#64) ↦₆₄ w38) ∗
        ((fsp + 0x40#64) ↦₆₄ w40) ∗
        ((fsp + 0x48#64) ↦₆₄ w48) ∗
        memRegion (fsp + 0x50#64) 320 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 0x30) (k := 352)
        (b' := fsp + 0x30#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x30#64) (n := 8) (k := 344)
        (b' := fsp + 0x38#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x38#64) (n := 8) (k := 336)
        (b' := fsp + 0x40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x40#64) (n := 8) (k := 328)
        (b' := fsp + 0x48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x48#64) (n := 8) (k := 320)
        (b' := fsp + 0x50#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 0x30#64),
      ProofLib.memRegion_eight (fsp + 0x38#64),
      ProofLib.memRegion_eight (fsp + 0x40#64),
      ProofLib.memRegion_eight (fsp + 0x48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w38
  apply Entails.sepExists_elim; intro w30
  refine Entails.sepExists_right w30
    (Entails.sepExists_right w38
      (Entails.sepExists_right w40
        (Entails.sepExists_right w48 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem src352_rejoin_1a8_to_1f20 (fsp : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) (bs320 : List (BitVec 8))
    (hlen320 : bs320.length = 320) :
    memRegion (fsp + 0x1a8#64) (0x1260 - 0x1a8) ∗
      ((fsp + 0x1260#64) ↦₆₄ w0) ∗
      ((fsp + 0x1268#64) ↦₆₄ w1) ∗
      ((fsp + 0x1270#64) ↦₆₄ w2) ∗
      ((fsp + 0x1278#64) ↦₆₄ w3) ∗
      ((fsp + 0x1280#64) ↦ₛ bs320) ∗
      memRegion (fsp + 0x13c0#64) (0x1f20 - 0x13c0) ⊢
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) := by
  have hm320 : ((fsp + 0x1280#64) ↦ₛ bs320) ⊢ memRegion (fsp + 0x1280#64) 320 := by
    rw [← hlen320]
    exact ProofLib.pointsToBytes_entails_memRegion (fsp + 0x1280#64) bs320
  have h352 :
      ((fsp + 0x1260#64) ↦₆₄ w0) ∗ ((fsp + 0x1268#64) ↦₆₄ w1) ∗
        ((fsp + 0x1270#64) ↦₆₄ w2) ∗ ((fsp + 0x1278#64) ↦₆₄ w3) ∗ ((fsp + 0x1280#64) ↦ₛ bs320) ⊢
      memRegion (fsp + 0x1260#64) 352 := by
    rw [ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 8) (k := 344)
          (b' := fsp + 0x1268#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1268#64) (n := 8) (k := 336)
          (b' := fsp + 0x1270#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1270#64) (n := 8) (k := 328)
          (b' := fsp + 0x1278#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1278#64) (n := 8) (k := 320)
          (b' := fsp + 0x1280#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1260#64) w0)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1268#64) w1)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1270#64) w2)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1278#64) w3) hm320)))
  rw [ProofLib.memRegion_split' (b := fsp + 0x1a8#64) (n := 0x1260 - 0x1a8) (k := 0x1f20 - 0x1260)
        (b' := fsp + 0x1260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 352) (k := 0x1f20 - 0x13c0)
        (b' := fsp + 0x13c0#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show _ =
      memRegion (fsp + 0x1a8#64) (0x1260 - 0x1a8) ∗
      (((fsp + 0x1260#64) ↦₆₄ w0) ∗ ((fsp + 0x1268#64) ↦₆₄ w1) ∗
       ((fsp + 0x1270#64) ↦₆₄ w2) ∗ ((fsp + 0x1278#64) ↦₆₄ w3) ∗ ((fsp + 0x1280#64) ↦ₛ bs320)) ∗
      memRegion (fsp + 0x13c0#64) (0x1f20 - 0x13c0) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left h352)

/-- `Ok(pq)` relocation step from `+80` to `+156` (`0x308ac..0x308f8`):
    loads the 32-byte header of `pq` into `x23 = w0` and `[sp + 0x190..0x1a8]`,
    checks `w0 ≠ none2Cap`, calls `memcpy(sp + 0x50, sp + 0x1280, 320)`, and reassembles
    `optChainPBAt A (sp + 0x60) pq.chain` and `optProtoPqRatchetInnerAt H_inner A (sp + 0xb0) pq.inner`. -/
theorem spqr_send_decode_state_ok_to_156 {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (ret : BitVec 64) (pq : PqRatchetState) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64) :
    SepWP (tripleRatchetProgAtExt b ext) (spqrSendEntry b + 156#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        ∃ w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64,
        ∃ bs16 : List (BitVec 8),
          w0 ≠ DecodeState.none2Cap ∧
          bs16.length = 16 ∧
          (Pm ⊢
            stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
            (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
            (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
            (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
            (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
            (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
            (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
            memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
            (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
              ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
            Rest) ∧
          sm.sp = s0.sp - 0x1f80#64 ∧
          sm.readReg64 .x19 = ret ∧
          sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
          sm.readReg64 .x23 = w0 ∧
          sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hmemcpy_raw : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy"))
      sessionMemcpyRegionSpec := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "memcpy") (by decide))
    hA.session_memcpy_region
  rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
  spqr_send_fetches_range b (Rust.withPanics ext) 80 76
  dsimp only [tripleRatchetProgAtExt, spqrSendName, decodeStateResultAt, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx21 hx26 ⊢
  refine SepWP.weaken_pre
    (sepConj_mono_right
      (sepConj_mono
        (Entails.trans (memRegion_1260_split_190 fsp)
          (Entails.sepExists_elim fun w190 => Entails.sepExists_elim fun w198 => Entails.sepExists_elim fun w1a0 =>
            Entails.sepExists_right w190 (Entails.sepExists_right w198 (Entails.sepExists_right w1a0
              (sepConj_mono_left (memRegion_190_split_30_50 fsp))))))
        (sepConj_mono_left (protoPqRatchetStateAt_entails_split32_16_304 H_inner A (fsp + 4704#64) pq)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro bs16
  apply ProofLib.SepWP.exists_left; intro bs304
  apply ProofLib.SepWP.exists_left; intro w190
  apply ProofLib.SepWP.exists_left; intro w198
  apply ProofLib.SepWP.exists_left; intro w1a0
  apply ProofLib.SepWP.exists_left; intro w30
  apply ProofLib.SepWP.exists_left; intro w38
  apply ProofLib.SepWP.exists_left; intro w40
  apply ProofLib.SepWP.exists_left; intro w48
  wp_focus_pure; rintro ⟨hw0, hl16, hl304⟩
  have hne2 := ne_none2Cap_add_two_beq_zero_false hw0
  have hlen_src : (bs16 ++ bs304).length = 320 := by rw [List.length_append, hl16, hl304]
  have hlen_lt64 : (bs16 ++ bs304).length < 2 ^ 64 := by rw [hlen_src]; decide
  wp_steps
  wp_apply
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine ⟨w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, ?_,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *]⟩
  have hci := reassemble_chain_and_inner_after_memcpy H_inner A (fsp + 48#64) bs16 bs304 pq hl16 hl304
  have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
  have ha96 : (fsp + 48#64) + 48#64 = fsp + 96#64 := by bv_omega
  have ha176 : (fsp + 48#64) + 128#64 = fsp + 176#64 := by bv_omega
  rw [ha80, ha96, ha176] at hci
  have hsrc := src352_rejoin_1a8_to_1f20 fsp w0 w1 w2 w3 (bs16 ++ bs304) hlen_src
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((fsp + 80#64) ↦ₛ (bs16 ++ bs304)) ∗ (relocChainAndInnerAt H_inner A pq).1 bs304) ∗
      (memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
       ((fsp + 4704#64) ↦₆₄ w0) ∗
       ((fsp + 4712#64) ↦₆₄ w1) ∗
       ((fsp + 4720#64) ↦₆₄ w2) ∗
       ((fsp + 4728#64) ↦₆₄ w3) ∗
       ((fsp + 4736#64) ↦ₛ (bs16 ++ bs304)) ∗
       memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
      (stackAt fsp spqrSendCalleeStack ∗
       memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ w30) ∗
       ((fsp + 56#64) ↦₆₄ w38) ∗
       ((fsp + 64#64) ↦₆₄ w40) ∗
       ((fsp + 72#64) ↦₆₄ w48) ∗
       ((fsp + 400#64) ↦₆₄ w1) ∗
       ((fsp + 408#64) ↦₆₄ w2) ∗
       ((fsp + 416#64) ↦₆₄ w3) ∗
       (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
         ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
       spqrSendSavedRegs fsp s0 ∗
       Rest) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hci (sepConj_mono_left hsrc)) ?_
  exact Entails.of_eq (by ac_rfl)


end CryptoVerification.SpqrV1.Top.Send
