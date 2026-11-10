/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled3
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Dispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves2
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: `<States>::send` 11-Arm Dispatch and Post-Arm Join (`0x31458..0x314d8`)

**Checked by Lean.**

Proves `statesSendPreInv_of_spqrDecodeState`, the shared post-arm reassembly epilogue
`step_send_post_arm_3068_to_3196` (`0x31458..0x314d8`), and the unified 11-arm dispatch
`step_send_statesSend` (`statesSendArmOffset st0 -> +3196`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## `statesSendPreInv` and `States.send` Elimination -/

@[simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

theorem headerReceived_rootKey_le_rawV1State {F : ShaCompress}
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    s.uc.auth.rootKey.length ≤ rawV1State (States.headerReceived s).into_pb := by
  unfold States.into_pb Chunked.SendCt.HeaderReceived.into_pb
    Unchunked.SendCt.HeaderReceived.into_pb spqrAuthApi Authenticator.intoPb
    rawV1State rawInnerState rawChHeaderReceived rawUcHeaderReceived rawAuth optRaw
  dsimp only
  omega

/-- Precondition on `st0 : States` for `States.send`: in the `.headerReceived` arm,
    `s.uc.auth.rootKey.length + 32 < 2 ^ 63` (discharging `authUpdateSpec`). -/
def statesSendPreInv {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .headerReceived s => s.uc.auth.rootKey.length + 32 < 2 ^ 63
  | _ => True

theorem statesSendPreInv_of_spqrDecodeState {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {st : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hlen : stateBytes.length < 2 ^ 32)
    (hdec : Proto.spqrDecodeState stateBytes = .ok st)
    (hinner : st.inner = some (.v1 pb))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    statesSendPreInv st0 := by
  cases st0 with
  | headerReceived s =>
    dsimp only [statesSendPreInv]
    have hraw_from := (States.from_pb_raw_le hfrom).1
    have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
    have hraw := decodeState_spqrDeps_raw_le hd
    rw [pbToPqRatchetState_pqRatchetStateToPb] at hraw
    unfold rawPqState at hraw
    rw [hinner] at hraw
    simp only [optRaw_some, rawPqInner] at hraw
    have hrk := headerReceived_rootKey_le_rawV1State s
    omega
  | _ => trivial

/-! ## Key-Slot and Payload-Slot Conversion Helpers (`0x31458..0x314d8`) -/

@[local arm64_norm, local wp_norm] theorem sp_add_190_add_8 (sp : BitVec 64) : (sp + 0x190#64) + 8#64 = sp + 0x198#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_190_add_16 (sp : BitVec 64) : (sp + 0x190#64) + 16#64 = sp + 0x1a0#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_190_add_24 (sp : BitVec 64) : (sp + 0x190#64) + 24#64 = sp + 0x1a8#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_190_add_32 (sp : BitVec 64) : (sp + 0x190#64) + 32#64 = sp + 0x1b0#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_198_add_8 (sp : BitVec 64) : (sp + 0x198#64) + 8#64 = sp + 0x1a0#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_198_add_16 (sp : BitVec 64) : (sp + 0x198#64) + 16#64 = sp + 0x1a8#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_198_add_24 (sp : BitVec 64) : (sp + 0x198#64) + 24#64 = sp + 0x1b0#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_590_add_8 (sp : BitVec 64) : (sp + 0x590#64) + 8#64 = sp + 0x598#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_590_add_16 (sp : BitVec 64) : (sp + 0x590#64) + 16#64 = sp + 0x5a0#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_590_add_24 (sp : BitVec 64) : (sp + 0x590#64) + 24#64 = sp + 0x5a8#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_580_add_8 (sp : BitVec 64) : (sp + 0x580#64) + 8#64 = sp + 0x588#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1bc0_add_8 (sp : BitVec 64) : (sp + 0x1bc0#64) + 8#64 = sp + 0x1bc8#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_530_add_8 (sp : BitVec 64) : (sp + 0x530#64) + 8#64 = sp + 0x538#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_550_add_8 (sp : BitVec 64) : (sp + 0x550#64) + 8#64 = sp + 0x558#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_560_add_8 (sp : BitVec 64) : (sp + 0x560#64) + 8#64 = sp + 0x568#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_550_add_30 (sp : BitVec 64) : (sp + 0x550#64) + 30#64 = sp + 0x56e#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_99_add_ff (sp : BitVec 64) : (sp + 0x99#64) + 0xff#64 = sp + 0x198#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1000_add_d70 (sp : BitVec 64) : (sp + 0x1000#64) + 0xd70#64 = sp + 0x1d70#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d70_add_8 (sp : BitVec 64) : (sp + 0x1d70#64) + 8#64 = sp + 0x1d78#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d70_add_9 (sp : BitVec 64) : (sp + 0x1d70#64) + 9#64 = sp + 0x1d79#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d70_add_10 (sp : BitVec 64) : (sp + 0x1d70#64) + 10#64 = sp + 0x1d7a#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d70_add_26 (sp : BitVec 64) : (sp + 0x1d70#64) + 26#64 = sp + 0x1d8a#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d7a_add_8 (sp : BitVec 64) : (sp + 0x1d7a#64) + 8#64 = sp + 0x1d82#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d8a_add_8 (sp : BitVec 64) : (sp + 0x1d8a#64) + 8#64 = sp + 0x1d92#64 := by rw [BitVec.add_assoc]; rfl

theorem chunkedStatesTail920At_590_entails_reloc (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesTail920At A (sp + 0x590#64) st1 ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2) ∗
        ((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦ₛ bs896) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A dst st1) bs := by
  refine Entails.trans (Relocatable.of_chunkedStatesTail920At A st1 (sp + 0x590#64)) ?_
  apply ProofLib.Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen920
  have hsplit := pointsToBytes_920_split_3words_896 (sp + 0x590#64) hlen920
  rw [sp_add_590_add_8 sp, sp_add_590_add_16 sp, sp_add_590_add_24 sp] at hsplit
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  rw [sepExists_sepConj_left]; apply ProofLib.Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left]; apply ProofLib.Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left]; apply ProofLib.Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left]; apply ProofLib.Entails.sepExists_elim; intro bs896
  refine Entails.sepExists_right bs (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
  exact Entails.of_eq (by ac_rfl)

theorem reassemble_chunkedStatesAt_190 (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    ((sp + 0x190#64) ↦₆₄ chunkedStatesWord0 st1) ∗
      ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
      ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st1) bs ⊢
      chunkedStatesAt A (sp + 0x190#64) st1 := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x190#64) st1, sp_add_190_add_8 sp]
  refine sepConj_mono_right ?_
  have h920 := words3_and_896_entails_pointsToBytes_920 (sp + 0x198#64) w1 w2 w3 hbs
  rw [sp_add_198_add_8 sp, sp_add_198_add_16 sp, sp_add_198_add_24 sp] at h920
  have hreord :
      ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
      ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st1) bs =
      (((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦ₛ bs896)) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st1) bs := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left h920) ?_
  exact relocatedHeap_recompose (fun dst => chunkedStatesTail920At A dst st1) bs (sp + 0x198#64)

theorem reassemble_590_after_memcpy (sp w1 w2 w3 : BitVec 64)
    {bs896 : List (BitVec 8)} (hlen896 : bs896.length = 896) :
    ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2) ∗
      ((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦ₛ bs896) ⊢
      memRegion (sp + 0x590#64) 920 := by
  have hm0 : ((sp + 0x590#64) ↦₆₄ w1) ⊢ memRegion (sp + 0x590#64) 8 := ProofLib.pointsTo64_entails_memRegion (sp + 0x590#64) w1
  have hm1 : ((sp + 0x598#64) ↦₆₄ w2) ⊢ memRegion (sp + 0x598#64) 8 := ProofLib.pointsTo64_entails_memRegion (sp + 0x598#64) w2
  have hm2 : ((sp + 0x5a0#64) ↦₆₄ w3) ⊢ memRegion (sp + 0x5a0#64) 8 := ProofLib.pointsTo64_entails_memRegion (sp + 0x5a0#64) w3
  have hm3 : ((sp + 0x5a8#64) ↦ₛ bs896) ⊢ memRegion (sp + 0x5a8#64) 896 := by
    rw [← hlen896]; exact pointsToBytes_entails_memRegion (sp + 0x5a8#64) bs896
  refine Entails.trans (sepConj_mono hm0 (sepConj_mono hm1 (sepConj_mono hm2 hm3))) ?_
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 8) (k := 912)
        (b' := sp + 0x598#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x598#64) (n := 8) (k := 904)
        (b' := sp + 0x5a0#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x5a0#64) (n := 8) (k := 896)
        (b' := sp + 0x5a8#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_580_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 0x580#64) 16 =
      (∃∗ d0 : BitVec 64, ((sp + 0x580#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x588#64) ↦₆₄ d1)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x580#64) (n := 8) (k := 8)
        (b' := sp + 0x588#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 0x580#64), ProofLib.memRegion_eight (sp + 0x588#64)]

theorem memRegion_1bc0_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 0x1bc0#64) 16 =
      (∃∗ d0 : BitVec 64, ((sp + 0x1bc0#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x1bc8#64) ↦₆₄ d1)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x1bc0#64) (n := 8) (k := 8)
        (b' := sp + 0x1bc8#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 0x1bc0#64), ProofLib.memRegion_eight (sp + 0x1bc8#64)]

/-- In `States.send`, `.ct1Ack b` only occurs with `b = true` (at `0x314d0`, `mov w8, #1; strb w8, [x9, #9]`). -/
def validSendPayload : MessagePayload spqrPolyApi → Prop
  | .ct1Ack b => b = true
  | _ => True

theorem x21_ne_noneCap_of_toNat_lt {x21 : BitVec 64} (h : x21.toNat < 2 ^ 63) :
    x21 ≠ LibsignalTripleRatchetRepr.noneCap := by
  intro heq; subst heq; revert h; decide

@[local arm64_norm, local wp_norm] theorem sp_add_568_add_4 (sp : BitVec 64) : (sp + 0x568#64) + 4#64 = sp + 0x56c#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_568_add_6 (sp : BitVec 64) : (sp + 0x568#64) + 6#64 = sp + 0x56e#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_568_add_8 (sp : BitVec 64) : (sp + 0x568#64) + 8#64 = sp + 0x570#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_568_add_10 (sp : BitVec 64) : (sp + 0x568#64) + 10#64 = sp + 0x572#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d92_add_4 (sp : BitVec 64) : (sp + 0x1d92#64) + 4#64 = sp + 0x1d96#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d92_add_6 (sp : BitVec 64) : (sp + 0x1d92#64) + 6#64 = sp + 0x1d98#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d92_add_8 (sp : BitVec 64) : (sp + 0x1d92#64) + 8#64 = sp + 0x1d9a#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm, local wp_norm] theorem sp_add_1d92_add_10 (sp : BitVec 64) : (sp + 0x1d92#64) + 10#64 = sp + 0x1d9c#64 := by rw [BitVec.add_assoc]; rfl

theorem unpack_tail14_eq (w3 : BitVec 64) (w4 : BitVec 16) (pad32 : BitVec 32) :
    unpack64 w3 ++ (unpack16 w4 ++ unpack32 pad32) =
      unpack32 (w3.extractLsb' 0 32) ++
        (unpack16 (w3.extractLsb' 32 16) ++ unpack64 (pad32 ++ w4 ++ w3.extractLsb' 48 16)) := by
  unfold unpack64 unpack32 unpack16
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits

theorem tail14_formA_eq_formB (a : BitVec 64) (w3 : BitVec 64) (w4 : BitVec 16) (pad32 : BitVec 32) :
    (a ↦₆₄ w3) ∗ ((a + 8#64) ↦₁₆ w4) ∗ ((a + 10#64) ↦₃₂ pad32) =
      (a ↦₃₂ w3.extractLsb' 0 32) ∗ ((a + 4#64) ↦₁₆ w3.extractLsb' 32 16) ∗
        ((a + 6#64) ↦₆₄ (pad32 ++ w4 ++ w3.extractLsb' 48 16)) := by
  have h1 : (a ↦₆₄ w3) ∗ ((a + 8#64) ↦₁₆ w4) ∗ ((a + 10#64) ↦₃₂ pad32) =
      (a ↦ₛ (unpack64 w3 ++ (unpack16 w4 ++ unpack32 pad32))) := by
    rw [pointsToBytes_append, unpack64_length, pointsToBytes_append, unpack16_length,
        ← pointsTo64_eq_pointsToBytes, ← pointsTo16_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
        show (a + BitVec.ofNat 64 8) + BitVec.ofNat 64 2 = a + 10#64 by bv_omega]
  have h2 : (a ↦₃₂ w3.extractLsb' 0 32) ∗ ((a + 4#64) ↦₁₆ w3.extractLsb' 32 16) ∗
      ((a + 6#64) ↦₆₄ (pad32 ++ w4 ++ w3.extractLsb' 48 16)) =
      (a ↦ₛ (unpack32 (w3.extractLsb' 0 32) ++
        (unpack16 (w3.extractLsb' 32 16) ++ unpack64 (pad32 ++ w4 ++ w3.extractLsb' 48 16)))) := by
    rw [pointsToBytes_append, unpack32_length, pointsToBytes_append, unpack16_length,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo16_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
        show (a + BitVec.ofNat 64 4) + BitVec.ofNat 64 2 = a + 6#64 by bv_omega]
  rw [h1, h2, unpack_tail14_eq]

def keyWordsDetached (A : RustAlloc) (x21 x27 : BitVec 64) (key : Option EpochSecret)
    (kw0 kw1 : BitVec 64) : SepProp :=
  match key with
  | none => ⌜x21 = noneCap⌝
  | some es =>
      ⌜x21 ≠ noneCap ∧ kw0 = BitVec.ofNat 64 es.secret.length ∧ kw1 = es.epoch⌝ ∗
        vecU8Heap A x21 x27 es.secret

theorem spqrSendKeySlotAt_entails_words (A : RustAlloc) (sp x21 x27 : BitVec 64)
    (key : Option EpochSecret) :
    spqrSendKeySlotAt A sp x21 x27 key ⊢
      ∃∗ kw0 : BitVec 64, ∃∗ kw1 : BitVec 64,
        ((sp + 0x580#64) ↦₆₄ kw0) ∗ ((sp + 0x588#64) ↦₆₄ kw1) ∗
        keyWordsDetached A x21 x27 key kw0 kw1 := by
  cases key with
  | none =>
    dsimp only [spqrSendKeySlotAt, keyWordsDetached]
    rw [memRegion_580_16_eq_words2 sp]
    apply Entails.pure_left; intro hx21
    rw [sepExists_sepConj_left]
    apply ProofLib.Entails.sepExists_elim; intro kw0
    rw [sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro kw1
    refine Entails.sepExists_right kw0 (Entails.sepExists_right kw1 ?_)
    exact Entails.trans (Entails.pure_right hx21 (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some es =>
    dsimp only [spqrSendKeySlotAt, keyWordsDetached]
    apply Entails.pure_left; intro hx21_lt
    have hne : x21 ≠ noneCap := x21_ne_noneCap_of_toNat_lt hx21_lt
    have hbuf : RustHeap.vecU8Buf A x21 x27 es.secret = vecU8Heap A x21 x27 es.secret := rfl
    have hp : x21 ≠ noneCap ∧ BitVec.ofNat 64 es.secret.length = BitVec.ofNat 64 es.secret.length ∧
        es.epoch = es.epoch := ⟨hne, rfl, rfl⟩
    rw [hbuf]
    refine Entails.sepExists_right (BitVec.ofNat 64 es.secret.length)
      (Entails.sepExists_right es.epoch ?_)
    exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem words_keyWordsDetached_entails_optEpochSecretRegSlotAt (A : RustAlloc) (sp x21 x27 : BitVec 64)
    (key : Option EpochSecret) (kw0 kw1 : BitVec 64) :
    ((sp + 0x1bc0#64) ↦₆₄ kw0) ∗ ((sp + 0x1bc8#64) ↦₆₄ kw1) ∗
      keyWordsDetached A x21 x27 key kw0 kw1 ⊢
      optEpochSecretRegSlotAt A sp x21 x27 key := by
  cases key with
  | none =>
    dsimp only [keyWordsDetached, optEpochSecretRegSlotAt]
    have hreord :
        ((sp + 0x1bc0#64) ↦₆₄ kw0) ∗ ((sp + 0x1bc8#64) ↦₆₄ kw1) ∗ ⌜x21 = noneCap⌝ =
        ⌜x21 = noneCap⌝ ∗ (((sp + 0x1bc0#64) ↦₆₄ kw0) ∗ ((sp + 0x1bc8#64) ↦₆₄ kw1)) := by ac_rfl
    rw [hreord]
    apply Entails.pure_left; intro hx21
    refine Entails.pure_right hx21 ?_
    rw [memRegion_1bc0_16_eq_words2 sp]
    exact sepConj_mono (Entails.sepExists_right kw0 (Entails.refl _))
      (Entails.sepExists_right kw1 (Entails.refl _))
  | some es =>
    dsimp only [keyWordsDetached, optEpochSecretRegSlotAt]
    have hreord :
        ((sp + 0x1bc0#64) ↦₆₄ kw0) ∗ ((sp + 0x1bc8#64) ↦₆₄ kw1) ∗
        ⌜x21 ≠ noneCap ∧ kw0 = BitVec.ofNat 64 es.secret.length ∧ kw1 = es.epoch⌝ ∗
        vecU8Heap A x21 x27 es.secret =
        ⌜x21 ≠ noneCap ∧ kw0 = BitVec.ofNat 64 es.secret.length ∧ kw1 = es.epoch⌝ ∗
        (((sp + 0x1bc0#64) ↦₆₄ kw0) ∗ ((sp + 0x1bc8#64) ↦₆₄ kw1) ∗
         vecU8Heap A x21 x27 es.secret) := by ac_rfl
    rw [hreord]
    apply Entails.pure_left; rintro ⟨hne, rfl, rfl⟩
    refine Entails.pure_right hne ?_
    exact Entails.of_eq (by ac_rfl)

def payloadTagByte : MessagePayload spqrPolyApi → BitVec 8
  | .none => 0#8
  | .hdr _ => 1#8
  | .ek _ => 2#8
  | .ekCt1Ack _ => 3#8
  | .ct1Ack _ => 4#8
  | .ct1 _ => 5#8
  | .ct2 _ => 6#8

def payloadWordsReconstruct (pay : MessagePayload spqrPolyApi)
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 16) : Prop :=
  match pay with
  | .none | .ct1Ack _ => True
  | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c =>
      ∀ a : BitVec 64,
        chunkAt a c =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₁₆ w4)

theorem spqrSendPayloadSlotAt_entails_words (sp : BitVec 64) (w24 : BitVec 8)
    (pay : MessagePayload spqrPolyApi) :
    spqrSendPayloadSlotAt sp w24 pay ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 16, ∃∗ pad32 : BitVec 32,
        ⌜w24 = payloadTagByte pay ∧ payloadWordsReconstruct pay w0 w1 w2 w3 w4⌝ ∗
        ((sp + 0x550#64) ↦₆₄ w0) ∗ ((sp + 0x558#64) ↦₆₄ w1) ∗
        ((sp + 0x560#64) ↦₆₄ w2) ∗ ((sp + 0x568#64) ↦₆₄ w3) ∗
        ((sp + 0x570#64) ↦₁₆ w4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) := by
  cases pay with
  | none | ct1Ack _ =>
    dsimp only [spqrSendPayloadSlotAt, payloadTagByte, payloadWordsReconstruct]
    rw [memRegion_38_eq_chunk_slot sp, ProofLib.memRegion_four (sp + 0x572#64)]
    apply Entails.pure_left; intro hw24
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro pad32
    apply ProofLib.Entails.sepExists_elim; intro w4
    apply ProofLib.Entails.sepExists_elim; intro w3
    apply ProofLib.Entails.sepExists_elim; intro w2
    apply ProofLib.Entails.sepExists_elim; intro w1
    apply ProofLib.Entails.sepExists_elim; intro w0
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right pad32 ?_)))))
    exact Entails.pure_right ⟨hw24, trivial⟩ (Entails.of_eq (by ac_rfl))
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    dsimp only [spqrSendPayloadSlotAt, payloadTagByte, payloadWordsReconstruct]
    obtain ⟨w0, w1, w2, w3, hchunk⟩ := chunkAt_extract_words c
    have hc550 := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 c w0 w1 w2 w3 hchunk
    rw [hc550, ProofLib.memRegion_four (sp + 0x572#64)]
    apply Entails.pure_left; intro hw24
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro pad32
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right c.index (Entails.sepExists_right pad32 ?_)))))
    exact Entails.pure_right ⟨hw24, hchunk⟩ (Entails.of_eq (by ac_rfl))

theorem words_to_memRegion_38 (a w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 16) (pad32 : BitVec 32) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
      ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₁₆ w4) ∗ ((a + 34#64) ↦₃₂ pad32) ⊢
      memRegion a 38 := by
  have hm0 : (a ↦₆₄ w0) ⊢ memRegion a 8 := ProofLib.pointsTo64_entails_memRegion a w0
  have hm1 : ((a + 8#64) ↦₆₄ w1) ⊢ memRegion (a + 8#64) 8 := ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1
  have hm2 : ((a + 16#64) ↦₆₄ w2) ⊢ memRegion (a + 16#64) 8 := ProofLib.pointsTo64_entails_memRegion (a + 16#64) w2
  have hm3 : ((a + 24#64) ↦₆₄ w3) ⊢ memRegion (a + 24#64) 8 := ProofLib.pointsTo64_entails_memRegion (a + 24#64) w3
  have hm4 : ((a + 32#64) ↦₁₆ w4) ⊢ memRegion (a + 32#64) 2 := by
    rw [pointsTo16_eq_pointsToBytes, ← unpack16_length w4]; exact pointsToBytes_entails_memRegion _ _
  have hm5 : ((a + 34#64) ↦₃₂ pad32) ⊢ memRegion (a + 34#64) 4 := ProofLib.pointsTo32_entails_memRegion (a + 34#64) pad32
  refine Entails.trans (sepConj_mono hm0 (sepConj_mono hm1 (sepConj_mono hm2
    (sepConj_mono hm3 (sepConj_mono hm4 hm5))))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 30) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 22) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 14) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 6) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 2) (k := 4) (b' := a + 34#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_1d70_48_split (sp : BitVec 64) :
    memRegion (sp + 0x1d70#64) 48 =
      (∃∗ d_ep : BitVec 64, (sp + 0x1d70#64) ↦₆₄ d_ep) ∗
      (∃∗ d_tag : BitVec 8, (sp + 0x1d78#64) ↦₈ d_tag) ∗
      (∃∗ d_b9 : BitVec 8, (sp + 0x1d79#64) ↦₈ d_b9) ∗
      (∃∗ d_w0 : BitVec 64, (sp + 0x1d7a#64) ↦₆₄ d_w0) ∗
      (∃∗ d_w1 : BitVec 64, (sp + 0x1d82#64) ↦₆₄ d_w1) ∗
      (∃∗ d_w2 : BitVec 64, (sp + 0x1d8a#64) ↦₆₄ d_w2) ∗
      (∃∗ d_w3 : BitVec 64, (sp + 0x1d92#64) ↦₆₄ d_w3) ∗
      (∃∗ d_w4 : BitVec 16, (sp + 0x1d9a#64) ↦₁₆ d_w4) ∗
      (∃∗ d_pad32 : BitVec 32, (sp + 0x1d9c#64) ↦₃₂ d_pad32) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x1d70#64) (n := 8) (k := 40) (b' := sp + 0x1d78#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d78#64) (n := 1) (k := 39) (b' := sp + 0x1d79#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d79#64) (n := 1) (k := 38) (b' := sp + 0x1d7a#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d7a#64) (n := 8) (k := 30) (b' := sp + 0x1d82#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d82#64) (n := 8) (k := 22) (b' := sp + 0x1d8a#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d8a#64) (n := 8) (k := 14) (b' := sp + 0x1d92#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d92#64) (n := 8) (k := 6) (b' := sp + 0x1d9a#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1d9a#64) (n := 2) (k := 4) (b' := sp + 0x1d9c#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 0x1d70#64),
      ProofLib.memRegion_one (sp + 0x1d78#64),
      ProofLib.memRegion_one (sp + 0x1d79#64),
      ProofLib.memRegion_eight (sp + 0x1d7a#64),
      ProofLib.memRegion_eight (sp + 0x1d82#64),
      ProofLib.memRegion_eight (sp + 0x1d8a#64),
      ProofLib.memRegion_eight (sp + 0x1d92#64),
      ProofLib.memRegion_two (sp + 0x1d9a#64),
      ProofLib.memRegion_four (sp + 0x1d9c#64)]

theorem words_entails_messageAt_1d70 (sp : BitVec 64) (msg : Message spqrPolyApi)
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 16) (pad32 : BitVec 32)
    (hvalid : validSendPayload msg.payload)
    (hrec : payloadWordsReconstruct msg.payload w0 w1 w2 w3 w4) :
    ((sp + 0x1d70#64) ↦₆₄ msg.epoch) ∗
      ((sp + 0x1d78#64) ↦₈ payloadTagByte msg.payload) ∗
      ((sp + 0x1d79#64) ↦₈ 1#8) ∗
      ((sp + 0x1d7a#64) ↦₆₄ w0) ∗ ((sp + 0x1d82#64) ↦₆₄ w1) ∗
      ((sp + 0x1d8a#64) ↦₆₄ w2) ∗ ((sp + 0x1d92#64) ↦₆₄ w3) ∗
      ((sp + 0x1d9a#64) ↦₁₆ w4) ∗ ((sp + 0x1d9c#64) ↦₃₂ pad32) ⊢
      messageAt spqrPolyApi (sp + 0x1d70#64) msg := by
  rcases msg with ⟨epoch, pay⟩
  unfold messageAt
  dsimp only
  refine sepConj_mono_right ?_
  have h38 :
      ((sp + 0x1d7a#64) ↦₆₄ w0) ∗ ((sp + 0x1d82#64) ↦₆₄ w1) ∗
        ((sp + 0x1d8a#64) ↦₆₄ w2) ∗ ((sp + 0x1d92#64) ↦₆₄ w3) ∗
        ((sp + 0x1d9a#64) ↦₁₆ w4) ∗ ((sp + 0x1d9c#64) ↦₃₂ pad32) ⊢
        memRegion (sp + 0x1d7a#64) 38 := by
    have h := words_to_memRegion_38 (sp + 0x1d7a#64) w0 w1 w2 w3 w4 pad32
    rwa [show (sp + 0x1d7a#64) + 8#64 = sp + 0x1d82#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x1d7a#64) + 16#64 = sp + 0x1d8a#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x1d7a#64) + 24#64 = sp + 0x1d92#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x1d7a#64) + 32#64 = sp + 0x1d9a#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x1d7a#64) + 34#64 = sp + 0x1d9c#64 by rw [BitVec.add_assoc]; rfl] at h
  have hm1 : ((sp + 0x1d79#64) ↦₈ 1#8) ⊢ memRegion (sp + 0x1d79#64) 1 :=
    ProofLib.pointsTo8_entails_memRegion (sp + 0x1d79#64) 1#8
  have hm4 : ((sp + 0x1d9c#64) ↦₃₂ pad32) ⊢ memRegion (sp + 0x1d9c#64) 4 :=
    ProofLib.pointsTo32_entails_memRegion (sp + 0x1d9c#64) pad32
  cases pay with
  | none =>
    dsimp only [messagePayloadAt, payloadTagByte]
    rw [sp_add_1d70_add_8 sp,
        show (sp + 0x1d70#64) + 0x09#64 = sp + 0x1d79#64 by rw [BitVec.add_assoc]; rfl,
        ProofLib.memRegion_split' (b := sp + 0x1d79#64) (n := 1) (k := 38)
          (b' := sp + 0x1d7a#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    exact sepConj_mono_right (sepConj_mono hm1 h38)
  | ct1Ack b =>
    dsimp only [validSendPayload] at hvalid
    subst hvalid
    dsimp only [messagePayloadAt, payloadTagByte, ↓reduceIte]
    rw [sp_add_1d70_add_8 sp, sp_add_1d70_add_9 sp, sp_add_1d70_add_10 sp]
    exact sepConj_mono_right (sepConj_mono_right h38)
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    rcases c with ⟨idx, dat⟩
    dsimp only [payloadWordsReconstruct] at hrec
    dsimp only [messagePayloadAt, payloadTagByte, spqrPolyApi]
    rw [sp_add_1d70_add_8 sp, sp_add_1d70_add_9 sp, sp_add_1d70_add_10 sp,
        show (sp + 0x1d70#64) + 0x2c#64 = sp + 0x1d9c#64 by rw [BitVec.add_assoc]; rfl,
        hrec (sp + 0x1d7a#64),
        show (sp + 0x1d7a#64) + 8#64 = sp + 0x1d82#64 by rw [BitVec.add_assoc]; rfl,
        show (sp + 0x1d7a#64) + 16#64 = sp + 0x1d8a#64 by rw [BitVec.add_assoc]; rfl,
        show (sp + 0x1d7a#64) + 24#64 = sp + 0x1d92#64 by rw [BitVec.add_assoc]; rfl,
        show (sp + 0x1d7a#64) + 32#64 = sp + 0x1d9a#64 by rw [BitVec.add_assoc]; rfl]
    simp only [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono hm1 (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm4))))))

theorem memRegion_190_928_split (sp : BitVec 64) :
    memRegion (sp + 0x190#64) 928 =
      (∃∗ d0 : BitVec 64, (sp + 0x190#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 0x198#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 0x1a0#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp + 0x1a8#64) ↦₆₄ d3) ∗
      memRegion (sp + 0x1b0#64) 896 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x190#64) (n := 8) (k := 920) (b' := sp + 0x198#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x198#64) (n := 8) (k := 912) (b' := sp + 0x1a0#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1a0#64) (n := 8) (k := 904) (b' := sp + 0x1a8#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1a8#64) (n := 8) (k := 896) (b' := sp + 0x1b0#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 0x190#64), ProofLib.memRegion_eight (sp + 0x198#64),
      ProofLib.memRegion_eight (sp + 0x1a0#64), ProofLib.memRegion_eight (sp + 0x1a8#64)]

theorem memRegion_530_24_split (sp : BitVec 64) :
    memRegion (sp + 0x530#64) 24 =
      (∃∗ d0 : BitVec 64, (sp + 0x530#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 0x538#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 0x540#64) ↦₆₄ d2) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x530#64) (n := 8) (k := 16) (b' := sp + 0x538#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x538#64) (n := 8) (k := 8) (b' := sp + 0x540#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 0x530#64), ProofLib.memRegion_eight (sp + 0x538#64),
      ProofLib.memRegion_eight (sp + 0x540#64)]

theorem words3_to_memRegion_530_24 (sp w0 w1 w2 : BitVec 64) :
    ((sp + 0x530#64) ↦₆₄ w0) ∗ ((sp + 0x538#64) ↦₆₄ w1) ∗ ((sp + 0x540#64) ↦₆₄ w2) ⊢
      memRegion (sp + 0x530#64) 24 := by
  rw [memRegion_530_24_split sp]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem words2_to_memRegion_580_16 (sp w0 w1 : BitVec 64) :
    ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ⊢
      memRegion (sp + 0x580#64) 16 := by
  rw [memRegion_580_16_eq_words2 sp]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (Entails.sepExists_right w1 (Entails.refl _))

def optChainPBWord0 (g : ChainFrom.ChainPBGhost) : Option ChainPB → BitVec 64
  | none => noneCap
  | some _ => g.linksCap

def optChainPBRestAt (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (a : BitVec 64) :
    Option ChainPB → SepProp
  | none => memRegion (a + 8#64) 72
  | some pb =>
      ⌜g.epochs.length = pb.links.length⌝ ∗
        ((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        vecBuf A chainEpochSize chainEpochAlign (ChainFrom.chainEpochPBAt A)
          g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
        vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
        ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
        ChainFromVersionNegotiation.optChainParamsPBAt (a + 0x40#64) pb.params ∗
        ((a + 0x4c#64) ↦₃₂ pb.direction)

theorem optChainPBAt_eq_word0_rest (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (a : BitVec 64)
    (chain : Option ChainPB) :
    ChainFrom.optChainPBAt A g a chain =
      (a ↦₆₄ optChainPBWord0 g chain) ∗ optChainPBRestAt A g a chain := by
  cases chain with
  | none => rfl
  | some pb =>
    dsimp only [ChainFrom.optChainPBAt, ChainFrom.chainPBAt, vecAt, vecHeader,
      optChainPBWord0, optChainPBRestAt]
    ac_rfl

theorem optChainPBRestAt_expose_word0_inv (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (a : BitVec 64)
    (chain : Option ChainPB) :
    optChainPBRestAt A g a chain ⊢
      ⌜(optChainPBWord0 g chain = noneCap ↔ chain = none)⌝ ∗
        optChainPBRestAt A g a chain := by
  cases chain with
  | none =>
    exact Entails.pure_right ⟨fun _ => rfl, fun _ => rfl⟩ (Entails.refl _)
  | some pb =>
    dsimp only [optChainPBRestAt, optChainPBWord0, vecBuf, chainEpochSize]
    apply Entails.pure_left; intro hlen
    have hreord :
        ((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        (⌜(g.epochs.zip pb.links).length ≤ g.linksCap.toNat ∧ g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0⌝ ∗
          if g.linksCap = 0 then emp
          else
            A.live g.linksPtr (g.linksCap.toNat * 112) chainEpochAlign ∗
              arrayAt (ChainFrom.chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
              memRegion (g.linksPtr + BitVec.ofNat 64 ((g.epochs.zip pb.links).length * 112))
                ((g.linksCap.toNat - (g.epochs.zip pb.links).length) * 112)) ∗
        vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
        ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
        ChainFromVersionNegotiation.optChainParamsPBAt (a + 0x40#64) pb.params ∗
        ((a + 0x4c#64) ↦₃₂ pb.direction) =
        ⌜(g.epochs.zip pb.links).length ≤ g.linksCap.toNat ∧ g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0⌝ ∗
        (((a + 8#64) ↦₆₄ g.linksPtr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
         (if g.linksCap = 0 then emp
          else
            A.live g.linksPtr (g.linksCap.toNat * 112) chainEpochAlign ∗
              arrayAt (ChainFrom.chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip pb.links) ∗
              memRegion (g.linksPtr + BitVec.ofNat 64 ((g.epochs.zip pb.links).length * 112))
                ((g.linksCap.toNat - (g.epochs.zip pb.links).length) * 112)) ∗
         vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
         ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
         ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
         ChainFromVersionNegotiation.optChainParamsPBAt (a + 0x40#64) pb.params ∗
         ((a + 0x4c#64) ↦₃₂ pb.direction)) := by ac_rfl
    rw [hreord]
    apply Entails.pure_left; intro hpure
    have hlt : g.linksCap.toNat < 2 ^ 63 := by omega
    have hne : g.linksCap ≠ noneCap := x21_ne_noneCap_of_toNat_lt hlt
    have hiff : g.linksCap = noneCap ↔ some pb = none :=
      ⟨fun h => False.elim (hne h), fun h => nomatch h⟩
    refine Entails.pure_right hiff (Entails.pure_right hlen ?_)
    exact Entails.pure_right hpure (Entails.refl _)

/-! ## Shared Post-Arm Reassembly Epilogue (`0x31458..0x314d8`, `+3068..+3196`) -/

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-- Framed `memcpy` call rule for an explicit byte slice `src ↦ₛ bs`. -/
theorem call_memcpy_bytes {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.2.2

/-- Shared post-`States::send` reassembly epilogue (`0x31458 -> 0x314d8`, offsets `3068..3196`):
    - Relocates `chunkedStatesTail920At A (sp + 0x590#64) st1` and `x20 = chunkedStatesWord0 st1`
      into `chunkedStatesAt A (sp + 0x190#64) st1` (leaving `memRegion (sp + 0x590#64) 920` and
      `memRegion (sp + 0x530#64) 24`),
    - Moves `spqrSendKeySlotAt A sp x21 x27 key` (`sp + 0x580..0x590`) into
      `optEpochSecretRegSlotAt A sp x21 x27 key` (`sp + 0x1bc0..0x1bd0`),
    - Moves `spqrSendPayloadSlotAt sp w24 msg.payload` (`sp + 0x550..0x576`) and `x22 = msg.epoch`
      into `messageAt spqrPolyApi (sp + 0x1d70#64) msg`,
    - Loads `x23` from `[sp + 0x60]` (`ProtoRepr.optChainPBAt A (sp + 0x60#64) chain`) and executes
      `cmn x23, #0x1`, setting `sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64`. -/
theorem step_send_post_arm_3068_to_3196 {F : ShaCompress}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) {s0 s : State} (sp : BitVec 64)
    (chain : Option ChainPB) (msg : Message spqrPolyApi) (key : Option EpochSecret)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (hvalid : validSendPayload msg.payload)
    (hjoin : SpqrSendJoinState img.base sp ext s0 s msg st1)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hP : P = (ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      spqrSendPayloadSlotAt sp ((s.readReg64 .x24).setWidth 8) msg.payload ∗
      spqrSendKeySlotAt A sp (s.readReg64 .x21) (s.readReg64 .x27) key ∗
      chunkedStatesTail920At A (sp + 0x590#64) st1 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48) ∗ Frame)
    (hnext : ∀ sf : State, ImgCallInv img sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = msg.epoch →
      sf.readReg64 .x25 = sp + 0x550#64 → sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s0.readReg64 .x28 →
      (sf.readReg64 .x23 = noneCap ↔ chain = none) →
      sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
          chunkedStatesAt A (sp + 0x190#64) st1 ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          optEpochSecretRegSlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) msg) ∗ Frame) post panicPost) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post panicPost := by
  have hmemcpy := spqrSend_memcpy_ok hA
  rcases hjoin with ⟨hpc, hrun, hsp, htr, hx19, hx20, hx22, hx25, hx26, hx28, hvregs⟩
  spqr_send_fetches_range img.base (Rust.withPanics ext) 3068 128
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  apply of_sepWP_inImage (mid := entry + 3196#64) img hinv
  rw [ChainFrom.optChainPBAt_protoRepr_eq_exists A (sp + 0x60#64) chain]
  simp only [sepExists_sepConj_left]; apply SepWP.exists_elim; intro gChain
  rw [optChainPBAt_eq_word0_rest A gChain (sp + 0x60#64) chain]
  refine SepWP.focus_weaken (optChainPBRestAt_expose_word0_inv A gChain (sp + 0x60#64) chain) (by sep_focus) ?_
  wp_focus_pure; intro hchain_iff
  refine SepWP.focus_weaken (chunkedStatesTail920At_590_entails_reloc A sp st1) (by sep_focus) ?_
  wp_pull_exists; rename_i bs920 sw1 sw2 sw3 bs896
  wp_focus_pure; rintro ⟨hbs920, hlen896⟩
  refine SepWP.focus_weaken (spqrSendPayloadSlotAt_entails_words sp ((s.readReg64 .x24).setWidth 8) msg.payload) (by sep_focus) ?_
  wp_pull_exists; rename_i pw0 pw1 pw2 pw3 pw4 pad32
  wp_focus_pure; rintro ⟨hw24, hpay_rec⟩
  refine SepWP.focus_weaken (spqrSendKeySlotAt_entails_words A sp (s.readReg64 .x21) (s.readReg64 .x27) key) (by sep_focus) ?_
  wp_pull_exists; rename_i kw0 kw1
  rw [memRegion_190_928_split sp, memRegion_530_24_split sp,
      memRegion_1bc0_16_eq_words2 sp, memRegion_1d70_48_split sp]
  wp_pull_exists; wp_steps
  refine call_memcpy_bytes hmemcpy (sp + 0x1b0#64) (sp + 0x5a8#64) hlen896
    (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x60#64) ↦₆₄ optChainPBWord0 gChain chain) ∗
      optChainPBRestAt A gChain (sp + 0x60#64) chain ∗
      ((sp + 0x190#64) ↦₆₄ _) ∗ ((sp + 0x198#64) ↦₆₄ _) ∗ ((sp + 0x1a0#64) ↦₆₄ _) ∗ ((sp + 0x1a8#64) ↦₆₄ _) ∗
      ((sp + 0x530#64) ↦₆₄ sw1) ∗ ((sp + 0x538#64) ↦₆₄ sw2) ∗ ((sp + 0x540#64) ↦₆₄ sw3) ∗
      ((sp + 0x550#64) ↦₆₄ pw0) ∗ ((sp + 0x558#64) ↦₆₄ pw1) ∗ ((sp + 0x560#64) ↦₆₄ pw2) ∗ ((sp + 0x568#64) ↦₆₄ pw3) ∗
      ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ∗ ((sp + 0x580#64) ↦₆₄ kw0) ∗ ((sp + 0x588#64) ↦₆₄ kw1) ∗
      keyWordsDetached A (s.readReg64 .x21) (s.readReg64 .x27) key kw0 kw1 ∗
      ((sp + 0x590#64) ↦₆₄ sw1) ∗ ((sp + 0x598#64) ↦₆₄ sw2) ∗ ((sp + 0x5a0#64) ↦₆₄ sw3) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st1) bs920 ∗
      ((sp + 0x1bc0#64) ↦₆₄ _) ∗ ((sp + 0x1bc8#64) ↦₆₄ _) ∗ ((sp + 0x1d70#64) ↦₆₄ _) ∗ ((sp + 0x1d78#64) ↦₈ _) ∗
      ((sp + 0x1d79#64) ↦₈ _) ∗ ((sp + 0x1d7a#64) ↦₆₄ _) ∗ ((sp + 0x1d82#64) ↦₆₄ _) ∗ ((sp + 0x1d8a#64) ↦₆₄ _) ∗
      ((sp + 0x1d92#64) ↦₆₄ _) ∗ ((sp + 0x1d9a#64) ↦₁₆ _) ∗ ((sp + 0x1d9c#64) ↦₃₂ _) ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 3108#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sm hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx21_m hx22_m _ hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  simp only [arm64_norm, *] at hx19_m hx20_m hx21_m hx22_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  wp_steps
  have h568_to_B :
      ((sp + 0x568#64) ↦₆₄ pw3) ∗ ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ⊢
      ((sp + 0x568#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x56c#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x56e#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) := by
    have h := tail14_formA_eq_formB (sp + 0x568#64) pw3 pw4 pad32
    rw [sp_add_568_add_4 sp, sp_add_568_add_6 sp, sp_add_568_add_8 sp, sp_add_568_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken h568_to_B (by sep_focus) ?_; wp_steps
  have h1d92_to_B (dw4 : BitVec 16) (dpad32 : BitVec 32) :
      ((sp + 0x1d92#64) ↦₆₄ pw3) ∗ ((sp + 0x1d9a#64) ↦₁₆ dw4) ∗ ((sp + 0x1d9c#64) ↦₃₂ dpad32) ⊢
      ((sp + 0x1d92#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x1d96#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x1d98#64) ↦₆₄ (dpad32 ++ dw4 ++ pw3.extractLsb' 48 16)) := by
    have h := tail14_formA_eq_formB (sp + 0x1d92#64) pw3 dw4 dpad32
    rw [sp_add_1d92_add_4 sp, sp_add_1d92_add_6 sp, sp_add_1d92_add_8 sp, sp_add_1d92_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken (h1d92_to_B _ _) (by sep_focus) ?_; wp_steps
  have h568_to_A :
      ((sp + 0x568#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x56c#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x56e#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) ⊢
      ((sp + 0x568#64) ↦₆₄ pw3) ∗ ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) := by
    have h := (tail14_formA_eq_formB (sp + 0x568#64) pw3 pw4 pad32).symm
    rw [sp_add_568_add_4 sp, sp_add_568_add_6 sp, sp_add_568_add_8 sp, sp_add_568_add_10 sp] at h
    exact Entails.of_eq h
  have h1d92_to_A :
      ((sp + 0x1d92#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x1d96#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x1d98#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) ⊢
      ((sp + 0x1d92#64) ↦₆₄ pw3) ∗ ((sp + 0x1d9a#64) ↦₁₆ pw4) ∗ ((sp + 0x1d9c#64) ↦₃₂ pad32) := by
    have h := (tail14_formA_eq_formB (sp + 0x1d92#64) pw3 pw4 pad32).symm
    rw [sp_add_1d92_add_4 sp, sp_add_1d92_add_6 sp, sp_add_1d92_add_8 sp, sp_add_1d92_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken h568_to_A (by sep_focus) ?_
  refine SepWP.focus_weaken h1d92_to_A (by sep_focus) ?_
  have h550_38 :
      ((sp + 0x550#64) ↦₆₄ pw0) ∗ ((sp + 0x558#64) ↦₆₄ pw1) ∗
      ((sp + 0x560#64) ↦₆₄ pw2) ∗ ((sp + 0x568#64) ↦₆₄ pw3) ∗
      ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ⊢
      memRegion (sp + 0x550#64) 38 := by
    have h := words_to_memRegion_38 (sp + 0x550#64) pw0 pw1 pw2 pw3 pw4 pad32
    rwa [sp_add_550_add_8 sp,
         show (sp + 0x550#64) + 16#64 = sp + 0x560#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 24#64 = sp + 0x568#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 32#64 = sp + 0x570#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 34#64 = sp + 0x572#64 by rw [BitVec.add_assoc]; rfl] at h
  have hchain_recompose :
      ((sp + 0x60#64) ↦₆₄ optChainPBWord0 gChain chain) ∗
      optChainPBRestAt A gChain (sp + 0x60#64) chain ⊢
      ProtoRepr.optChainPBAt A (sp + 0x60#64) chain := by
    rw [← optChainPBAt_eq_word0_rest A gChain (sp + 0x60#64) chain]
    exact ChainFrom.optChainPBAt_entails_protoRepr A gChain (sp + 0x60#64) chain
  refine SepWP.focus_weaken hchain_recompose (by sep_focus) ?_
  refine SepWP.focus_weaken (reassemble_chunkedStatesAt_190 A sp st1 sw1 sw2 sw3 hbs920) (by sep_focus) ?_
  refine SepWP.focus_weaken (words3_to_memRegion_530_24 sp sw1 sw2 sw3) (by sep_focus) ?_
  refine SepWP.focus_weaken h550_38 (by sep_focus) ?_
  refine SepWP.focus_weaken (words2_to_memRegion_580_16 sp kw0 kw1) (by sep_focus) ?_
  refine SepWP.focus_weaken (reassemble_590_after_memcpy sp sw1 sw2 sw3 hlen896) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (words_keyWordsDetached_entails_optEpochSecretRegSlotAt A sp (s.readReg64 .x21) (s.readReg64 .x27) key kw0 kw1)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (words_entails_messageAt_1d70 sp msg pw0 pw1 pw2 pw3 pw4 pad32 hvalid hpay_rec) (by sep_focus) ?_
  refine finish_sepWP_inImage (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hinv_f => ?_) (Entails.refl _)
  refine SepWPp.mono_pre' ?_ (hnext _ hinv_f
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]))
  simp only [arm64_norm, *]; exact Entails.of_eq (by ac_rfl)

/-! ## Unified 11-Arm `<States>::send` Dispatch (`statesSendArmOffset st0 -> +3196`) -/

private theorem tapeAt_entails_tapeAfter_same (a cur : BitVec 64) (tape : List (BitVec 8)) :
    tapeAt a cur tape ⊢ tapeAfter a cur tape (tape.length - tape.length) := by
  rw [Nat.sub_self]; unfold tapeAt tapeAfter; rw [BitVec.add_zero, Nat.sub_zero]
  exact Entails.pure_left fun _ => Entails.refl _

private theorem memRegion_190_928_eq (sp : BitVec 64) :
    memRegion (sp + 0x190#64) 928 = memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1320#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 400#64) (n := 920) (k := 8)
    (b' := sp + 1320#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

private theorem memRegion_4080_104_eq (sp : BitVec 64) :
    memRegion (sp + 4080#64) 104 = memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 4128#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 4080#64) (n := 48) (k := 56)
    (b' := sp + 4128#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

private theorem memRegion_4192_504_eq (sp : BitVec 64) :
    memRegion (sp + 4192#64) 504 = memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4640#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 4192#64) (n := 448) (k := 56)
    (b' := sp + 4640#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

private theorem memRegion_1260_2400_split (sp : BitVec 64) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide) :
    memRegion (sp + 0x1260#64) 2400 =
      memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
      memRegion (sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize)) (2400 - (sz + chunkSize)) :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := sz + chunkSize) (k := 2400 - (sz + chunkSize))
    (b' := sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize))
    (by change 2400 = sz + 34 + (2400 - (sz + 34)); have : sz + 34 ≤ 2400 := hsz; omega) rfl (by omega)

private theorem memRegion_7104_24_eq (sp : BitVec 64) :
    memRegion (sp + 7104#64) 24 = memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7120#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 0x1bc0#64) (n := 16) (k := 8)
    (b' := sp + 7120#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

private theorem memRegion_7536_400_eq (sp : BitVec 64) :
    memRegion (sp + 7536#64) 400 = memRegion (sp + 0x1d70#64) 48 ∗ memRegion (sp + 7584#64) 352 :=
  ProofLib.memRegion_split' (b := sp + 0x1d70#64) (n := 48) (k := 352)
    (b' := sp + 7584#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

/-- Scratch slots in `[sp + 0xde0, sp + 0x1f00)` untouched after `+3068`,
    excluding `sp + 0x1bc0..0x1bd0` (16B) and `sp + 0x1d70..0x1da0` (48B). -/
def statesSendPostArmScratch (sp : BitVec 64) : SepProp :=
  memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 0x1260#64) 2400 ∗
  memRegion (sp + 7120#64) 8 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7584#64) 352

/-- Pre-arm scratch slots in `[sp + 0x20, sp + 0x30)` and `[sp + 0xde0, sp + 0x1f00)`. -/
def statesSendPreArmScratch (sp : BitVec 64) : SepProp :=
  memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 0x1260#64) 2400 ∗
  memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400

private theorem statesSendPreArmScratch_eq_post (sp : BitVec 64) :
    statesSendPreArmScratch sp = memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗ statesSendPostArmScratch sp := by
  unfold statesSendPreArmScratch statesSendPostArmScratch; rw [memRegion_7104_24_eq sp, memRegion_7536_400_eq sp]; ac_rfl

private def statesSendLeafScratchRest (sp : BitVec 64) (sz : Nat) : SepProp :=
  memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 4192#64) 504 ∗
  memRegion (sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize)) (2400 - (sz + chunkSize)) ∗
  memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400

private theorem statesSendPreArmScratch_eq_leaf (sp : BitVec 64) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide) :
    statesSendPreArmScratch sp = memRegion (sp + 0x1260#64) (sz + chunkSize) ∗ statesSendLeafScratchRest sp sz := by
  unfold statesSendPreArmScratch statesSendLeafScratchRest; rw [memRegion_1260_2400_split sp sz hsz]; ac_rfl

private def statesSendLeafFrame {ctl : BitVec 64} (b : BitVec 64) (A : RustAlloc) (sp cur : BitVec 64)
    (tape : List (BitVec 8)) (chain : Option ChainPB) (sz : Nat) (Frame : SepProp) : SepProp :=
  spqrLogLevelZeroAt b ∗ tapeAt ctl cur tape ∗ ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
  memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗ statesSendLeafScratchRest sp sz ∗ Frame

private def statesSendImmFrame {ctl : BitVec 64} (b : BitVec 64) (A : RustAlloc) (sp cur : BitVec 64)
    (tape : List (BitVec 8)) (chain : Option ChainPB) (Frame : SepProp) : SepProp :=
  stackAt sp spqrSendCalleeStack ∗ A.pool ∗ GF.Mul2U16.tokenInitAt b ∗ GF.UnacceleratedMul.reduceTableAt b ∗ spqrLogLevelZeroAt b ∗
  tapeAt ctl cur tape ∗ ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
  memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗ statesSendPreArmScratch sp ∗ Frame

/-- Continuation contract at `+3196` (`0x314d8`) after `<States>::send` and post-arm reassembly. -/
abbrev SpqrSendAt3196 {F : ShaCompress} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (s0 : State) (sp cur : BitVec 64) (tape tape' : List (BitVec 8)) (chain : Option ChainPB) (key : Option EpochSecret)
    (msg : Message spqrPolyApi) (st1 : States spqrPolyApi (spqrAuthApi F))
    (ret : BitVec 64) (Frame Fr : SepProp) (post : State → SepProp → Prop) : Prop :=
  ∀ sf : State, ImgCallInv img sf → sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64 →
    sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
    sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
    sf.readReg64 .x22 = msg.epoch → sf.readReg64 .x25 = sp + 0x550#64 →
    sf.readReg64 .x26 = sp + 0x1260#64 → sf.readReg64 .x28 = s0.readReg64 .x28 →
    (sf.readReg64 .x23 = noneCap ↔ chain = none) → sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
      ((ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗ chunkedStatesAt A (sp + 0x190#64) st1 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
        memRegion (sp + 0x950#64) 928 ∗ optEpochSecretRegSlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ statesSendPostArmScratch sp ∗
        tapeAfter ctl cur tape (tape.length - tape'.length) ∗ GF.Mul2U16.tokenInitAt img.base ∗
        GF.UnacceleratedMul.reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))

/-- Shared continuation from `+3068` (`0x31458`) to `+3196` (`0x314d8`) after any of the 11 arms. -/
theorem step_send_post_arm_cont {F : ShaCompress} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) (hA : AllocContracts img.base A ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape tape' : List (BitVec 8)) (chain : Option ChainPB) (key : Option EpochSecret)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinState img.base sp ext s0 s1 msg st1) (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) {ret : BitVec 64} {P0 Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv1 : ImgCallInv img s1)
    (hP0 : P0 ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ GF.Mul2U16.tokenInitAt img.base ∗
        GF.UnacceleratedMul.reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗
        tapeAfter ctl cur tape (tape.length - tape'.length) ∗ ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A sp (s1.readReg64 .x21) (s1.readReg64 .x27) key ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1 ∗ statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196 (ctl := ctl) img A ext s0 sp cur tape tape' chain key msg st1 ret Frame Fr post) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s1 P0 post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.mono_pre' hP0 ?_; rw [statesSendPreArmScratch_eq_post sp]
  refine step_send_post_arm_3068_to_3196 img A ext hA sp chain msg key st1 hvalid hjoin1 hsp_align hinv1
    (Frame := memRegion (sp + 0x950#64) 928 ∗ statesSendPostArmScratch sp ∗ tapeAfter ctl cur tape (tape.length - tape'.length) ∗
      GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    (by ac_rfl) ?_
  intro sf hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f _ hx22_f hx25_f hx26_f _ hx28_f hx23_none hz_f hvregs_f
  refine SepWPp.mono_pre' ?_
    (hnext sf hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f)
  exact Entails.of_eq (by ac_rfl)

private theorem step_send_post_arm_cont_leaf {F : ShaCompress} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) {s0 s1 : State} (sp cur : BitVec 64) (tape : List (BitVec 8))
    (chain : Option ChainPB) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinState img.base sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {Frame Fr : SepProp} {post : State → SepProp → Prop} (hinv1 : ImgCallInv img s1)
    (hnext : SpqrSendAt3196 (ctl := ctl) img A ext s0 sp cur tape tape chain none msg st1 ret Frame Fr post) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
      ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A sp (s1.readReg64 .x21) (s1.readReg64 .x27) none ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1) ∗
       statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain sz Frame) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine step_send_post_arm_cont (ctl := ctl) img A ext hA sp cur tape tape chain none hjoin1 hvalid hsp_align hinv1 ?_ hnext
  unfold statesSendLeafFrame; rw [statesSendPreArmScratch_eq_leaf sp sz hsz]
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (tapeAt_entails_tapeAfter_same _ _ _))))
    (Entails.of_eq (by ac_rfl))

private theorem step_send_post_arm_cont_imm {F : ShaCompress} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) (hA : AllocContracts img.base A ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape : List (BitVec 8)) (chain : Option ChainPB)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinState img.base sp ext s0 s1 msg st1) (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) {ret : BitVec 64} {Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv1 : ImgCallInv img s1)
    (hnext : SpqrSendAt3196 (ctl := ctl) img A ext s0 sp cur tape tape chain none msg st1 ret Frame Fr post) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
      ((memRegion (sp + 0x950#64) 928 ∗ spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A sp (s1.readReg64 .x21) (s1.readReg64 .x27) none ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1) ∗
       statesSendImmFrame (ctl := ctl) img.base A sp cur tape chain Frame) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine step_send_post_arm_cont (ctl := ctl) img A ext hA sp cur tape tape chain none hjoin1 hvalid hsp_align hinv1 ?_ hnext
  unfold statesSendImmFrame
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (tapeAt_entails_tapeAfter_same _ _ _))))))))
    (Entails.of_eq (by ac_rfl))

private theorem states_send_ok_elim {F : ShaCompress} {α : Type}
    {r : Except StatesPanic α} {f : α → V1Send spqrPolyApi (spqrAuthApi F) × Bytes}
    {sOut : V1Send spqrPolyApi (spqrAuthApi F)} {tape' : Bytes}
    (h : (StatesResult.ofPanic r >>= fun x => Except.ok (f x)) = Except.ok (sOut, tape')) :
    ∃ x, r = Except.ok x ∧ f x = (sOut, tape') := by
  cases r with
  | error p => contradiction
  | ok x => exact ⟨x, rfl, Except.ok.inj h⟩

set_option maxHeartbeats 800000 in
/-- Unified `*Ext` 11-arm `<States>::send` + post-arm reassembly (`statesSendArmOffset st0 -> +3196`,
    `0x309cc..0x31458 -> 0x314d8`) when `st0.send K tape = .ok (sOut, tape')`. -/
theorem step_send_statesSend_ext {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl)) (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K))
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec) (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec)
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64, ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64, ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedOkX img F A ext) (hres_call : DoReserve2OkX img A ext)
    (henc_call : EncodeBytesOkX img A ext) (hnc_call : PolyNextChunkOkX img A ext)
    (hhkdf : HkdfToVecOkExt img A (spqrHkdfWith F) ext) (hupd : AuthUpdateOkExt img F A ext)
    (hhs_call : HeaderSentSendEkChunkOkX img A F ext) (hct1r_call : Ct1ReceivedSendEkChunkOkX img A F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkOkX img A F ext) (hct2s_call : Ct2SampledSendCt2ChunkOkX img A F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkOkX img A F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F)) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop} (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19) (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
      GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗
      tapeAt ctl cur tape ∗ ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A (sp + 0x950#64) st0 ∗ statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196 (ctl := ctl) img A ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state ret Frame Fr post) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  subst hP; cases st0 with
  | keysUnsampled st =>
    obtain ⟨⟨outSt, chunk, tape1⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2.symm with ⟨rfl, rfl⟩; unfold statesSendPreArmScratch
    refine step_send_arm_keysUnsampled img A ext hA hbase hrng hseed hpk1 hpk2
      hmac_call hres_call henc_call hnc_call hpk1_slice hpk2_slice sp cur tape tape' st outSt chunk h1
      (Frame := ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗ memRegion (sp + 0x190#64) 928 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 4064#64) 16 ∗ Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28_0 hvregs
      (by rw [show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    refine step_send_post_arm_cont img A ext hA sp cur tape tape' chain none hjoin1 trivial hsp_align hinv1 ?_ hnext
    unfold statesSendPreArmScratch; rw [show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
    exact Entails.of_eq (by ac_rfl)
  | keysSampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 504]
    refine step_send_arm_keysSampled img A ext hA hbase hct1r_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain 504 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf img A ext hA sp cur tape chain 504 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | headerSent st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 880]
    refine step_send_arm_headerSent img A ext hA hbase hhs_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain 880 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf img A ext hA sp cur tape chain 880 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ct1Received st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 504]
    refine step_send_arm_ct1Received img A ext hA hbase hct1r_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain 504 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf img A ext hA sp cur tape chain 504 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ekSentCt1Received st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64) img hinv
    refine step_send_arm_ekSentCt1Received img.base A ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) img.base A sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; ac_rfl) fun s1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm img A ext hA sp cur tape chain hjoin1 rfl hsp_align hinv1 hnext
  | noHeaderReceived st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64) img hinv
    refine step_send_arm_noHeaderReceived img.base A ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) img.base A sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; ac_rfl) fun s1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm img A ext hA sp cur tape chain hjoin1 trivial hsp_align hinv1 hnext
  | headerReceived st =>
    obtain ⟨⟨outSt, chunk, ek, tape1⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2.symm with ⟨rfl, rfl⟩; unfold statesSendPreArmScratch
    rw [memRegion_190_928_eq sp, memRegion_4080_104_eq sp, memRegion_4192_504_eq sp]
    refine step_send_arm_headerReceived_ext img A ext himg hbase hA hZero hrng henc1
      hhkdf hupd henc_call hnc_call sp cur tape tape' st outSt chunk ek (hroot_len st rfl) h1
      (Frame := ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗ memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 3552#64) 504 ∗
        memRegion (sp + 4128#64) 56 ∗ memRegion (sp + 4640#64) 56 ∗ Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28 hx28_0 hvregs (by ac_rfl) fun s1 hinv1 hjoin1 => ?_
    refine step_send_post_arm_cont img A ext hA sp cur tape tape' chain (some ek) hjoin1 trivial hsp_align hinv1 ?_ hnext
    unfold statesSendPreArmScratch
    rw [memRegion_190_928_eq sp, memRegion_4080_104_eq sp, memRegion_4192_504_eq sp]
    exact Entails.of_eq (by ac_rfl)
  | ct1Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 928]
    refine step_send_arm_ct1Sampled img A ext hA hbase hct1s_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain 928 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf img A ext hA sp cur tape chain 928 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ekReceivedCt1Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 528]
    refine step_send_arm_ekReceivedCt1Sampled img A ext hA hbase hekct1s_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain 528 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf img A ext hA sp cur tape chain 528 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ct1Acknowledged st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64) img hinv
    refine step_send_arm_ct1Acknowledged img.base A ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) img.base A sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; ac_rfl) fun s1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm img A ext hA sp cur tape chain hjoin1 trivial hsp_align hinv1 hnext
  | ct2Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 456]
    refine step_send_arm_ct2Sampled img A ext hA hbase hct2s_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) img.base A sp cur tape chain 456 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf img A ext hA sp cur tape chain 456 (by decide) hjoin1 trivial hsp_align hinv1 hnext

/-- Unified 11-arm `<States>::send` + post-arm reassembly (`statesSendArmOffset st0 -> +3196`,
    `0x309cc..0x31458 -> 0x314d8`) when `st0.send K tape = .ok (sOut, tape')`. -/
theorem step_send_statesSend {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl)) (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K))
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec) (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec)
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64, ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64, ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedOkX img F A ext) (hres_call : DoReserve2OkX img A ext)
    (henc_call : EncodeBytesOkX img A ext) (hnc_call : PolyNextChunkOkX img A ext)
    (hhkdf : HkdfToVecOkX img A (spqrHkdfWith F) ext) (hupd : AuthUpdateOkX img F A ext)
    (hhs_call : HeaderSentSendEkChunkOkX img A F ext) (hct1r_call : Ct1ReceivedSendEkChunkOkX img A F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkOkX img A F ext) (hct2s_call : Ct2SampledSendCt2ChunkOkX img A F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkOkX img A F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F)) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop} (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19) (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
      GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗
      tapeAt ctl cur tape ∗ ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A (sp + 0x950#64) st0 ∗ statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196 (ctl := ctl) img A ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state ret Frame Fr post) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  step_send_statesSend_ext img A ext himg hbase hA hZero hrng hseed hpk1 hpk2 henc1 hpk1_slice hpk2_slice
    hmac_call hres_call henc_call hnc_call (hkdfToVecOkExt_of_okX hhkdf) (authUpdateOkExt_of_okX hupd)
    hhs_call hct1r_call hct1s_call hct2s_call hekct1s_call sp cur tape tape' chain st0 sOut hroot_len hsend
    hinv hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hx28_0 hvregs hP hnext

end CryptoVerification.SpqrV1.Top.Send

