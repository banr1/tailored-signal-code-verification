/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp

/-!
# `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (`0x29b30`) — Success Path

Proves the Segment 4 `.ok` branch (`0x2a3a8 .. 0x2a4a4` → `0x2a034`) when
`SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg`, and combines it with
`post_seg4_err_wp` into `post_seg4_after_signal_wp`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm]
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48
  bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_80 bv_add_neg_87
  bv_add_neg_88 bv_add_neg_96 bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136
  bv_add_neg_152 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186
  bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216
  bv_add_neg_512
  bv_sub_add_lit' bv_sub_sub_lit
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56

/-! ## Cleanup Tail `0x2a4a0 .. 0x2a4a4` (`+2416 .. +2420` → `+1284`) -/

/-- Tail `0x2a4a0 .. 0x2a4a4` (`+2416 .. +2420` → `+1284`):
branches on `cbnz x26, 0x2a558; b 0x2a568` to free `msgVec`, `ikVec`, `bkVec` and reach
`0x2a034`. -/
theorem cleanup_4a0_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8))
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2416#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have h558 := @cleanup_558_wp img C A S ctl abs hS s0
  have h568 := @cleanup_568_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2416 8
  clear hfn
  dsimp only [tripleRatchetProgAt] at h558 h568 hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2416#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  by_cases hcap : msgCap = 0#64
  · clear h558
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
          A.pool ∗ stackAt sp' smallRootStack) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (h568 ik bk
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx23, arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  · clear h568
    have hcap_beq : (msgCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h558 msg ik bk hcap
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm])

/-! ## Memory Packing Helpers for `sret` (`248` B) and `sp' + 176` (`112` B) -/

theorem msgHeapAt_pqCap_lt (A : RustAlloc) (g : SignalMessageGhost) (m : SignalMessage)
    (addrW0 addrW1 : BitVec 64) :
    msgHeapAt A g m addrW0 addrW1 ⊢
      ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗ msgHeapAt A g m addrW0 addrW1 := by
  unfold msgHeapAt vecU8Heap
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hbnd => ?_
  refine Entails.pure_left fun ⟨hlen, hlt, hptr⟩ => ?_
  rw [pure_true_emp hlt, emp_sepConj,
    pure_true_emp hbnd, emp_sepConj,
    pure_true_emp ⟨hlen, hlt, hptr⟩, emp_sepConj]
  exact Entails.refl _

theorem memRegion120_words15 (r : BitVec 64) :
    memRegion r 120 =
      (∃∗ s0 : BitVec 64, r ↦₆₄ s0) ∗
      (∃∗ s1 : BitVec 64, (r + 8#64) ↦₆₄ s1) ∗
      (∃∗ s2 : BitVec 64, (r + 16#64) ↦₆₄ s2) ∗
      (∃∗ s3 : BitVec 64, (r + 24#64) ↦₆₄ s3) ∗
      (∃∗ s4 : BitVec 64, (r + 32#64) ↦₆₄ s4) ∗
      (∃∗ s5 : BitVec 64, (r + 40#64) ↦₆₄ s5) ∗
      (∃∗ s6 : BitVec 64, (r + 48#64) ↦₆₄ s6) ∗
      (∃∗ s7 : BitVec 64, (r + 56#64) ↦₆₄ s7) ∗
      (∃∗ s8 : BitVec 64, (r + 64#64) ↦₆₄ s8) ∗
      (∃∗ s9 : BitVec 64, (r + 72#64) ↦₆₄ s9) ∗
      (∃∗ s10 : BitVec 64, (r + 80#64) ↦₆₄ s10) ∗
      (∃∗ s11 : BitVec 64, (r + 88#64) ↦₆₄ s11) ∗
      (∃∗ s12 : BitVec 64, (r + 96#64) ↦₆₄ s12) ∗
      (∃∗ s13 : BitVec 64, (r + 104#64) ↦₆₄ s13) ∗
      (∃∗ s14 : BitVec 64, (r + 112#64) ↦₆₄ s14) := by
  rw [show (120 : Nat) = 48 + (48 + (8 + (8 + 8))) by decide,
    memRegion_split r 48 72 (by decide),
    memRegion_split (r + 48#64) 48 24 (by decide),
    memRegion_split (r + 48#64 + 48#64) 8 16 (by decide),
    memRegion_split (r + 48#64 + 48#64 + 8#64) 8 8 (by decide),
    memRegion48_words6 r,
    memRegion48_words6 (r + 48#64),
    ProofLib.memRegion_eight (r + 48#64 + 48#64),
    ProofLib.memRegion_eight (r + 48#64 + 48#64 + 8#64),
    ProofLib.memRegion_eight (r + 48#64 + 48#64 + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion48_mid_eq (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ p0 : BitVec 32, a ↦₃₂ p0) ∗
      (∃∗ p1 : BitVec 32, (a + 4#64) ↦₃₂ p1) ∗
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
      (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
      (∃∗ k40 : BitVec 32, (a + 40#64) ↦₃₂ k40) ∗
      memRegion (a + 44#64) 4 := by
  rw [show (48 : Nat) = 4 + (4 + (32 + (4 + 4))) by decide,
    memRegion_split a 4 44 (by decide),
    memRegion_split (a + 4#64) 4 40 (by decide),
    memRegion_split (a + 4#64 + 4#64) 32 8 (by decide),
    memRegion_split (a + 4#64 + 4#64 + 32#64) 4 4 (by decide),
    ProofLib.memRegion_four a, ProofLib.memRegion_four (a + 4#64),
    memRegion32_words4 (a + 4#64 + 4#64),
    ProofLib.memRegion_four (a + 4#64 + 4#64 + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion48_tail_eq (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
      (∃∗ u32 : BitVec 32, (a + 32#64) ↦₃₂ u32) ∗
      (∃∗ u36 : BitVec 32, (a + 36#64) ↦₃₂ u36) ∗
      (∃∗ b40 : BitVec 8, (a + 40#64) ↦₈ b40) ∗
      memRegion (a + 41#64) 7 := by
  rw [show (48 : Nat) = 32 + (4 + (4 + (1 + 7))) by decide,
    memRegion_split a 32 16 (by decide),
    memRegion_split (a + 32#64) 4 12 (by decide),
    memRegion_split (a + 32#64 + 4#64) 4 8 (by decide),
    memRegion_split (a + 32#64 + 4#64 + 4#64) 1 7 (by decide),
    memRegion32_words4 a,
    ProofLib.memRegion_four (a + 32#64),
    ProofLib.memRegion_four (a + 32#64 + 4#64),
    ProofLib.memRegion_one (a + 32#64 + 4#64 + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion248_sret_split (r : BitVec 64) :
    memRegion r 248 =
      memRegion (r + 168#64) 32 ∗
      memRegion r 120 ∗
      memRegion (r + 120#64) 48 ∗
      memRegion (r + 200#64) 48 := by
  rw [show (248 : Nat) = 120 + (48 + (32 + 48)) by decide,
    memRegion_split r 120 128 (by decide),
    memRegion_split (r + 120#64) 48 80 (by decide),
    memRegion_split (r + 120#64 + 48#64) 32 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem memRegion112_words14 (a : BitVec 64) :
    memRegion a 112 =
      (∃∗ w1 : BitVec 64, a ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 8#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 16#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 24#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 32#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 40#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 48#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (a + 56#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (a + 64#64) ↦₆₄ w9) ∗
      (∃∗ w10 : BitVec 64, (a + 72#64) ↦₆₄ w10) ∗
      (∃∗ w11 : BitVec 64, (a + 80#64) ↦₆₄ w11) ∗
      (∃∗ w12 : BitVec 64, (a + 88#64) ↦₆₄ w12) ∗
      (∃∗ w13 : BitVec 64, (a + 96#64) ↦₆₄ w13) ∗
      (∃∗ w14 : BitVec 64, (a + 104#64) ↦₆₄ w14) := by
  rw [show (112 : Nat) = 48 + (48 + (8 + 8)) by decide,
    memRegion_split a 48 64 (by decide),
    memRegion_split (a + 48#64) 48 16 (by decide),
    memRegion_split (a + 48#64 + 48#64) 8 8 (by decide),
    memRegion48_words6 a,
    memRegion48_words6 (a + 48#64),
    ProofLib.memRegion_eight (a + 48#64 + 48#64),
    ProofLib.memRegion_eight (a + 48#64 + 48#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words14_entails_memRegion112
    (a w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
    ((a + 24#64) ↦₆₄ w4) ∗ ((a + 32#64) ↦₆₄ w5) ∗ ((a + 40#64) ↦₆₄ w6) ∗
    ((a + 48#64) ↦₆₄ w7) ∗ ((a + 56#64) ↦₆₄ w8) ∗ ((a + 64#64) ↦₆₄ w9) ∗
    ((a + 72#64) ↦₆₄ w10) ∗ ((a + 80#64) ↦₆₄ w11) ∗ ((a + 88#64) ↦₆₄ w12) ∗
    ((a + 96#64) ↦₆₄ w13) ∗ ((a + 104#64) ↦₆₄ w14) ⊢
      memRegion a 112 := by
  rw [memRegion112_words14 a]
  exact sepConj_mono (Entails.sepExists_intro w1)
    (sepConj_mono (Entails.sepExists_intro w2)
      (sepConj_mono (Entails.sepExists_intro w3)
        (sepConj_mono (Entails.sepExists_intro w4)
          (sepConj_mono (Entails.sepExists_intro w5)
            (sepConj_mono (Entails.sepExists_intro w6)
              (sepConj_mono (Entails.sepExists_intro w7)
                (sepConj_mono (Entails.sepExists_intro w8)
                  (sepConj_mono (Entails.sepExists_intro w9)
                    (sepConj_mono (Entails.sepExists_intro w10)
                      (sepConj_mono (Entails.sepExists_intro w11)
                        (sepConj_mono (Entails.sepExists_intro w12)
                          (sepConj_mono (Entails.sepExists_intro w13)
                            (Entails.sepExists_intro w14)))))))))))))

theorem sevenBytesHead_tail_assoc (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (R : SepProp) :
    (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗
      ((a + 6#64) ↦₈ b6) ∗ R =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
      ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ R := by
  have h := congrArg (· ∗ R) (sevenBytesHeadAt_eq_tailAt a b0 b1 b2 b3 b4 b5 b6)
  dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at h
  simpa only [sepConj_assoc] using h

theorem preKeyResultAt_ok_intro (A : RustAlloc) (x : PreKeyTryFromArgs)
    (innerMsg : SignalMessage)
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg)
    (msgG : SignalMessageGhost) (serBoxPtr kyberBoxPtr : BitVec 64)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (opkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3))
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3)) :
    (msgWords15At x.sret
      msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
      msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
      msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
    (((x.sret + 120#64) ↦₃₂ opkTag x) ∗ ((x.sret + 124#64) ↦₃₂ opkVal)) ∗
    (((x.sret + 128#64) ↦₆₄ serBoxPtr) ∗
      ((x.sret + 136#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
      boxU8Buf A serBoxPtr x.bytes) ∗
    (((x.sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
      ((x.sret + 152#64) ↦₆₄ 1569#64) ∗
      boxU8Buf A kyberBoxPtr x.kyberBytes ∗
      ((x.sret + 160#64) ↦₃₂ x.kpkId) ∗
      memRegion (x.sret + 164#64) 4) ∗
    pkLayoutAt (x.sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
    (((x.sret + 200#64) ↦₆₄ ik0) ∗ ((x.sret + 208#64) ↦₆₄ ik1) ∗
      ((x.sret + 216#64) ↦₆₄ ik2) ∗ ((x.sret + 224#64) ↦₆₄ ik3)) ∗
    ((x.sret + 232#64) ↦₃₂ x.regId) ∗
    ((x.sret + 236#64) ↦₃₂ x.spkId) ∗
    ((x.sret + 240#64) ↦₈ 4#8) ∗
    memRegion (x.sret + 241#64) 7 ⊢
      preKeyResultAt A x.sret x := by
  unfold preKeyResultAt
  rw [hsig]
  refine Entails.trans ?_ (Entails.sepExists_intro ⟨msgG, serBoxPtr, kyberBoxPtr⟩)
  unfold preKeyMsgAt PreKeyTryFromArgs.toModel optKyberAt
  dsimp only
  have hmsg := signalMessageAt_pack A msgG x.sret innerMsg rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 hrk
  have hopk' := pointsTo32_pair_entails_optU32At (x.sret + 120#64) x opkVal hopk
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hopk'
  refine Entails.trans (sepConj_mono hmsg (sepConj_mono_left hopk')) ?_
  rw [boxU8At_eq_boxU8Buf A (x.sret + 0x80#64) serBoxPtr x.bytes,
      boxU8At_eq_boxU8Buf A (x.sret + 0x90#64) kyberBoxPtr x.kyberBytes,
      PreKeyTryFromArgs.kyberBytes_length,
      hpk, ← pkLayoutAt_eq_pointsToBytes (x.sret + 0xa8#64),
      hik (x.sret + 0xc8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-! ## `post_seg4_ok_pack_wp` (`+2236 .. +2420` → `+1284`) -/

theorem opkTag_mask64_truncate32 (x : PreKeyTryFromArgs) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (opkTag x) &&& 1#64) = opkTag x := by
  unfold opkTag
  cases x.opkId <;> simp

theorem post_seg4_ok_pack_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' serBoxPtr kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3))
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hser : serBoxPtr ≠ 0#64)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serBoxPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret)
    (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx25 : s.readReg64 .x25 = 1569#64)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hx27 : s.readReg64 .x27 = msgG.pqCap)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
        msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
        boxU8Buf A serBoxPtr x.bytes ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have h4a0 := @cleanup_4a0_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2236 180
  clear hfn
  dsimp only [tripleRatchetProgAt] at h4a0 hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2236#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hser_beq : (serBoxPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hser
  rw [memRegion248_sret_split x.sret]
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (memRegion32_entails_pkLayoutAt (x.sret + 168#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
    SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
    SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
    SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun c7 =>
    SepWPp.exists_pre fun c8 => SepWPp.exists_pre fun cw9 =>
    SepWPp.exists_pre fun cw13 => SepWPp.exists_pre fun cw15 =>
    SepWPp.exists_pre fun cw23 => SepWPp.exists_pre fun cb31 => ?_
  rw [memRegion120_words15 x.sret,
      memRegion48_mid_eq (x.sret + 120#64),
      memRegion48_tail_eq (x.sret + 200#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b240 =>
    SepWPp.exists_pre fun u1 => SepWPp.exists_pre fun u0 =>
    SepWPp.exists_pre fun w224 => SepWPp.exists_pre fun w216 =>
    SepWPp.exists_pre fun w208 => SepWPp.exists_pre fun w200 =>
    SepWPp.exists_pre fun k160 =>
    SepWPp.exists_pre fun w152 => SepWPp.exists_pre fun w144 =>
    SepWPp.exists_pre fun w136 => SepWPp.exists_pre fun w128 =>
    SepWPp.exists_pre fun p1 => SepWPp.exists_pre fun p0 =>
    SepWPp.exists_pre fun s14 => SepWPp.exists_pre fun s13 =>
    SepWPp.exists_pre fun s12 => SepWPp.exists_pre fun s11 =>
    SepWPp.exists_pre fun s10 => SepWPp.exists_pre fun s9 =>
    SepWPp.exists_pre fun s8 => SepWPp.exists_pre fun s7 =>
    SepWPp.exists_pre fun s6 => SepWPp.exists_pre fun s5 =>
    SepWPp.exists_pre fun s4 => SepWPp.exists_pre fun s3 =>
    SepWPp.exists_pre fun s2 => SepWPp.exists_pre fun s1 =>
    SepWPp.exists_pre fun s0 => ?_
  dsimp only [sevenBytesHeadAt, pkLayoutAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2244#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have h136_tail := fun R => sevenBytesHead_tail_assoc (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h136_tail
  rw [h136_tail]
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 2268#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  rw [← h136_tail]
  have h168_tail := fun R => sevenBytesHead_tail_assoc (x.sret + 168#64) b0 b1 b2 b3 c4 c5 c6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_tail
  rw [h168_tail]
  dsimp only [pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + 2416#64) ?_
  wp_steps
  refine @SepWP.done _ _ _ _ _ _ ⟨by simp [arm64_norm]⟩ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF3 hsym3
  have h168_head := fun R => sevenBytesHead_tail_assoc (x.sret + 168#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_head
  rw [← h168_head]
  have hres := preKeyResultAt_ok_intro A x innerMsg hsig msgG serBoxPtr kyberBoxPtr
    rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3 opkVal
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 hopk hpk hrk hik
  dsimp only [msgWords15At, pkLayoutAt, sevenBytesHeadAt, pkRestAt] at hres
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hres
  have hm112 :
      ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
      ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
      ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
      ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ⊢
        memRegion (sp' + 176#64) 112 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words14_entails_memRegion112 (sp' + 176#64)
        msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter)
        (verHi56 ++ innerMsg.messageVersion)
  have hcomb := sepConj_mono_right
    (P := ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      Wire.vecU8Buf A msgCap msgPtr x.inner ∗
      Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
      Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (sepConj_mono hres
      (sepConj_mono_right (P :=
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        ((sp' + 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sp' + 140#64) ↦₈ b4) ∗ ((sp' + 141#64) ↦₈ b5) ∗ ((sp' + 142#64) ↦₈ b6) ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3)) hm112))
  refine SepWPp.mono_pre (P' :=
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack) ∗
      (preKeyResultAt A x.sret x ∗
        (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          ((sp' + 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((sp' + 140#64) ↦₈ b4) ∗ ((sp' + 141#64) ↦₈ b5) ∗ ((sp' + 142#64) ↦₈ b6) ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3)) ∗
        memRegion (sp' + 176#64) 112))
    (by
      refine Entails.trans ?_ hcomb
      rw [opkTag_mask64_truncate32 x]
      simp only [sepConj_assoc, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (h4a0 x.inner x.ikBytes x.bkBytes
      (PostEpilogueState.of_steps hF3 hsym3 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]))
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; ac_rfl

/-! ## `post_seg4_ok_wp` and `post_seg4_after_signal_wp` (`0x2a3a8` → `0x2a034`) -/

theorem post_seg4_ok_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs)
    (hTryClone : TryCloneFromRefOk img.base C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {innerMsg : SignalMessage}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32)
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2168#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion (sp' + 176#64) 112 ∗
        (x.ptr ↦ₛ x.bytes) ∗
        memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗
          (x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 312#64) 120 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallClone := tryCloneFromRef_ok_at_prekey hTryClone
  clear hTryClone
  have hpack := @post_seg4_ok_pack_wp img C A S ctl abs hS x s0
  have hpan := panic_at_prekey_handle_alloc_error (b := img.base) (C := C) (ctl := ctl)
    (abs := abs)
  have hlen_toNat : (BitVec.ofNat 64 x.bytes.length).toNat = x.bytes.length :=
    Nat.mod_eq_of_lt (by omega)
  have hlen_le63 : x.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hstackClone :=
    stackAt_sub_split sp' tryCloneFromRefStack smallRootStack (by decide) (by decide)
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2168 72
  responder_wire_fetches_from img.base H hfn 0x29c14 2664 12
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcallClone hpack hpan hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2168#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      18446744073709433996#64) _ at hcallClone
  change (libsignalSessionCode.rebase img.base H).externAt?
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x29c14)) =
      some Rust.panicked at hpan
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rw [hsig]
  refine SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion112_words14 (sp' + 176#64))))) ?_
  dsimp only [signalMessageResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w280 => SepWPp.exists_pre fun w272 =>
    SepWPp.exists_pre fun w264 => SepWPp.exists_pre fun w256 =>
    SepWPp.exists_pre fun w248 => SepWPp.exists_pre fun w240 =>
    SepWPp.exists_pre fun w232 => SepWPp.exists_pre fun w224 =>
    SepWPp.exists_pre fun w216 => SepWPp.exists_pre fun w208 =>
    SepWPp.exists_pre fun w200 => SepWPp.exists_pre fun w192 =>
    SepWPp.exists_pre fun w184 => SepWPp.exists_pre fun w176 =>
    SepWPp.exists_pre fun msgG => ?_
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length innerMsg.senderRatchetKey.bytes)
  refine SepWPp.mono_pre
    (sepConj_mono_left
      (signalMessageAt_unpack A msgG (sp' + 312#64) innerMsg rk0 rk1 rk2 rk3 hrk)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun addrW0 => SepWPp.exists_pre fun addrW1 =>
    SepWPp.exists_pre fun verHi56 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (msgHeapAt_pqCap_lt A msgG innerMsg addrW0 addrW1))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine SepWPp.pure_pre fun hpq_lt => ?_
  have hpq_eq := cap_add1_eq_of_lt hpq_lt
  dsimp only [msgWords15At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709433996#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hm312 :
      ((sp' + 312#64) ↦₆₄ msgG.pqCap) ∗
      ((sp' + 320#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 328#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 336#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 344#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 352#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 360#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 368#64) ↦₆₄ rk0) ∗ ((sp' + 376#64) ↦₆₄ rk1) ∗
      ((sp' + 384#64) ↦₆₄ rk2) ∗ ((sp' + 392#64) ↦₆₄ rk3) ∗
      ((sp' + 400#64) ↦₆₄ addrW0) ∗ ((sp' + 408#64) ↦₆₄ addrW1) ∗
      ((sp' + 416#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 424#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ⊢
        memRegion (sp' + 312#64) 120 := by
    simpa [msgWords15At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      msgWords15At_entails_memRegion (sp' + 312#64)
        msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter)
        (verHi56 ++ innerMsg.messageVersion)
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 312#64) 120 ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
      ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
      ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
      ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
      ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
      (x.ptr ↦ₛ x.bytes) ∗
      memRegion x.sret 248 ∗
      ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
      ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
      ((sp' + 20#64) ↦₃₂ opkTag x) ∗
      ((sp' + 24#64) ↦₃₂ opkVal) ∗
      ((sp' + 28#64) ↦₃₂ x.spkId) ∗
      ((sp' + 56#64) ↦₃₂ x.regId) ∗
      ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
      ((sp' + 72#64) ↦₆₄ w15) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
      ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
      ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
      boxU8Buf A kyberBoxPtr x.kyberBytes ∗
      Wire.vecU8Buf A msgCap msgPtr x.inner ∗
      Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
      Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (by
      refine Entails.trans ?_ (sepConj_mono_left hm312)
      simp only [sepConj_assoc]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_noPanic_tryFrom (⟨x.ptr, x.bytes⟩ : TryCloneSliceCall) hcallClone
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 2236#64) (by simp [arm64_norm])
    (T := (x.ptr ↦ₛ x.bytes) ∗ A.pool ∗ stackAt sp' tryCloneFromRefStack)
    (φ := x.ptr = x.ptr ∧ (BitVec.ofNat 64 x.bytes.length).toNat = x.bytes.length ∧
      x.bytes.length + 1 ≤ 2 ^ 63)
    (by simp [tryCloneFromRefSpec, hsp_eq, arm64_norm])
    ⟨rfl, hlen_toNat, hlen_le63⟩
    (by rw [hstackClone]; sep_focus)
    ?_
  clear hcallClone
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [tryCloneFromRefSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun hx1_2 => ?_
  rcases hcs2 with
    ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have hx19_2 : s2.readReg64 .x19 = x.sret := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length := by
    simp [hx20_cs, hx20, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = 0x44#64 := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, hx23, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = 1569#64 := by simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = msgG.pqCap := by simp [hx27_cs, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = kyberBoxPtr := by simp [hx28_cs, hx28, arm64_norm]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · clear hpack
    simp only [hoom, ite_true, sepConj_pure_left_comm, sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨_, htr2⟩ => ?_
    refine SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x29c14)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    refine SepWPp.panic (by simp [hrun2, arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_pure_left_comm, sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine SepWPp.mono_pre
      (P' := (memRegion x.sret 248 ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
          ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
          ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
          ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
          ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
          ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
          ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
          ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
          ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
          ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
          ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
          msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A (s2.readReg64 .x0) x.bytes ∗
          boxU8Buf A kyberBoxPtr x.kyberBytes ∗
          Wire.vecU8Buf A msgCap msgPtr x.inner ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
          A.pool ∗ stackAt sp' smallRootStack) ∗
        ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 312#64) 120))
      (by
        simp only [hstackClone, hsp_eq, arm64_norm]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hpack hsig hopk hpk hrk hik hoom
        ⟨hsp2_eq, hsp2_align, hF2, hsym2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2 hx28_2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl

theorem post_seg4_after_signal_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs)
    (hTryClone : TryCloneFromRefOk img.base C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2168#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion (sp' + 176#64) 112 ∗
        (x.ptr ↦ₛ x.bytes) ∗
        memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗
          (x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 312#64) 120 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hsig : SignalMessage.tryFrom protoSignalCodec x.inner with e | innerMsg
  · rw [← hsig]
    have h112_split : memRegion (sp' + 176#64) 112 =
        memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 64 := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        memRegion_split (sp' + 176#64) 48 64 (by decide)
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          memRegion (sp' + 176#64) 48 ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
          memRegion x.sret 248 ∗
          boxU8Buf A kyberBoxPtr x.kyberBytes ∗
          Wire.vecU8Buf A msgCap msgPtr x.inner ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
          A.pool ∗ stackAt sp' smallRootStack) ∗
        ((x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 224#64) 64))
      (by
        rw [h112_split]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_seg4_err_wp hS hsig hst hpc hrun hx29 hx28 hx26 hx25 hx24 hx23 hx19)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    rw [h112_split]
    apply entails_of_eq; ac_rfl
  · rw [← hsig]
    exact post_seg4_ok_wp hS hTryClone hlt hsig hopk hpk hik hst hpc hrun
      hx29 hx28 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19

end CryptoVerification.E2E.Pqxdh.ResponderWire
