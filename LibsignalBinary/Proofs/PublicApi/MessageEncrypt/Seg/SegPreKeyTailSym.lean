/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Basic-Block Stepping Lemmas for `segPreKey_tail_ok` (`+0x8b4..+0xa70`)

Small-footprint `SepWP` stepping lemmas for the `OTR::encrypt` call (`+0x8b4..+0x8c4`), its error
staging branch (`+0x8c8..+0x8ec`), `PreKeySignalMessage::new` argument setup (`+0x8c8..+0x98c`),
and the 248-byte `PreKeySignalMessage` result copy (`+0x990..+0xa70`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem preKeyEncrypt_step_bl {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {oA ptA len remA locA : BitVec 64}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x8b4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 18446744073709515544#64)
      s (((sp + 0x38#64) ↦₆₄ oA) ∗
        ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗
        ((sp + 0xc0#64) ↦₆₄ remA) ∗ ((sp + 0xc8#64) ↦₆₄ locA))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x580#64 ∧ sm.readReg64 .x1 = oA ∧
        sm.readReg64 .x2 = ptA ∧ sm.readReg64 .x3 = len ∧
        sm.readReg64 .x4 = locA ∧ sm.readReg64 .x5 = remA ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x8c8#64 ∧
        (Pm ⊢ ((sp + 0x38#64) ↦₆₄ oA) ∗
          ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗
          ((sp + 0xc0#64) ↦₆₄ remA) ∗ ((sp + 0xc8#64) ↦₆₄ locA))) := by
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  messageEncryptPreKey_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x8b4 20
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem preKeyEncrypt_step_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 v0 v1 v2 : BitVec 64}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x8c8#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xc38#64)
      s (((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = w1 ∧ sm.readReg64 .x23 = w2 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = w0 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          words64At (sp + 0xb00#64) [w3, w4, w5])) := by
  dsimp only [tripleRatchetProgAt, errTag] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  messageEncryptPreKey_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x8c8 40
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 3200000 in
theorem buildPreKeyMsg_step_bl {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {u0 : BitVec 64} {regId spk pkVal : BitVec 32} {ver : BitVec 8}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 : BitVec 64}
    {k0 k1 k2 kd0 kd1 kd2 : BitVec 64}
    {bk0 bk1 bk2 bk3 bkd0 bkd1 bkd2 bkd3 : BitVec 64}
    {ikd0 ikd1 ikd2 ikd3 : BitVec 64}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x8c8#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = sp + 0x8b8#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64)
    (hw0 : w0 + 1#64 ≠ 0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 18446744073709389144#64)
      s ((sp ↦₆₄ u0) ∗
        ((sp + 0x14#64) ↦₃₂ regId) ∗ ((sp + 0x24#64) ↦₃₂ spk) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
        words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
        ((sp + 0x348#64) ↦₈ ver) ∗
        words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        words64At (sp + 0x8a0#64) [k0, k1, k2] ∗
        words64At (sp + 0x8b8#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗
        words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗
        words64At (sp + 0xae0#64) [bkd0, bkd1, bkd2, bkd3] ∗
        words64At (sp + 0xb00#64) [ikd0, ikd1, ikd2, ikd3])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        (sm.readReg64 .x0).setWidth 8 = ver ∧
        (sm.readReg64 .x1).setWidth 32 = regId ∧
        (sm.readReg64 .x2).setWidth 32 = (s.readReg64 .x24).setWidth 32 ∧
        (sm.readReg64 .x3).setWidth 32 = pkVal ∧
        (sm.readReg64 .x4).setWidth 32 = spk ∧
        sm.readReg64 .x5 = sp + 0x950#64 ∧
        sm.readReg64 .x6 = sp + 0xae0#64 ∧
        sm.readReg64 .x7 = sp + 0xb00#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x990#64 ∧
        (Pm ⊢ (sp ↦₆₄ (sp + 0x8b8#64)) ∗
          ((sp + 0x14#64) ↦₃₂ regId) ∗ ((sp + 0x24#64) ↦₃₂ spk) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
          words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
          ((sp + 0x348#64) ↦₈ ver) ∗
          words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          words64At (sp + 0x8a0#64) [k0, k1, k2] ∗
          words64At (sp + 0x8b8#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          words64At (sp + 0x950#64) [k0, k1, k2] ∗
          words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗
          words64At (sp + 0xae0#64) [bk0, bk1, bk2, bk3] ∗
          words64At (sp + 0xb00#64) [ik0, ik1, ik2, ik3])) := by
  have hw0_beq : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  messageEncryptPreKey_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x8c8 200
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 4800000 in
theorem cmCopy_step_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      w25 w26 w27 w28 w29 w30 : BitVec 64}
    {v0 v1 v2 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24
      d25 d26 d27 d28 d29 d30 : BitVec 64}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x990#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = sp + 0x8b8#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hw0 : w0 + 1#64 ≠ 0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xa70#64)
      s (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        words64At (sp + 0x930#64) [v0, v1, v2] ∗
        words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
            w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29,
            w30] ∗
          words64At (sp + 0x930#64) [w4, w5, w6] ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
            w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29,
            w30])) := by
  have hw0_beq : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  messageEncryptPreKey_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x990 224
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
