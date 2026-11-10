/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# `decode_kyber_pre_key` Stack Frame and Memory Packing Helpers

SIMD lane normalization, 128-byte stack frame splitting (`sub sp, sp, #128`), and 88-byte `Ok` /
`Err` result buffer packing lemmas for `signal_session::stores::decode_kyber_pre_key`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## 1. Scoped normalization rules for SIMD lanes, `cmn errTag, #1`, and `State` updates -/

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_lo_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_hi_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem cmn_errTag_eq :
    ConditionHolds .EQ (addsPState64 errTag 1#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64 errTag
  decide

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem status_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem trace_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem pc_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).pc = pc := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem pc_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pc = s.pc := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## 2. Model bridge & callee-saved registers (`x21..x28`) -/

theorem kyberDeserialize_of_some {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    (h : SignedPreKeyRecordStructure.decode bs = some m) :
    KyberPreKeyRecord.deserialize bs = .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  simp [h]

theorem kyberDeserialize_of_none {bs : List (BitVec 8)}
    (h : SignedPreKeyRecordStructure.decode bs = none) :
    KyberPreKeyRecord.deserialize bs = .error .invalidProtobufEncoding := by
  unfold KyberPreKeyRecord.deserialize
  simp [h]

structure KpkSavedRegs (s0 s : State) : Prop where
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28

theorem KpkSavedRegs.refl (s0 : State) : KpkSavedRegs s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem KpkSavedRegs.of_calleeSaved {s0 s1 s2 : State}
    (h1 : KpkSavedRegs s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    KpkSavedRegs s0 s2 where
  x21 := hcs.2.2.1.trans h1.x21
  x22 := hcs.2.2.2.1.trans h1.x22
  x23 := hcs.2.2.2.2.1.trans h1.x23
  x24 := hcs.2.2.2.2.2.1.trans h1.x24
  x25 := hcs.2.2.2.2.2.2.1.trans h1.x25
  x26 := hcs.2.2.2.2.2.2.2.1.trans h1.x26
  x27 := hcs.2.2.2.2.2.2.2.2.1.trans h1.x27
  x28 := hcs.2.2.2.2.2.2.2.2.2.1.trans h1.x28

/-! ## 3. Stack frame splitting & reassembly (`sub sp, sp, #128`) -/

abbrev kpkSubStack : Nat := smallRootStack - 128

theorem kpkStack_smallRoot_split (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 128#64) signedDecodeStack ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        memRegion (sp - 128#64) 8 ∗
        memRegion (sp - 128#64 + 8#64) 88 ∗
        memRegion (sp - 128#64 + 96#64) 32 := by
  have h1 := stackAt_sub_split sp 128 smallRootStack
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) kpkSubStack =
      stackAt (sp - 128#64) kpkSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 128#64 - BitVec.ofNat 64 kpkSubStack := by
      change sp - 65536#64 = sp - 128#64 - 65408#64
      bv_omega
    rw [ha]
  have h3 := stackAt_sub_split (sp - 128#64) signedDecodeStack kpkSubStack
  have h4 : stackAt sp 128 =
      memRegion (sp - 128#64) 8 ∗
        memRegion (sp - 128#64 + 8#64) 88 ∗
        memRegion (sp - 128#64 + 96#64) 32 := by
    unfold stackAt
    rw [show (128 : Nat) = 8 + (88 + 32) by decide,
      ProofLib.memRegion_split (sp - 128#64) 8 120 (by decide),
      ProofLib.memRegion_split (sp - 128#64 + 8#64) 88 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h1, h2, h3, h4]
  ac_rfl

theorem kpkFrame32_unpack (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 32 ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ((sp' + 96#64) ↦₆₄ c0) ∗ ((sp' + 104#64) ↦₆₄ c1) ∗
        ((sp' + 112#64) ↦₆₄ c2) ∗ ((sp' + 120#64) ↦₆₄ c3) := by
  rw [ProofLib.memRegion_split (sp' + 96#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 96#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 96#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun c3 => Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c1 => Entails.sepExists_elim fun c0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro c0)
  refine Entails.trans ?_ (Entails.sepExists_intro c1)
  refine Entails.trans ?_ (Entails.sepExists_intro c2)
  refine Entails.trans ?_ (Entails.sepExists_intro c3)
  exact Entails.refl _

theorem kpkFrame32_pack (sp' c0 c1 c2 c3 : BitVec 64) :
    ((sp' + 96#64) ↦₆₄ c0) ∗ ((sp' + 104#64) ↦₆₄ c1) ∗
      ((sp' + 112#64) ↦₆₄ c2) ∗ ((sp' + 120#64) ↦₆₄ c3) ⊢
      memRegion (sp' + 96#64) 32 := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by decide,
    ProofLib.memRegion_split (sp' + 96#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 96#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 96#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))

theorem kpkStack_exit_pack (sp c0 c1 c2 c3 : BitVec 64) :
    memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 128#64 + 8#64) 88 ∗
      ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
      ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
      ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
      ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
      stackAt (sp - 128#64) signedDecodeStack ∗
      memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ⊢
      stackAt sp smallRootStack := by
  rw [kpkStack_smallRoot_split sp]
  have hf32 := kpkFrame32_pack (sp - 128#64) c0 c1 c2 c3
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hf32))))
  apply entails_of_eq; ac_rfl

theorem kpkDecodeStack_drop_split (sp' : BitVec 64) :
    stackAt sp' signedDecodeStack =
      stackAt sp' dropDecodeErrorStack ∗
        memRegion (sp' - BitVec.ofNat 64 signedDecodeStack)
          (signedDecodeStack - dropDecodeErrorStack) := by
  have hs := stackAt_sub_split sp' dropDecodeErrorStack signedDecodeStack
  rw [hs]
  ac_rfl

/-! ## 4. 88-byte `Ok` & `Err` memory packing/unpacking helpers -/

def words88Sp (sp' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) : SepProp :=
  ((sp' + 8#64) ↦₆₄ w0) ∗ ((sp' + 16#64) ↦₆₄ w1) ∗
  ((sp' + 24#64) ↦₆₄ w2) ∗ ((sp' + 32#64) ↦₆₄ w3) ∗
  ((sp' + 40#64) ↦₆₄ w4) ∗ ((sp' + 48#64) ↦₆₄ w5) ∗
  ((sp' + 56#64) ↦₆₄ w6) ∗ ((sp' + 64#64) ↦₆₄ w7) ∗
  ((sp' + 72#64) ↦₆₄ w8) ∗ ((sp' + 80#64) ↦₆₄ w9) ∗
  ((sp' + 88#64) ↦₆₄ w10)

def words88Ret (ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) : SepProp :=
  (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗
  ((ret + 16#64) ↦₆₄ w2) ∗ ((ret + 24#64) ↦₆₄ w3) ∗
  ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ∗
  ((ret + 48#64) ↦₆₄ w6) ∗ ((ret + 56#64) ↦₆₄ w7) ∗
  ((ret + 64#64) ↦₆₄ w8) ∗ ((ret + 72#64) ↦₆₄ w9) ∗
  ((ret + 80#64) ↦₆₄ w10)

def signedPreKeyBufs (A : RustAlloc) (pubCap pubPtr privCap privPtr sigCap sigPtr : BitVec 64)
    (m : SignedPreKeyRecordStructure) : SepProp :=
  vecU8Buf A pubCap pubPtr m.publicKey ∗
  vecU8Buf A privCap privPtr m.privateKey ∗
  vecU8Buf A sigCap sigPtr m.signature

theorem vecU8At_entails_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢ vecU8 A a bs := by
  unfold vecU8
  exact Entails.trans
    (Entails.sepExists_intro (P := fun p => vecU8At A a cap p bs) ptr)
    (Entails.sepExists_intro (P := fun c => ∃∗ p, vecU8At A a c p bs) cap)

theorem vecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h, pure_true_emp h.2.1, emp_sepConj, emp_sepConj]
  exact Entails.refl _

theorem signedPreKeyStructAt_sp8_unpack (A : RustAlloc) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) :
    signedPreKeyStructAt A (sp' + 8#64) m ⊢
      ∃∗ pubCap : BitVec 64, ∃∗ pubPtr : BitVec 64,
      ∃∗ privCap : BitVec 64, ∃∗ privPtr : BitVec 64,
      ∃∗ sigCap : BitVec 64, ∃∗ sigPtr : BitVec 64,
      ∃∗ pad32 : BitVec 32,
        ⌜pubCap.toNat < 2 ^ 63⌝ ∗
        words88Sp sp' pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        signedPreKeyBufs A pubCap pubPtr privCap privPtr sigCap sigPtr m := by
  unfold signedPreKeyStructAt vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun sigCap => Entails.sepExists_elim fun sigPtr =>
    Entails.sepExists_elim fun privCap => Entails.sepExists_elim fun privPtr =>
    Entails.sepExists_elim fun pubCap => Entails.sepExists_elim fun pubPtr => ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (memRegion_four_entails (sp' + 8#64 + 0x54#64))))))) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad32 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pubCap)
  refine Entails.trans ?_ (Entails.sepExists_intro pubPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro privCap)
  refine Entails.trans ?_ (Entails.sepExists_intro privPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro sigCap)
  refine Entails.trans ?_ (Entails.sepExists_intro sigPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro pad32)
  rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
  dsimp only [vecHeader]
  have hp88 : ((sp' + 8#64 + 0x50#64) ↦₃₂ m.id) ∗ ((sp' + 8#64 + 0x54#64) ↦₃₂ pad32) =
      ((sp' + 88#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 88#64) m.id pad32
  rw [hp88]
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (vecU8Buf_cap_lt A pubCap pubPtr m.publicKey))) ?_
  unfold words88Sp signedPreKeyBufs
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; ac_rfl

theorem words88Sp_pack (sp' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    words88Sp sp' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ⊢ memRegion (sp' + 8#64) 88 := by
  unfold words88Sp
  rw [show (88 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8))))))))) by decide,
    ProofLib.memRegion_split (sp' + 8#64) 8 80 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64) 8 72 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (pointsTo64_entails_memRegion _ _))))))))))

theorem memRegion88_unpack (ret : BitVec 64) :
    memRegion ret 88 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
      ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64, ∃∗ r7 : BitVec 64,
      ∃∗ r8 : BitVec 64, ∃∗ r9 : BitVec 64, ∃∗ r10 : BitVec 64,
        words88Ret ret r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 := by
  unfold words88Ret
  rw [ProofLib.memRegion_split ret 8 80 (by decide),
    ProofLib.memRegion_split (ret + 8#64) 8 72 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64) 8 64 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (ret + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
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

theorem signedPreKeyStructAt_ret_pack (A : RustAlloc) (ret : BitVec 64)
    (pubCap pubPtr privCap privPtr sigCap sigPtr : BitVec 64) (pad32 : BitVec 32)
    (m : SignedPreKeyRecordStructure) :
    words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
        privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
        sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
        m.timestamp (pad32 ++ m.id) ∗
      signedPreKeyBufs A pubCap pubPtr privCap privPtr sigCap sigPtr m ⊢
      kyberPreKeyResultAt A ret (.ok ⟨m⟩) := by
  dsimp only [kyberPreKeyResultAt]
  unfold signedPreKeyStructAt words88Ret signedPreKeyBufs
  refine Entails.trans ?_
    (sepConj_mono (vecU8At_entails_vecU8 A ret pubCap pubPtr m.publicKey)
      (sepConj_mono (vecU8At_entails_vecU8 A (ret + 0x18#64) privCap privPtr m.privateKey)
        (sepConj_mono_left (vecU8At_entails_vecU8 A (ret + 0x30#64) sigCap sigPtr m.signature))))
  rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
  dsimp only [vecHeader]
  have hp80 : ((ret + 80#64) ↦₆₄ (pad32 ++ m.id)) =
      ((ret + 0x50#64) ↦₃₂ m.id) ∗ ((ret + 0x54#64) ↦₃₂ pad32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (pointsTo32_pair (ret + 80#64) m.id pad32).symm
  rw [hp80]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (pointsTo32_entails_memRegion (ret + 84#64) pad32)))))))))))))))
  apply entails_of_eq; ac_rfl

theorem memRegion88_err_unpack (ret : BitVec 64) :
    memRegion ret 88 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64,
        (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ memRegion (ret + 16#64) 72 := by
  rw [ProofLib.memRegion_split ret 8 80 (by decide),
    ProofLib.memRegion_split (ret + 8#64) 8 72 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r1 => Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  exact Entails.refl _

theorem errLocal88_pack (sp' e : BitVec 64) :
    ((sp' + 8#64) ↦₆₄ errTag) ∗ ((sp' + 16#64) ↦₆₄ e) ∗ memRegion (sp' + 24#64) 72 ⊢
      memRegion (sp' + 8#64) 88 := by
  rw [show (88 : Nat) = 8 + (8 + 72) by decide,
    ProofLib.memRegion_split (sp' + 8#64) 8 80 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64) 8 72 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))

theorem kyberErr88_pack (A : RustAlloc) (ret : BitVec 64) :
    (ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (ret + 16#64) 72 ⊢
      kyberPreKeyResultAt A ret (.error .invalidProtobufEncoding) := by
  dsimp only [kyberPreKeyResultAt, errResultAt, speAt, speWord]
  rw [ProofLib.memRegion_split (ret + 16#64) 40 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  apply entails_of_eq; ac_rfl

theorem okExit_pack (A : RustAlloc) (sp ret bytesA : BitVec 64) (bytes : List (BitVec 8))
    (pubCap pubPtr privCap privPtr sigCap sigPtr c0 c1 c2 c3 : BitVec 64) (pad32 : BitVec 32)
    (m : SignedPreKeyRecordStructure) :
    words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
        privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
        sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
        m.timestamp (pad32 ++ m.id) ∗
      signedPreKeyBufs A pubCap pubPtr privCap privPtr sigCap sigPtr m ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStack ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack)) ∗
      A.pool ⊢
      kyberPreKeyResultAt A ret (.ok ⟨m⟩) ∗
        (bytesA ↦ₛ bytes) ∗
        stackAt sp smallRootStack ∗
        A.pool := by
  have hsp88 := words88Sp_pack (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
    privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
    sigCap sigPtr (BitVec.ofNat 64 m.signature.length) m.timestamp (pad32 ++ m.id)
  have hret := signedPreKeyStructAt_ret_pack A ret pubCap pubPtr privCap privPtr sigCap sigPtr pad32 m
  have hstk := kpkStack_exit_pack sp c0 c1 c2 c3
  have hstk' :
      memRegion (sp - 128#64) 8 ∗
        words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStack ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ⊢
      stackAt sp smallRootStack :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hsp88)) hstk
  rw [← sepConj_assoc (words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
      privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
      sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
      m.timestamp (pad32 ++ m.id))]
  exact sepConj_mono hret (sepConj_mono_right (sepConj_mono_left hstk'))

theorem errExit_pack (A : RustAlloc) (sp ret bytesA e c0 c1 c2 c3 : BitVec 64)
    (bytes : List (BitVec 8)) :
    ((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (ret + 16#64) 72) ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStack ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack)) ∗
      A.pool ⊢
      kyberPreKeyResultAt A ret (.error .invalidProtobufEncoding) ∗
        (bytesA ↦ₛ bytes) ∗
        stackAt sp smallRootStack ∗
        A.pool := by
  have hsp88 := errLocal88_pack (sp - 128#64) e
  have hret := kyberErr88_pack A ret
  have hstk := kpkStack_exit_pack sp c0 c1 c2 c3
  have hstk' :
      memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStack ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ⊢
      stackAt sp smallRootStack :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hsp88)) hstk
  exact sepConj_mono hret (sepConj_mono_right (sepConj_mono_left hstk'))

end CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers
