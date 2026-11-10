/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.RoundLemmas
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Decodes
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Write36
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.WriteU8
import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Lemmas
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Correctness of `RandomState::hash_one::<&ProtocolAddress>`

Proves `hashOneAddrBorrow36_ok`: `<RandomState as BuildHasher>::hash_one::<&ProtocolAddress>`
hashes a 36-byte UUID name, `0xff` string terminator, and 1-byte `device_id` via three calls
to `SipHasher13::write` followed by an inlined `SipHasher13::finish`, returning `hashAddrBv`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

namespace HashOne

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

/-! ## Call-Site Transport of `SipHasher13::write` -/

theorem sipWrite36_ok_at_hashOne (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashOneAddrName + bv% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" - ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>"))
      sipWrite36Spec := by
  have h1 : libsignalSessionCode.fnOff hashOneAddrName = num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") :=
    (ls_lemma% fnOff "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")
  have h2 : libsignalSessionCode.fnOff sipWriteName = num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write") :=
    (ls_lemma% fnOff "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")
  have haddr :
      (RebasedProg b ext).fnAddr hashOneAddrName + bv% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" - ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") =
      (RebasedProg b ext).fnAddr sipWriteName := by
    simp only [RebasedProg, Program.fnAddr_rebase, h1, h2]
    rw [BitVec.add_assoc]; rfl
  rw [haddr]
  exact sipWrite36_ok b ext

/-- `BitVec 8` wrapper around `SipHasher13.writeU8` avoiding raw `UInt8.ofBitVec`
inside postcondition lambdas during `foldStructEtaTarget`. -/
def writeBv8 (h : SipHasher13) (b : BitVec 8) : SipHasher13 :=
  h.writeU8 (UInt8.ofBitVec b)

def sipWriteBv8Spec : Spec SipWriteU8Ghost where
  pre := sipWriteU8Spec.pre
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sipHasher13At x.hAddr (writeBv8 x.h x.b) ∗
      (x.bPtr ↦₈ x.b)

theorem sipWriteU8_ok_at_hashOne (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashOneAddrName + bv% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" - ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>"))
      sipWriteBv8Spec := by
  have h1 : libsignalSessionCode.fnOff hashOneAddrName = num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") :=
    (ls_lemma% fnOff "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")
  have h2 : libsignalSessionCode.fnOff sipWriteName = num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write") :=
    (ls_lemma% fnOff "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")
  have haddr :
      (RebasedProg b ext).fnAddr hashOneAddrName + bv% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" - ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") =
      (RebasedProg b ext).fnAddr sipWriteName := by
    simp only [RebasedProg, Program.fnAddr_rebase, h1, h2]
    rw [BitVec.add_assoc]; rfl
  rw [haddr]
  exact sipWriteU8_ok b ext

/-! ## Stack Frame Decomposition -/

theorem stackAt_hashOne_eq (sp : BitVec 64) :
    stackAt sp hashOneAddrStack =
      memRegion (sp - 0x70#64) 8 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 0x68#64) ↦₆₄ c0) ∗ ((sp - 0x60#64) ↦₆₄ c1) ∗
        ((sp - 0x58#64) ↦₆₄ c2) ∗ ((sp - 0x50#64) ↦₆₄ c3) ∗
        ((sp - 0x48#64) ↦₆₄ c4) ∗ ((sp - 0x40#64) ↦₆₄ c5) ∗
        ((sp - 0x38#64) ↦₆₄ c6) ∗ ((sp - 0x30#64) ↦₆₄ c7) ∗
        ((sp - 0x28#64) ↦₆₄ c8) ∗ ((sp - 0x20#64) ↦₆₄ c9) ∗
        ((sp - 0x18#64) ↦₆₄ c10) ∗ ((sp - 0x10#64) ↦₆₄ c11)) ∗
      memRegion (sp - 0x08#64) 4 ∗
      (∃∗ b0 : BitVec 8, (sp - 0x04#64) ↦₈ b0) ∗
      memRegion (sp - 0x03#64) 3 := by
  simp only [stackAt, hashOneAddrStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 112) (n := 8) (k := 104)
        (b' := sp - 0x68#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x68#64) (n := 96) (k := 8)
        (b' := sp - 0x08#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x08#64) (n := 4) (k := 4)
        (b' := sp - 0x04#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x04#64) (n := 1) (k := 3)
        (b' := sp - 0x03#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - 0x70#64) 8 ∗
    (memRegion (sp - 0x68#64) (8 * 12) ∗
      (memRegion (sp - 0x08#64) 4 ∗
        (memRegion (sp - 0x04#64) 1 ∗ memRegion (sp - 0x03#64) 3))) = _
  rw [memRegion_cells (sp - 0x68#64) 12 (by decide), memRegion_one (sp - 0x04#64)]
  have hc12 : cells (sp - 0x68#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 0x68#64) ↦₆₄ c0) ∗ ((sp - 0x60#64) ↦₆₄ c1) ∗
        ((sp - 0x58#64) ↦₆₄ c2) ∗ ((sp - 0x50#64) ↦₆₄ c3) ∗
        ((sp - 0x48#64) ↦₆₄ c4) ∗ ((sp - 0x40#64) ↦₆₄ c5) ∗
        ((sp - 0x38#64) ↦₆₄ c6) ∗ ((sp - 0x30#64) ↦₆₄ c7) ∗
        ((sp - 0x28#64) ↦₆₄ c8) ∗ ((sp - 0x20#64) ↦₆₄ c9) ∗
        ((sp - 0x18#64) ↦₆₄ c10) ∗ ((sp - 0x10#64) ↦₆₄ c11)) := by
    cells_unfold
  rw [hc12]

theorem rejoin_stack_hashOne (sp : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) (b0 : BitVec 8) :
    memRegion (sp - 0x70#64) 8 ∗
      (((sp - 0x68#64) ↦₆₄ c0) ∗ ((sp - 0x60#64) ↦₆₄ c1) ∗
       ((sp - 0x58#64) ↦₆₄ c2) ∗ ((sp - 0x50#64) ↦₆₄ c3) ∗
       ((sp - 0x48#64) ↦₆₄ c4) ∗ ((sp - 0x40#64) ↦₆₄ c5) ∗
       ((sp - 0x38#64) ↦₆₄ c6) ∗ ((sp - 0x30#64) ↦₆₄ c7) ∗
       ((sp - 0x28#64) ↦₆₄ c8) ∗ ((sp - 0x20#64) ↦₆₄ c9) ∗
       ((sp - 0x18#64) ↦₆₄ c10) ∗ ((sp - 0x10#64) ↦₆₄ c11)) ∗
      memRegion (sp - 0x08#64) 4 ∗
      ((sp - 0x04#64) ↦₈ b0) ∗
      memRegion (sp - 0x03#64) 3 ⊢
      stackAt sp hashOneAddrStack := by
  rw [stackAt_hashOne_eq sp]
  have hc12 :
      ((sp - 0x68#64) ↦₆₄ c0) ∗ ((sp - 0x60#64) ↦₆₄ c1) ∗
      ((sp - 0x58#64) ↦₆₄ c2) ∗ ((sp - 0x50#64) ↦₆₄ c3) ∗
      ((sp - 0x48#64) ↦₆₄ c4) ∗ ((sp - 0x40#64) ↦₆₄ c5) ∗
      ((sp - 0x38#64) ↦₆₄ c6) ∗ ((sp - 0x30#64) ↦₆₄ c7) ∗
      ((sp - 0x28#64) ↦₆₄ c8) ∗ ((sp - 0x20#64) ↦₆₄ c9) ∗
      ((sp - 0x18#64) ↦₆₄ c10) ∗ ((sp - 0x10#64) ↦₆₄ c11) ⊢
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 0x68#64) ↦₆₄ c0) ∗ ((sp - 0x60#64) ↦₆₄ c1) ∗
        ((sp - 0x58#64) ↦₆₄ c2) ∗ ((sp - 0x50#64) ↦₆₄ c3) ∗
        ((sp - 0x48#64) ↦₆₄ c4) ∗ ((sp - 0x40#64) ↦₆₄ c5) ∗
        ((sp - 0x38#64) ↦₆₄ c6) ∗ ((sp - 0x30#64) ↦₆₄ c7) ∗
        ((sp - 0x28#64) ↦₆₄ c8) ∗ ((sp - 0x20#64) ↦₆₄ c9) ∗
        ((sp - 0x18#64) ↦₆₄ c10) ∗ ((sp - 0x10#64) ↦₆₄ c11)) :=
    Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
          (Entails.sepExists_right c9 (Entails.sepExists_right c10
            (Entails.sepExists_right c11 (Entails.refl _))))))))))))
  have hb0 : ((sp - 0x04#64) ↦₈ b0) ⊢ (∃∗ b0 : BitVec 8, (sp - 0x04#64) ↦₈ b0) :=
    Entails.sepExists_right b0 (Entails.refl _)
  exact sepConj_mono_right (sepConj_mono hc12 (sepConj_mono_right (sepConj_mono_left hb0)))

/-! ## `sipHasher13At` Unfolding at `sp - 0x68` -/

theorem sipHasher13At_sp_sub_68 (sp : BitVec 64) (h : SipHasher13)
    (hlen : h.length < 2 ^ 64) (hnt : h.ntail < 8) :
    sipHasher13At (sp - 0x68#64) h =
      ((sp - 0x68#64) ↦₆₄ h.state.v0.toBitVec) ∗
      ((sp - 0x60#64) ↦₆₄ h.state.v2.toBitVec) ∗
      ((sp - 0x58#64) ↦₆₄ h.state.v1.toBitVec) ∗
      ((sp - 0x50#64) ↦₆₄ h.state.v3.toBitVec) ∗
      ((sp - 0x48#64) ↦₆₄ h.k0.toBitVec) ∗
      ((sp - 0x40#64) ↦₆₄ h.k1.toBitVec) ∗
      ((sp - 0x38#64) ↦₆₄ BitVec.ofNat 64 h.length) ∗
      ((sp - 0x30#64) ↦₆₄ h.tail.toBitVec) ∗
      ((sp - 0x28#64) ↦₆₄ BitVec.ofNat 64 h.ntail) := by
  unfold sipHasher13At sipStateAt
  have hpure : (h.length < 2 ^ 64 ∧ h.ntail < 8) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hlen, hnt⟩⟩
  have ha1 : sp - 0x68#64 + 8#64 = sp - 0x60#64 := by bv_omega
  have ha2 : sp - 0x68#64 + 16#64 = sp - 0x58#64 := by bv_omega
  have ha3 : sp - 0x68#64 + 24#64 = sp - 0x50#64 := by bv_omega
  have ha4 : sp - 0x68#64 + 0x20#64 = sp - 0x48#64 := by bv_omega
  have ha5 : sp - 0x68#64 + 0x28#64 = sp - 0x40#64 := by bv_omega
  have ha6 : sp - 0x68#64 + 0x30#64 = sp - 0x38#64 := by bv_omega
  have ha7 : sp - 0x68#64 + 0x38#64 = sp - 0x30#64 := by bv_omega
  have ha8 : sp - 0x68#64 + 0x40#64 = sp - 0x28#64 := by bv_omega
  simp only [hpure, pure_true, emp_sepConj, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, sepConj_assoc]

theorem sipHasher13At_newWithKeys (sp k0 k1 : BitVec 64) :
    ((sp - 0x68#64) ↦₆₄ (k0 ^^^ 0x736f6d6570736575#64)) ∗
    ((sp - 0x60#64) ↦₆₄ (k0 ^^^ 0x6c7967656e657261#64)) ∗
    ((sp - 0x58#64) ↦₆₄ (k1 ^^^ 0x646f72616e646f6d#64)) ∗
    ((sp - 0x50#64) ↦₆₄ (k1 ^^^ 0x7465646279746573#64)) ∗
    ((sp - 0x48#64) ↦₆₄ k0) ∗
    ((sp - 0x40#64) ↦₆₄ k1) ∗
    ((sp - 0x38#64) ↦₆₄ 0#64) ∗
    ((sp - 0x30#64) ↦₆₄ 0#64) ∗
    ((sp - 0x28#64) ↦₆₄ 0#64) =
      sipHasher13At (sp - 0x68#64)
        (SipHasher13.newWithKeys (UInt64.ofBitVec k0) (UInt64.ofBitVec k1)) := by
  have hlen : (SipHasher13.newWithKeys (UInt64.ofBitVec k0) (UInt64.ofBitVec k1)).length < 2 ^ 64 := by
    simp
  have hnt : (SipHasher13.newWithKeys (UInt64.ofBitVec k0) (UInt64.ofBitVec k1)).ntail < 8 := by
    simp
  rw [sipHasher13At_sp_sub_68 sp
    (SipHasher13.newWithKeys (UInt64.ofBitVec k0) (UInt64.ofBitVec k1)) hlen hnt]
  unfold SipHasher13.newWithKeys SipHasher13.initState
  simp only [toBitVec_xor64]
  rfl

/-! ## Inlined `SipHasher13::finish` Word Identities -/

def finishCRoundBv (v0 v1 v2 v3 b : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let v3_0 := b ^^^ v3
  let v2_a := v3_0 + v2
  let v0_a := v1 + v0
  let v3_b := v2_a ^^^ v3_0.rotateRight 48
  let v1_a := v0_a ^^^ v1.rotateRight 51
  let v2_b := v2_a + v1_a
  let v2_1 := v2_b.rotateRight 32
  let v1_1 := v2_b ^^^ v1_a.rotateRight 47
  let v0_b := v3_b + v0_a.rotateRight 32
  let v3_1 := v0_b ^^^ v3_b.rotateRight 43
  let v0_1 := v0_b ^^^ b
  (v0_1, v1_1, v2_1, v3_1)

theorem finishCRoundBv_eq (v0 v1 v2 v3 b : BitVec 64) :
    let c := compressBv v0 v1 v2 (v3 ^^^ b)
    (c.1 ^^^ b, c.2.1, c.2.2.1, c.2.2.2) = finishCRoundBv v0 v1 v2 v3 b := by
  dsimp only [compressBv, finishCRoundBv]
  rw [BitVec.xor_comm v3 b, BitVec.add_comm v2 (b ^^^ v3)]

def finishDRound1Bv (v0 v1 v2 v3 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let v2' := v2 ^^^ 0xff#64
  let v2_a := v3 + v2'
  let v3_a := v2_a ^^^ v3.rotateRight 48
  let v0_a := v0 + v1
  let v1_a := v0_a ^^^ v1.rotateRight 51
  let v2_b := v1_a + v2_a
  let v1_1 := v2_b ^^^ v1_a.rotateRight 47
  let v0_1 := v3_a + v0_a.rotateRight 32
  let v3_1 := v0_1 ^^^ v3_a.rotateRight 43
  let v2_1 := v2_b.rotateRight 32
  (v0_1, v1_1, v2_1, v3_1)

theorem finishDRound1Bv_eq (v0 v1 v2 v3 : BitVec 64) :
    compressBv v0 v1 (v2 ^^^ 0xff#64) v3 = finishDRound1Bv v0 v1 v2 v3 := by
  dsimp only [compressBv, finishDRound1Bv]
  rw [BitVec.add_comm v1 v0,
      BitVec.add_comm (v2 ^^^ 0xff#64) v3,
      BitVec.add_comm (v3 + (v2 ^^^ 0xff#64)) ((v0 + v1) ^^^ v1.rotateRight 51)]

def finishDRound2Bv (v0 v1 v2 v3 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let v0_a := v1 + v0
  let v2_a := v3 + v2
  let v1_a := v0_a ^^^ v1.rotateRight 51
  let v3_a := v2_a ^^^ v3.rotateRight 48
  let v0_1 := v3_a + v0_a.rotateRight 32
  let v3_1 := v0_1 ^^^ v3_a.rotateRight 43
  let v2_b := v1_a + v2_a
  let v1_1 := v2_b ^^^ v1_a.rotateRight 47
  let v2_1 := v2_b.rotateRight 32
  (v0_1, v1_1, v2_1, v3_1)

theorem finishDRound2Bv_eq (v0 v1 v2 v3 : BitVec 64) :
    compressBv v0 v1 v2 v3 = finishDRound2Bv v0 v1 v2 v3 := by
  dsimp only [compressBv, finishDRound2Bv]
  rw [BitVec.add_comm v2 v3,
      BitVec.add_comm (v3 + v2) ((v1 + v0) ^^^ v1.rotateRight 51)]

def finishDRound3XorBv (v0 v1 v2 v3 : BitVec 64) : BitVec 64 :=
  let v0_a := v1 + v0
  let v2_a := v3 + v2
  let v1_a := v0_a ^^^ v1.rotateRight 51
  let v3_a := v2_a ^^^ v3.rotateRight 48
  let v2_b := v1_a + v2_a
  let r9 := v3_a.rotateRight 43 ^^^ v1_a.rotateRight 47
  (r9 ^^^ v2_b.rotateRight 32) ^^^ v2_b

theorem xor_finish_cancel (v0_1 v2_b r47 r43 : BitVec 64) :
    v0_1 ^^^ (v2_b ^^^ r47) ^^^ v2_b.rotateRight 32 ^^^ (v0_1 ^^^ r43) =
      ((r43 ^^^ r47) ^^^ v2_b.rotateRight 32) ^^^ v2_b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases v0_1.getLsbD i <;> cases v2_b.getLsbD i <;> cases r47.getLsbD i <;>
    cases (v2_b.rotateRight 32).getLsbD i <;> cases r43.getLsbD i <;> rfl

theorem finishDRound3XorBv_eq (v0 v1 v2 v3 : BitVec 64) :
    let c := compressBv v0 v1 v2 v3
    c.1 ^^^ c.2.1 ^^^ c.2.2.1 ^^^ c.2.2.2 = finishDRound3XorBv v0 v1 v2 v3 := by
  dsimp only [compressBv, finishDRound3XorBv]
  rw [BitVec.add_comm v2 v3,
      BitVec.add_comm (v3 + v2) ((v1 + v0) ^^^ v1.rotateRight 51)]
  exact xor_finish_cancel _ _ _ _

attribute [local irreducible] compressBv in
theorem toBitVec_finish_of_length_38 (h : SipHasher13) (hlen : h.length = 38) :
    h.finish.toBitVec =
      let b := h.tail.toBitVec ||| 0x2600000000000000#64
      let c0 := finishCRoundBv h.state.v0.toBitVec h.state.v1.toBitVec h.state.v2.toBitVec h.state.v3.toBitVec b
      let d1 := finishDRound1Bv c0.1 c0.2.1 c0.2.2.1 c0.2.2.2
      let d2 := finishDRound2Bv d1.1 d1.2.1 d1.2.2.1 d1.2.2.2
      finishDRound3XorBv d2.1 d2.2.1 d2.2.2.1 d2.2.2.2 := by
  unfold SipHasher13.finish SipHashModel.dRounds
  rw [hlen, eq_stateOfBv h.state]
  have hb : ((((UInt64.ofNat 38) &&& 0xff) <<< 56) ||| h.tail).toBitVec =
      h.tail.toBitVec ||| 0x2600000000000000#64 := by
    rw [toBitVec_or64]
    change 0x2600000000000000#64 ||| h.tail.toBitVec = h.tail.toBitVec ||| 0x2600000000000000#64
    exact BitVec.or_comm _ _
  dsimp only
  rw [compressBlock_stateOfBv, hb]
  have hc0 := finishCRoundBv_eq h.state.v0.toBitVec h.state.v1.toBitVec
    h.state.v2.toBitVec h.state.v3.toBitVec (h.tail.toBitVec ||| 0x2600000000000000#64)
  dsimp only at hc0
  rw [Prod.mk.injEq] at hc0; rcases hc0 with ⟨hc0_0, hc0⟩
  rw [Prod.mk.injEq] at hc0; rcases hc0 with ⟨hc0_1, hc0⟩
  rw [Prod.mk.injEq] at hc0; rcases hc0 with ⟨hc0_2, hc0_3⟩
  rw [hc0_0, hc0_1, hc0_2, hc0_3]
  set c0 := finishCRoundBv h.state.v0.toBitVec h.state.v1.toBitVec
    h.state.v2.toBitVec h.state.v3.toBitVec (h.tail.toBitVec ||| 0x2600000000000000#64)
  have hs2 : { stateOfBv c0.1 c0.2.1 c0.2.2.1 c0.2.2.2 with
      v2 := (stateOfBv c0.1 c0.2.1 c0.2.2.1 c0.2.2.2).v2 ^^^ 0xff } =
      stateOfBv c0.1 c0.2.1 (c0.2.2.1 ^^^ 0xff#64) c0.2.2.2 := by
    apply state_ext <;> simp [stateOfBv]
  rw [hs2, compress_stateOfBv, finishDRound1Bv_eq]
  set d1 := finishDRound1Bv c0.1 c0.2.1 c0.2.2.1 c0.2.2.2
  rw [compress_stateOfBv, finishDRound2Bv_eq]
  set d2 := finishDRound2Bv d1.1 d1.2.1 d1.2.2.1 d1.2.2.2
  rw [compress_stateOfBv]
  simp only [stateOfBv, toBitVec_xor64, UInt64.toBitVec_ofBitVec]
  exact finishDRound3XorBv_eq d2.1 d2.2.1 d2.2.2.1 d2.2.2.2

end HashOne

open HashOne

attribute [local irreducible] Program.fnOff

set_option maxHeartbeats 1600000 in
/-- `<RandomState as BuildHasher>::hash_one::<&ProtocolAddress>` satisfies
`hashOneAddrBorrow36Spec` on `RebasedProg b ext`. -/
theorem hashOneAddrBorrow36_ok (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashOneAddrName)
      hashOneAddrBorrow36Spec := by
  have h_w36 := sipWrite36_ok_at_hashOne b ext
  have h_wu8 := sipWriteU8_ok_at_hashOne b ext
  simp only [hashOneAddrBorrow36Spec]
  have hfn : libsignalSessionCode.fnOff hashOneAddrName = num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") :=
    (ls_lemma% fnOff "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")) 380
  clear hfn
  dsimp only [RebasedProg, hashOneAddrName, BitVec.ofNat_eq_ofNat] at h_w36 h_wu8 ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr
    "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨k0, k1, addr, ptr, name, dev⟩ := x
  dsimp only at *
  unfold addrBorrowAt
  rw [h]
  wp_conv_pre => rw [stackAt_hashOne_eq s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  wp_steps
  -- Call 1: write(ptr, 36)
  let h0 := SipHasher13.newWithKeys (UInt64.ofBitVec k0) (UInt64.ofBitVec k1)
  have hh0_len : h0.length + 36 < 2 ^ 64 := by change 0 + 36 < 2 ^ 64; decide
  have hh0_nt : h0.ntail = 0 := rfl
  refine SepWP.fold (Entails.of_eq (sipHasher13At_newWithKeys s0.sp k0 k1)) (by sep_focus) ?_
  wp_apply
  wp_steps
  -- Call 2: write(&0xff, 1)
  let h1 := h0.write (name.map UInt8.ofBitVec)
  have hh1_len_eq : h1.length = 36 := by
    simp [h1, h0, SipHasher13.write_length, h]
  have hh1_nt_eq : h1.ntail = 4 := by
    rw [show h1 = h0.write (name.map UInt8.ofBitVec) from rfl,
        SipHasher13.write_of_ntail_zero h0 (name.map UInt8.ofBitVec) hh0_nt]
    simp [h]
  have hh1_len : h1.length + 1 < 2 ^ 64 := by rw [hh1_len_eq]; decide
  have hh1_nt1 : 1 ≤ h1.ntail := by rw [hh1_nt_eq]; decide
  have hh1_nt6 : h1.ntail ≤ 6 := by rw [hh1_nt_eq]; decide
  wp_apply
  wp_steps
  -- Call 3: write(&dev, 1)
  let h2 := writeBv8 h1 0xff#8
  have hh2_len_eq : h2.length = 37 := by
    simp [h2, writeBv8, SipHasher13.writeU8_length, hh1_len_eq]
  have hh2_nt_eq : h2.ntail = 5 := by
    rw [show h2 = h1.writeU8 (UInt8.ofBitVec 0xff#8) from rfl,
        SipHasher13.writeU8_of_ntail_between h1 (UInt8.ofBitVec 0xff#8)
          (by omega) (by omega)]
    dsimp only
    omega
  have hh2_len : h2.length + 1 < 2 ^ 64 := by rw [hh2_len_eq]; decide
  have hh2_nt1 : 1 ≤ h2.ntail := by rw [hh2_nt_eq]; decide
  have hh2_nt6 : h2.ntail ≤ 6 := by rw [hh2_nt_eq]; decide
  wp_apply
  -- Inlined SipHasher13::finish
  let h3 := writeBv8 h2 dev
  have hh3_len_eq : h3.length = 38 := by
    simp [h3, writeBv8, SipHasher13.writeU8_length, hh2_len_eq]
  have hh3_nt_eq : h3.ntail = 6 := by
    rw [show h3 = h2.writeU8 (UInt8.ofBitVec dev) from rfl,
        SipHasher13.writeU8_of_ntail_between h2 (UInt8.ofBitVec dev)
          (by omega) (by omega)]
    dsimp only
    omega
  have hh3_unfold := sipHasher13At_sp_sub_68 s0.sp h3
    (by rw [hh3_len_eq]; decide) (by rw [hh3_nt_eq]; decide)
  rw [hh3_len_eq, hh3_nt_eq] at hh3_unfold
  refine SepWP.fold (Entails.of_eq hh3_unfold) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (rejoin_stack_hashOne s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  have hhash_eq : hashAddrBv k0 k1 name dev = h3.finish.toBitVec := rfl
  rw [hhash_eq, toBitVec_finish_of_length_38 h3 hh3_len_eq]
  dsimp only [finishCRoundBv, finishDRound1Bv, finishDRound2Bv, finishDRound3XorBv]
  wp_done

end CryptoVerification.E2E.InMem.SipHashBin
