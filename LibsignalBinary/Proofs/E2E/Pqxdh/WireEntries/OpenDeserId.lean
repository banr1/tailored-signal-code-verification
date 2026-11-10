/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenEmptyPrefix
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.CalleesStoreRecord -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenEmpty -- shake: keep

/-!
# Non-Empty Session Proof (`open_subroutine_ok`) for `libsignal_pqxdh_e2e::open`

Proves `open_subroutine_ok` for `openSpecP C A img` by combining the shared prefix (`+0x000..+0x1b8`),
the non-empty session deserialization and identity/session store branch (`+0x1b8..+0x2a4`), and the
shared epilogue (`+0x2a4..+0x328`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
export CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.InMem

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb_append_lo_open (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi_lt; simp [hi_lt]

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb_append_hi_open (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi_lt; simp [hi_lt]

@[local arm64_norm, local wp_norm]
private theorem spAligned_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).spAligned = s.spAligned := rfl
@[local arm64_norm, local wp_norm]
private theorem sp_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl
@[local arm64_norm, local wp_norm]
private theorem readReg64_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) (reg : Reg)
    :
    (s.writeVReg128 r v).readReg64 reg = s.readReg64 reg := rfl
@[local arm64_norm, local wp_norm]
private theorem readReg32_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) (reg : Reg)
    :
    (s.writeVReg128 r v).readReg32 reg = s.readReg32 reg := rfl
@[local arm64_norm, local wp_norm]
private theorem readReg_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) (w :
    RegWidth) (reg : Reg) :
    (s.writeVReg128 r v).readReg w reg = s.readReg w reg := rfl
@[local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).tpidrEl0 = s.tpidrEl0 := rfl
@[local arm64_norm, local wp_norm]
private theorem trace_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := rfl
@[local arm64_norm, local wp_norm]
private theorem symtab_writeVReg128_open (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).symtab = s.symtab := rfl
@[local arm64_norm, local wp_norm]
private theorem symtab_setPC_open (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := rfl
@[local arm64_norm, local wp_norm]
private theorem symtab_setMem_setPC_open (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setMem m).setPC pc).symtab = s.symtab := rfl

attribute [local arm64_norm, local wp_norm]
  extractLsb_append_lo_open extractLsb_append_hi_open

/-! ## Instruction-Level `SepWP` Lemmas (`+0x1bc..+0x2a4`) -/

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## Segment Composition (`+0x1b8..ret`) -/

theorem stateLenBv_beq_zero_false {stateLenBv : BitVec 64} {stateBytes : List (BitVec 8)}
    {sess : Session (List (BitVec 8))}
    (hx5 : stateLenBv.toNat = stateBytes.length)
    (hcan : RecordCanonical stateBytes sess) :
    (stateLenBv == 0#64) = false :=
  reg_nz_of_toNat_pos hx5 (recordCanonical_length_pos hcan)

theorem openSpecP_panic_of_allocFailed (C : Crypto) (A : RustAlloc) (img : Obj.Image)
    (g : OpenGhostP) (R : SepProp) {s0 s1 sf : State}
    (htr : s1.trace = s0.trace) (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ anyHeap ∗ R) (halloc : allocFailedIn s1 sf ∧ s1.trace <+: sf.trace) :
    SubroutineOutcome (openSpecP C A img) g R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  dsimp only [openSpecP, Spec.inImage]
  have ⟨ha0, hpref⟩ := allocFailedIn_of_trace_eq htr halloc
  have h1 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R =
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ R) := by ac_rfl
  rw [h1, satisfies_pure_sepConj]
  exact ⟨⟨ha0, hpref⟩, hm⟩

theorem openSpecP_panic_of_callee_onPanic (C : Crypto) (A : RustAlloc) (img : Obj.Image)
    (g : OpenGhostP) (R R_extra : SepProp) {s0 s1 sf : State}
    (htr : s1.trace = s0.trace) (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (R_extra ∗ R)) :
    SubroutineOutcome (openSpecP C A img) g R s0 sf := by
  have hm' : sf.mem ⊨ ⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ ((anyHeap ∗ R_extra) ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [satisfies_pure_sepConj] at hm'
  exact openSpecP_panic_of_allocFailed C A img g R htr hpan
    (Arm64.Satisfies.mono (sepConj_mono_left (anyHeap_absorb_right R_extra)) hm'.2) hm'.1

theorem memRegion_openP_0x0f0_0x360_deser_split (sp : BitVec 64) :
    memRegion (sp + 0x0f0#64) 0x360 =
      memRegion (sp + 0x0f0#64) 0x170 ∗
      memRegion (sp + 0x260#64) 0x170 ∗
      memRegion (sp + 0x3d0#64) 0x80 := by
  rw [memRegion_split' (b := sp + 0x0f0#64) (b' := sp + 0x260#64)
        (N := 0x360) (n := 0x170) (k := 0x1f0) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x3d0#64)
        (N := 0x1f0) (n := 0x170) (k := 0x80) (by decide) (by bv_lin) (by decide)]

theorem memRegion_openP_0x260_0x1f0_join (sp : BitVec 64) :
    memRegion (sp + 0x260#64) 0x170 ∗ memRegion (sp + 0x3d0#64) 0x80 =
      memRegion (sp + 0x260#64) 0x1f0 := by
  rw [← memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x3d0#64)
        (N := 0x1f0) (n := 0x170) (k := 0x80) (by decide) (by bv_lin) (by decide)]

def OpenSeam1e8P (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (img : Obj.Image) (abs : String → Option (State → State))
    (g : OpenGhostP) (role : Role) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr openPqxdhName + 0x1e8#64 ∧
    s.status = .Running ∧ s.spAligned = true ∧
    s0.spAligned = true ∧ openPqxdhStack ≤ s0.sp.toNat ∧
    s.sp = s0.sp - 0x4b0#64 ∧
    s.tpidrEl0 = s0.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s.mem ∧
    s.trace = s0.trace ∧
    s.readReg64 .x19 = g.outPtr ∧
    s.readReg64 .x24 = s.sp + 0x008#64 ∧
    s.readReg64 .x25 = s.sp + 0x260#64 ∧
    OpenX27VPreserved s s0 ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    g.meBytes.length = 36 ∧
    g.stateBytes.length < 2 ^ 63 ∧
    RecordCanonical g.stateBytes g.sess ∧
    g.sess.state.remoteIdentity.isSome ∧
    img.FrozenLoaded s ∧
    (s.mem ⊨
      callEmptyAtP A img (s.sp + 0x008#64) role
        (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes) ∗
      (∃∗ G, ⌜BinCanonSession G g.sess⌝ ∗
        sessionRecordAt A (s.sp + 0x0f0#64) ⟨0#64, 8#64, some G⟩ ⟨some g.sess⟩) ∗
      memRegion s.sp 8 ∗ memRegion (s.sp + 0x260#64) 0x1f0 ∗
      openSavedRegsAtP s0 ∗
      memRegion g.outPtr 232 ∗ (g.mePtr ↦ₛ g.meBytes) ∗
      (g.statePtr ↦ₛ g.stateBytes) ∗ logOff img ∗
      (∃∗ tlsCur, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur) ∗
      A.pool ∗ memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
      R ∗ anyHeap)

/-! ### Segment 3b (`+0x1e8..+0x21c`): `remote_identity_key_bytes` and `IdentityKey::decode` -/

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 : cap = 0xffffffffffffffff#64 := by bv_omega
  subst h1
  revert h; decide

theorem memRegion_openP_0x260_0x1f0_rem_split (sp : BitVec 64) :
    memRegion (sp + 0x260#64) 0x1f0 =
      memRegion (sp + 0x260#64) 32 ∗
      memRegion (sp + 0x280#64) 8 ∗
      memRegion (sp + 0x288#64) 0x1c8 := by
  rw [memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x280#64)
        (N := 0x1f0) (n := 32) (k := 464) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64)
        (N := 464) (n := 8) (k := 0x1c8) (by decide) (by bv_lin) (by decide)]

theorem words4_and_8_entails_memRegion_40 (sp w0 w1 w2 w3 : BitVec 64) :
    ((sp + 0x260#64) ↦₆₄ w0) ∗ ((sp + 0x268#64) ↦₆₄ w1) ∗
    ((sp + 0x270#64) ↦₆₄ w2) ∗ ((sp + 0x278#64) ↦₆₄ w3) ∗
    memRegion (sp + 0x280#64) 8 ⊢
      memRegion (sp + 0x260#64) 40 := by
  rw [memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x268#64)
        (N := 40) (n := 8) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x268#64) (b' := sp + 0x270#64)
        (N := 32) (n := 8) (k := 24) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x270#64) (b' := sp + 0x278#64)
        (N := 24) (n := 8) (k := 16) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x278#64) (b' := sp + 0x280#64)
        (N := 16) (n := 8) (k := 8) (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))

theorem vecU8_33_elim (A : RustAlloc) (sp : BitVec 64) (ik : IdentityKey) :
    RustHeap.vecU8 A (sp + 0x260#64 + 8#64) (0x05#8 :: ik.publicKey.bytes.toList) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜(cap + 1#64 == 0#64) = false⌝ ∗
        ((sp + 0x268#64) ↦₆₄ cap) ∗ ((sp + 0x270#64) ↦₆₄ ptr) ∗ ((sp + 0x278#64) ↦₆₄ 33#64) ∗
        (ptr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗ anyHeap := by
  unfold RustHeap.vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have hlen : (0x05#8 :: ik.publicKey.bytes.toList).length = 33 := by
    simp [List.Vector.toList_length]
  have ha0 : sp + 0x260#64 + 8#64 = sp + 0x268#64 := by bv_lin
  have ha1 : (sp + 0x260#64 + 8#64) + 8#64 = sp + 0x270#64 := by bv_lin
  have ha2 : (sp + 0x260#64 + 8#64) + 16#64 = sp + 0x278#64 := by bv_lin
  rw [ha1, ha2, ha0, hlen]
  by_cases hcap0 : cap = 0
  · simp only [hcap0, ↓reduceIte]
    refine Entails.trans (Entails.of_eq (show
      (((sp + 0x268#64) ↦₆₄ 0) ∗ ((sp + 0x270#64) ↦₆₄ ptr) ∗ ((sp + 0x278#64) ↦₆₄ 33#64)) ∗
        ⌜33 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ emp =
      ⌜33 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((sp + 0x268#64) ↦₆₄ 0) ∗ ((sp + 0x270#64) ↦₆₄ ptr) ∗ ((sp + 0x278#64) ↦₆₄ 33#64) ∗
          emp) by ac_rfl)) ?_
    exact Entails.pure_left fun ⟨h33, _⟩ => False.elim (by revert h33; decide)
  · simp only [hcap0, ↓reduceIte]
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    refine Entails.trans (Entails.of_eq (show
      (((sp + 0x268#64) ↦₆₄ cap) ∗ ((sp + 0x270#64) ↦₆₄ ptr) ∗ ((sp + 0x278#64) ↦₆₄ 33#64)) ∗
        ⌜33 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗
        memRegion (ptr + 33#64) (cap.toNat - 33) =
      ⌜33 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((sp + 0x268#64) ↦₆₄ cap) ∗ ((sp + 0x270#64) ↦₆₄ ptr) ∗ ((sp + 0x278#64) ↦₆₄ 33#64) ∗
         (ptr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗
         (A.live ptr cap.toNat 1 ∗ memRegion (ptr + 33#64) (cap.toNat - 33))) by ac_rfl)) ?_
    refine Entails.pure_left fun ⟨_, hcap_lt, _⟩ => ?_
    refine Entails.pure_right (cap_add_one_beq_zero_false hcap_lt) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (ProofLib.entails_anyHeap _))))

def OpenSeam21cP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (img : Obj.Image) (abs : String → Option (State → State))
    (g : OpenGhostP) (role : Role) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr openPqxdhName + 0x21c#64 ∧
    s.status = .Running ∧ s.spAligned = true ∧
    s0.spAligned = true ∧ openPqxdhStack ≤ s0.sp.toNat ∧
    s.sp = s0.sp - 0x4b0#64 ∧
    s.tpidrEl0 = s0.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s.mem ∧
    s.trace = s0.trace ∧
    s.readReg64 .x19 = g.outPtr ∧
    s.readReg64 .x24 = s.sp + 0x008#64 ∧
    s.readReg64 .x25 = s.sp + 0x260#64 ∧
    OpenX27VPreserved s s0 ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    g.meBytes.length = 36 ∧
    g.stateBytes.length < 2 ^ 63 ∧
    RecordCanonical g.stateBytes g.sess ∧
    img.FrozenLoaded s ∧
    (s.mem ⊨
      callEmptyAtP A img (s.sp + 0x008#64) role
        (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes) ∗
      (∃∗ G, ⌜BinCanonSession G g.sess⌝ ∗
        sessionRecordAt A (s.sp + 0x0f0#64) ⟨0#64, 8#64, some G⟩ ⟨some g.sess⟩) ∗
      (∃∗ peerKey : IdentityKey,
        ⌜g.sess.state.remoteIdentity = some peerKey⌝ ∗
        ((s.sp + 0x260#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((s.sp + 0x268#64) ↦ₛ peerKey.publicKey.bytes.toList)) ∗
      memRegion s.sp 8 ∗ memRegion (s.sp + 0x288#64) 0x1c8 ∗
      openSavedRegsAtP s0 ∗
      memRegion g.outPtr 232 ∗ (g.mePtr ↦ₛ g.meBytes) ∗
      (g.statePtr ↦ₛ g.stateBytes) ∗ logOff img ∗
      (∃∗ tlsCur, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur) ∗
      A.pool ∗ memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
      R ∗ anyHeap)

/-! ### Segment 3c (`+0x21c..+0x264`): `<InMemIdentityKeyStore>::save_identity` and `poll_once` -/

theorem memRegion_openP_0x288_0x1c8_save_split (sp : BitVec 64) :
    memRegion (sp + 0x288#64) 0x1c8 =
      memRegion (sp + 0x288#64) 8 ∗
      memRegion (sp + 0x290#64) 0x140 ∗
      memRegion (sp + 0x3d0#64) 32 ∗
      memRegion (sp + 0x3f0#64) 24 ∗
      memRegion (sp + 0x408#64) 0x48 := by
  rw [memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x290#64)
        (N := 0x1c8) (n := 8) (k := 448) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x3d0#64)
        (N := 448) (n := 0x140) (k := 128) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x3d0#64) (b' := sp + 0x3f0#64)
        (N := 128) (n := 32) (k := 96) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x3f0#64) (b' := sp + 0x408#64)
        (N := 96) (n := 24) (k := 0x48) (by decide) (by bv_lin) (by decide)]

theorem words5_and_8_entails_memRegion_48 (sp w0 w1 w2 w3 w4 : BitVec 64) :
    ((sp + 0x260#64) ↦₆₄ w0) ∗ ((sp + 0x268#64) ↦₆₄ w1) ∗
    ((sp + 0x270#64) ↦₆₄ w2) ∗ ((sp + 0x278#64) ↦₆₄ w3) ∗
    ((sp + 0x280#64) ↦₆₄ w4) ∗ memRegion (sp + 0x288#64) 8 ⊢
      memRegion (sp + 0x260#64) 48 := by
  rw [memRegion_split' (b := sp + 0x260#64) (b' := sp + 0x268#64)
        (N := 48) (n := 8) (k := 40) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x268#64) (b' := sp + 0x270#64)
        (N := 40) (n := 8) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x270#64) (b' := sp + 0x278#64)
        (N := 32) (n := 8) (k := 24) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x278#64) (b' := sp + 0x280#64)
        (N := 24) (n := 8) (k := 16) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64)
        (N := 16) (n := 8) (k := 8) (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))

theorem save_poll_tail_entails_memRegion_40_and_0x160
    (sp : BitVec 64) (v32 : BitVec 32) (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    (((sp + 0x268#64) ↦₃₂ v32) ∗ memRegion (sp + 0x26c#64) 36) ∗
    (memRegion (sp + 0x290#64) 0x140 ∗ ((sp + 0x3d0#64) ↦ₛ bs)) ⊢
      memRegion (sp + 0x268#64) 40 ∗ memRegion (sp + 0x290#64) 0x160 := by
  have h40 : (((sp + 0x268#64) ↦₃₂ v32) ∗
      memRegion (sp + 0x26c#64) 36) ⊢ memRegion (sp + 0x268#64) 40 := by
    rw [memRegion_split' (b := sp + 0x268#64) (b' := sp + 0x26c#64)
          (N := 40) (n := 4) (k := 36) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)
  have h32 : ((sp + 0x3d0#64) ↦ₛ bs) ⊢ memRegion (sp + 0x3d0#64) 0x20 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 0x3d0#64) bs
    rwa [hbs] at h
  have h160 : (memRegion (sp + 0x290#64) 0x140 ∗
      ((sp + 0x3d0#64) ↦ₛ bs)) ⊢ memRegion (sp + 0x290#64) 0x160 := by
    rw [memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x3d0#64)
          (N := 0x160) (n := 0x140) (k := 0x20) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_right h32
  exact sepConj_mono h40 h160

theorem table4SingleAt_identityBucketEntryAt_entails_inMemIdentityStoreAtP
    (A : RustAlloc) (img : Obj.Image) (out k0 k1 : BitVec 64) (role : Role)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32) (peerKey : IdentityKey)
    (gPeer clonedG : AddrGhost) (k : Nat)
    (hkp : keyPairBytes.length = 64)
    (hPeer : gPeer.val = role.peer.addrVal)
    (hcName : clonedG.name.bytes = gPeer.name.bytes) (hcDev : clonedG.device = gPeer.device) :
    (((out + 48#64) ↦ₛ keyPairBytes) ∗ ((out + 112#64) ↦₃₂ regId) ∗ memRegion (out + 116#64) 4 ∗
     HashbrownBin.table4SingleAt A HashbrownBin.identityBucketStride out k0 k1 k
       gPeer.name.bytes gPeer.device (HashbrownBin.identityBucketEntryAt A clonedG
         peerKey.publicKey.bytes.toList)) ⊢
      inMemIdentityStoreAtP A img out role keyPairBytes regId (some peerKey) := by
  have hPeerName : gPeer.name.bytes = role.peer.nameBytes := by injection hPeer with h1 _
  have hPeerDev : gPeer.device = 1#8 := by injection hPeer with _ h2
  have hcVal : clonedG.val = role.peer.addrVal := by
    unfold AddrGhost.val Role.addrVal; rw [hcName, hcDev, hPeerName, hPeerDev]
  unfold inMemIdentityStoreAtP
  refine Entails.pure_right hkp ?_
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
  rw [hPeerName, hPeerDev]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  exact Entails.sepExists_right k (Entails.sepExists_right clonedG (Entails.pure_right hcVal
      (Entails.refl _)))

end CryptoVerification.E2E.Pqxdh.WireEntries
