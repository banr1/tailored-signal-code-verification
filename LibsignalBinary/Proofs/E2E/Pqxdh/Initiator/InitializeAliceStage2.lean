/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.ResponderCore
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  CryptoVerification.libsignalSessionCode_fnOff_0x3e6e0
  CryptoVerification.libsignalSessionCode_fnOff_0x1fa74
  CryptoVerification.libsignalSessionCode_fnOff_0x1ceb8
  CryptoVerification.libsignalSessionCode_fnOff_0x3dc30
  CryptoVerification.libsignalSessionCode_fnOff_0x14d14
  CryptoVerification.libsignalSessionCode_fnOff_0x21c6c
  CryptoVerification.libsignalSessionCode_fnOff_0x125a4
  CryptoVerification.libsignalSessionCode_fnOff_0x11c98
  CryptoVerification.libsignalSessionCode_fnOff_0x117e8
  CryptoVerification.libsignalSessionCode_fnOff_0x12064
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "alloc::alloc::handle_alloc_error")
  (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "libsignal_session_rng_fill")
theorem SepWPp.bind_loaded {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩
theorem stackAt_tryClone_split_alloc (fsp : BitVec 64) :
    stackAt fsp tryCloneFromRefStack =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 4144#64) 48 := by
  have h1 := stackAt_split_top fsp 48 allocHookStack (by decide)
  have h2 : (48 + allocHookStack : Nat) = tryCloneFromRefStack := by decide
  have h3 : BitVec.ofNat 64 (48 + allocHookStack) = 4144#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]
theorem kyberEncapsOut_split_3648 {P : Primitives} {pqspkB kemCoins kemSs kemCt : Bytes}
    (fsp : BitVec 64) (hencaps : P.kemEncaps pqspkB kemCoins = some (kemSs, kemCt))
    (hct_len : kemCt.length = 1568) (hss_len : kemSs.length = 32) :
    ((fsp + 3648#64) ↦ₛ fitBv8 1600 (kyberEncapsOutBytes P pqspkB kemCoins)) =
      ((fsp + 3648#64) ↦ₛ bytesToBv8 kemCt) ∗ ((fsp + 5216#64) ↦ₛ bytesToBv8 kemSs) := by
  unfold kyberEncapsOutBytes
  rw [hencaps]
  have hfit : fitBv8 1600 (kemCt ++ kemSs) = bytesToBv8 kemCt ++ bytesToBv8 kemSs := by
    unfold fitBv8
    have hlen : (bytesToBv8 (kemCt ++ kemSs)).length = 1600 := by
      simp [bytesToBv8, hct_len, hss_len]
    rw [List.take_of_length_le (by omega), hlen, Nat.sub_self, List.replicate_zero,
        List.append_nil, bytesToBv8_append]
  have hct_bv_len : (bytesToBv8 kemCt).length = 1568 := by simp [bytesToBv8, hct_len]
  rw [hfit, pointsToBytes_append, hct_bv_len]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
theorem ct_3648_entails_cells2_memRegion1552 (fsp : BitVec 64) {kemCt : Bytes}
    (hct_len : kemCt.length = 1568) : ((fsp + 3648#64) ↦ₛ bytesToBv8 kemCt) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ((fsp + 3648#64) ↦₆₄ w0) ∗ ((fsp + 3656#64) ↦₆₄ w1) ∗
        memRegion (fsp + 3664#64) 1552 := by
  have hbv : (bytesToBv8 kemCt).length = 1568 := by simp [bytesToBv8, hct_len]
  refine Entails.trans (hbv ▸ pointsToBytes_entails_memRegion (fsp + 3648#64) (bytesToBv8 kemCt)) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 16) (k := 1552)
      (b' := fsp + 3664#64) rfl (by bv_omega) (by decide), memRegion16_eq_cells2 (fsp + 3648#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  exact Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
    Entails.sepExists_right w1 (Entails.sepExists_right w0 (Entails.refl _))
theorem memRegion1600_3648_merge_ser (fsp : BitVec 64) (w0 w1 : BitVec 64) {kemSs : Bytes}
    (hss_len : kemSs.length = 32) : ((fsp + 3648#64) ↦₆₄ w0) ∗ ((fsp + 3656#64) ↦₆₄ w1) ∗
    memRegion (fsp + 3664#64) 1552 ∗ ((fsp + 5216#64) ↦ₛ bytesToBv8 kemSs) ⊢
      memRegion (fsp + 3648#64) 1600 := by
  have hss_bv : (bytesToBv8 kemSs).length = 32 := by simp [bytesToBv8, hss_len]
  have h16 := cells2_entails_memRegion16 (fsp + 3648#64) w0 w1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16
  have h32 : ((fsp + 5216#64) ↦ₛ bytesToBv8 kemSs) ⊢ memRegion (fsp + 5216#64) 32 :=
    hss_bv ▸ pointsToBytes_entails_memRegion (fsp + 5216#64) (bytesToBv8 kemSs)
  rw [ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 16) (k := 1584)
      (b' := fsp + 3664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3664#64) (n := 1552) (k := 32)
      (b' := fsp + 5216#64) rfl (by bv_omega) (by decide)]
  rw [← sepConj_assoc ((fsp + 3648#64) ↦₆₄ w0)]
  exact sepConj_mono h16 (sepConj_mono_right h32)
theorem encodeKemCt_pointsTo_eq (ptr : BitVec 64) (kemCt : Bytes) :
    (ptr ↦₈ 8#8) ∗ ((ptr + 1#64) ↦ₛ bytesToBv8 kemCt) = (ptr ↦ₛ bytesToBv8 (encodeKEM kemCt)) := by
  change (ptr ↦₈ 8#8) ∗ ((ptr + 1#64) ↦ₛ bytesToBv8 kemCt) = (ptr ↦ₛ (8#8 :: bytesToBv8 kemCt))
  exact (pointsToBytes_cons ptr 8#8 (bytesToBv8 kemCt)).symm
theorem stackAt_pqxdhEntry_split_alloc (fsp : BitVec 64) :
    stackAt fsp pqxdhEntryStack =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 16384#64) 12288 := by
  have h1 := stackAt_split_top fsp 12288 allocHookStack (by decide)
  have h2 : (12288 + allocHookStack : Nat) = pqxdhEntryStack := by decide
  have h3 : BitVec.ofNat 64 (12288 + allocHookStack) = 16384#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]
theorem secrets_none_append_ss (secretsPtr : BitVec 64) {dh1 dh2 dh3 kemSs : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32) :
    (secretsPtr ↦ₛ bytesToBv8 (dhSecretsPrefix dh1 dh2 dh3 none)) ∗
    ((secretsPtr + 128#64) ↦ₛ bytesToBv8 kemSs) =
      (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 none kemSs)) := by
  have hpfx : (bytesToBv8 (dhSecretsPrefix dh1 dh2 dh3 none)).length = 128 := by
    simp [dhSecretsPrefix, F_X25519, bytesToBv8, h1, h2, h3]
  exact pointsToBytes_append_at secretsPtr (dhSecretsPrefix dh1 dh2 dh3 none) kemSs 128 hpfx
theorem secrets_some_append_ss (secretsPtr : BitVec 64) {dh1 dh2 dh3 dh4 kemSs : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32) (h4 : dh4.length = 32) :
    (secretsPtr ↦ₛ bytesToBv8 (dhSecretsPrefix dh1 dh2 dh3 (some dh4))) ∗
    ((secretsPtr + 160#64) ↦ₛ bytesToBv8 kemSs) =
      (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) kemSs)) := by
  have hpfx : (bytesToBv8 (dhSecretsPrefix dh1 dh2 dh3 (some dh4))).length = 160 := by
    simp [dhSecretsPrefix, F_X25519, bytesToBv8, h1, h2, h3, h4]
  exact pointsToBytes_append_at secretsPtr (dhSecretsPrefix dh1 dh2 dh3 (some dh4)) kemSs 160 hpfx
theorem secrets_none_entails_memRegion192 (secretsPtr : BitVec 64) {dh1 dh2 dh3 kemSs : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32) (hss : kemSs.length = 32) :
    (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 none kemSs)) ∗
    memRegion (secretsPtr + 160#64) 32 ⊢ memRegion secretsPtr 192 := by
  have hlen : (bytesToBv8 (buildSecrets dh1 dh2 dh3 none kemSs)).length = 160 := by
    simp [buildSecrets, F_X25519, bytesToBv8, h1, h2, h3, hss]
  rw [ProofLib.memRegion_split' (b := secretsPtr) (n := 160) (k := 32)
      (b' := secretsPtr + 160#64) rfl rfl (by decide)]
  exact sepConj_mono_left (hlen ▸ pointsToBytes_entails_memRegion secretsPtr _)
theorem secrets_some_entails_memRegion192 (secretsPtr : BitVec 64) {dh1 dh2 dh3 dh4 kemSs : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (h4 : dh4.length = 32) (hss : kemSs.length = 32) :
    (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) kemSs)) ⊢
      memRegion secretsPtr 192 := by
  have hlen : (bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) kemSs)).length = 192 := by
    simp [buildSecrets, F_X25519, bytesToBv8, h1, h2, h3, h4, hss]
  exact hlen ▸ pointsToBytes_entails_memRegion secretsPtr _
theorem buildSecrets_take32 (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (kemSs : Bytes) :
    (buildSecrets dh1 dh2 dh3 dh4? kemSs).take 32 = discontinuityBytes := by
  cases dh4? <;>
    simp [buildSecrets, F_X25519, discontinuityBytes, List.append_assoc,
      List.take_append_of_le_length]
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFill_ok_at_tripleRatchet
  rngFillAfter0Spec)
attribute [local simp, local arm64_norm, local wp_norm]
  clamp_byte0_norm clamp_byte0_norm32 clamp_byte31_bfxil_norm clamp_byte31_bfxil_norm'
theorem tapeAfter_vec32 (ctl cur : BitVec 64) (v : List.Vector (BitVec 8) 32) (rest : List (BitVec
    8)) :
    tapeAfter ctl cur (v.toList ++ rest) 32 =
      (cur ↦ₛ v.toList) ∗ tapeAfter ctl (cur + 32#64) rest 0 := by
  unfold tapeAfter
  have hv_len : v.toList.length = 32 := v.2
  have hlen : (v.toList ++ rest).length - 32 = rest.length := by simp [hv_len]
  have h32 : BitVec.ofNat 64 32 = 32#64 := rfl
  have hpts : (cur ↦ₛ (v.toList ++ rest)) = (cur ↦ₛ v.toList) ∗ ((cur + 32#64) ↦ₛ rest) := by
    rw [pointsToBytes_append, hv_len, h32]
  rw [hlen, h32, hpts, BitVec.add_zero, Nat.sub_zero]
  ac_rfl
def sp2Rng32Spec (ctl : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List.Vector (BitVec 8) 32 × List (BitVec 8)) where
  pre := fun (destPtr, cur, v, rest) s =>
    ⌜s.readReg64 .x0 = destPtr ∧ s.readReg64 .x1 = 32#64⌝ ∗ memRegion destPtr 32 ∗
      tapeAfter ctl cur (v.toList ++ rest) 0
  post := fun (destPtr, cur, v, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (destPtr ↦ₛ v.toList) ∗ (cur ↦ₛ v.toList) ∗
      tapeAfter ctl (cur + 32#64) rest 0
theorem sp2Rng32_ok_at {img : Obj.Image} {C : Crypto} {ctl : BitVec 64} {absHooks : String → Option
    (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "libsignal_session_rng_fill" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (sp2Rng32Spec ctl) := by
  have hrng := rngFill_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := absHooks) (name := name) (k := k) hk
  refine subroutine_ok_outcome_intro fun ⟨destPtr, cur, v, rest⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [sp2Rng32Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  have hx1_nat : (s0.readReg64 .x1).toNat = 32 := by rw [hx1]; rfl
  have hpre' : s0.mem ⊨ (rngFillAfter0Spec ctl).pre (destPtr, 32, cur, v.toList ++ rest) s0 ∗ R :=
    by
    dsimp only [rngFillAfter0Spec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_nat⟩, hpre⟩
  refine hrng.mono_outcome (destPtr, 32, cur, v.toList ++ rest) R s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rngFillAfter0Spec] at hq
    have hv_len : v.toList.length = 32 := v.2
    have htake : ((v.toList ++ rest) ++ List.replicate 32 0#8).take 32 = v.toList := by
      rw [List.append_assoc, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    have hmin : min 32 (v.toList ++ rest).length = 32 := by simp [hv_len]
    rw [htake, hmin, tapeAfter_vec32 ctl cur v rest] at hq
    dsimp only [sp2Rng32Spec]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · exact Or.inr hpan
theorem memRegion24_eq_cells3 (base : BitVec 64) :
    memRegion base 24 = ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) := by
  rw [(memRegion_cells base 3 (by decide) : memRegion base 24 = cells base 3)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem cells3_entails_memRegion24 (base : BitVec 64) (w0 w1 w2 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ⊢ memRegion base 24 := by
  rw [memRegion24_eq_cells3 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.refl _)))
theorem memRegion36_224_split (fsp : BitVec 64) :
    memRegion (fsp + 224#64) 36 =
      memRegion (fsp + 224#64) 32 ∗ (∃∗ w : BitVec 32, (fsp + 256#64) ↦₃₂ w) := by
  rw [ProofLib.memRegion_split' (b := fsp + 224#64) (n := 32) (k := 4)
      (b' := fsp + 256#64) rfl (by bv_omega) (by decide), memRegion_four (fsp + 256#64)]
theorem handshakeKeysBytes100_unpack (p : BitVec 64) (dk : DRKey)
    {rk0 rk1 rk2 rk3 pq0 pq1 pq2 pq3 ck0 ck1 ck2 ck3 : BitVec 64}
    (hrk : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 dk.rootKey) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hpq : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 dk.pqrKey) =
      (a ↦₆₄ pq0) ∗ ((a + 8#64) ↦₆₄ pq1) ∗ ((a + 16#64) ↦₆₄ pq2) ∗ ((a + 24#64) ↦₆₄ pq3))
    (hck : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 dk.chainKey) =
      (a ↦₆₄ ck0) ∗ ((a + 8#64) ↦₆₄ ck1) ∗ ((a + 16#64) ↦₆₄ ck2) ∗ ((a + 24#64) ↦₆₄ ck3))
    (hrk_len : dk.rootKey.length = 32) (hpq_len : dk.pqrKey.length =
      32) (hck_len : dk.chainKey.length = 32) :
    (p ↦ₛ bytesToBv8 (handshakeKeysBytes100 dk)) =
      (p ↦₆₄ rk0) ∗ ((p + 8#64) ↦₆₄ rk1) ∗ ((p + 16#64) ↦₆₄ rk2) ∗ ((p + 24#64) ↦₆₄ rk3) ∗
      ((p + 32#64) ↦₆₄ pq0) ∗ ((p + 40#64) ↦₆₄ pq1) ∗ ((p + 48#64) ↦₆₄ pq2) ∗ ((p +
        56#64) ↦₆₄ pq3) ∗
      ((p + 64#64) ↦₆₄ ck0) ∗ ((p + 72#64) ↦₆₄ ck1) ∗ ((p + 80#64) ↦₆₄ ck2) ∗ ((p +
        88#64) ↦₆₄ ck3) ∗
      ((p + 96#64) ↦₃₂ 0#32) := by
  unfold handshakeKeysBytes100 DRKey.ck0
  have h100 :=
    pointsToBytes_100_3blocks_zero p dk.rootKey dk.pqrKey dk.chainKey hrk_len hpq_len hck_len
  change (p ↦ₛ bytesToBv8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++ encodeU32LE 0)) = _
  rw [h100, hrk p, hpq (p + 32#64), hck (p + 64#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem handshakeKeysBytes100_entails_memRegion100 (p : BitVec 64) (dk : DRKey)
    (hrk_len : dk.rootKey.length = 32) (hpq_len : dk.pqrKey.length =
      32) (hck_len : dk.chainKey.length = 32) :
    (p ↦ₛ bytesToBv8 (handshakeKeysBytes100 dk)) ⊢ memRegion p 100 := by
  have hlen : (bytesToBv8 (handshakeKeysBytes100 dk)).length = 100 := by
    simp [handshakeKeysBytes100, DRKey.ck0, encodeU32LE, bytesToBv8, hrk_len, hpq_len, hck_len]
  exact hlen ▸ pointsToBytes_entails_memRegion p _
theorem vec32_toList_split_ends (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get ⟨0, by decide⟩] ++ ((v.toList.drop 1).take 30 ++ [v.get ⟨31, by decide⟩]) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | (dsimp [List.Vector.toList, List.Vector.get]; rfl) | cases hl
theorem vec32_clampScalar_toList_eq (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList = [v.get ⟨0, by decide⟩ &&& 0xf8#8] ++
        ((v.toList.drop 1).take 30 ++ [(v.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8]) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | (dsimp [List.Vector.toList, List.Vector.get, Ratchet.clampScalar,
      List.Vector.set]; rfl) | cases hl
theorem pointsTo_vec32_split_ends (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) = ((a ↦₈ v.get ⟨0, by decide⟩) ∗ ((a + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
       ((a + 31#64) ↦₈ v.get ⟨31, by decide⟩)) := by
  have hmid : ((v.toList.drop 1).take 30).length = 30 := by simp
  conv_lhs => rw [vec32_toList_split_ends v]
  rw [pointsToBytes_append, pointsToBytes_append,
      show ([v.get ⟨0, by decide⟩] : List (BitVec 8)).length = 1 from rfl, hmid,
      ProofLib.pointsToBytes_singleton a, ProofLib.pointsToBytes_singleton (a + 1#64 + 30#64),
      show a + 1#64 + 30#64 = a + 31#64 by bv_omega]
theorem pointsTo_vec32_clamp_fold (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    ((a ↦₈ (v.get ⟨0, by decide⟩ &&& 0xf8#8)) ∗ ((a + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
     ((a + 31#64) ↦₈ ((v.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8))) =
      (a ↦ₛ (Ratchet.clampScalar v).toList) := by
  have hmid : ((v.toList.drop 1).take 30).length = 30 := by simp
  conv_rhs => rw [vec32_clampScalar_toList_eq v]
  rw [pointsToBytes_append, pointsToBytes_append,
      show ([v.get ⟨0, by decide⟩ &&& 0xf8#8] : List (BitVec 8)).length = 1 from rfl, hmid,
      ProofLib.pointsToBytes_singleton a, ProofLib.pointsToBytes_singleton (a + 1#64 + 30#64),
      show a + 1#64 + 30#64 = a + 31#64 by bv_omega]
open CryptoGames.HMAC CryptoGames.HKDF
@[simp, arm64_norm]
abbrev createChainStack : Nat := LibsignalTripleRatchet.createChainStack
theorem pqxdh_createChain_ok_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A absHooks) :
    CreateChainOk_trap img C A absHooks :=
  Keys.createChain_ok_trap himg (ConsumeMessageKeyTransfer.ctEqRO_ok_trap _ _ _)
    (extract_ok_trap img C absHooks (ConsumeMessageKeyTransfer.new_from_slice_ok_trap _ _ _ himg))
    (expand_multi_info_ok_trap img.base C absHooks) hA
theorem pqxdh_createChain_ok
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A absHooks) :
    CreateChainOk img C A ctl absHooks := by
  unfold CreateChainOk CreateChainOkExt
  simp only [← trTrapProgAt_fnAddr_eq]
  exact subroutine_ok_kit_of_trTrap (pqxdh_createChain_ok_trap (C := C) himg hA)
theorem stackAt_createChain_split_alloc (fsp : BitVec 64) :
    stackAt fsp createChainStack =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 4832#64) 736 := by
  have h1 := stackAt_split_top fsp 736 allocHookStack (by decide)
  have h2 : (736 + allocHookStack : Nat) = createChainStack := by decide
  have h3 : BitVec.ofNat 64 (736 + allocHookStack) = 4832#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]
theorem stackAt_pqxdhEntry_split_createChain (fsp : BitVec 64) :
    stackAt fsp pqxdhEntryStack =
      stackAt fsp createChainStack ∗ memRegion (fsp - 16384#64) 11552 := by
  have h1 := stackAt_split_top fsp 11552 createChainStack (by decide)
  have h2 : (11552 + createChainStack : Nat) = pqxdhEntryStack := by decide
  have h3 : BitVec.ofNat 64 (11552 + createChainStack) = 16384#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]
theorem stackAt_pqxdhEntry_split_tryClone (fsp : BitVec 64) :
    stackAt fsp pqxdhEntryStack =
      stackAt fsp tryCloneFromRefStack ∗ memRegion (fsp - 16384#64) 12240 := by
  have h1 := stackAt_split_top fsp 12240 tryCloneFromRefStack (by decide)
  have h2 : (12240 + tryCloneFromRefStack : Nat) = pqxdhEntryStack := by decide
  have h3 : BitVec.ofNat 64 (12240 + tryCloneFromRefStack) = 16384#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]
theorem memRegion48_eq_cells6 (base : BitVec 64) :
    memRegion base 48 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
        ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗
        ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) := by
  rw [(memRegion_cells base 6 (by decide) : memRegion base 48 = cells base 6)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem cells6_entails_memRegion48 (base : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
    ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗
    ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) ⊢
      memRegion base 48 := by
  rw [memRegion48_eq_cells6 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))
theorem memRegion56_3664_split (fsp : BitVec 64) :
    memRegion (fsp + 3664#64) 56 =
      memRegion (fsp + 3664#64) 40 ∗ memRegion (fsp + 3704#64) 16 :=
  ProofLib.memRegion_split' (b := fsp + 3664#64) (n := 40) (k := 16)
    (b' := fsp + 3704#64) rfl (by bv_omega) (by decide)
theorem createChainErr_entails_memRegion72 (fsp : BitVec 64) (e0 e1 e2 e3 e4 e5 : BitVec 64) :
    ((fsp + 3648#64) ↦₃₂ 1#32) ∗
    memRegion (fsp + 3652#64) 4 ∗
    ((fsp + 3656#64) ↦₆₄ e0) ∗
    ((fsp + 3664#64) ↦₆₄ e1) ∗
    ((fsp + 3672#64) ↦₆₄ e2) ∗
    ((fsp + 3680#64) ↦₆₄ e3) ∗
    ((fsp + 3688#64) ↦₆₄ e4) ∗
    ((fsp + 3696#64) ↦₆₄ e5) ∗
    memRegion (fsp + 3704#64) 16 ⊢
      memRegion (fsp + 3648#64) 72 := by
  have h4 : ((fsp + 3648#64) ↦₃₂ 1#32) ⊢ memRegion (fsp + 3648#64) 4 :=
    pointsTo32_entails_memRegion4 (fsp + 3648#64) 1#32
  have h48 := cells6_entails_memRegion48 (fsp + 3656#64) e0 e1 e2 e3 e4 e5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48
  rw [ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 4) (k := 68)
      (b' := fsp + 3652#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3652#64) (n := 4) (k := 64)
      (b' := fsp + 3656#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3656#64) (n := 48) (k := 16)
      (b' := fsp + 3704#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono h4 (sepConj_mono_right (sepConj_mono_left h48)))
theorem aliceErrResult_fold (outPtr tagWord e1 e2 e3 e4 e5 : BitVec 64) :
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ tagWord) ∗
    ((outPtr + 16#64) ↦₆₄ e1) ∗
    ((outPtr + 24#64) ↦₆₄ e2) ∗
    ((outPtr + 32#64) ↦₆₄ e3) ∗
    ((outPtr + 40#64) ↦₆₄ e4) ∗
    ((outPtr + 48#64) ↦₆₄ e5) ⊢
      aliceErrResultAt outPtr tagWord := by
  dsimp only [aliceErrResultAt]
  have h40 := cells5_entails_memRegion40 (outPtr + 16#64) e1 e2 e3 e4 e5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40
  exact sepConj_mono_right (sepConj_mono_right h40)
theorem deriveDRKeys_lengths (P : Primitives) (hWF : StructuralPrims P) (secrets : Bytes) :
    (Model.deriveDRKeys P secrets).rootKey.length = 32 ∧
    (Model.deriveDRKeys P secrets).pqrKey.length = 32 ∧
    (Model.deriveDRKeys P secrets).chainKey.length = 32 := by
  unfold Model.deriveDRKeys
  rw [hWF.hkdfDerive96_eq_ref secrets]
  exact ⟨hmacSha256Ref_length P _ _, hmacSha256Ref_length P _ _, hmacSha256Ref_length P _ _⟩
theorem memRegion1568_2080_split32 (fsp : BitVec 64) :
    memRegion (fsp + 2080#64) 1568 =
      memRegion (fsp + 2080#64) 32 ∗ memRegion (fsp + 2112#64) 1536 :=
  ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 32) (k := 1536)
    (b' := fsp + 2112#64) rfl (by bv_omega) (by decide)
theorem memRegion32_2080_split4 (fsp : BitVec 64) :
    memRegion (fsp + 2080#64) 32 =
      memRegion (fsp + 2080#64) 4 ∗ memRegion (fsp + 2084#64) 28 :=
  ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 4) (k := 28)
    (b' := fsp + 2084#64) rfl (by bv_omega) (by decide)
theorem memRegion1536_2112_split20 (fsp : BitVec 64) :
    memRegion (fsp + 2112#64) 1536 =
      memRegion (fsp + 2112#64) 20 ∗ memRegion (fsp + 2132#64) 1516 :=
  ProofLib.memRegion_split' (b := fsp + 2112#64) (n := 20) (k := 1516)
    (b' := fsp + 2132#64) rfl (by bv_omega) (by decide)
theorem memRegion48_2084_split28 (fsp : BitVec 64) :
    memRegion (fsp + 2084#64) 48 =
      memRegion (fsp + 2084#64) 28 ∗ memRegion (fsp + 2112#64) 20 :=
  ProofLib.memRegion_split' (b := fsp + 2084#64) (n := 28) (k := 20)
    (b' := fsp + 2112#64) rfl (by bv_omega) (by decide)
theorem memRegion1568_2080_split_err (fsp : BitVec 64) :
    memRegion (fsp + 2080#64) 1568 =
      memRegion (fsp + 2080#64) 4 ∗
      memRegion (fsp + 2084#64) 48 ∗
      memRegion (fsp + 2132#64) 1516 := by
  rw [ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 4) (k := 1564)
      (b' := fsp + 2084#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2084#64) (n := 48) (k := 1516)
      (b' := fsp + 2132#64) rfl (by bv_omega) (by decide),
      ← sepConj_assoc]
theorem memRegion1600_3648_split72 (fsp : BitVec 64) :
    memRegion (fsp + 3648#64) 1600 =
      memRegion (fsp + 3648#64) 72 ∗ memRegion (fsp + 3720#64) 1528 :=
  ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 72) (k := 1528)
    (b' := fsp + 3720#64) rfl (by bv_omega) (by decide)
theorem memRegion72_3648_split32 (fsp : BitVec 64) :
    memRegion (fsp + 3648#64) 72 =
      memRegion (fsp + 3648#64) 32 ∗ memRegion (fsp + 3680#64) 40 :=
  ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 32) (k := 40)
    (b' := fsp + 3680#64) rfl (by bv_omega) (by decide)
theorem encodeKemCt_entails_memRegion1569 (ptr : BitVec 64) {kemCt : Bytes}
    (hct_len : kemCt.length = 1568) :
    (ptr ↦ₛ bytesToBv8 (encodeKEM kemCt)) ⊢ memRegion ptr 1569 := by
  have hlen : (bytesToBv8 (encodeKEM kemCt)).length = 1569 := by
    simp [encodeKEM, bytesToBv8, hct_len]
  exact hlen ▸ pointsToBytes_entails_memRegion ptr _
end CryptoVerification.E2E.Pqxdh.Initiator
