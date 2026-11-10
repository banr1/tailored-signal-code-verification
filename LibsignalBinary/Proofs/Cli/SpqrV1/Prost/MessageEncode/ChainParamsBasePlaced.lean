/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Relocatable `encode<ChainParams> [local#3]` Step Lemmas (Block `453`)

Proves `[LibsignalPlacement]` basic-block step lemmas for CLI Block `453`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
  CryptoVerification.SpqrV1.Prost.MessageEncode
  CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local arm64_norm] private theorem zext64_trunc32_orr_1 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 1#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_trunc32_orr_100000001 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 0x100000001#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_orr_1_32 (w : BitVec 32) :
    BitVec.zeroExtend 64 (w ||| 1#32) = BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

def EncodeChainParams1PlacedOk [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_453 H) (blkPl_453).base
    (withLsCodeLoaded lsmpl (encodeChainParamsSpec A))

def EncodeChainParams1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_453 H) (blkPl_453).base
    (withLsCodeLoaded lsmpl (encodeChainParamsSpecX A))

def EncodeChainParams1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  EncodeChainParams1PlacedOk A (Rust.withPanics ext)

def EncodeChainParams1PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  EncodeChainParams1PlacedOkX A (Rust.withPanics ext)

theorem step_chainParams_prologue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (H : String → Option (State → State))
    (v sp : BitVec 64) (tag : BitVec 32) (p : ChainParamsPB)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hhs0 : s = s0)
    (hP : P = stackAt sp (msgEnc48VarintStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = (blkPl_453).base + 40#64 →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (2#32 ||| (tag <<< 3)).zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_453 H) ret sm
        ((stackAt (sp - 48#64) (0x30 + resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_453 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP hhs0
  dsimp only [State.readReg32, Reg.x0, Reg.x1, Reg.x2] at hw0 hw1 hw2
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_varint hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 40#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ sv3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; congr 1; bv_bits)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))
  dsimp only [msgEnc48SavedFrame]
  exact Entails.of_eq (by ac_rfl)

theorem step_chainParams_len_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + 44#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + (if p.maxOooKeys == 0#32 then 204#64 else 116#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_453 H) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_453 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hraw := chainParams_encodeRaw_length p
  cases hmj : (p.maxJump == 0#32) <;> cases hmo : (p.maxOooKeys == 0#32)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmj)
    have hmo_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmo)
    have hadd := EncodedLen.bv_add_ofNat_comm (u32VarintFieldEncodedLen p.maxJump) (u32VarintFieldEncodedLen p.maxOooKeys)
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmj)
    have hmo_z := u32VarintFieldEncodedLen_of_beq_true hmo
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmo_z, Nat.add_zero]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_z := u32VarintFieldEncodedLen_of_beq_true hmj
    have hmo_val := EncodedLen.bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmo)
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmj_z, Nat.zero_add]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    have hmj_z := u32VarintFieldEncodedLen_of_beq_true hmj
    have hmo_z := u32VarintFieldEncodedLen_of_beq_true hmo
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmj_z, hmo_z]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)

theorem step_chainParams_push_maxJump_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + 256#64 →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = p.maxJump.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_453 H) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_453 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 256#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]
  exact Entails.of_eq (by ac_rfl)

theorem step_chainParams_push_maxOooKeys_epilogue_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + 184#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr →
      sm.readReg64 .x0 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      CalleeSavedPreserved s0 sm →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_453 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_453 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [msgEnc48SavedFrame]
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 184#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by epochEncLen_cc_close)
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩)
  dsimp only [msgEnc48SavedFrame]
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]
  exact Entails.of_eq (by ac_rfl)

theorem step_chainParams_epilogue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (H : String → Option (State → State))
    (sp sv3 : BitVec 64)
    {s0 s : State} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + 264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf (stackAt sp (msgEnc48VarintStackOf resStack) ∗ F)) :
    SepWPp (lsProg_453 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [msgEnc48SavedFrame]
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1).1))
  exact sepConj_mono_left
    (stackAt_msgEnc48_varint_recombine hres sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19))

theorem step_chainParams_after_hdr_branch_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + (if p.maxOooKeys == 0#32 then 208#64 else 120#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + (if p.maxJump == 0#32 then 124#64 else 212#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_453 H) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_453 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  cases hmo : (p.maxOooKeys == 0#32) <;> cases hmj : (p.maxJump == 0#32)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 124#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmj]
    simp only [hmo, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 124#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)

theorem step_chainParams_after_maxJump_branch_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + (if p.maxJump == 0#32 then 124#64 else 260#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + (if p.maxOooKeys == 0#32 then 264#64 else 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_453 H) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_453 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  cases hmj : (p.maxJump == 0#32) <;> cases hmo : (p.maxOooKeys == 0#32)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 128#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 264#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 128#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hmo]
    simp only [hmj, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_453).base + 264#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
