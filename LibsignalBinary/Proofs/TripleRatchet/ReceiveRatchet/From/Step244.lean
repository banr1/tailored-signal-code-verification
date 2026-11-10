/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Frame
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom
open FromFetches

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

theorem sc_pack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
       ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12))) :
    (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) ∗ ((sp - 416#64) ↦₆₄ w2) ∗
     ((sp - 408#64) ↦₆₄ w3) ∗ ((sp - 400#64) ↦₆₄ w4) ∗ ((sp - 392#64) ↦₆₄ w5) ∗
     ((sp - 384#64) ↦₆₄ w6) ∗ ((sp - 376#64) ↦₆₄ w7) ∗ ((sp - 368#64) ↦₆₄ w8) ∗
     ((sp - 360#64) ↦₆₄ w9) ∗ ((sp - 352#64) ↦₆₄ w10) ∗ ((sp - 344#64) ↦₆₄ w11) ∗
     ((sp - 336#64) ↦₆₄ w12)) ⊢
      ((sp - 432#64) ↦ₛ bs) := by
  rw [h (sp - 432#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem sc_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
       ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12))) :
    (((r + 24#64) ↦₆₄ w0) ∗ ((r + 32#64) ↦₆₄ w1) ∗ ((r + 40#64) ↦₆₄ w2) ∗
     ((r + 48#64) ↦₆₄ w3) ∗ ((r + 56#64) ↦₆₄ w4) ∗ ((r + 64#64) ↦₆₄ w5) ∗
     ((r + 72#64) ↦₆₄ w6) ∗ ((r + 80#64) ↦₆₄ w7) ∗ ((r + 88#64) ↦₆₄ w8) ∗
     ((r + 96#64) ↦₆₄ w9) ∗ ((r + 104#64) ↦₆₄ w10) ∗ ((r + 112#64) ↦₆₄ w11) ∗
     ((r + 120#64) ↦₆₄ w12)) ⊢
      ((r + 24#64) ↦ₛ bs) := by
  rw [h (r + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem rk_pack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    (((sp - 328#64) ↦₆₄ w0) ∗ ((sp - 320#64) ↦₆₄ w1) ∗
     ((sp - 312#64) ↦₆₄ w2) ∗ ((sp - 304#64) ↦₆₄ w3)) ⊢
      ((sp - 328#64) ↦ₛ bs) := by
  rw [h (sp - 328#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem rk_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    (((r + 128#64) ↦₆₄ w0) ∗ ((r + 136#64) ↦₆₄ w1) ∗
     ((r + 144#64) ↦₆₄ w2) ∗ ((r + 152#64) ↦₆₄ w3)) ⊢
      ((r + 128#64) ↦ₛ bs) := by
  rw [h (r + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem lik_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
       ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
       ((a + 6#64) ↦₈ b6) ∗
       ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
       ((a + 15#64) ↦₆₄ w15) ∗
       ((a + 23#64) ↦₆₄ w23) ∗
       ((a + 31#64) ↦₈ b31))) :
    (((r + 200#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((r + 204#64) ↦₁₆ (b5 ++ b4)) ∗
     ((r + 206#64) ↦₈ b6) ∗
     ((r + 207#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
     ((r + 215#64) ↦₆₄ w15) ∗
     ((r + 223#64) ↦₆₄ w23) ∗
     ((r + 231#64) ↦₈ b31)) ⊢
      ((r + 200#64) ↦ₛ bs) := by
  rw [h (r + 200#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem rem_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 w22 : BitVec 64} {h30 : BitVec 16}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₆₄ w22) ∗ ((a + 30#64) ↦₁₆ h30))) :
    (((r + 232#64) ↦₃₂ d0) ∗ ((r + 236#64) ↦₁₆ h4) ∗ ((r + 238#64) ↦₆₄ w6) ∗
     ((r + 246#64) ↦₆₄ w14) ∗ ((r + 254#64) ↦₆₄ w22) ∗ ((r + 262#64) ↦₁₆ h30)) ⊢
      ((r + 232#64) ↦ₛ bs) := by
  rw [h (r + 232#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem err22_pack_stack (sp p w16 : BitVec 64)
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 : BitVec 64} {h22 : BitVec 16}
    (h : ∀ a : BitVec 64, ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ ((a + 16#64) ↦₆₄ w16)) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ h22))) :
    (((sp - 152#64) ↦₃₂ d0) ∗ ((sp - 148#64) ↦₁₆ h4) ∗ ((sp - 146#64) ↦₆₄ w6) ∗
     ((sp - 138#64) ↦₆₄ w14) ∗ ((sp - 130#64) ↦₁₆ h22)) ⊢
      (((sp - 152#64) ↦₆₄ p) ∗ ((sp - 144#64) ↦₆₄ 27#64) ∗ ((sp - 136#64) ↦₆₄ w16)) := by
  have h1 := h (sp - 152#64)
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] at h1 ⊢
  rw [h1]
  exact Entails.refl _

theorem err22_pack_ret (r p : BitVec 64)
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 : BitVec 64}
    (h : ∀ a : BitVec 64, ∀ r22 : BitVec 16,
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ r22)) ⊢
        ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ memRegion (a + 16#64) 8))
    (r38 : BitVec 16) :
    (((r + 16#64) ↦₃₂ d0) ∗ ((r + 20#64) ↦₁₆ h4) ∗ ((r + 22#64) ↦₆₄ w6) ∗
     ((r + 30#64) ↦₆₄ w14) ∗ ((r + 38#64) ↦₁₆ r38) ∗ memRegion (r + 40#64) 16) ⊢
      (((r + 16#64) ↦₆₄ p) ∗ ((r + 24#64) ↦₆₄ 27#64) ∗ memRegion (r + 32#64) 24) := by
  have h1 := h (r + 16#64) r38
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  rw [mr_cut_add r 32 8 16 (by decide)]
  have h2 := sepConj_mono h1 (Entails.refl (memRegion (r + 40#64) 16))
  simpa only [sepConj_assoc] using h2

theorem lik_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (h : ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₈ b7) ∗
         ((a + 8#64) ↦₈ b8) ∗
         ((a + 9#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
         ((a + 13#64) ↦₁₆ (b14 ++ b13)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31))) :
    ((sp - 159#64) ↦ₛ bs) =
      (((sp - 159#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
       ((sp - 155#64) ↦₁₆ (b5 ++ b4)) ∗
       ((sp - 153#64) ↦₈ b6) ∗
       ((sp - 152#64) ↦₈ b7) ∗
       ((sp - 151#64) ↦₈ b8) ∗
       ((sp - 150#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
       ((sp - 146#64) ↦₁₆ (b14 ++ b13)) ∗
       ((sp - 144#64) ↦₆₄ w15) ∗
       ((sp - 136#64) ↦₆₄ w23) ∗
       ((sp - 128#64) ↦₈ b31)) := by
  rw [h (sp - 159#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem rem_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 w22 : BitVec 64} {h30 : BitVec 16}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₆₄ w22) ∗ ((a + 30#64) ↦₁₆ h30))) :
    ((sp - 158#64) ↦ₛ bs) =
      (((sp - 158#64) ↦₃₂ d0) ∗ ((sp - 154#64) ↦₁₆ h4) ∗ ((sp - 152#64) ↦₆₄ w6) ∗
       ((sp - 144#64) ↦₆₄ w14) ∗ ((sp - 136#64) ↦₆₄ w22) ∗ ((sp - 128#64) ↦₁₆ h30)) := by
  rw [h (sp - 158#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem pointsTo64_sp_160 (sp : BitVec 64) (b0 b1 : BitVec 8) (d2 : BitVec 32) (h6 : BitVec 16) :
    (((sp - 160#64) ↦₈ b0) ∗ ((sp - 159#64) ↦₈ b1) ∗
     ((sp - 158#64) ↦₃₂ d2) ∗ ((sp - 154#64) ↦₁₆ h6)) =
      ((sp - 160#64) ↦₆₄ (h6 ++ d2 ++ b1 ++ b0)) := by
  have h := pointsTo64_of_8_8_32_16 (sp - 160#64) b0 b1 d2 h6
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem SepWP.mono_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  SepWP.weaken_pre hP h

theorem trFrom_step_244_to_428
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {P_A : Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (_hA : P_A)
    (hRemoteIk : RemoteIdentityKeyOkExt img A ext)
    (ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (target_pc : BitVec 64) (F_rest : SepProp)
    (post : State → SepProp → Prop)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hlik_split1 : ∀ a : BitVec 64,
      (a ↦ₛ st.localIdentity.publicKey.bytes.toList) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₈ b7) ∗
         ((a + 8#64) ↦₈ b8) ∗
         ((a + 9#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
         ((a + 13#64) ↦₁₆ (b14 ++ b13)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31)))
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length)
    (hrik : match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx21 : s.readReg64 .x21 = G.pq.ptr)
    (hx22 : s.readReg64 .x22 = ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ sm (remBs : List (BitVec 8))
      (rd0 : BitVec 32) (rh4 : BitVec 16) (rw6 rw14 rw22 : BitVec 64) (rh30 : BitVec 16)
      (u_232 : BitVec 32) (u_228 : BitVec 16) (u_208 : BitVec 32),
      remBs.length = 32 →
      (∀ ik, st.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList) →
      (∀ a : BitVec 64, (a ↦ₛ remBs) =
        ((a ↦₃₂ rd0) ∗ ((a + 4#64) ↦₁₆ rh4) ∗ ((a + 6#64) ↦₆₄ rw6) ∗
         ((a + 14#64) ↦₆₄ rw14) ∗ ((a + 22#64) ↦₆₄ rw22) ∗ ((a + 30#64) ↦₁₆ rh30))) →
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 1064#64 →
      sm.status = .Running → sm.trace = s0.trace →
      sm.readReg64 .x8 = img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)) →
      sm.readReg64 .x9 = 27#64 →
      sm.readReg64 .x10 = (remoteIdentityTag st.remoteIdentity).zeroExtend 64 →
      sm.readReg64 .x11 = rw14 →
      sm.readReg64 .x12 = rw6 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 →
      sm.readReg64 .x22 = s0.sp - 160#64 →
      sm.readReg64 .x23 = 0x8000000000000014#64 →
      sm.readReg64 .x24 = s0.sp - 184#64 →
      sm.readReg64 .x25 = b7.zeroExtend 64 →
      sm.readReg64 .x26 = (b12 ++ b11 ++ b10 ++ b9).zeroExtend 64 →
      sm.readReg64 .x27 = (b14 ++ b13).zeroExtend 64 →
      sm.readReg64 .x28 = b8.zeroExtend 64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.sp = s0.sp - 496#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext) target_pc sm
        ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
         vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
         memRegion (s0.sp - 496#64) 8 ∗
         ((s0.sp - 488#64) ↦₃₂ (b5 ++ b4).zeroExtend 32) ∗
         ((s0.sp - 484#64) ↦₃₂ b6.zeroExtend 32) ∗
         ((s0.sp - 480#64) ↦₆₄ w15) ∗
         ((s0.sp - 472#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
         ((s0.sp - 464#64) ↦₆₄ G.pq.ptr) ∗
         ((s0.sp - 280#64) ↦₆₄ w23) ∗
         ((s0.sp - 272#64) ↦₈ b31) ∗
         memRegion (s0.sp - 271#64) 7 ∗
         ((s0.sp - 264#64) ↦₃₂ rd0) ∗
         ((s0.sp - 260#64) ↦₁₆ rh4) ∗
         memRegion (s0.sp - 258#64) 26 ∗
         ((s0.sp - 232#64) ↦₃₂ u_232) ∗
         ((s0.sp - 228#64) ↦₁₆ u_228) ∗
         memRegion (s0.sp - 226#64) 18 ∗
         ((s0.sp - 208#64) ↦₃₂ u_208) ∗
         memRegion (s0.sp - 204#64) 20 ∗
         ((s0.sp - 184#64) ↦₆₄ rw22) ∗
         ((s0.sp - 176#64) ↦₁₆ rh30) ∗
         memRegion (s0.sp - 174#64) 14 ∗
         ((s0.sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
         ((s0.sp - 152#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) ∗
         ((s0.sp - 144#64) ↦₆₄ 27#64) ∗
         ((s0.sp - 136#64) ↦₆₄ rw22) ∗
         ((s0.sp - 128#64) ↦₁₆ rh30) ∗
         memRegion (s0.sp - 126#64) 14 ∗
         memRegion (s0.sp - 112#64) 16 ∗
         stackAt (s0.sp - 496#64) dropVecChainStack ∗
         logOff img ∗
         F_rest)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) target_pc s
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 280#64) 184 ∗
       stackAt (s0.sp - 496#64) dropVecChainStack ∗
       logOff img ∗
       F_rest)
      post := by
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  have hpkTryFrom := pkTryFrom_ok_at_from (ext := ext) himg
  have hremIk := remoteIdentityKey_ok_at_from hRemoteIk
  have hadrp := fnAddr_adrp_40000 (ext := ext) (base_aligned_of_loads himg)
  clear hRemoteIk
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x244 5
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x378 20
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x3ec 15
  dsimp only [tripleRatchetProgAtExt] at hpc hpkTryFrom hremIk hadrp hcont ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = entry
  examples_hide_fetches
  let mid_428 := entry + bv% (1064)
  apply SepWP.of_sepWP_inv (mid := mid_428) hfl hsym
  rw [stack_496_40_split s0.sp, stack_280_184_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u_176 => SepWP.exists_elim fun u_184 => ?_
  refine SepWP.exists_elim fun u_208 => SepWP.exists_elim fun u_228 => ?_
  refine SepWP.exists_elim fun u_232 => SepWP.exists_elim fun u_260 => ?_
  refine SepWP.exists_elim fun u_264 => SepWP.exists_elim fun u_272 => ?_
  refine SepWP.exists_elim fun u_280 => SepWP.exists_elim fun u_464 => ?_
  refine SepWP.exists_elim fun u_472 => SepWP.exists_elim fun u_480 => ?_
  refine SepWP.exists_elim fun u_484 => SepWP.exists_elim fun u_488 => ?_
  wp_steps
  wp_apply
  have hsub159 : s0.sp - 160#64 + 1#64 = s0.sp - 159#64 := by bv_omega
  rw [lik_unpack_stack s0.sp hlik_split1]
  simp only [sepConj_assoc]
  have hcmp_ok : (0#8 == 1#8) = false := by decide
  wp_steps
  have hlen_lik : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  have hmr34 :
      (((s0.sp - 160#64) ↦₈ 0#8) ∗
       ((s0.sp - 159#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
       ((s0.sp - 155#64) ↦₁₆ (b5 ++ b4)) ∗
       ((s0.sp - 153#64) ↦₈ b6) ∗
       ((s0.sp - 152#64) ↦₈ b7) ∗
       ((s0.sp - 151#64) ↦₈ b8) ∗
       ((s0.sp - 150#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
       ((s0.sp - 146#64) ↦₁₆ (b14 ++ b13)) ∗
       ((s0.sp - 144#64) ↦₆₄ w15) ∗
       ((s0.sp - 136#64) ↦₆₄ w23) ∗
       ((s0.sp - 128#64) ↦₈ b31) ∗
       memRegion (s0.sp - 127#64) 1) ⊢
      memRegion (s0.sp - 160#64) 34 := by
    have hpack :
        (((s0.sp - 160#64) ↦₈ 0#8) ∗
         ((s0.sp - 159#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((s0.sp - 155#64) ↦₁₆ (b5 ++ b4)) ∗
         ((s0.sp - 153#64) ↦₈ b6) ∗
         ((s0.sp - 152#64) ↦₈ b7) ∗
         ((s0.sp - 151#64) ↦₈ b8) ∗
         ((s0.sp - 150#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
         ((s0.sp - 146#64) ↦₁₆ (b14 ++ b13)) ∗
         ((s0.sp - 144#64) ↦₆₄ w15) ∗
         ((s0.sp - 136#64) ↦₆₄ w23) ∗
         ((s0.sp - 128#64) ↦₈ b31) ∗
         memRegion (s0.sp - 127#64) 1) =
        (((s0.sp - 160#64) ↦₈ 0#8) ∗
         ((s0.sp - 159#64) ↦ₛ st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (s0.sp - 127#64) 1) := by
      rw [lik_unpack_stack s0.sp hlik_split1]
      simp only [sepConj_assoc]
    rw [hpack]
    have hsub127 : s0.sp - 160#64 + 33#64 = s0.sp - 127#64 := by bv_omega
    have h := memRegion_34_of_tag_32_1 (s0.sp - 160#64) 0#8
      st.localIdentity.publicKey.bytes.toList hlen_lik
    rwa [hsub159, hsub127] at h
  refine SepWP.fold hmr34 (by sep_focus) ?_
  rw [stackAt_dropVecChain_eq_remoteIdentityKey s0.sp]
  wp_apply
  simp only [arm64_norm, *]
  have hstack_fold :
      (memRegion (s0.sp - 4688#64) 4048 ∗ stackAt (s0.sp - 496#64) remoteIdentityKeyStack) ⊢
        stackAt (s0.sp - 496#64) dropVecChainStack :=
    Entails.of_eq (stackAt_dropVecChain_eq_remoteIdentityKey s0.sp).symm
  refine SepWP.fold hstack_fold (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_unified (s0.sp - 160#64) st.remoteIdentity) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun remBs => ?_
  refine SepWP.pure_elim fun ⟨hrem_len, hrem_eq⟩ => ?_
  obtain ⟨rd0, rh4, rw6, rw14, rw22, rh30, hrem_split⟩ :=
    exists_remoteIk_split_of_length_32 hrem_len
  have hsub158 : s0.sp - 160#64 + 2#64 = s0.sp - 158#64 := by bv_omega
  rw [hsub159, hsub158, rem_unpack_stack s0.sp hrem_split]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_sp_160 s0.sp 0#8 (remoteIdentityTag st.remoteIdentity) rd0 rh4))
    (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by simp only [mid_428, arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hfl_m hsym_m
  refine SepWP.mono_pre (by exact Entails.of_eq (by ac_rfl))
    (hcont _ remBs rd0 rh4 rw6 rw14 rw22 rh30 u_232 u_228 u_208
      hrem_len hrem_eq hrem_split hfl_m hsym_m
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))

@[arm64_norm, wp_norm]
theorem bv_lik_w9 (b4 b5 b6 : BitVec 8) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (b5 ++ b4) |||
          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b6 <<< 16))) =
      (0#8 ++ b6 ++ b5 ++ b4 : BitVec 32).zeroExtend 64 := by
  have h1 : (0#8 ++ b6 ++ b5 ++ b4 : BitVec 32) = 0#8 ++ b6 ++ (b5 ++ b4) := by bv_kernel
  rw [h1]; clear h1
  generalize b5 ++ b4 = x
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv_lik_x8 (b9 b10 b11 b12 b13 b14 : BitVec 8) :
    (0#16 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) |||
      (BitVec.zeroExtend 64 (b14 ++ b13) <<< 48) =
      b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 := by
  have h1 : (0#16 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      0#16 ++ (b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8) := by bv_kernel
  have h2 : (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      (b14 ++ b13) ++ (b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8) := by bv_kernel
  rw [h1, h2]; clear h1 h2
  generalize b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 = x
  generalize b14 ++ b13 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv_lik_x24 (b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8) :
    (0#48 ++ b8 ++ b7 : BitVec 64) |||
      (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 := by
  have h1 : (0#48 ++ b8 ++ b7 : BitVec 64) = 0#48 ++ (b8 ++ b7) := by bv_kernel
  have h2 : (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9) ++ 0#16 := by bv_kernel
  have h3 : (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 : BitVec 64) =
      (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9) ++ (b8 ++ b7) := by bv_kernel
  rw [h1, h2, h3]; clear h1 h2 h3
  generalize b8 ++ b7 = x
  generalize b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv16_eta_bytes (w : BitVec 16) :
    w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv32_eta_bytes (w : BitVec 32) :
    w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_eta_bytes (w : BitVec 64) :
    w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++ w.extractLsb' 32 8 ++
      w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  bv_kernel

@[arm64_norm, wp_norm]
theorem zext32_bv16_zext64 (w : BitVec 16) :
    (w.zeroExtend 32).zeroExtend 64 = w.zeroExtend 64 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext_bv8_and_ff (b : BitVec 8) :
    (b.zeroExtend 32 &&& 0xff#32) = b.zeroExtend 32 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext64_bv8_setWidth_32 (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 32 = b.zeroExtend 32 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext64_bv8_setWidth_8 (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 8 = b := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext32_bv8_zext64 (b : BitVec 8) :
    (b.zeroExtend 32).zeroExtend 64 = b.zeroExtend 64 := by bv_kernel

theorem sc_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
       ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12))) :
    ((sp - 432#64) ↦ₛ bs) =
      (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) ∗ ((sp - 416#64) ↦₆₄ w2) ∗
       ((sp - 408#64) ↦₆₄ w3) ∗ ((sp - 400#64) ↦₆₄ w4) ∗ ((sp - 392#64) ↦₆₄ w5) ∗
       ((sp - 384#64) ↦₆₄ w6) ∗ ((sp - 376#64) ↦₆₄ w7) ∗ ((sp - 368#64) ↦₆₄ w8) ∗
       ((sp - 360#64) ↦₆₄ w9) ∗ ((sp - 352#64) ↦₆₄ w10) ∗ ((sp - 344#64) ↦₆₄ w11) ∗
       ((sp - 336#64) ↦₆₄ w12)) := by
  rw [h (sp - 432#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem rk_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((sp - 328#64) ↦ₛ bs) =
      (((sp - 328#64) ↦₆₄ w0) ∗ ((sp - 320#64) ↦₆₄ w1) ∗
       ((sp - 312#64) ↦₆₄ w2) ∗ ((sp - 304#64) ↦₆₄ w3)) := by
  rw [h (sp - 328#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem err22_unpack_stack (sp p w16 : BitVec 64)
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 : BitVec 64} {h22 : BitVec 16}
    (h : ∀ a : BitVec 64, ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ ((a + 16#64) ↦₆₄ w16)) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ h22))) :
    (((sp - 152#64) ↦₆₄ p) ∗ ((sp - 144#64) ↦₆₄ 27#64) ∗ ((sp - 136#64) ↦₆₄ w16)) ⊢
      (((sp - 152#64) ↦₃₂ d0) ∗ ((sp - 148#64) ↦₁₆ h4) ∗ ((sp - 146#64) ↦₆₄ w6) ∗
       ((sp - 138#64) ↦₆₄ w14) ∗ ((sp - 130#64) ↦₁₆ h22)) := by
  have h1 := h (sp - 152#64)
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] at h1 ⊢
  rw [h1]
  exact Entails.refl _

theorem sp_288_combine_prev (sp : BitVec 64) (prev u_284 : BitVec 32) :
    (((sp - 288#64) ↦₃₂ prev) ∗ ((sp - 284#64) ↦₃₂ u_284)) =
      ((sp - 288#64) ↦₆₄ (u_284 ++ prev)) := by
  have h := (pointsTo64_eq_pointsTo32 (sp - 288#64) prev u_284).symm
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem ret_168_split_prev (r : BitVec 64) (prev u_284 : BitVec 32) :
    ((r + 168#64) ↦₆₄ (u_284 ++ prev)) ⊢
      ((r + 168#64) ↦₃₂ prev) ∗ memRegion (r + 172#64) 4 := by
  rw [pointsTo64_eq_pointsTo32 (r + 168#64) prev u_284]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _) (pointsTo32_entails_memRegion _ _)

theorem ret_200_split_lik (r : BitVec 64) :
    memRegion (r + 200#64) 32 =
      (∃∗ l0 : BitVec 32, (r + 200#64) ↦₃₂ l0) ∗
      (∃∗ l4 : BitVec 16, (r + 204#64) ↦₁₆ l4) ∗
      (∃∗ l6 : BitVec 8, (r + 206#64) ↦₈ l6) ∗
      (∃∗ l7 : BitVec 64, (r + 207#64) ↦₆₄ l7) ∗
      (∃∗ l15 : BitVec 64, (r + 215#64) ↦₆₄ l15) ∗
      (∃∗ l23 : BitVec 64, (r + 223#64) ↦₆₄ l23) ∗
      (∃∗ l31 : BitVec 8, (r + 231#64) ↦₈ l31) := by
  rw [mr_cut_add r 200 4 28 (by decide)]
  rw [mr_cut_add r 204 2 26 (by decide)]
  rw [mr_cut_add r 206 1 25 (by decide)]
  rw [mr_cut_add r 207 8 17 (by decide)]
  rw [mr_cut_add r 215 8 9 (by decide)]
  rw [mr_cut_add r 223 8 1 (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two, memRegion_one]

theorem ret_232_split_rem (r : BitVec 64) :
    memRegion (r + 232#64) 32 =
      (∃∗ m0 : BitVec 32, (r + 232#64) ↦₃₂ m0) ∗
      (∃∗ m4 : BitVec 16, (r + 236#64) ↦₁₆ m4) ∗
      (∃∗ m6 : BitVec 64, (r + 238#64) ↦₆₄ m6) ∗
      (∃∗ m14 : BitVec 64, (r + 246#64) ↦₆₄ m14) ∗
      (∃∗ m22 : BitVec 64, (r + 254#64) ↦₆₄ m22) ∗
      (∃∗ m30 : BitVec 16, (r + 262#64) ↦₁₆ m30) := by
  rw [mr_cut_add r 232 4 28 (by decide)]
  rw [mr_cut_add r 236 2 26 (by decide)]
  rw [mr_cut_add r 238 8 18 (by decide)]
  rw [mr_cut_add r 246 8 10 (by decide)]
  rw [mr_cut_add r 254 8 2 (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two]

theorem speAt_missingRemoteIdentity_sp_160 (A : RustAlloc) (sp base : BitVec 64) :
    (((sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
     ((sp - 152#64) ↦₆₄ (base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) ∗
     ((sp - 144#64) ↦₆₄ 27#64) ∗
     ((base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
     memRegion (sp - 136#64) 24) ⊢
      speAt A (utf8 "decrypt") (sp - 160#64) (.invalidSessionStructure .missingRemoteIdentity) := by
  have h := speAt_missingRemoteIdentity_intro A (sp - 160#64) (base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem vecU8Buf_zero_entails_emp (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (h : cap = 0) :
    vecU8Buf A cap ptr bs ⊢ emp := by
  subst h
  unfold vecU8Buf
  simp only [↓reduceIte]
  exact Entails.pure_left (fun _ => Entails.refl _)

theorem vecU8Buf_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (h : cap ≠ 0) :
    vecU8Buf A cap ptr bs ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  rw [ite_eq_right_iff.mpr (fun hc => (h hc).elim)]
  apply Entails.pure_left
  rintro ⟨hle, _, _⟩
  refine sepConj_mono (Entails.refl _) ?_
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    memRegion_split' (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono (pointsToBytes_entails_memRegion ptr bs) (Entails.refl _)

theorem trFrom_step_428_to_0e8
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDropSpe : DropSpeOkExt img A ext)
    (hDropVecChain : DropVecChainOkExt img.base A ext)
    (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (senderPad : List (BitVec 8))
    (s0 sm : State) (target_pc : BitVec 64) (F_cs : SepProp)
    (post : State → SepProp → Prop)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {remBs : List (BitVec 8)}
    {rd0 : BitVec 32} {rh4 : BitVec 16} {rw6 rw14 rw22 : BitVec 64} {rh30 : BitVec 16}
    {u_232 : BitVec 32} {u_228 : BitVec 16} {u_208 u_284 : BitVec 32}
    {sc0 sc1 sc2 sc3 sc4 sc5 sc6 sc7 sc8 sc9 sc10 sc11 sc12 : BitVec 64}
    {rk0 rk1 rk2 rk3 : BitVec 64}
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : G.chains.length = st.receiverChains.length)
    (hpq_ne : G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_split2 : ∀ a : BitVec 64,
      (a ↦ₛ st.localIdentity.publicKey.bytes.toList) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31)))
    (hsc_split : ∀ a : BitVec 64, (a ↦ₛ optSenderChainBytes st.senderChain senderPad) =
      ((a ↦₆₄ sc0) ∗ ((a + 8#64) ↦₆₄ sc1) ∗ ((a + 16#64) ↦₆₄ sc2) ∗
       ((a + 24#64) ↦₆₄ sc3) ∗ ((a + 32#64) ↦₆₄ sc4) ∗ ((a + 40#64) ↦₆₄ sc5) ∗
       ((a + 48#64) ↦₆₄ sc6) ∗ ((a + 56#64) ↦₆₄ sc7) ∗ ((a + 64#64) ↦₆₄ sc8) ∗
       ((a + 72#64) ↦₆₄ sc9) ∗ ((a + 80#64) ↦₆₄ sc10) ∗ ((a + 88#64) ↦₆₄ sc11) ∗
       ((a + 96#64) ↦₆₄ sc12)))
    (hrk_split : ∀ a : BitVec 64, (a ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) =
      ((a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3)))
    (hrem_eq : ∀ ik, st.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList)
    (hrem_split : ∀ a : BitVec 64, (a ↦ₛ remBs) =
      ((a ↦₃₂ rd0) ∗ ((a + 4#64) ↦₁₆ rh4) ∗ ((a + 6#64) ↦₆₄ rw6) ∗
       ((a + 14#64) ↦₆₄ rw14) ∗ ((a + 22#64) ↦₆₄ rw22) ∗ ((a + 30#64) ↦₁₆ rh30)))
    (hfl : img.FrozenLoaded sm) (hsym : sm.symtab = img.symtab)
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 1064#64)
    (hrun : sm.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : sm.trace = s0.trace)
    (_hx8 : sm.readReg64 .x8 = img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))
    (_hx9 : sm.readReg64 .x9 = 27#64)
    (hx10 : sm.readReg64 .x10 = (remoteIdentityTag st.remoteIdentity).zeroExtend 64)
    (hx11 : sm.readReg64 .x11 = rw14)
    (hx12 : sm.readReg64 .x12 = rw6)
    (hx19 : sm.readReg64 .x19 = ret)
    (hx20 : sm.readReg64 .x20 = G.pq.cap)
    (hx21 : sm.readReg64 .x21 = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64)
    (hx22 : sm.readReg64 .x22 = s0.sp - 160#64)
    (hx23 : sm.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : sm.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : sm.readReg64 .x25 = b7.zeroExtend 64)
    (hx26 : sm.readReg64 .x26 = (b12 ++ b11 ++ b10 ++ b9).zeroExtend 64)
    (hx27 : sm.readReg64 .x27 = (b14 ++ b13).zeroExtend 64)
    (hx28 : sm.readReg64 .x28 = b8.zeroExtend 64)
    (hx29 : sm.readReg64 .x29 = s0.sp - 96#64)
    (hsp : sm.sp = s0.sp - 496#64)
    (hcont : ∀ sf,
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 232#64 →
      sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp - 496#64 →
      calleeSavedVRegs sf = calleeSavedVRegs sm →
      SepWP (tripleRatchetProgAtExt img.base ext) target_pc sf
        (A.pool ∗
         trResultAt A ret G
           (match st.remoteIdentity with
            | some rem =>
              .ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains,
                    st.previousCounter, maxForwardJumps⟩,
                   st.pqRatchetState, st.localIdentity, rem⟩
            | none => .error (.invalidSessionStructure .missingRemoteIdentity)) ∗
         sessionStateAt A ss G.afterTrFrom
           { st with receiverChains := [], pqRatchetState := [] } ∗
         memRegion (s0.sp - 496#64) 400 ∗
         stackAt (s0.sp - 496#64) dropVecChainStack ∗
         F_cs)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) target_pc sm
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 8 ∗
       ((s0.sp - 488#64) ↦₃₂ (b5 ++ b4).zeroExtend 32) ∗
       ((s0.sp - 484#64) ↦₃₂ b6.zeroExtend 32) ∗
       ((s0.sp - 480#64) ↦₆₄ w15) ∗
       ((s0.sp - 472#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
       ((s0.sp - 464#64) ↦₆₄ G.pq.ptr) ∗
       ((s0.sp - 280#64) ↦₆₄ w23) ∗
       ((s0.sp - 272#64) ↦₈ b31) ∗
       memRegion (s0.sp - 271#64) 7 ∗
       ((s0.sp - 264#64) ↦₃₂ rd0) ∗
       ((s0.sp - 260#64) ↦₁₆ rh4) ∗
       memRegion (s0.sp - 258#64) 26 ∗
       ((s0.sp - 232#64) ↦₃₂ u_232) ∗
       ((s0.sp - 228#64) ↦₁₆ u_228) ∗
       memRegion (s0.sp - 226#64) 18 ∗
       ((s0.sp - 208#64) ↦₃₂ u_208) ∗
       memRegion (s0.sp - 204#64) 20 ∗
       ((s0.sp - 184#64) ↦₆₄ rw22) ∗
       ((s0.sp - 176#64) ↦₁₆ rh30) ∗
       memRegion (s0.sp - 174#64) 14 ∗
       ((s0.sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
       ((s0.sp - 152#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) ∗
       ((s0.sp - 144#64) ↦₆₄ 27#64) ∗
       ((s0.sp - 136#64) ↦₆₄ rw22) ∗
       ((s0.sp - 128#64) ↦₁₆ rh30) ∗
       memRegion (s0.sp - 126#64) 14 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       stackAt (s0.sp - 496#64) dropVecChainStack ∗
       (A.pool ∗
        ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
        ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
        ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
        ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
        ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
        ((s0.sp - 284#64) ↦₃₂ u_284) ∗
        memRegion ret 264 ∗
        sessionAfter208Frame A ss G st ∗
        F_cs))
      post := by
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  have hdropSpe := dropSpe_ok_at_from hDropSpe
  have hdropCh := dropVecChain_ok_at_from hDropVecChain
  have hdealloc := dealloc_ok_at_from (b := img.base) hA
  clear hDropSpe hDropVecChain
  have hsc_len : (optSenderChainBytes st.senderChain senderPad).length = 104 :=
    optSenderChainBytes_length st.senderChain hpad
  have hrk_len : (CryptoGames.HMAC.keyToBytes32 st.rootKey).length = 32 :=
    length_keyToBytes32 st.rootKey
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x428 59
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0x58c 23
  dsimp only [tripleRatchetProgAtExt] at hpc hdropSpe hdropCh hdealloc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = entry
  examples_hide_fetches
  apply SepWP.of_sepWP_inv (mid := entry + bv% (232)) hfl hsym
  refine SepWP.fold (sessionStateAt_reassemble_after208 A ss G st hlik) (by sep_focus) ?_
  generalize hS_post :
    sessionStateAt A ss G.afterTrFrom { st with receiverChains := [], pqRatchetState := [] } = S_post at *
  cases hrem : st.remoteIdentity with
  | some rem =>
    have hrem_bs : remBs = rem.publicKey.bytes.toList := hrem_eq rem hrem
    subst hrem_bs
    dsimp only [remoteIdentityTag] at hx10
    refine SepWP.intro_rodata_missingRemoteIdentity himg hfl ?_
    refine SepWP.fold (memRegion_24_of_8_2_14 s0.sp rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold (speAt_missingRemoteIdentity_sp_160 A s0.sp img.base) (by sep_focus) ?_
    rw [stackAt_dropVecChain_eq_dropSpe s0.sp]
    apply SepWP.of_sepWP_inv (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))) hfl hsym
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hfl_454 hsym_454
    refine SepWP.call_dropSpe (sp_val := s0.sp - 496#64) hdropSpe
      ⟨s0.sp - 160#64, utf8 "decrypt", .invalidSessionStructure .missingRemoteIdentity⟩
      hfl_454 hsym_454 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro s_458 hpc_458 hsp_458 hrun_458 _ hcs_458 htr_458 hfl_458 hsym_458
    rcases hcs_458 with ⟨hx19_458, hx20_458, hx21_458, hx22_458, hx23_458, hx24_458,
      hx25_458, hx26_458, hx27_458, hx28_458, hx29_458, hvregs_458⟩
    simp only [arm64_norm, hsp, hx19, hx20, hx25, hx26, hx27, hx28, hx29] at hpc_458 hsp_458 hx19_458 hx20_458 hx21_458 hx22_458 hx23_458 hx24_458 hx25_458 hx26_458 hx27_458 hx28_458 hx29_458 hvregs_458
    have hstack_dropSpe_fold :
        (memRegion (s0.sp - 4688#64) 64 ∗ stackAt (s0.sp - 496#64) dropSpeStack) ⊢
          stackAt (s0.sp - 496#64) dropVecChainStack :=
      Entails.of_eq (stackAt_dropVecChain_eq_dropSpe s0.sp).symm
    refine SepWP.fold hstack_dropSpe_fold (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sp_288_combine_prev s0.sp st.previousCounter u_284)) (by sep_focus) ?_
    refine SepWP.fold (Entails.refl (memRegion ret 264)) (by sep_focus) ?_
    refine SepWP.fold (Entails.refl (memRegion (s0.sp - 160#64) 48)) (by sep_focus) ?_
    rw [memRegion_48_split_8_2_38 s0.sp,
        sc_unpack_stack s0.sp hsc_split,
        rk_unpack_stack s0.sp hrk_split,
        ret_264_split_some ret,
        ret_200_split_lik ret,
        ret_232_split_rem ret]
    simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun u_152 => SepWP.exists_elim fun u_160 => ?_
    refine SepWP.exists_elim fun m30 => SepWP.exists_elim fun m22 => ?_
    refine SepWP.exists_elim fun m14 => SepWP.exists_elim fun m6 => ?_
    refine SepWP.exists_elim fun m4 => SepWP.exists_elim fun m0 => ?_
    refine SepWP.exists_elim fun l31 => SepWP.exists_elim fun l23 => ?_
    refine SepWP.exists_elim fun l15 => SepWP.exists_elim fun l7 => ?_
    refine SepWP.exists_elim fun l6 => SepWP.exists_elim fun l4 => ?_
    refine SepWP.exists_elim fun l0 => SepWP.exists_elim fun w24 => ?_
    refine SepWP.exists_elim fun w23_r => SepWP.exists_elim fun w22_r => ?_
    refine SepWP.exists_elim fun w21_r => SepWP.exists_elim fun w20_r => ?_
    refine SepWP.exists_elim fun w19_r => SepWP.exists_elim fun w18_r => ?_
    refine SepWP.exists_elim fun w17_r => SepWP.exists_elim fun w16_r => ?_
    refine SepWP.exists_elim fun w15_r => SepWP.exists_elim fun w14_r => ?_
    refine SepWP.exists_elim fun w13_r => SepWP.exists_elim fun w12_r => ?_
    refine SepWP.exists_elim fun w11_r => SepWP.exists_elim fun w10_r => ?_
    refine SepWP.exists_elim fun w9_r => SepWP.exists_elim fun w8_r => ?_
    refine SepWP.exists_elim fun w7_r => SepWP.exists_elim fun w6_r => ?_
    refine SepWP.exists_elim fun w5_r => SepWP.exists_elim fun w4_r => ?_
    refine SepWP.exists_elim fun w3_r => SepWP.exists_elim fun w2_r => ?_
    refine SepWP.exists_elim fun w1_r => SepWP.exists_elim fun w0_r => ?_
    wp_steps
    refine SepWP.fold (sc_pack_stack s0.sp hsc_split) (by sep_focus) ?_
    refine SepWP.fold (sc_pack_ret ret hsc_split) (by sep_focus) ?_
    refine SepWP.fold (rk_pack_stack s0.sp hrk_split) (by sep_focus) ?_
    refine SepWP.fold (rk_pack_ret ret hrk_split) (by sep_focus) ?_
    refine SepWP.fold (lik_pack_ret ret hlik_split2) (by sep_focus) ?_
    refine SepWP.fold (rem_pack_ret ret hrem_split) (by sep_focus) ?_
    clear hlik_split2 hsc_split hrk_split hrem_split hdropSpe hdropCh hdealloc
    refine SepWP.fold (ret_168_split_prev ret st.previousCounter u_284) (by sep_focus) ?_
    refine SepWP.fold (trResultAt_ok_intro A ret G st rem senderPad hclamp hchains hpad) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sp_288_combine_prev s0.sp st.previousCounter u_284).symm) (by sep_focus) ?_
    refine SepWP.fold (memRegion_48_of_8_2_38 s0.sp rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_280_184_fold s0.sp w23 b31 rd0 rh4 u_232 u_228 u_208 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
        w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
    refine SepWP.fold
      (memRegion_24_of_8_8_8 s0.sp G.chainsCap G.chainsPtr
        (BitVec.ofNat 64 st.receiverChains.length)) (by sep_focus) ?_
    refine SepWP.fold
      (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
        (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
        25000#64 st.previousCounter u_284) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hfl_f hsym_f
    have hcont' := hcont _ hfl_f hsym_f
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    rw [hrem] at hcont'
    exact SepWP.mono_pre (Entails.of_eq (by ac_rfl)) hcont'
  | none =>
    clear hlik_split2 hsc_split hrk_split hrem_split hrem_eq hdropSpe
    dsimp only [remoteIdentityTag] at hx10
    refine SepWP.intro_rodata_missingRemoteIdentity himg hfl ?_
    obtain ⟨ed0, eh4, ew6, ew14, eh22, herr_split, herr_ret⟩ :=
      exists_err22_split (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22
    refine SepWP.fold (err22_unpack_stack s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22 herr_split) (by sep_focus) ?_
    rw [ret_264_split_none ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun r38 => SepWP.exists_elim fun r30 => ?_
    refine SepWP.exists_elim fun r22 => SepWP.exists_elim fun r20 => ?_
    refine SepWP.exists_elim fun r16 => SepWP.exists_elim fun r8 => ?_
    refine SepWP.exists_elim fun r0 => ?_
    wp_steps
    refine SepWP.fold (err22_pack_stack s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22 herr_split) (by sep_focus) ?_
    refine SepWP.fold (err22_pack_ret ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) herr_ret r38) (by sep_focus) ?_
    clear herr_split herr_ret
    refine SepWP.fold
      (trResultAt_err_missingRemoteIdentity_intro A ret G (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) (by sep_focus) ?_
    refine SepWP.fold
      (memRegion_48_of_8_8_8_8_2_14 s0.sp 0x8000000000000014#64
        (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) 27#64 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_280_184_fold s0.sp w23 b31 rd0 rh4 ed0 eh4 ed0 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
        w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
    refine SepWP.fold (vecAt_chains_stack_fold A s0.sp G st hchains) (by sep_focus) ?_
    by_cases hpq0 : G.pq.cap = 0
    · rw [hpq0] at hx20
      refine SepWP.fold
        (vecU8Buf_zero_entails_emp A G.pq.cap G.pq.ptr st.pqRatchetState hpq0) (by sep_focus) ?_
      simp only [emp_sepConj, hpq0, show ((0 : BitVec 64) == 0#64) = true from rfl, not_true_eq_false, ↓reduceIte]
      rw [← hsp]
      wp_steps
      wp_apply
      rw [hsp]
      wp_steps
      refine SepWP.fold
        (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
          (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
          25000#64 st.previousCounter u_284) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_f hsym_f
      have hcont' := hcont _ hfl_f hsym_f
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      rw [hrem] at hcont'
      exact SepWP.mono_pre (Entails.of_eq (by ac_rfl)) hcont'
    · have hpq_beq_false : (G.pq.cap == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; exact hpq0
      simp only [hpq_beq_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      obtain ⟨hpq_pos, hpq_lt, hpq_ptr⟩ := hpq_ne hpq0
      refine SepWP.fold
        (vecU8Buf_entails_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState hpq0) (by sep_focus) ?_
      simp only [sepConj_assoc]
      rw [stackAt_dropVecChain_eq_allocHook s0.sp, ← hsp]
      wp_steps
      wp_apply
      rw [hsp]
      have hstack_dealloc_fold :
          (memRegion (s0.sp - 4688#64) 96 ∗ stackAt (s0.sp - 496#64) allocHookStack) ⊢
            stackAt (s0.sp - 496#64) dropVecChainStack :=
        Entails.of_eq (stackAt_dropVecChain_eq_allocHook s0.sp).symm
      refine SepWP.fold hstack_dealloc_fold (by sep_focus) ?_
      wp_steps
      wp_apply
      rw [hsp_sf, hsp]
      wp_steps
      refine SepWP.fold
        (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
          (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
          25000#64 st.previousCounter u_284) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_f hsym_f
      have hcont' := hcont _ hfl_f hsym_f
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      rw [hrem] at hcont'
      exact SepWP.mono_pre (Entails.of_eq (by ac_rfl)) hcont'

theorem trFrom_step_244_to_0e8
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hRemoteIk : RemoteIdentityKeyOkExt img A ext)
    (hDropSpe : DropSpeOkExt img A ext)
    (hDropVecChain : DropVecChainOkExt img.base A ext)
    (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (senderPad : List (BitVec 8))
    (s0 s : State) (target_pc : BitVec 64) (F_cs : SepProp)
    (post : State → SepProp → Prop)
    {u_284 : BitVec 32}
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : G.chains.length = st.receiverChains.length)
    (hpq_ne : G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length)
    (hrik : match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = G.pq.cap)
    (hx21 : s.readReg64 .x21 = G.pq.ptr)
    (hx22 : s.readReg64 .x22 = ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ sf,
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 232#64 →
      sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp - 496#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext) target_pc sf
        (A.pool ∗
         trResultAt A ret G
           (match st.remoteIdentity with
            | some rem =>
              .ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains,
                    st.previousCounter, maxForwardJumps⟩,
                   st.pqRatchetState, st.localIdentity, rem⟩
            | none => .error (.invalidSessionStructure .missingRemoteIdentity)) ∗
         sessionStateAt A ss G.afterTrFrom
           { st with receiverChains := [], pqRatchetState := [] } ∗
         memRegion (s0.sp - 496#64) 400 ∗
         stackAt (s0.sp - 496#64) dropVecChainStack ∗
         (logOff img ∗ F_cs))
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) target_pc s
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 280#64) 184 ∗
       stackAt (s0.sp - 496#64) dropVecChainStack ∗
       (A.pool ∗
        ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
        ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
        ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
        ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
        ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
        ((s0.sp - 284#64) ↦₃₂ u_284) ∗
        memRegion ret 264 ∗
        sessionAfter208Frame A ss G st ∗
        (logOff img ∗ F_cs)))
      post := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, w15, w23, b31,
    hlik_split1, hlik_split2⟩ :=
    exists_localIk_split_of_length_32 st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨sc0, sc1, sc2, sc3, sc4, sc5, sc6, sc7, sc8, sc9, sc10, sc11, sc12, hsc_split⟩ :=
    exists_unpack64_of_length_104 (optSenderChainBytes_length st.senderChain hpad)
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_split⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 st.rootKey)
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (trFrom_step_244_to_428 himg hA hRemoteIk ss G st s0 s target_pc
      (A.pool ∗
       ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
       ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
       ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
       vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
       vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
       ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
       ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
       ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
       ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion ret 264 ∗
       sessionAfter208Frame A ss G st ∗
       F_cs) post
      hlik_split1 hlik hlik_toNat hrik hfl hsym hpc hrun halign htr
      hx0 hx1 hx8 hx21 hx22 hx23 hx24 hx25 hx29 hsp ?_)
  intro sm remBs rd0 rh4 rw6 rw14 rw22 rh30 u_232 u_228 u_208
    _ hrem_eq hrem_split hfl_m hsym_m hpc_m hrun_m htr_m
    hx8_m hx9_m hx10_m hx11_m hx12_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
    hx25_m hx26_m hx27_m hx28_m hx29_m hsp_m hvregs_m
  rw [hx19] at hx19_m
  rw [hx20] at hx20_m
  exact SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (trFrom_step_428_to_0e8 himg hA hDropSpe hDropVecChain ret ss G st senderPad s0 sm target_pc (logOff img ∗ F_cs) post
      hpad hclamp hchains hpq_ne hlik hlik_split2 hsc_split hrk_split hrem_eq hrem_split
      hfl_m hsym_m hpc_m hrun_m halign htr_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
      hx25_m hx26_m hx27_m hx28_m hx29_m hsp_m
      fun sf hfl_f hsym_f hpc_f hrun_f htr_f hsp_f hvregs_f =>
        hcont sf hfl_f hsym_f hpc_f hrun_f htr_f hsp_f (hvregs_f.trans hvregs_m))

end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet

