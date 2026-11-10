/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureA
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureDecode
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
namespace CryptoVerification.E2E.Pqxdh.Shared
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open SignalPqxdh SignalPqxdh.Model
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
private theorem calleeSavedVRegs_setPC_pre_trap (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc
private theorem calleeSavedVRegs_setMem_setPC_pre_trap (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre_trap calleeSavedVRegs_setMem_setPC_pre_trap
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3dd44
  libsignalSessionCode_fnOff_0x3de30
  libsignalSessionCode_fnOff_0x3de58
  libsignalSessionCode_fnOff_0x3eda8
  (ls_stub% "memset")
  (ls_stub% "memcpy")
  (ls_stub% "sha2::sha512::compress512")
  (ls_stub% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide")
  (ls_stub% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::compress")
  (ls_stub% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint")
  (ls_hook% "memset")
  (ls_hook% "memcpy")
  (ls_hook% "sha2::sha512::compress512")
  (ls_hook% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide")
  (ls_hook% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::compress")
  (ls_hook% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint")
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3de58
  and64_mask255_ite_1_0
  csinc_eq_zero32_ite_1_0
private theorem list_sig_split_63 {sig : Bytes} (hsig : sig.length = 64) :
    bytesToBv8 sig = bytesToBv8 (sig.take 63) ++ [(bytesToBv8 sig).getD 63 0#8] := by
  rcases sig with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | ⟨b32, _ | ⟨b33, _ | ⟨b34, _ | ⟨b35, _ | ⟨b36, _ | ⟨b37, _ | ⟨b38, _ | ⟨b39,
    _ | ⟨b40, _ | ⟨b41, _ | ⟨b42, _ | ⟨b43, _ | ⟨b44, _ | ⟨b45, _ | ⟨b46, _ | ⟨b47,
    _ | ⟨b48, _ | ⟨b49, _ | ⟨b50, _ | ⟨b51, _ | ⟨b52, _ | ⟨b53, _ | ⟨b54, _ | ⟨b55,
    _ | ⟨b56, _ | ⟨b57, _ | ⟨b58, _ | ⟨b59, _ | ⟨b60, _ | ⟨b61, _ | ⟨b62, _ | ⟨b63, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hsig)
  rfl
private theorem sig_focus_63 {sig : Bytes} (sigPtr : BitVec 64) (h : sig.length = 64) :
    (sigPtr ↦ₛ bytesToBv8 sig) = ((sigPtr ↦ₛ bytesToBv8 (sig.take 63)) ∗
       ((sigPtr + 63#64) ↦₈ (bytesToBv8 sig).getD 63 0#8)) := by
  have hl63 : (bytesToBv8 (sig.take 63)).length = 63 := by simp [bytesToBv8, h]
  conv => lhs; rw [list_sig_split_63 h]
  rw [pointsToBytes_append, hl63]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
@[local simp, local wp_norm, local arm64_norm]
private theorem sig_getD63_ushiftRight7_eq_signBit (sig : Bytes) :
    (bytesToBv8 sig).getD 63 0#8 >>> 7 = BitVec.ofNat 8 (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) :=
      by
  rw [bytesToBv8_getD_eq]
  rcases sig.getD 63 0 with ⟨bv⟩
  revert bv; decide
private theorem cells_12_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ⊢ memRegion a 96 := by
  rw [memRegion_cells a 12 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <| Entails.refl _
theorem stackAt_verifySig_merge (fsp : BitVec 64) :
    stackAt fsp pqxdhHookStack ∗ memRegion fsp 1152 ∗ memRegion (fsp + 1152#64) 96 =
      stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) := by
  have h1248 : memRegion fsp 1152 ∗ memRegion (fsp + 1152#64) 96 = memRegion fsp 1248 :=
    (ProofLib.memRegion_split' (b := fsp) (n := 1152) (k := 96) (b' := fsp + 1152#64)
      rfl (by bv_omega) (by decide)).symm
  rw [h1248, memRegion_cells fsp 156 (by decide)]
  have hsp : fsp = (fsp + 1248#64) - 1248#64 := by bv_omega
  conv => lhs; rw [hsp]
  exact (stackAt_split_cells (fsp + 1248#64) pqxdhHookStack 156 (by decide)).symm
private theorem dalekMontToEdOutBv8_none_eq (P : Primitives) (pk : Bytes) (signBit : UInt8)
    (hmont : P.montToEd pk signBit = none) (a : BitVec 64) :
    dalekMontToEdOutAt P a pk signBit = (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 160 :=
  dalekMontToEdOutAt_none P pk signBit hmont a
private theorem dalekMontToEdOutBv8_some_eq (P : Primitives) (pk edPt : Bytes) (signBit : UInt8)
    (hmont : P.montToEd pk signBit = some edPt) (hlen : edPt.length = 160) (a : BitVec 64) :
    dalekMontToEdOutAt P a pk signBit = (a ↦₆₄ 1#64) ∗ ((a + 8#64) ↦ₛ bytesToBv8 edPt) :=
  dalekMontToEdOutAt_some P pk edPt signBit hmont hlen a
private theorem memRegion168_of_cell_and_memRegion160_v (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ⊢ memRegion a 168 := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := pointsTo64_entails_memRegion a v
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 160) (b' :=
    a + 8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _
private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ⊢ memRegion a 168 := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := pointsTo64_entails_memRegion a v
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 :=
    pointsToBytes_entails_memRegion_n (a + 8#64) bs hlen
  refine Entails.trans (sepConj_mono h1 h2) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 160) (b' :=
    a + 8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _
private theorem exists_unpack64_of_length_160_eq {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
         ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
         ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a +
         88#64) ↦₆₄ w11) ∗
         ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a +
         120#64) ↦₆₄ w15) ∗
         ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17) ∗ ((a + 144#64) ↦₆₄ w18) ∗ ((a +
         152#64) ↦₆₄ w19)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19,
    fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++ ((bs.drop 64).take 32 ++
    ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3; rw [s3] at s2; rw [s2] at s1; exact s1
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, pointsToBytes_append, h1, hp1, pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
private theorem uint8_and7f_ule32_of_and60_eq_false (b : UInt8) (h : (b &&& 0x60 == 0) = false) :
    (32#64).ule (BitVec.zeroExtend 64 b.toBitVec &&& 545460846719#64) = true := by
  rcases b with ⟨bv⟩; revert bv h; decide
private theorem uint8_and7f_ule32_of_and60_eq_true (b : UInt8) (h : (b &&& 0x60 == 0) = true) :
    (32#64).ule (BitVec.zeroExtend 64 b.toBitVec &&& 545460846719#64) = false := by
  rcases b with ⟨bv⟩; revert bv h; decide
private theorem truncate32_and7f_eq (sig : Bytes) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec &&& 545460846719#64) =
      BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32 := by
  rw [bytesToBv8_getD_eq]
  generalize sig.getD 63 0 = b
  rcases b with ⟨bv⟩; revert bv; decide
theorem SepWP.of_sepWP_sha512IV {prog : Program} {mid target_pc : BitVec 64} {s : State} {P :
    SepProp} {post : State → SepProp → Prop} {b : BitVec 64}
    (hro : Obj.HoldsBytes s.mem (b + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (h : SepWP prog (roStop mid) s P
      (fun sm Pm => Obj.HoldsBytes sm.mem (b + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro) →
        SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold roStop at h
  with_unfolding_all intro R hm hL
  obtain ⟨sm, hsteps1, ⟨_, _, Pm, hmm, hnext⟩ | hoom1⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      (hnext (holdsBytes_ro_of_keepsFrozen hro hsteps1.keepsFrozen)).elim hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hoom1⟩
private theorem sha512IV_cells_eq (a : BitVec 64) : ((a ↦₆₄ 0x6a09e667f3bcc908#64) ∗
     ((a + 8#64) ↦₆₄ 0xbb67ae8584caa73b#64) ∗ ((a + 16#64) ↦₆₄ 0x3c6ef372fe94f82b#64) ∗
     ((a + 24#64) ↦₆₄ 0xa54ff53a5f1d36f1#64) ∗ ((a + 32#64) ↦₆₄ 0x510e527fade682d1#64) ∗
     ((a + 40#64) ↦₆₄ 0x9b05688c2b3e6c1f#64) ∗ ((a + 48#64) ↦₆₄ 0x1f83d9abfb41bd6b#64) ∗
     ((a + 56#64) ↦₆₄ 0x5be0cd19137e2179#64)) = (a ↦ₛ sha512IVBytesLE) := by
  rw [sha512IVBytesLE_eq_unpack64]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ←
    pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
private theorem stackAt_verifySig_split (fsp : BitVec 64) :
    stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) =
      stackAt fsp pqxdhHookStack ∗ memRegion fsp 1152 ∗ cells (fsp + 1152#64) 12 := by
  rw [← stackAt_verifySig_merge fsp, memRegion_cells (fsp + 1152#64) 12 (by decide)]
private theorem memRegion_1152_seg1a_split (fsp : BitVec 64) :
    memRegion fsp 1152 = cells fsp 1 ∗ memRegion (fsp + 8#64) 8 ∗ cells (fsp + 16#64) 4 ∗
      memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 800#64) 168 ∗
      memRegion (fsp + 968#64) 184 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 1144) (b' :=
    fsp + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 1136) (b' :=
      fsp + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 16#64) (n := 32) (k := 1104) (b' :=
      fsp + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 48#64) (n := 752) (k := 352) (b' :=
      fsp + 800#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 800#64) (n := 168) (k := 184) (b' :=
      fsp + 968#64) rfl (by bv_omega) (by decide),
    memRegion_cells fsp 1 (by decide), memRegion_cells (fsp + 16#64) 4 (by decide)]
private theorem memRegion_1152_seg1a_merge (fsp : BitVec 64) : (fsp ↦₆₄ 0#64) ∗
    memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 752 ∗
    memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ⊢ memRegion fsp 1152 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion fsp 0#64)) (Entails.of_eq
    ?_)
  rw [← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 168) (k := 184) (b' :=
    fsp + 968#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 48#64) (n := 752) (k := 352) (b' :=
      fsp + 800#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 16#64) (n := 32) (k := 1104) (b' :=
      fsp + 48#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 1136) (b' :=
      fsp + 16#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 1144) (b' :=
      fsp + 8#64) rfl (by bv_omega) (by decide)]
private theorem memRegion_752_seg1b_split (fsp : BitVec 64) :
    memRegion (fsp + 48#64) 752 = cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗
      memRegion (fsp + 368#64) 32 ∗ memRegion (fsp + 400#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 48#64) (n := 160) (k := 592) (b' :=
    fsp + 208#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 208#64) (n := 160) (k := 432) (b' :=
      fsp + 368#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 368#64) (n := 32) (k := 400) (b' :=
      fsp + 400#64) rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 48#64) 20 (by decide), memRegion_cells (fsp + 208#64) 20 (by decide)]
private theorem memRegion_752_seg1b_merge (fsp : BitVec 64) {edPt capA : Bytes}
    (hed : edPt.length = 160) (hcapA : capA.length = 32) :
    memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
    ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗
    memRegion (fsp + 400#64) 400 ⊢ memRegion (fsp + 48#64) 752 := by
  have h1 : ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ⊢ memRegion (fsp + 208#64) 160 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hed])
  have h2 : ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ⊢ memRegion (fsp + 368#64) 32 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hcapA])
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) (Entails.of_eq
    ?_)
  rw [← ProofLib.memRegion_split' (b := fsp + 368#64) (n := 32) (k := 400) (b' :=
    fsp + 400#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 208#64) (n := 160) (k := 432) (b' :=
      fsp + 368#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 48#64) (n := 160) (k := 592) (b' :=
      fsp + 208#64) rfl (by bv_omega) (by decide)]
private theorem seg1b_to_seg1c_split (fsp : BitVec 64) : (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗
    memRegion (fsp + 400#64) 400 ⊢
      memRegion fsp 4 ∗ memRegion (fsp + 4#64) 4 ∗ cells (fsp + 8#64) 1 ∗
      memRegion (fsp + 400#64) 160 ∗ cells (fsp + 560#64) 8 ∗ memRegion (fsp + 624#64) 63 ∗
      memRegion (fsp + 687#64) 1 ∗ cells (fsp + 688#64) 10 ∗ memRegion (fsp + 768#64) 32 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion fsp 0#64)) (Entails.of_eq
    ?_)
  rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 4) (b' :=
    fsp + 4#64) rfl (by bv_omega) (by decide), memRegion_cells (fsp + 8#64) 1 (by decide),
    ProofLib.memRegion_split' (b := fsp + 400#64) (n := 160) (k := 240) (b' :=
      fsp + 560#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 560#64) (n := 64) (k := 176) (b' :=
      fsp + 624#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 624#64) (n := 63) (k := 113) (b' :=
      fsp + 687#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 687#64) (n := 1) (k := 112) (b' :=
      fsp + 688#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 688#64) (n := 80) (k := 32) (b' :=
      fsp + 768#64) rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 560#64) 8 (by decide), memRegion_cells (fsp + 688#64) 10 (by decide)]
  simp only [sepConj_assoc]
private theorem memRegion_800_seg3a_split (fsp : BitVec 64) :
    memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 = cells (fsp + 800#64) 16 ∗
      cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
      memRegion (fsp + 1136#64) 16 := by
  rw [← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 168) (k := 184) (b' :=
    fsp + 968#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 800#64) (n := 128) (k := 224) (b' :=
      fsp + 928#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 928#64) (n := 80) (k := 144) (b' :=
      fsp + 1008#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 128) (k := 16) (b' :=
      fsp + 1136#64) rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 800#64) 16 (by decide),
    memRegion_cells (fsp + 928#64) 10 (by decide),
    memRegion_cells (fsp + 1008#64) 16 (by decide)]
private theorem seg3a_to_seg3b_split (fsp : BitVec 64) :
    cells (fsp + 800#64) 16 ∗
    cells (fsp + 928#64) 10 ∗
    cells (fsp + 1008#64) 16 =
      cells (fsp + 800#64) 4 ∗
      memRegion (fsp + 832#64) 128 ∗
      memRegion (fsp + 960#64) 48 ∗
      memRegion (fsp + 1008#64) 32 ∗
      memRegion (fsp + 1040#64) 96 := by
  rw [← memRegion_cells (fsp + 800#64) 16 (by decide),
    ← memRegion_cells (fsp + 928#64) 10 (by decide),
    ← memRegion_cells (fsp + 1008#64) 16 (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 928#64) (n := 80) (k := 128) (b' :=
      fsp + 1008#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 128) (k := 208) (b' :=
      fsp + 928#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 800#64) (n := 32) (k := 304) (b' :=
      fsp + 832#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 832#64) (n := 128) (k := 176) (b' :=
      fsp + 960#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 960#64) (n := 48) (k := 128) (b' :=
      fsp + 1008#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 32) (k := 96) (b' :=
      fsp + 1040#64) rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 800#64) 4 (by decide)]
private theorem seg3b_to_epilogue_merge (fsp : BitVec 64)
    (v4 : BitVec 32) (v8 : BitVec 64) {capA minusCapA hScalar : Bytes}
    (hcapA : capA.length = 32) (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32) :
    memRegion fsp 4 ∗
    ((fsp + 4#64) ↦₃₂ v4) ∗
    ((fsp + 8#64) ↦₆₄ v8) ∗
    memRegion (fsp + 16#64) 32 ∗
    memRegion (fsp + 48#64) 160 ∗
    memRegion (fsp + 208#64) 160 ∗
    ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗
    ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗
    cells (fsp + 560#64) 16 ∗
    cells (fsp + 688#64) 10 ∗
    ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
    memRegion (fsp + 800#64) 160 ∗
    memRegion (fsp + 960#64) 48 ∗
    memRegion (fsp + 1008#64) 32 ∗
    memRegion (fsp + 1040#64) 96 ∗
    memRegion (fsp + 1136#64) 16 ⊢ memRegion fsp 1152 := by
  have hw4 : ((fsp + 4#64) ↦₃₂ v4) ⊢ memRegion (fsp + 4#64) 4 := pointsTo32_entails_memRegion _ _
  have hw8 : ((fsp + 8#64) ↦₆₄ v8) ⊢ memRegion (fsp + 8#64) 8 := pointsTo64_entails_memRegion _ _
  have hw368 : ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ⊢ memRegion (fsp + 368#64) 32 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hcapA])
  have hw400 : ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ⊢ memRegion (fsp + 400#64) 160 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hnegA])
  have hw768 : ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ⊢ memRegion (fsp + 768#64) 32 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hh])
  rw [← memRegion_cells (fsp + 560#64) 16 (by decide),
    ← memRegion_cells (fsp + 688#64) 10 (by decide)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hw4 (sepConj_mono hw8
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hw368 (sepConj_mono hw400
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw768)))))))))))
    (Entails.of_eq ?_)
  rw [← ProofLib.memRegion_split' (b := fsp + 1040#64) (n := 96) (k := 16) (b' :=
    fsp + 1136#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 32) (k := 112) (b' :=
      fsp + 1040#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 960#64) (n := 48) (k := 144) (b' :=
      fsp + 1008#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 160) (k := 192) (b' :=
      fsp + 960#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 768#64) (n := 32) (k := 352) (b' :=
      fsp + 800#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 688#64) (n := 80) (k := 384) (b' :=
      fsp + 768#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 560#64) (n := 128) (k := 464) (b' :=
      fsp + 688#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 400#64) (n := 160) (k := 592) (b' :=
      fsp + 560#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 368#64) (n := 32) (k := 752) (b' :=
      fsp + 400#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 208#64) (n := 160) (k := 784) (b' :=
      fsp + 368#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 48#64) (n := 160) (k := 944) (b' :=
      fsp + 208#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 16#64) (n := 32) (k := 1104) (b' :=
      fsp + 48#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 1136) (b' :=
      fsp + 16#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 4#64) (n := 4) (k := 1144) (b' :=
      fsp + 8#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 1148) (b' :=
      fsp + 4#64) rfl (by bv_omega) (by decide)]
private theorem SepWP.seq_seg {prog : Program} {mid target : BitVec 64} {s : State} {P P' P_mid :
    SepProp}
    {Q_regs : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P' (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_regs sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.weaken_pre hP <| SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)
private theorem SepWP.end_seg {prog : Program} {target : BitVec 64} {s : State} {P P' P_out :
    SepProp}
    {Q_regs : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog target s P' (fun sm Pm => (Pm ⊢ P_out) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (hpost : ∀ sm Pm, (Pm ⊢ P_out) → Q_regs sm → post sm Pm) :
    SepWP prog target s P post :=
  SepWP.weaken_pre hP <| SepWP.mono h1 fun sm Pm _ _ ⟨hent, hQ⟩ => hpost sm Pm hent hQ
private theorem SepWP.seq_seg_ro {prog : Program} {mid target : BitVec 64} {s : State} {P P' P_mid :
    SepProp}
    {Q_regs : State → Prop} {post : State → SepProp → Prop} {b : BitVec 64}
    (hro : Obj.HoldsBytes s.mem (b + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (h1 : SepWP prog mid s P' (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (h2 : ∀ (sm : State), sm.pc = mid → sm.status = .Running →
      Obj.HoldsBytes sm.mem (b + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro) →
      Q_regs sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  with_unfolding_all intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpc1, hrun1, Pm, hmm, hent, hQ⟩ | hoom1⟩ := (SepWP.weaken_pre hP h1).elim hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      (SepWP.weaken_pre hent (h2 sm hpc1 hrun1 (holdsBytes_ro_of_keepsFrozen hro hsteps1.keepsFrozen) hQ)).elim
        hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hoom1⟩
private theorem xeddsaVerifyRef_of_montToEd_none (P : Primitives) {pk m sig : Bytes}
    (hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) = none) :
    xeddsaVerifyRef P pk m sig = false := by
  unfold xeddsaVerifyRef
  dsimp only
  rw [hmont]
  split <;> rfl
private theorem xeddsaVerifyRef_of_60_false (P : Primitives) {pk m sig : Bytes}
    (h60 : (sig.getD 63 0 &&& 0x60 == 0) = false) :
    xeddsaVerifyRef P pk m sig = false := by
  unfold xeddsaVerifyRef
  rw [h60, Bool.and_false]
  rfl
private theorem xeddsaVerifyRef_of_some (P : Primitives) (m : Bytes) {pk sig edPt : Bytes}
    (hpk : pk.length = 32) (hsig : sig.length = 64)
    (h60 : (sig.getD 63 0 &&& 0x60 == 0) = true)
    (hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) = some edPt) :
    (let capA := P.compress edPt
     let minusCapA := P.edNeg edPt
     let capR := sig.take 32
     let sRaw := sig.drop 32
     let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
     let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
     let sScalar := P.scalarFromBytesModOrder sClamped
     let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
     if (capRCheck == capR) = true then (1#64 : BitVec 64) else 0#64) =
    (if xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) := by
  have heq : xeddsaVerifyRef P pk m sig =
      (let capA := P.compress edPt
       let minusCapA := P.edNeg edPt
       let capR := sig.take 32
       let sRaw := sig.drop 32
       let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
       let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
       let sScalar := P.scalarFromBytesModOrder sClamped
       let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
       capRCheck == capR) := by
    unfold xeddsaVerifyRef
    have hpkb : (pk.length == 32) = true := beq_iff_eq.mpr hpk
    have hsigb : (sig.length == 64) = true := beq_iff_eq.mpr hsig
    rw [hpkb, hsigb, h60]
    dsimp only [Bool.true_and, ↓reduceIte]
    rw [hmont]
    rfl
  rw [heq]
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3de30 libsignalSessionCode_fnOff_0x3de58
private theorem stackAt_1280_split (fsp : BitVec 64) :
    stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) =
      stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ cells (fsp + 1248#64) 4 := by
  have h1 : fsp + 1280#64 - 32#64 = fsp + 1248#64 := by bv_omega
  have h2 : pqxdhHookStack + 1280 = (pqxdhHookStack + 1248) + 4 * 8 := by decide
  rw [h2, stackAt_split_cells (fsp + 1280#64) (pqxdhHookStack + 1248) 4 (by decide), h1]
private theorem stackAt_1280_merge (fsp v0 v1 v2 v3 : BitVec 64) :
    ((fsp + 1248#64) ↦₆₄ v0) ∗ ((fsp + 1256#64) ↦₆₄ v1) ∗
    ((fsp + 1264#64) ↦₆₄ v2) ∗ ((fsp + 1272#64) ↦₆₄ v3) ∗
    stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ⊢
      stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) := by
  rw [stackAt_1280_split fsp, sepConj_comm (stackAt _ _), ← sepConj_assoc, ← sepConj_assoc, ←
    sepConj_assoc]
  refine sepConj_mono_left ?_
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <| Entails.refl _

section WithProgramTrap
variable {C : Crypto}
local notation "PP" b:arg absHooks:arg => trTrapProgAt b C absHooks

theorem verifySig_seg1a_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp pkPtr slicesPtr sigPtr retAddr : BitVec 64) (pk sig : Bytes) (Frame : SepProp)
    (hpk : pk.length = 32) (hsig : sig.length = 64) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym)
    (hsp : s.sp = fsp + 1248#64) (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr) (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr) (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks) ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64)
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ cells fsp 1 ∗ cells (fsp + 16#64) 4 ∗
       memRegion (fsp + 800#64) 168 ∗ cells (fsp + 1152#64) 12 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
          memRegion (fsp + 16#64) 32 ∗
          dalekMontToEdOutAt P (fsp + 800#64) pk ((sig.getD 63 0 &&& 0x80) >>> 7) ∗
          ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
          ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
          1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
          ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
          1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
          1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
          1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
          ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
          1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = sigPtr ∧ sm.readReg64 (.gpr 20#5) = slicesPtr ∧
        sm.readReg64 (.gpr 21#5) = 1#64 ∧
        sm.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 ((bytesToBv8 sig).getD 63 0#8) ∧
        sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hmont : subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr verifySignatureMultipartSym +
        BitVec.ofNat 64 (num% (ls_off% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards" - 0x3de58)))
      (dalekMontToEdStubSpec P img) :=
    hook_ok_at (hname := dalekMontToEdStub) rfl
      (by fnoff_eq) (by fnoff_eq)
      (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekMontToEdStub])
      (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekMontToEd)
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    0) hfn (by decide) verifySignatureMultipart_decode_0x3de58
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at f0
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    4) hfn (by decide) verifySignatureMultipart_decode_0x3de5c
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    8) hfn (by decide) verifySignatureMultipart_decode_0x3de60
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    12) hfn (by decide) verifySignatureMultipart_decode_0x3de64
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    16) hfn (by decide) verifySignatureMultipart_decode_0x3de68
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    20) hfn (by decide) verifySignatureMultipart_decode_0x3de6c
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    24) hfn (by decide) verifySignatureMultipart_decode_0x3de70
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    28) hfn (by decide) verifySignatureMultipart_decode_0x3de74
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    32) hfn (by decide) verifySignatureMultipart_decode_0x3de78
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    36) hfn (by decide) verifySignatureMultipart_decode_0x3de7c
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    40) hfn (by decide) verifySignatureMultipart_decode_0x3de80
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    44) hfn (by decide) verifySignatureMultipart_decode_0x3de84
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    48) hfn (by decide) verifySignatureMultipart_decode_0x3de88
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    52) hfn (by decide) verifySignatureMultipart_decode_0x3de8c
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    56) hfn (by decide) verifySignatureMultipart_decode_0x3de90
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    60) hfn (by decide) verifySignatureMultipart_decode_0x3de94
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    64) hfn (by decide) verifySignatureMultipart_decode_0x3de98
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    68) hfn (by decide) verifySignatureMultipart_decode_0x3de9c
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    72) hfn (by decide) verifySignatureMultipart_decode_0x3dea0
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    76) hfn (by decide) verifySignatureMultipart_decode_0x3dea4
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    80) hfn (by decide) verifySignatureMultipart_decode_0x3dea8
  dsimp only [trTrapProgAt] at hmont hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  have hpk_bv : (bytesToBv8 pk).length = 32 := by simp [bytesToBv8, hpk]
  obtain ⟨p0, p1, p2, p3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hpk_bv
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_focus_63 sigPtr hsig)) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hpk_cells pkPtr)) (by sep_focus)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (sig_focus_63 sigPtr hsig).symm) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hpk_cells pkPtr).symm) (by sep_focus)
  have hpk_sp16 := (hpk_cells (fsp + 16#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk_sp16
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hpk_sp16) (by sep_focus)
  wp_call hmont ⟨pk, (sig.getD 63 0 &&& 0x80) >>> 7, fsp + 16#64, fsp + 800#64⟩
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (congrArg (dalekMontToEdOutAt P (fsp + 800#64) pk)
      (signBit_shr7_and_one (sig.getD 63 0))))
    (by sep_focus)
  have hm32_16 := pointsToBytes_entails_memRegion_n (fsp + 16#64) _ hpk_bv
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_16) (by sep_focus)
  wp_simp_pre_fast [hsp_sf]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩
set_option maxHeartbeats 4000000 in
theorem verifySig_epilogue_trap (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp retAddr res : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (Frame : SepProp) (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64)
    (hsp : s.sp = fsp) (hx0 : s.readReg64 (.gpr 0#5) = res) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (memRegion fsp 1152 ∗ ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ stackAt fsp pqxdhHookStack ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = res ∧ sm.readReg64 (.gpr 19#5) = x19_0 ∧
        sm.readReg64 (.gpr 20#5) = x20_0 ∧ sm.readReg64 (.gpr 21#5) = x21_0 ∧
        sm.readReg64 (.gpr 22#5) = x22_0 ∧ sm.readReg64 (.gpr 23#5) = x23_0 ∧
        sm.readReg64 (.gpr 24#5) = x24_0 ∧ sm.readReg64 (.gpr 25#5) = x25_0 ∧
        sm.readReg64 (.gpr 26#5) = x26_0 ∧ sm.readReg64 (.gpr 27#5) = x27_0 ∧
        sm.readReg64 (.gpr 28#5) = x28_0 ∧ sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1100) hfn (by decide) verifySignatureMultipart_decode_0x3e2a4
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1104) hfn (by decide) verifySignatureMultipart_decode_0x3e2a8
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1108) hfn (by decide) verifySignatureMultipart_decode_0x3e2ac
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1112) hfn (by decide) verifySignatureMultipart_decode_0x3e2b0
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1116) hfn (by decide) verifySignatureMultipart_decode_0x3e2b4
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1120) hfn (by decide) verifySignatureMultipart_decode_0x3e2b8
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1124) hfn (by decide) verifySignatureMultipart_decode_0x3e2bc
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1128) hfn (by decide) verifySignatureMultipart_decode_0x3e2c0
  dsimp only [trTrapProgAt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  wp_steps
  have hm12 := cells_12_merge (fsp +
    1152#64) x29_0 retAddr x28_0 x27_0 x26_0 x25_0 x24_0 x23_0 x22_0 x21_0 x20_0 x19_0
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm12
  apply ProofLib.SepWP.replace_pre (hPQ := hm12) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (stackAt_verifySig_merge fsp)) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
set_option maxHeartbeats 4000000 in
theorem verifySig_epilogue_false_trap (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (Frame : SepProp) (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64)
    (hsp : s.sp = fsp) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (memRegion fsp 1152 ∗ ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ stackAt fsp pqxdhHookStack ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = 0#64 ∧ sm.readReg64 (.gpr 19#5) = x19_0 ∧
        sm.readReg64 (.gpr 20#5) = x20_0 ∧ sm.readReg64 (.gpr 21#5) = x21_0 ∧
        sm.readReg64 (.gpr 22#5) = x22_0 ∧ sm.readReg64 (.gpr 23#5) = x23_0 ∧
        sm.readReg64 (.gpr 24#5) = x24_0 ∧ sm.readReg64 (.gpr 25#5) = x25_0 ∧
        sm.readReg64 (.gpr 26#5) = x26_0 ∧ sm.readReg64 (.gpr 27#5) = x27_0 ∧
        sm.readReg64 (.gpr 28#5) = x28_0 ∧ sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1096) hfn (by decide) verifySignatureMultipart_decode_0x3e2a0
  dsimp only [trTrapProgAt] at f0 hpc ⊢
  wp_step
  exact verifySig_epilogue_trap img absHooks _ fsp retAddr 0#64
    x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 Frame
    hfsp_align (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
set_option maxHeartbeats 4000000 in
theorem verifySig_seg1a_none_trap (P : Primitives) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (s : State) (fsp : BitVec 64)
    (pk : Bytes) (signBit : UInt8) (Frame : SepProp) (hmont : P.montToEd pk signBit = none)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64)
    (hsp : s.sp = fsp) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64)
      s
      (dalekMontToEdOutAt P (fsp + 800#64) pk signBit ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 800#64) 168 ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64 ∧ sm.sp = fsp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    84) hfn (by decide) verifySignatureMultipart_decode_0x3deac
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    88) hfn (by decide) verifySignatureMultipart_decode_0x3deb0
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    92) hfn (by decide) verifySignatureMultipart_decode_0x3deb4
  dsimp only [trTrapProgAt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (dalekMontToEdOutBv8_none_eq P pk signBit hmont (fsp + 800#64))) (by sep_focus)
  wp_steps
  have hm168 := memRegion168_of_cell_and_memRegion160_v (fsp + 800#64) 0#64
  apply ProofLib.SepWP.replace_pre (hPQ := hm168) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩
set_option maxHeartbeats 8000000 in
theorem verifySig_seg1b_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks) (s : State) (fsp : BitVec 64)
    (pk edPt : Bytes) (signBit : UInt8) (Frame : SepProp)
    (hmont : P.montToEd pk signBit = some edPt) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64)
    (hsp : s.sp = fsp) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64)
      s
      (cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗ memRegion (fsp + 368#64) 32 ∗
       dalekMontToEdOutAt P (fsp + 800#64) pk signBit ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
          ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗ memRegion (fsp + 800#64) 168 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hcomp := dalekCompressStub_ok_at_trap hH (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::compress" - 0x3de58))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    84) hfn (by decide) verifySignatureMultipart_decode_0x3deac
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    88) hfn (by decide) verifySignatureMultipart_decode_0x3deb0
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    92) hfn (by decide) verifySignatureMultipart_decode_0x3deb4
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    96) hfn (by decide) verifySignatureMultipart_decode_0x3deb8
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    100) hfn (by decide) verifySignatureMultipart_decode_0x3debc
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    104) hfn (by decide) verifySignatureMultipart_decode_0x3dec0
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    108) hfn (by decide) verifySignatureMultipart_decode_0x3dec4
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    112) hfn (by decide) verifySignatureMultipart_decode_0x3dec8
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    116) hfn (by decide) verifySignatureMultipart_decode_0x3decc
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    120) hfn (by decide) verifySignatureMultipart_decode_0x3ded0
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    124) hfn (by decide) verifySignatureMultipart_decode_0x3ded4
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    128) hfn (by decide) verifySignatureMultipart_decode_0x3ded8
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    132) hfn (by decide) verifySignatureMultipart_decode_0x3dedc
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    136) hfn (by decide) verifySignatureMultipart_decode_0x3dee0
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    140) hfn (by decide) verifySignatureMultipart_decode_0x3dee4
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    144) hfn (by decide) verifySignatureMultipart_decode_0x3dee8
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    148) hfn (by decide) verifySignatureMultipart_decode_0x3deec
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    152) hfn (by decide) verifySignatureMultipart_decode_0x3def0
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    156) hfn (by decide) verifySignatureMultipart_decode_0x3def4
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    160) hfn (by decide) verifySignatureMultipart_decode_0x3def8
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    164) hfn (by decide) verifySignatureMultipart_decode_0x3defc
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    168) hfn (by decide) verifySignatureMultipart_decode_0x3df00
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    172) hfn (by decide) verifySignatureMultipart_decode_0x3df04
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    176) hfn (by decide) verifySignatureMultipart_decode_0x3df08
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    180) hfn (by decide) verifySignatureMultipart_decode_0x3df0c
  have f25 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    184) hfn (by decide) verifySignatureMultipart_decode_0x3df10
  have f26 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    188) hfn (by decide) verifySignatureMultipart_decode_0x3df14
  have f27 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    192) hfn (by decide) verifySignatureMultipart_decode_0x3df18
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    196) hfn (by decide) verifySignatureMultipart_decode_0x3df1c
  have f29 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    200) hfn (by decide) verifySignatureMultipart_decode_0x3df20
  have f30 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    204) hfn (by decide) verifySignatureMultipart_decode_0x3df24
  have f31 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    208) hfn (by decide) verifySignatureMultipart_decode_0x3df28
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    212) hfn (by decide) verifySignatureMultipart_decode_0x3df2c
  have f33 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    216) hfn (by decide) verifySignatureMultipart_decode_0x3df30
  have f34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    220) hfn (by decide) verifySignatureMultipart_decode_0x3df34
  have f35 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    224) hfn (by decide) verifySignatureMultipart_decode_0x3df38
  have f36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    228) hfn (by decide) verifySignatureMultipart_decode_0x3df3c
  dsimp only [trTrapProgAt] at hcomp hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  have hed_len : edPt.length = 160 := hWF.montToEd_len pk signBit edPt hmont
  have hed_bv_len : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hed_len]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
    hed_cells⟩ := exists_unpack64_of_length_160_eq hed_bv_len
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (dalekMontToEdOutBv8_some_eq P pk edPt signBit hmont hed_len (fsp + 800#64)))
    (by sep_focus)
  have hed_808 := hed_cells (fsp + 800#64 + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_808
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_808) (by sep_focus)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_808.symm) (by sep_focus)
  have hm168 := memRegion168_of_cell_and_bytes160 (fsp + 800#64) 1#64 hed_bv_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm168
  apply ProofLib.SepWP.replace_pre (hPQ := hm168) (by sep_focus)
  have hed_48 := (hed_cells (fsp + 48#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_48
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_48) (by sep_focus)
  have hed_208 := (hed_cells (fsp + 208#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_208
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_208) (by sep_focus)
  wp_call hcomp ⟨fsp + 48#64, edPt, fsp + 368#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.compress_len _), hsp, hsp_sf]
  have hm160_48 := pointsToBytes_entails_memRegion_n (fsp + 48#64) _ hed_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_48) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
theorem verifySig_seg1c_invalid_trap (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (sig : Bytes) (Frame : SepProp) (hinv : (sig.getD 63 0 &&& 0x60 == 0) = false)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64)
      s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64 ∧ sm.sp = s.sp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    232) hfn (by decide) verifySignatureMultipart_decode_0x3df40
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    236) hfn (by decide) verifySignatureMultipart_decode_0x3df44
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    240) hfn (by decide) verifySignatureMultipart_decode_0x3df48
  dsimp only [trTrapProgAt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  wp_steps
  rw [uint8_and7f_ule32_of_and60_eq_false (sig.getD 63 0) hinv]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨Entails.refl _, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩
theorem verifySig_seg1c_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp sigPtr : BitVec 64) (edPt sig : Bytes) (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (hedPt : edPt.length = 160) (hsig : sig.length = 64)
    (hvalid : (sig.getD 63 0 &&& 0x60 == 0) = true) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 (.gpr 19#5) = sigPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
      s
      (memRegion fsp 4 ∗ memRegion (fsp + 4#64) 4 ∗ cells (fsp + 8#64) 1 ∗
       ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
       memRegion (fsp + 400#64) 160 ∗ cells (fsp + 560#64) 8 ∗ memRegion (fsp + 687#64) 1 ∗
       cells (fsp + 688#64) 10 ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion fsp 4 ∗
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 208#64) 160 ∗
          ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32 ++ P.compress edPt)) ∗
          ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ sha512IVBytesLE) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hedneg := dalekEdNegStub_ok_at_trap hH (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg" - 0x3de58))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    232) hfn (by decide) verifySignatureMultipart_decode_0x3df40
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    236) hfn (by decide) verifySignatureMultipart_decode_0x3df44
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    240) hfn (by decide) verifySignatureMultipart_decode_0x3df48
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    244) hfn (by decide) verifySignatureMultipart_decode_0x3df4c
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    248) hfn (by decide) verifySignatureMultipart_decode_0x3df50
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    252) hfn (by decide) verifySignatureMultipart_decode_0x3df54
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    256) hfn (by decide) verifySignatureMultipart_decode_0x3df58
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    260) hfn (by decide) verifySignatureMultipart_decode_0x3df5c
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    264) hfn (by decide) verifySignatureMultipart_decode_0x3df60
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    268) hfn (by decide) verifySignatureMultipart_decode_0x3df64
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    272) hfn (by decide) verifySignatureMultipart_decode_0x3df68
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    276) hfn (by decide) verifySignatureMultipart_decode_0x3df6c
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    280) hfn (by decide) verifySignatureMultipart_decode_0x3df70
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    284) hfn (by decide) verifySignatureMultipart_decode_0x3df74
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    288) hfn (by decide) verifySignatureMultipart_decode_0x3df78
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    292) hfn (by decide) verifySignatureMultipart_decode_0x3df7c
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    296) hfn (by decide) verifySignatureMultipart_decode_0x3df80
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    300) hfn (by decide) verifySignatureMultipart_decode_0x3df84
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    304) hfn (by decide) verifySignatureMultipart_decode_0x3df88
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    308) hfn (by decide) verifySignatureMultipart_decode_0x3df8c
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    312) hfn (by decide) verifySignatureMultipart_decode_0x3df90
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    316) hfn (by decide) verifySignatureMultipart_decode_0x3df94
  dsimp only [trTrapProgAt] at hedneg hpc ⊢
  have hent_eq : (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C
    absHooks))).fnAddr verifySignatureMultipartSym = img.base + 253528#64 := by
    rw [Program.fnAddr_rebase, hfn]
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  have hb0 : img.base &&& 0xfff#64 = 0#64 :=
    aligned_and_fff (ProofLib.ObjectLoad.Loads.aligned himg)
  have hadrp0 : ((entry + 260#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_xref% 0x3df5c 0x3df60) - 0x3d000) + bv% ((ls_xref% 0x3df5c 0x3df60) % 4096) =
      img.base + bv% (ls_xref% 0x3df5c 0x3df60) := by
    subst hent_eq; rw [and_pageMask_eq_sub_and_fff]; bv_bits
  have hadrp1 : ((entry + 260#64) &&& 0xfffffffffffff000#64) + bv% (ls_xref% 0x3df5c 0x3df60 - 0x3d000) =
      img.base + bv% (ls_xref% 0x3df5c 0x3df60) := by
    rw [← hadrp0, BitVec.add_assoc]; rfl
  have hadrp2 : ((entry + 260#64) &&& 0xfffffffffffff000#64) + bv% (ls_xref% 0x3df5c 0x3df60 + 32 - 0x3d000) =
      img.base + bv% (ls_xref% 0x3df5c 0x3df60 + 32) := by
    have h32 : (bv% (ls_xref% 0x3df5c 0x3df60 + 32 - 0x3d000) : BitVec 64) =
        bv% (ls_xref% 0x3df5c 0x3df60 - 0x3d000) + 32#64 := rfl
    rw [h32, ← BitVec.add_assoc, hadrp1, BitVec.add_assoc]; rfl
  clear hent_eq hb0 hadrp0
  have hsig32_bv : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  obtain ⟨r0, r1, r2, r3, _, hsig32_cells⟩ := exists_unpack64_of_length_32 hsig32_bv
  have hcapA_bv : (bytesToBv8 (P.compress edPt)).length = 32 := by
    simp [bytesToBv8, hWF.compress_len]
  obtain ⟨a0, a1, a2, a3, _, hcapA_cells⟩ := exists_unpack64_of_length_32 hcapA_bv
  rw [ProofLib.memRegion_four (fsp + 4#64), ProofLib.memRegion_one (fsp + 687#64)]
  cells_pre_unfold_fast
  wp_extract_exists
  apply SepWP.of_sepWP_sha512IV hro (mid := entry + 272#64)
  wp_step
  wp_step
  wp_step
  rw [uint8_and7f_ule32_of_and60_eq_true (sig.getD 63 0) hvalid]
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_steps
  wp_call hedneg ⟨fsp + 208#64, edPt, fsp + 400#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.edNeg_len _), truncate32_and7f_eq, hsp, hsp_sf]
  wp_steps
  apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs)
  intro hro1
  apply SepWP.of_sepWP_sha512IV hro1 (mid := entry + 288#64)
  wp_step_ldp_ro (sha512IV_quad0 hro1)
  wp_steps
  apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs)
  intro hro2
  wp_step_ldp_ro (sha512IV_quad1 hro2)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig32_cells sigPtr)) (by sep_focus)
  have hcapA_368 := hcapA_cells (fsp + 368#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcapA_368
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_368) (by sep_focus)
  wp_steps
  have hsha_688 := sha512IV_cells_eq (fsp + 688#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsha_688
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsha_688) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig32_cells sigPtr).symm) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (sig_split_32 sigPtr hsig).symm) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_368.symm) (by sep_focus)
  have hsig_560 := (hsig32_cells (fsp + 560#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsig_560
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsig_560) (by sep_focus)
  have hcapA_592 := (hcapA_cells (fsp + 592#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcapA_592
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_592) (by sep_focus)
  have hmerge_560 : ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((fsp +
    592#64) ↦ₛ bytesToBv8 (P.compress edPt)) =
      ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32 ++ P.compress edPt)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hsig32_bv, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge_560) (by sep_focus)
  have hedPt_bv : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hedPt]
  have hm160_208 := pointsToBytes_entails_memRegion_n (fsp + 208#64) _ hedPt_bv
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_208) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal⟩
private theorem verifySig_tail_from_548_trap
    (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp sigPtr retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (edPt m sig tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp)
    (_hedPt : edPt.length = 160)
    (hsig : sig.length = 64)
    (htail97 : tail97.length = 97)
    (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hsha_eq : revWords64 (sha512CompressOutBytes P st
      (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)) =
        P.sha512 (sig.take 32 ++ P.compress edPt ++ m))
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64)
    (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (memRegion fsp 4 ∗
       ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗
       memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 48#64) 160 ∗
       memRegion (fsp + 208#64) 160 ∗
       ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗
       memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗
       ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗
       ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗
       memRegion (fsp + 768#64) 32 ∗
       memRegion (fsp + 800#64) 168 ∗
       memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt fsp pqxdhHookStack ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) =
          (let capA := P.compress edPt
           let minusCapA := P.edNeg edPt
           let capR := sig.take 32
           let sRaw := sig.drop 32
           let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
           let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
           if (capRCheck == capR) = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = x19_0 ∧
        sm.readReg64 (.gpr 20#5) = x20_0 ∧
        sm.readReg64 (.gpr 21#5) = x21_0 ∧
        sm.readReg64 (.gpr 22#5) = x22_0 ∧
        sm.readReg64 (.gpr 23#5) = x23_0 ∧
        sm.readReg64 (.gpr 24#5) = x24_0 ∧
        sm.readReg64 (.gpr 25#5) = x25_0 ∧
        sm.readReg64 (.gpr 26#5) = x26_0 ∧
        sm.readReg64 (.gpr 27#5) = x27_0 ∧
        sm.readReg64 (.gpr 28#5) = x28_0 ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (memRegion_800_seg3a_split fsp)) (by sep_focus)
  apply SepWP.seq_seg (verifySig_seg3a_trap P A img absHooks hH s fsp tail97 st blkCnt L
    (memRegion fsp 4 ∗
     ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
     ((fsp + 8#64) ↦₆₄ sigPtr) ∗
     memRegion (fsp + 16#64) 32 ∗
     memRegion (fsp + 48#64) 160 ∗
     memRegion (fsp + 208#64) 160 ∗
     ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
     ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
     memRegion (fsp + 1136#64) 16 ∗
     ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
     ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
     ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
     ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
     ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
     ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗
     (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
    htail97 hst hblkL hfsp_align hrun hpc hsp hx23 hx29)
    (Entails.of_eq (by ac_rfl))
  intro s1 hpc1 hrun1 ⟨_, _, hsp1, hx23_1, hx29_1, hv1, htr1⟩
  rw [hsha_eq, fitBv8_of_length_eq (hWF.scalarFromWide_len _)]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (seg3a_to_seg3b_split fsp)) (by sep_focus)
  have hnegA : (P.edNeg edPt).length = 160 := hWF.edNeg_len edPt
  have hh : (P.scalarFromWide (P.sha512 (sig.take 32 ++ P.compress edPt ++ m))).length = 32 :=
    hWF.scalarFromWide_len _
  apply SepWP.seq_seg (verifySig_seg3b_trap P A img absHooks hWF hH s1 fsp sigPtr
    sig (P.edNeg edPt) (P.scalarFromWide (P.sha512 (sig.take 32 ++ P.compress edPt ++ m)))
    (memRegion fsp 4 ∗
     memRegion (fsp + 16#64) 32 ∗
     memRegion (fsp + 48#64) 160 ∗
     memRegion (fsp + 208#64) 160 ∗
     ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
     cells (fsp + 560#64) 16 ∗
     cells (fsp + 688#64) 10 ∗
     memRegion (fsp + 960#64) 48 ∗
     memRegion (fsp + 1040#64) 96 ∗
     memRegion (fsp + 1136#64) 16 ∗
     ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
     ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
     ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
     ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
     ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
     ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ Frame)
    hsig hnegA hh hfsp_align hrun1 hpc1 hsp1 hx23_1 hx29_1)
    (Entails.of_eq (by ac_rfl))
  intro s2 hpc2 hrun2 ⟨_, _, hsp2, hx0_2, hv2, htr2⟩
  have hcapA : (P.compress edPt).length = 32 := hWF.compress_len edPt
  apply ProofLib.SepWP.replace_pre
    (hPQ :=
      seg3b_to_epilogue_merge fsp (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)
      sigPtr hcapA hnegA hh)
    (by sep_focus)
  apply SepWP.end_seg (verifySig_epilogue_trap img absHooks s2 fsp retAddr (s2.readReg64 (.gpr 0#5))
    x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
    ((sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
    hfsp_align hrun2 hpc2 hsp2 rfl)
    (Entails.of_eq (by ac_rfl))
  intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
    hv3, htr3⟩
  exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hrun3, hpc3, hsp3,
    hx0_3.trans hx0_2, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
    hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩
theorem verifySignatureMultipart_sepWP_trap
    (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp pkPtr slicesPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes)
    (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32)
    (hm : m.length = 33 ∨ m.length = 1569)
    (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym)
    (hsp : s.sp = fsp + 1248#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (pkPtr ↦ₛ bytesToBv8 pk) ∗
          (slicesPtr ↦₆₄ msgPtr) ∗
          ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
          (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = (if xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (stackAt_verifySig_split fsp)) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (memRegion_1152_seg1a_split fsp)) (by sep_focus)
  apply SepWP.seq_seg_ro hro (verifySig_seg1a_trap P A img absHooks hH s fsp pkPtr slicesPtr sigPtr
    retAddr pk sig
    ((slicesPtr ↦₆₄ msgPtr) ∗
     ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
     (msgPtr ↦ₛ bytesToBv8 m) ∗
     memRegion (fsp + 8#64) 8 ∗
     memRegion (fsp + 48#64) 752 ∗
     memRegion (fsp + 968#64) 184 ∗
     Frame)
    hpk hsig hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30)
    (Entails.of_eq (by ac_rfl))
  intro s1 hpc1 hrun1 hro1 ⟨_, _, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hv1, htr1⟩
  cases hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) with
  | none =>
    have hxed : xeddsaVerifyRef P pk m sig = false := xeddsaVerifyRef_of_montToEd_none P hmont
    apply SepWP.seq_seg (verifySig_seg1a_none_trap P img absHooks s1 fsp pk ((sig.getD 63 0 &&& 0x80) >>>
      7)
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       (fsp ↦₆₄ 0#64) ∗
       memRegion (fsp + 8#64) 8 ∗
       memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 48#64) 752 ∗
       memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
       1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
       ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
       1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
       ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
       1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
       ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
       1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
       ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
       1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
       stackAt fsp pqxdhHookStack ∗
       (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
      hmont hfsp_align hrun1 hpc1 hsp1)
      (Entails.of_eq (by ac_rfl))
    intro s2 hpc2 hrun2 ⟨_, _, hsp2, hv2, htr2⟩
    apply ProofLib.SepWP.replace_pre (hPQ := memRegion_1152_seg1a_merge fsp) (by sep_focus)
    apply SepWP.end_seg (verifySig_epilogue_false_trap img absHooks s2 fsp retAddr
      (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5)) (s.readReg64
        (.gpr 22#5))
      (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 25#5)) (s.readReg64
        (.gpr 26#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
      hfsp_align hrun2 hpc2 hsp2)
      (Entails.of_eq (by ac_rfl))
    intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
      h29, hv3, htr3⟩
    rw [hxed]
    exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hrun3, hpc3, hsp3, hx0_3,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩
  | some edPt =>
    have hedPt : edPt.length = 160 := hWF.montToEd_len pk _ edPt hmont
    have hcapA : (P.compress edPt).length = 32 := hWF.compress_len edPt
    apply ProofLib.SepWP.replace_pre (hPQ :=
      Entails.of_eq (memRegion_752_seg1b_split fsp)) (by sep_focus)
    apply SepWP.seq_seg_ro hro1 (verifySig_seg1b_trap P A img absHooks hWF hH s1 fsp pk edPt ((sig.getD
      63 0 &&& 0x80) >>> 7)
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       (fsp ↦₆₄ 0#64) ∗
       memRegion (fsp + 8#64) 8 ∗
       memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 400#64) 400 ∗
       memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
       1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
       ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
       1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
       ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
       1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
       ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
       1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
       ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
       1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
       (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
      hmont hfsp_align hrun1 hpc1 hsp1)
      (Entails.of_eq (by ac_rfl))
    intro s2 hpc2 hrun2 hro2 ⟨_, _, hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx29_2, hv2, htr2⟩
    have hx19_s2 : s2.readReg64 (.gpr 19#5) = sigPtr := hx19_2.trans hx19_1
    have hx20_s2 : s2.readReg64 (.gpr 20#5) = slicesPtr := hx20_2.trans hx20_1
    have hx21_s2 : s2.readReg64 (.gpr 21#5) = 1#64 := hx21_2.trans hx21_1
    have hx22_s2 : s2.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec := by
      rw [hx22_2, hx22_1, bytesToBv8_getD_eq sig 63]; generalize sig.getD 63 0 = b; rcases b with
        ⟨bv⟩; revert bv; decide
    have hx29_s2 : s2.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_2.trans hx29_1
    cases h60 : (sig.getD 63 0 &&& 0x60 == 0) with
    | false =>
      have hxed : xeddsaVerifyRef P pk m sig = false := xeddsaVerifyRef_of_60_false P h60
      apply SepWP.seq_seg (verifySig_seg1c_invalid_trap img absHooks s2 sig
        (memRegion (fsp + 48#64) 160 ∗
         ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
         ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
         memRegion (fsp + 800#64) 168 ∗
         stackAt fsp pqxdhHookStack ∗
         (pkPtr ↦ₛ bytesToBv8 pk) ∗
         (sigPtr ↦ₛ bytesToBv8 sig) ∗
         (fsp ↦₆₄ 0#64) ∗
         memRegion (fsp + 8#64) 8 ∗
         memRegion (fsp + 16#64) 32 ∗
         memRegion (fsp + 400#64) 400 ∗
         memRegion (fsp + 968#64) 184 ∗
         ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
         ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
         1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
         ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
         1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
         ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
         1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
         ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
         1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
         ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
         1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
         (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
        h60 hrun2 hpc2 hx22_s2)
        (Entails.of_eq (by ac_rfl))
      intro s3 hpc3 hrun3 ⟨_, _, hsp3, hv3, htr3⟩
      have hsp3_eq : s3.sp = fsp := hsp3.trans hsp2
      apply ProofLib.SepWP.replace_pre (hPQ :=
        memRegion_752_seg1b_merge fsp hedPt hcapA) (by sep_focus)
      apply ProofLib.SepWP.replace_pre (hPQ := memRegion_1152_seg1a_merge fsp) (by sep_focus)
      apply SepWP.end_seg (verifySig_epilogue_false_trap img absHooks s3 fsp retAddr
        (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5)) (s.readReg64
        (.gpr 22#5))
        (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 25#5)) (s.readReg64
        (.gpr 26#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
        ((pkPtr ↦ₛ bytesToBv8 pk) ∗
         (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗
         (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
        hfsp_align hrun3 hpc3 hsp3_eq)
        (Entails.of_eq (by ac_rfl))
      intro s4 P4 hP4 ⟨hrun4, hpc4, hsp4, hx0_4, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
        h29, hv4, htr4⟩
      rw [hxed]
      exact ⟨Entails.trans hP4 (Entails.of_eq (by ac_rfl)), hrun4, hpc4, hsp4, hx0_4,
        h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
        hv4.trans (hv3.trans (hv2.trans hv1)), htr4.trans (htr3.trans (htr2.trans htr1))⟩
    | true =>
      have hxed_eq := xeddsaVerifyRef_of_some P m hpk hsig h60 hmont
      apply ProofLib.SepWP.replace_pre (hPQ := seg1b_to_seg1c_split fsp) (by sep_focus)
      apply SepWP.seq_seg (verifySig_seg1c_trap P A img absHooks himg hWF hH s2 fsp sigPtr edPt sig
        (memRegion (fsp + 16#64) 32 ∗
         memRegion (fsp + 48#64) 160 ∗
         memRegion (fsp + 624#64) 63 ∗
         memRegion (fsp + 768#64) 32 ∗
         memRegion (fsp + 800#64) 168 ∗
         memRegion (fsp + 968#64) 184 ∗
         ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
         ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
         1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
         ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
         1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
         ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
         1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
         ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
         1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
         ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
         1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
         (pkPtr ↦ₛ bytesToBv8 pk) ∗
         (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
        hro2 hedPt hsig h60 hfsp_align hrun2 hpc2 hsp2 hx19_s2 hx22_s2)
        (Entails.of_eq (by ac_rfl))
      intro s3 hpc3 hrun3 ⟨_, _, hsp3, hx20_3, hx21_3, hx23_3, hx29_3, hv3, htr3⟩
      have hx20_s3 : s3.readReg64 (.gpr 20#5) = slicesPtr := hx20_3.trans hx20_s2
      have hx21_s3 : s3.readReg64 (.gpr 21#5) = 1#64 := hx21_3.trans hx21_s2
      have hx23_s3 : s3.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_3.trans hx23_2
      have hx29_s3 : s3.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_3.trans hx29_s2
      have hpre64 : (sig.take 32 ++ P.compress edPt).length = 64 := by simp [hsig, hcapA]
      have hshaIV : sha512IVBytesLE = bytesToBv8 (revWords64 sha512InitState) := rfl
      have hst0 : (revWords64 sha512InitState).length = 64 := revWords64_length (by decide)
      rw [hshaIV]
      rcases hm with hm33 | hm1569
      · rw [hm33, show BitVec.ofNat 64 33 = 33#64 from rfl]
        apply SepWP.seq_seg (verifySig_seg2_33_trap img absHooks s3 fsp slicesPtr msgPtr
          (sig.take 32 ++ P.compress edPt) m (revWords64 sha512InitState)
          (memRegion fsp 4 ∗
           ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
           ((fsp + 8#64) ↦₆₄ sigPtr) ∗
           memRegion (fsp + 16#64) 32 ∗
           memRegion (fsp + 48#64) 160 ∗
           memRegion (fsp + 208#64) 160 ∗
           ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
           ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
           memRegion (fsp + 768#64) 32 ∗
           memRegion (fsp + 800#64) 168 ∗
           memRegion (fsp + 968#64) 184 ∗
           ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
           ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
           1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
           ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
           1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
           ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
           1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
           ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
           1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
           ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
           1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
           (pkPtr ↦ₛ bytesToBv8 pk) ∗
           (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
          hpre64 hm33 hfsp_align hrun3 hpc3 hsp3 hx20_s3 hx21_s3)
          (Entails.of_eq (by ac_rfl))
        intro s4 hpc4 hrun4 ⟨_, _, hsp4, hx23_4, hx29_4, hv4, htr4⟩
        have hx23_s4 : s4.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_4.trans hx23_s3
        have hx29_s4 : s4.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_4.trans hx29_s3
        have htail97 : ((sig.take 32 ++ P.compress edPt) ++ m).length = 97 := by
          simp [hsig, hcapA, hm33]
        have hsha_eq : revWords64 (sha512CompressOutBytes P (revWords64 sha512InitState)
            (((sig.take 32 ++ P.compress edPt) ++ m) ++ [0x80] ++ List.replicate 14 0 ++
            encodeBitLen128BE 97)) =
            P.sha512 (sig.take 32 ++ P.compress edPt ++ m) := by
          rw [hWF.sha512_eq_ref, sha512Ref_of_length_97 P htail97]
        apply SepWP.end_seg (verifySig_tail_from_548_trap P A img absHooks hWF hH s4 fsp sigPtr retAddr
          (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5)) (s.readReg64
          (.gpr 22#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 25#5)) (s.readReg64
          (.gpr 26#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
          edPt m sig ((sig.take 32 ++ P.compress edPt) ++ m) (revWords64 sha512InitState) 0#64 97
          ((pkPtr ↦ₛ bytesToBv8 pk) ∗
           (slicesPtr ↦₆₄ msgPtr) ∗
           ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗
           (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
          hedPt hsig htail97 hst0 (Or.inl ⟨rfl,
          rfl⟩) hsha_eq hfsp_align hrun4 hpc4 hsp4 hx23_s4 hx29_s4)
          (Entails.of_eq (by ac_rfl))
        intro s5 P5 hP5 ⟨hrun5, hpc5, hsp5, hx0_5, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
          h29, hv5, htr5⟩
        exact ⟨Entails.trans hP5 (Entails.of_eq (by ac_rfl)), hrun5, hpc5, hsp5,
          hx0_5.trans hxed_eq, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1))),
          htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1)))⟩
      · rw [hm1569, show BitVec.ofNat 64 1569 = 1569#64 from rfl]
        apply SepWP.seq_seg (verifySig_seg2_1569_trap P A img absHooks hH s3 fsp slicesPtr msgPtr
          (sig.take 32 ++ P.compress edPt) m (revWords64 sha512InitState)
          (memRegion fsp 4 ∗
           ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
           ((fsp + 8#64) ↦₆₄ sigPtr) ∗
           memRegion (fsp + 16#64) 32 ∗
           memRegion (fsp + 48#64) 160 ∗
           memRegion (fsp + 208#64) 160 ∗
           ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
           ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
           memRegion (fsp + 768#64) 32 ∗
           memRegion (fsp + 800#64) 168 ∗
           memRegion (fsp + 968#64) 184 ∗
           ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
           ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
           1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
           ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
           1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
           ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
           1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
           ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
           1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
           ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
           1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
           (pkPtr ↦ₛ bytesToBv8 pk) ∗
           (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
          hpre64 hm1569 hst0 hfsp_align hrun3 hpc3 hsp3 hx20_s3 hx21_s3)
          (Entails.of_eq (by ac_rfl))
        intro s4 hpc4 hrun4 ⟨_, _, hsp4, hx23_4, hx29_4, hv4, htr4⟩
        have hx23_s4 : s4.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_4.trans hx23_s3
        have hx29_s4 : s4.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_4.trans hx29_s3
        have hblk0 : ((sig.take 32 ++ P.compress edPt) ++ m.take 64).length = 128 := by
          simp [hsig, hcapA, hm1569]
        have hblks11 : ((m.drop 64).take 1408).length = 1408 := by simp [hm1569]
        have htail97 : (m.drop 1472).length = 97 := by simp [hm1569]
        have hm_split : ((sig.take 32 ++ P.compress edPt) ++ m.take 64) ++ (m.drop 64).take 1408 ++
          m.drop 1472 =
            sig.take 32 ++ P.compress edPt ++ m := by
          have h1 : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
            rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
          rw [List.append_assoc, List.append_assoc ((sig.take 32 ++ P.compress edPt)), h1,
            List.take_append_drop]
        have hst12 : (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64
          sha512InitState) ((sig.take 32 ++ P.compress edPt) ++
          m.take 64)) ((m.drop 64).take 1408)).length = 64 :=
          sha512CompressOutBytes_length P _ _
        have hsha_eq : revWords64 (sha512CompressOutBytes P
            (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
            ((sig.take 32 ++ P.compress edPt) ++ m.take 64)) ((m.drop 64).take 1408))
            (m.drop 1472 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633)) =
            P.sha512 (sig.take 32 ++ P.compress edPt ++ m) := by
          rw [hWF.sha512_eq_ref, ← hm_split, sha512Ref_of_length_1633 P hblk0 hblks11 htail97]
        apply SepWP.end_seg (verifySig_tail_from_548_trap P A img absHooks hWF hH s4 fsp sigPtr retAddr
          (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5)) (s.readReg64
          (.gpr 22#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 25#5)) (s.readReg64
          (.gpr 26#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5))
          edPt m sig (m.drop 1472)
          (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
          ((sig.take 32 ++ P.compress edPt) ++ m.take 64)) ((m.drop 64).take 1408))
          12#64 1633
          ((pkPtr ↦ₛ bytesToBv8 pk) ∗
           (slicesPtr ↦₆₄ msgPtr) ∗
           ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗
           (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
          hedPt hsig htail97 hst12 (Or.inr ⟨rfl,
          rfl⟩) hsha_eq hfsp_align hrun4 hpc4 hsp4 hx23_s4 hx29_s4)
          (Entails.of_eq (by ac_rfl))
        intro s5 P5 hP5 ⟨hrun5, hpc5, hsp5, hx0_5, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
          h29, hv5, htr5⟩
        exact ⟨Entails.trans hP5 (Entails.of_eq (by ac_rfl)), hrun5, hpc5, hsp5,
          hx0_5.trans hxed_eq, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1))),
          htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1)))⟩
private theorem fnAddr_verifySignatureMultipart_eq_trap (img : Obj.Image) (absHooks : String → Option
    (State → State)) :
    (PP img.base absHooks).fnAddr verifySignatureMultipartSym =
      (PP img.base absHooks).fnAddr verifySignatureSym + 40#64 := by
  with_unfolding_all simp [trTrapProgAt]
theorem verifySignature_prologue_trap
    (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp pkPtr msgPtr msgLen sigPtr retAddr : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureSym)
    (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = msgLen)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureSym + 40#64)
      s
      (cells (fsp + 1248#64) 4 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1248#64) ↦₆₄ msgPtr) ∗
          ((fsp + 1256#64) ↦₆₄ msgLen) ∗
          ((fsp + 1264#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗
          ((fsp + 1272#64) ↦₆₄ retAddr) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureSym + 40#64 ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = pkPtr ∧
        sm.readReg64 (.gpr 1#5) = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 2#5) = 1#64 ∧
        sm.readReg64 (.gpr 3#5) = sigPtr ∧
        sm.readReg64 (.gpr 4#5) = 64#64 ∧
        sm.readReg64 (.gpr 30#5) = (PP img.base absHooks).fnAddr verifySignatureSym + 28#64 ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureSym = 0x3de30 :=
    libsignalSessionCode_fnOff_0x3de30
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    0) hfn (by decide) verifySignature_decode_0x3de30
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at f0
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    4) hfn (by decide) verifySignature_decode_0x3de34
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    8) hfn (by decide) verifySignature_decode_0x3de38
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    12) hfn (by decide) verifySignature_decode_0x3de3c
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    16) hfn (by decide) verifySignature_decode_0x3de40
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    20) hfn (by decide) verifySignature_decode_0x3de44
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    24) hfn (by decide) verifySignature_decode_0x3de48
  dsimp only [trTrapProgAt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureSym = entry
  examples_hide_fetches
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWP.exists_left fun _ => SepWP.exists_left fun _ => SepWP.exists_left fun _ =>
    SepWP.exists_left fun _ => ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), ?_⟩
  refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal⟩
theorem verifySignature_epilogue_trap
    (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp msgPtr msgLen x29_0 retAddr : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureSym + 28#64)
    (hsp : s.sp = fsp + 1248#64) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (((fsp + 1248#64) ↦₆₄ msgPtr) ∗
       ((fsp + 1256#64) ↦₆₄ msgLen) ∗
       ((fsp + 1264#64) ↦₆₄ x29_0) ∗
       ((fsp + 1272#64) ↦₆₄ retAddr) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureSym = 0x3de30 :=
    libsignalSessionCode_fnOff_0x3de30
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    28) hfn (by decide) verifySignature_decode_0x3de4c
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    32) hfn (by decide) verifySignature_decode_0x3de50
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    36) hfn (by decide) verifySignature_decode_0x3de54
  dsimp only [trTrapProgAt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureSym = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_left (stackAt_1280_merge fsp msgPtr msgLen x29_0 retAddr))
theorem verifySignature_sepWP_trap
    (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp pkPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes)
    (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32)
    (hm : m.length = 33 ∨ m.length = 1569)
    (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureSym)
    (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 m.length)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (pkPtr ↦ₛ bytesToBv8 pk) ∗
          (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = (if P.sigVerify pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_1280_split fsp)) (by sep_focus)
  apply SepWP.seq_seg_ro hro (verifySignature_prologue_trap img absHooks s fsp pkPtr msgPtr (BitVec.ofNat
    64 m.length) sigPtr retAddr
    ((pkPtr ↦ₛ bytesToBv8 pk) ∗
     (msgPtr ↦ₛ bytesToBv8 m) ∗
     (sigPtr ↦ₛ bytesToBv8 sig) ∗
     stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
     Frame)
    hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30)
    (Entails.of_eq (by ac_rfl))
  intro s1 hpc1 hrun1 hro1 ⟨_, _, hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx30_1,
    h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hv1, htr1⟩
  have hpc1_mp : s1.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym := by
    rw [fnAddr_verifySignatureMultipart_eq_trap, hpc1]
  apply SepWP.seq_seg (verifySignatureMultipart_sepWP_trap P A img absHooks himg hWF hH s1
    fsp pkPtr (fsp + 1248#64) msgPtr sigPtr ((PP img.base absHooks).fnAddr verifySignatureSym +
      28#64)
    pk m sig
    (((fsp + 1264#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗
     ((fsp + 1272#64) ↦₆₄ retAddr) ∗
     Frame)
    hro1 hpk hm hsig hfsp_align hrun1 hpc1_mp hsp1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx30_1)
    (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl))
  intro s2 hpc2 hrun2 ⟨_, _, hsp2, hx0_2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2,
    h27_2, h28_2, _, hv2, htr2⟩
  apply SepWP.end_seg (verifySignature_epilogue_trap img absHooks s2 fsp msgPtr (BitVec.ofNat 64
    m.length)
    (s.readReg64 (.gpr 29#5)) retAddr
    ((pkPtr ↦ₛ bytesToBv8 pk) ∗
     (msgPtr ↦ₛ bytesToBv8 m) ∗
     (sigPtr ↦ₛ bytesToBv8 sig) ∗
     Frame)
    hfsp_align hrun2 hpc2 hsp2)
    (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl))
  intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3,
    h27_3, h28_3, h29_3, hv3, htr3⟩
  rw [hWF.sigVerify_eq_xeddsaVerifyRef pk m sig]
  exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hrun3, hpc3, hsp3,
    hx0_3.trans hx0_2,
    h19_3.trans (h19_2.trans h19_1), h20_3.trans (h20_2.trans h20_1),
    h21_3.trans (h21_2.trans h21_1), h22_3.trans (h22_2.trans h22_1),
    h23_3.trans (h23_2.trans h23_1), h24_3.trans (h24_2.trans h24_1),
    h25_3.trans (h25_2.trans h25_1), h26_3.trans (h26_2.trans h26_1),
    h27_3.trans (h27_2.trans h27_1), h28_3.trans (h28_2.trans h28_1),
    h29_3, hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩
abbrev verifySignatureMultipart_base_ok_trap {C : Crypto} :=
  verifySignatureMultipart_sepWP_trap (C := C) 
abbrev verifySignature_base_ok_trap {C : Crypto} :=
  verifySignature_sepWP_trap (C := C) 
end WithProgramTrap

section WithProgram
variable {C : Crypto} {ctl : BitVec 64}
local notation "PP" b:arg absHooks:arg => tripleRatchetProgAt b C ctl absHooks

theorem verifySig_seg1a (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp pkPtr slicesPtr sigPtr retAddr : BitVec 64) (pk sig : Bytes) (Frame : SepProp)
    (hpk : pk.length = 32) (hsig : sig.length = 64) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym)
    (hsp : s.sp = fsp + 1248#64) (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr) (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr) (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks) ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64)
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ cells fsp 1 ∗ cells (fsp + 16#64) 4 ∗
       memRegion (fsp + 800#64) 168 ∗ cells (fsp + 1152#64) 12 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
          memRegion (fsp + 16#64) 32 ∗
          dalekMontToEdOutAt P (fsp + 800#64) pk ((sig.getD 63 0 &&& 0x80) >>> 7) ∗
          ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
          ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((fsp +
          1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
          ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((fsp +
          1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((fsp +
          1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((fsp +
          1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
          ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((fsp +
          1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = sigPtr ∧ sm.readReg64 (.gpr 20#5) = slicesPtr ∧
        sm.readReg64 (.gpr 21#5) = 1#64 ∧
        sm.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 ((bytesToBv8 sig).getD 63 0#8) ∧
        sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧ sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg1a_trap P A img absHooks hH s fsp pkPtr slicesPtr sigPtr retAddr pk sig Frame hpk hsig hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, _, htr⟩ => ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, htr⟩)

set_option maxHeartbeats 4000000 in
theorem verifySig_epilogue (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp retAddr res : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (Frame : SepProp) (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64)
    (hsp : s.sp = fsp) (hx0 : s.readReg64 (.gpr 0#5) = res) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (memRegion fsp 1152 ∗ ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ stackAt fsp pqxdhHookStack ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = res ∧ sm.readReg64 (.gpr 19#5) = x19_0 ∧
        sm.readReg64 (.gpr 20#5) = x20_0 ∧ sm.readReg64 (.gpr 21#5) = x21_0 ∧
        sm.readReg64 (.gpr 22#5) = x22_0 ∧ sm.readReg64 (.gpr 23#5) = x23_0 ∧
        sm.readReg64 (.gpr 24#5) = x24_0 ∧ sm.readReg64 (.gpr 25#5) = x25_0 ∧
        sm.readReg64 (.gpr 26#5) = x26_0 ∧ sm.readReg64 (.gpr 27#5) = x27_0 ∧
        sm.readReg64 (.gpr 28#5) = x28_0 ∧ sm.readReg64 (.gpr 29#5) = x29_0 ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_epilogue_trap img absHooks s fsp retAddr res x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 Frame hfsp_align hrun hpc hsp hx0).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, htr⟩)

set_option maxHeartbeats 4000000 in
theorem verifySig_epilogue_false (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (Frame : SepProp) (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64)
    (hsp : s.sp = fsp) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (memRegion fsp 1152 ∗ ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ stackAt fsp pqxdhHookStack ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = 0#64 ∧ sm.readReg64 (.gpr 19#5) = x19_0 ∧
        sm.readReg64 (.gpr 20#5) = x20_0 ∧ sm.readReg64 (.gpr 21#5) = x21_0 ∧
        sm.readReg64 (.gpr 22#5) = x22_0 ∧ sm.readReg64 (.gpr 23#5) = x23_0 ∧
        sm.readReg64 (.gpr 24#5) = x24_0 ∧ sm.readReg64 (.gpr 25#5) = x25_0 ∧
        sm.readReg64 (.gpr 26#5) = x26_0 ∧ sm.readReg64 (.gpr 27#5) = x27_0 ∧
        sm.readReg64 (.gpr 28#5) = x28_0 ∧ sm.readReg64 (.gpr 29#5) = x29_0 ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_epilogue_false_trap img absHooks s fsp retAddr x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 Frame hfsp_align hrun hpc hsp).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, htr⟩)

set_option maxHeartbeats 4000000 in
theorem verifySig_seg1a_none (P : Primitives) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (s : State) (fsp : BitVec 64)
    (pk : Bytes) (signBit : UInt8) (Frame : SepProp) (hmont : P.montToEd pk signBit = none)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64)
    (hsp : s.sp = fsp) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64)
      s
      (dalekMontToEdOutAt P (fsp + 800#64) pk signBit ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 800#64) 168 ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64 ∧ sm.sp = fsp ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg1a_none_trap P img absHooks s fsp pk signBit Frame hmont hfsp_align hrun hpc hsp).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, _, htr⟩ => ⟨hPm, h1, h2, h3, htr⟩)

set_option maxHeartbeats 8000000 in
theorem verifySig_seg1b (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks) (s : State) (fsp : BitVec 64)
    (pk edPt : Bytes) (signBit : UInt8) (Frame : SepProp)
    (hmont : P.montToEd pk signBit = some edPt) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 84#64)
    (hsp : s.sp = fsp) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64)
      s
      (cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗ memRegion (fsp + 368#64) 32 ∗
       dalekMontToEdOutAt P (fsp + 800#64) pk signBit ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
          ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗ memRegion (fsp + 800#64) 168 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg1b_trap P A img absHooks hWF hH s fsp pk edPt signBit Frame hmont hfsp_align hrun hpc hsp).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, htr⟩)

theorem verifySig_seg1c_invalid (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (sig : Bytes) (Frame : SepProp) (hinv : (sig.getD 63 0 &&& 0x60 == 0) = false)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64)
      s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1096#64 ∧ sm.sp = s.sp ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg1c_invalid_trap img absHooks s sig Frame hinv hrun hpc hx22).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, _, htr⟩ => ⟨hPm, h1, h2, h3, htr⟩)

theorem verifySig_seg1c (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp sigPtr : BitVec 64) (edPt sig : Bytes) (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (hedPt : edPt.length = 160) (hsig : sig.length = 64)
    (hvalid : (sig.getD 63 0 &&& 0x60 == 0) = true) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 232#64)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 (.gpr 19#5) = sigPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
      s
      (memRegion fsp 4 ∗ memRegion (fsp + 4#64) 4 ∗ cells (fsp + 8#64) 1 ∗
       ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
       memRegion (fsp + 400#64) 160 ∗ cells (fsp + 560#64) 8 ∗ memRegion (fsp + 687#64) 1 ∗
       cells (fsp + 688#64) 10 ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion fsp 4 ∗
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 208#64) 160 ∗
          ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32 ++ P.compress edPt)) ∗
          ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ sha512IVBytesLE) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg1c_trap P A img absHooks himg hWF hH s fsp sigPtr edPt sig Frame hro hedPt hsig hvalid hfsp_align hrun hpc hsp hx19 hx22).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, _, htr⟩ => ⟨hPm, h1, h2, h3, h4, h5, h6, h7, htr⟩)

private theorem verifySig_tail_from_548
    (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp sigPtr retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (edPt m sig tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp)
    (_hedPt : edPt.length = 160)
    (hsig : sig.length = 64)
    (htail97 : tail97.length = 97)
    (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hsha_eq : revWords64 (sha512CompressOutBytes P st
      (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)) =
        P.sha512 (sig.take 32 ++ P.compress edPt ++ m))
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64)
    (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (memRegion fsp 4 ∗
       ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗
       memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 48#64) 160 ∗
       memRegion (fsp + 208#64) 160 ∗
       ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗
       memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗
       ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗
       ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗
       memRegion (fsp + 768#64) 32 ∗
       memRegion (fsp + 800#64) 168 ∗
       memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt fsp pqxdhHookStack ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) =
          (let capA := P.compress edPt
           let minusCapA := P.edNeg edPt
           let capR := sig.take 32
           let sRaw := sig.drop 32
           let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
           let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
           if (capRCheck == capR) = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = x19_0 ∧
        sm.readReg64 (.gpr 20#5) = x20_0 ∧
        sm.readReg64 (.gpr 21#5) = x21_0 ∧
        sm.readReg64 (.gpr 22#5) = x22_0 ∧
        sm.readReg64 (.gpr 23#5) = x23_0 ∧
        sm.readReg64 (.gpr 24#5) = x24_0 ∧
        sm.readReg64 (.gpr 25#5) = x25_0 ∧
        sm.readReg64 (.gpr 26#5) = x26_0 ∧
        sm.readReg64 (.gpr 27#5) = x27_0 ∧
        sm.readReg64 (.gpr 28#5) = x28_0 ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_tail_from_548_trap P A img absHooks hWF hH s fsp sigPtr retAddr x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 edPt m sig tail97 st blkCnt L Frame _hedPt hsig htail97 hst hblkL hsha_eq hfsp_align hrun hpc hsp hx23 hx29).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, htr⟩)

theorem verifySignatureMultipart_sepWP
    (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp pkPtr slicesPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes)
    (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32)
    (hm : m.length = 33 ∨ m.length = 1569)
    (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym)
    (hsp : s.sp = fsp + 1248#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (pkPtr ↦ₛ bytesToBv8 pk) ∗
          (slicesPtr ↦₆₄ msgPtr) ∗
          ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
          (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = (if xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySignatureMultipart_sepWP_trap P A img absHooks himg hWF hH s fsp pkPtr slicesPtr msgPtr sigPtr retAddr pk m sig Frame hro hpk hm hsig hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, htr⟩)

private theorem fnAddr_verifySignatureMultipart_eq (img : Obj.Image) (absHooks : String → Option
    (State → State)) :
    (PP img.base absHooks).fnAddr verifySignatureMultipartSym =
      (PP img.base absHooks).fnAddr verifySignatureSym + 40#64 := by
  with_unfolding_all simp [tripleRatchetProgAt]

theorem verifySignature_prologue
    (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp pkPtr msgPtr msgLen sigPtr retAddr : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureSym)
    (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = msgLen)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureSym + 40#64)
      s
      (cells (fsp + 1248#64) 4 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1248#64) ↦₆₄ msgPtr) ∗
          ((fsp + 1256#64) ↦₆₄ msgLen) ∗
          ((fsp + 1264#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗
          ((fsp + 1272#64) ↦₆₄ retAddr) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureSym + 40#64 ∧
        sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) = pkPtr ∧
        sm.readReg64 (.gpr 1#5) = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 2#5) = 1#64 ∧
        sm.readReg64 (.gpr 3#5) = sigPtr ∧
        sm.readReg64 (.gpr 4#5) = 64#64 ∧
        sm.readReg64 (.gpr 30#5) = (PP img.base absHooks).fnAddr verifySignatureSym + 28#64 ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySignature_prologue_trap img absHooks s fsp pkPtr msgPtr msgLen sigPtr retAddr Frame hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, htr⟩)

theorem verifySignature_epilogue
    (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp msgPtr msgLen x29_0 retAddr : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureSym + 28#64)
    (hsp : s.sp = fsp + 1248#64) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      (((fsp + 1248#64) ↦₆₄ msgPtr) ∗
       ((fsp + 1256#64) ↦₆₄ msgLen) ∗
       ((fsp + 1264#64) ↦₆₄ x29_0) ∗
       ((fsp + 1272#64) ↦₆₄ retAddr) ∗
       stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySignature_epilogue_trap img absHooks s fsp msgPtr msgLen x29_0 retAddr Frame hfsp_align hrun hpc hsp).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, htr⟩)

theorem verifySignature_sepWP
    (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp pkPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes)
    (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32)
    (hm : m.length = 33 ∨ m.length = 1569)
    (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureSym)
    (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 m.length)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP (PP img.base absHooks)
      retAddr
      s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          (pkPtr ↦ₛ bytesToBv8 pk) ∗
          (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = retAddr ∧
        sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = (if P.sigVerify pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySignature_sepWP_trap P A img absHooks himg hWF hH s fsp pkPtr msgPtr sigPtr retAddr pk m sig Frame hro hpk hm hsig hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, htr⟩ =>
      ⟨hPm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, htr⟩)

abbrev verifySignatureMultipart_base_ok {C : Crypto} {ctl : BitVec 64} :=
  verifySignatureMultipart_sepWP (C := C) (ctl := ctl)
abbrev verifySignature_base_ok {C : Crypto} {ctl : BitVec 64} :=
  verifySignature_sepWP (C := C) (ctl := ctl)
end WithProgram
end CryptoVerification.E2E.Pqxdh.Shared
