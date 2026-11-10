/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedA
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignature
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.WPFrozen

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib CryptoVerification
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open SignalPqxdh

/-!
# Relocatable `VerifySignature` — Block `204` Segment 1, Epilogues, and Tail

Proves Segment 1 (`1a`, `1b`, `1c`), epilogues, and `verifySig_tail_from_548_placed` for unmutated
Block `204` (`verify_signature_for_multipart_message`) under `[LibsignalPlacement]`, decoupled from
Block `202` (`PublicKey::is_canonical`).

## Framing, Bit-Mask, and Frozen-Memory Helpers
-/

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
    (sigPtr ↦ₛ bytesToBv8 sig) =
      ((sigPtr ↦ₛ bytesToBv8 (sig.take 63)) ∗ ((sigPtr + 63#64) ↦₈ (bytesToBv8 sig).getD 63 0#8)) := by
  have hl63 : (bytesToBv8 (sig.take 63)).length = 63 := by simp [bytesToBv8, h]
  conv => lhs; rw [list_sig_split_63 h]
  rw [pointsToBytes_append, hl63]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

@[local simp, local wp_norm, local arm64_norm]
private theorem sig_getD63_ushiftRight7_eq_signBit (sig : Bytes) :
    (bytesToBv8 sig).getD 63 0#8 >>> 7 =
      BitVec.ofNat 8 (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) := by
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

private theorem memRegion168_of_cell_and_memRegion160_v (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ⊢ memRegion a 168 := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := pointsTo64_entails_memRegion a v
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 160) (b' := a + 8#64)
    rfl (by bv_omega) (by decide)]
  exact Entails.refl _

private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ⊢ memRegion a 168 := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := pointsTo64_entails_memRegion a v
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 :=
    pointsToBytes_entails_memRegion_n (a + 8#64) bs hlen
  refine Entails.trans (sepConj_mono h1 h2) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 160) (b' := a + 8#64)
    rfl (by bv_omega) (by decide)]
  exact Entails.refl _

private theorem exists_unpack64_of_length_160_eq {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
         ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
         ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
         ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ∗
         ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17) ∗ ((a + 144#64) ↦₆₄ w18) ∗ ((a + 152#64) ↦₆₄ w19)) := by
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

private theorem SepWP.of_sepWP_sha512IV_placed {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {pl : Obj.MultiPlacement}
    (hro : Obj.HoldsBytes s.mem (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (h : SepWP prog (roStop mid) s P
      (fun sm Pm =>
        Obj.HoldsBytes sm.mem (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro) →
          SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold roStop at h
  exact SepWP.seq_frozen (fun _ _ h0 hkf => holdsBytes_ro_of_keepsFrozen h0 hkf) hro h

private theorem sha512IV_cells_eq (a : BitVec 64) :
    ((a ↦₆₄ 0x6a09e667f3bcc908#64) ∗ ((a + 8#64) ↦₆₄ 0xbb67ae8584caa73b#64) ∗
     ((a + 16#64) ↦₆₄ 0x3c6ef372fe94f82b#64) ∗ ((a + 24#64) ↦₆₄ 0xa54ff53a5f1d36f1#64) ∗
     ((a + 32#64) ↦₆₄ 0x510e527fade682d1#64) ∗ ((a + 40#64) ↦₆₄ 0x9b05688c2b3e6c1f#64) ∗
     ((a + 48#64) ↦₆₄ 0x1f83d9abfb41bd6b#64) ∗ ((a + 56#64) ↦₆₄ 0x5be0cd19137e2179#64)) =
      (a ↦ₛ sha512IVBytesLE) := by
  rw [sha512IVBytesLE_eq_unpack64]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem verifySig_stackAt_1248_split (fsp : BitVec 64) :
    stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) =
      stackAt fsp pqxdhHookStack ∗ memRegion fsp 1152 ∗ cells (fsp + 1152#64) 12 := by
  rw [← stackAt_verifySig_merge fsp, memRegion_cells (fsp + 1152#64) 12 (by decide)]

theorem verifySig_memRegion_1152_seg1a_split (fsp : BitVec 64) :
    memRegion fsp 1152 = cells fsp 1 ∗ memRegion (fsp + 8#64) 8 ∗ cells (fsp + 16#64) 4 ∗
      memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 800#64) 168 ∗
      memRegion (fsp + 968#64) 184 := by
  rw [@ProofLib.memRegion_split' fsp (fsp + 8#64) 8 1144 1152 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 8#64) (fsp + 16#64) 8 1136 1144 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 16#64) (fsp + 48#64) 32 1104 1136 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 48#64) (fsp + 800#64) 752 352 1104 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 968#64) 168 184 352 rfl (by bv_omega) (by decide),
      memRegion_cells fsp 1 (by decide), memRegion_cells (fsp + 16#64) 4 (by decide)]

theorem verifySig_memRegion_1152_seg1a_merge (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗
      memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ⊢
      memRegion fsp 1152 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion fsp 0#64)) (Entails.of_eq ?_)
  rw [← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 968#64) 168 184 352 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 48#64) (fsp + 800#64) 752 352 1104 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 16#64) (fsp + 48#64) 32 1104 1136 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 8#64) (fsp + 16#64) 8 1136 1144 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' fsp (fsp + 8#64) 8 1144 1152 rfl (by bv_omega) (by decide)]

theorem verifySig_memRegion_752_seg1b_split (fsp : BitVec 64) :
    memRegion (fsp + 48#64) 752 = cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗
      memRegion (fsp + 368#64) 32 ∗ memRegion (fsp + 400#64) 400 := by
  rw [@ProofLib.memRegion_split' (fsp + 48#64) (fsp + 208#64) 160 592 752 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 208#64) (fsp + 368#64) 160 432 592 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 368#64) (fsp + 400#64) 32 400 432 rfl (by bv_omega) (by decide),
      memRegion_cells (fsp + 48#64) 20 (by decide), memRegion_cells (fsp + 208#64) 20 (by decide)]

theorem verifySig_memRegion_752_seg1b_merge (fsp : BitVec 64) {edPt capA : Bytes}
    (hed : edPt.length = 160) (hcapA : capA.length = 32) :
    memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
      ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗ memRegion (fsp + 400#64) 400 ⊢
      memRegion (fsp + 48#64) 752 := by
  have h1 : ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ⊢ memRegion (fsp + 208#64) 160 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hed])
  have h2 : ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ⊢ memRegion (fsp + 368#64) 32 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hcapA])
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) (Entails.of_eq ?_)
  rw [← @ProofLib.memRegion_split' (fsp + 368#64) (fsp + 400#64) 32 400 432 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 208#64) (fsp + 368#64) 160 432 592 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 48#64) (fsp + 208#64) 160 592 752 rfl (by bv_omega) (by decide)]

theorem verifySig_seg1b_to_seg1c_split (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 400#64) 400 ⊢
      memRegion fsp 4 ∗ memRegion (fsp + 4#64) 4 ∗ cells (fsp + 8#64) 1 ∗
      memRegion (fsp + 400#64) 160 ∗ cells (fsp + 560#64) 8 ∗ memRegion (fsp + 624#64) 63 ∗
      memRegion (fsp + 687#64) 1 ∗ cells (fsp + 688#64) 10 ∗ memRegion (fsp + 768#64) 32 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion fsp 0#64)) (Entails.of_eq ?_)
  rw [@ProofLib.memRegion_split' fsp (fsp + 4#64) 4 4 8 rfl (by bv_omega) (by decide),
      memRegion_cells (fsp + 8#64) 1 (by decide),
      @ProofLib.memRegion_split' (fsp + 400#64) (fsp + 560#64) 160 240 400 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 560#64) (fsp + 624#64) 64 176 240 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 624#64) (fsp + 687#64) 63 113 176 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 687#64) (fsp + 688#64) 1 112 113 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 688#64) (fsp + 768#64) 80 32 112 rfl (by bv_omega) (by decide),
      memRegion_cells (fsp + 560#64) 8 (by decide), memRegion_cells (fsp + 688#64) 10 (by decide)]
  simp only [sepConj_assoc]

private theorem memRegion_800_seg3a_split (fsp : BitVec 64) :
    memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 =
      cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
      memRegion (fsp + 1136#64) 16 := by
  rw [← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 968#64) 168 184 352 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 928#64) 128 224 352 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 928#64) (fsp + 1008#64) 80 144 224 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 1008#64) (fsp + 1136#64) 128 16 144 rfl (by bv_omega) (by decide),
      memRegion_cells (fsp + 800#64) 16 (by decide),
      memRegion_cells (fsp + 928#64) 10 (by decide),
      memRegion_cells (fsp + 1008#64) 16 (by decide)]

private theorem seg3a_to_seg3b_split (fsp : BitVec 64) :
    cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 =
      cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 960#64) 48 ∗
      memRegion (fsp + 1008#64) 32 ∗ memRegion (fsp + 1040#64) 96 := by
  rw [← memRegion_cells (fsp + 800#64) 16 (by decide),
      ← memRegion_cells (fsp + 928#64) 10 (by decide),
      ← memRegion_cells (fsp + 1008#64) 16 (by decide),
      ← @ProofLib.memRegion_split' (fsp + 928#64) (fsp + 1008#64) 80 128 208 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 928#64) 128 208 336 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 832#64) 32 304 336 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 832#64) (fsp + 960#64) 128 176 304 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 960#64) (fsp + 1008#64) 48 128 176 rfl (by bv_omega) (by decide),
      @ProofLib.memRegion_split' (fsp + 1008#64) (fsp + 1040#64) 32 96 128 rfl (by bv_omega) (by decide),
      memRegion_cells (fsp + 800#64) 4 (by decide)]

private theorem seg3b_to_epilogue_merge (fsp : BitVec 64)
    (v4 : BitVec 32) (v8 : BitVec 64) {capA minusCapA hScalar : Bytes}
    (hcapA : capA.length = 32) (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32) :
    memRegion fsp 4 ∗ ((fsp + 4#64) ↦₃₂ v4) ∗ ((fsp + 8#64) ↦₆₄ v8) ∗
      memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
      ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗ ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗
      cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
      ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗ memRegion (fsp + 800#64) 160 ∗
      memRegion (fsp + 960#64) 48 ∗ memRegion (fsp + 1008#64) 32 ∗
      memRegion (fsp + 1040#64) 96 ∗ memRegion (fsp + 1136#64) 16 ⊢ memRegion fsp 1152 := by
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
  rw [← @ProofLib.memRegion_split' (fsp + 1040#64) (fsp + 1136#64) 96 16 112 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 1008#64) (fsp + 1040#64) 32 112 144 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 960#64) (fsp + 1008#64) 48 144 192 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 960#64) 160 192 352 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 768#64) (fsp + 800#64) 32 352 384 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 688#64) (fsp + 768#64) 80 384 464 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 560#64) (fsp + 688#64) 128 464 592 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 400#64) (fsp + 560#64) 160 592 752 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 368#64) (fsp + 400#64) 32 752 784 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 208#64) (fsp + 368#64) 160 784 944 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 48#64) (fsp + 208#64) 160 944 1104 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 16#64) (fsp + 48#64) 32 1104 1136 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 8#64) (fsp + 16#64) 8 1136 1144 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' (fsp + 4#64) (fsp + 8#64) 4 1144 1148 rfl (by bv_omega) (by decide),
      ← @ProofLib.memRegion_split' fsp (fsp + 4#64) 4 1148 1152 rfl (by bv_omega) (by decide)]

theorem verifySig_seq_seg {prog : Program} {mid target : BitVec 64} {s : State}
    {P P' P_mid : SepProp} {Q_regs : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P' (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_regs sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.weaken_pre hP <| SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

theorem verifySig_end_seg {prog : Program} {target : BitVec 64} {s : State}
    {P P' P_out : SepProp} {Q_regs : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog target s P' (fun sm Pm => (Pm ⊢ P_out) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (hpost : ∀ sm Pm, (Pm ⊢ P_out) → Q_regs sm → post sm Pm) :
    SepWP prog target s P post :=
  SepWP.weaken_pre hP <| SepWP.mono h1 fun sm Pm _ _ ⟨hent, hQ⟩ => hpost sm Pm hent hQ

theorem verifySig_seq_seg_lscl {prog : Program} {mid target : BitVec 64} {s : State}
    {P P' P_mid : SepProp} {Q_regs : State → Prop} {post : State → SepProp → Prop}
    {pl : Obj.MultiPlacement}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P' (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (h2 : ∀ (sm : State), sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Q_regs sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq_frozen (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl <|
    SepWP.weaken_pre hP <| SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hQ⟩ hclm =>
      SepWP.weaken_pre hent (h2 sm hpc hrun hclm hQ)

theorem verifySig_seq_seg_lscro {prog : Program} {mid target : BitVec 64} {s : State}
    {P P' P_mid : SepProp} {Q_regs : State → Prop} {post : State → SepProp → Prop}
    {pl : Obj.MultiPlacement}
    (hcro : LibsignalCodeLoaded pl s.mem ∧
      Obj.HoldsBytes s.mem (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (h1 : SepWP prog mid s P' (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (hP : P ⊢ P')
    (h2 : ∀ (sm : State), sm.pc = mid → sm.status = .Running →
      (LibsignalCodeLoaded pl sm.mem ∧
        Obj.HoldsBytes sm.mem (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro)) →
      Q_regs sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq_frozen
    (Φ := fun m => LibsignalCodeLoaded pl m ∧
      Obj.HoldsBytes m (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, holdsBytes_ro_of_keepsFrozen hr hkf⟩) hcro <|
    SepWP.weaken_pre hP <| SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hQ⟩ hcrom =>
      SepWP.weaken_pre hent (h2 sm hpc hrun hcrom hQ)

theorem verifySig_xeddsaVerifyRef_of_montToEd_none (P : Primitives) {pk m sig : Bytes}
    (hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) = none) :
    xeddsaVerifyRef P pk m sig = false := by
  unfold xeddsaVerifyRef
  dsimp only
  rw [hmont]
  split <;> rfl

theorem verifySig_xeddsaVerifyRef_of_60_false (P : Primitives) {pk m sig : Bytes}
    (h60 : (sig.getD 63 0 &&& 0x60 == 0) = false) :
    xeddsaVerifyRef P pk m sig = false := by
  unfold xeddsaVerifyRef
  rw [h60, Bool.and_false]
  rfl

theorem verifySig_xeddsaVerifyRef_of_some (P : Primitives) (m : Bytes) {pk sig edPt : Bytes}
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

/-! ## Block `204` Segment 1 and Epilogues -/

set_option maxHeartbeats 1600000 in
/-- Segment 1a (`+0 .. +84`, prologue & `MontgomeryPoint::to_edwards`) of Block `204`
    under `[LibsignalPlacement]`. -/
theorem verifySig_seg1a_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks' P H)
    (s : State) (fsp pkPtr slicesPtr sigPtr retAddr : BitVec 64) (pk sig : Bytes) (Frame : SepProp)
    (hpk : pk.length = 32) (hsig : sig.length = 64) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base)
    (hsp : s.sp = fsp + 1248#64) (hx0 : s.readReg64 (.gpr 0#5) = pkPtr)
    (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr) (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr) (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 84#64) s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ cells fsp 1 ∗ cells (fsp + 16#64) 4 ∗
       memRegion (fsp + 800#64) 168 ∗ cells (fsp + 1152#64) 12 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
          memRegion (fsp + 16#64) 32 ∗
          dalekMontToEdOutAt P (fsp + 800#64) pk ((sig.getD 63 0 &&& 0x80) >>> 7) ∗
          ((fsp + 1152#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
          ((fsp + 1168#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
          ((fsp + 1176#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
          ((fsp + 1184#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
          ((fsp + 1192#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((fsp + 1200#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
          ((fsp + 1208#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          ((fsp + 1216#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
          ((fsp + 1224#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
          ((fsp + 1232#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
          ((fsp + 1240#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 84#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = sigPtr ∧ sm.readReg64 (.gpr 20#5) = slicesPtr ∧
        sm.readReg64 (.gpr 21#5) = 1#64 ∧
        sm.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 ((bytesToBv8 sig).getD 63 0#8) ∧
        sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmont := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.montToEd
    (by set_option maxRecDepth 20000 in decide)
  clear hH
  have hpk_bv : (bytesToBv8 pk).length = 32 := by simp [bytesToBv8, hpk]
  obtain ⟨p0, p1, p2, p3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hpk_bv
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_focus_63 sigPtr hsig)) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hpk_cells pkPtr)) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_focus_63 sigPtr hsig).symm)
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hpk_cells pkPtr).symm) (by sep_frame)
  have hpk_sp16 := (hpk_cells (fsp + 16#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk_sp16
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hpk_sp16) (by sep_frame)
  wp_call hmont ⟨pk, (sig.getD 63 0 &&& 0x80) >>> 7, fsp + 16#64, fsp + 800#64⟩
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (congrArg (dalekMontToEdOutAt P (fsp + 800#64) pk)
      (signBit_shr7_and_one (sig.getD 63 0))))
    (by sep_frame)
  have hm32_16 := pointsToBytes_entails_memRegion_n (fsp + 16#64) _ hpk_bv
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_16) (by sep_frame)
  wp_simp_pre_fast [hsp_sf]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 1600000 in
theorem verifySig_epilogue_placed [LibsignalPlacement]
    (H : LibsignalHooks) (s : State) (fsp retAddr res : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (Frame : SepProp) (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 1100#64)
    (hsp : s.sp = fsp) (hx0 : s.readReg64 (.gpr 0#5) = res) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) retAddr s
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
  wp_steps
  have hm12 := cells_12_merge (fsp + 1152#64)
    x29_0 retAddr x28_0 x27_0 x26_0 x25_0 x24_0 x23_0 x22_0 x21_0 x20_0 x19_0
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm12
  apply ProofLib.SepWP.replace_pre (hPQ := hm12) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_verifySig_merge fsp))
    (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

theorem verifySig_epilogue_false_placed [LibsignalPlacement]
    (H : LibsignalHooks) (s : State) (fsp retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (Frame : SepProp) (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 1096#64) (hsp : s.sp = fsp) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) retAddr s
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
  wp_step
  exact verifySig_epilogue_placed H _ fsp retAddr 0#64
    x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 Frame
    hfsp_align (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)

theorem verifySig_seg1a_none_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (s : State) (fsp : BitVec 64)
    (pk : Bytes) (signBit : UInt8) (Frame : SepProp) (hmont : P.montToEd pk signBit = none)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 84#64) (hsp : s.sp = fsp) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 1096#64) s
      (dalekMontToEdOutAt P (fsp + 800#64) pk signBit ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 800#64) 168 ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 1096#64 ∧ sm.sp = fsp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (dalekMontToEdOutAt_none P pk signBit hmont (fsp + 800#64)))
    (by sep_frame)
  wp_steps
  have hm168 := memRegion168_of_cell_and_memRegion160_v (fsp + 800#64) 0#64
  apply ProofLib.SepWP.replace_pre (hPQ := hm168) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
/-- Segment 1b (`+84 .. +232`, `to_edwards = some edPt` & `EdwardsPoint::compress`) of Block `204`. -/
theorem verifySig_seg1b_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H) (s : State) (fsp : BitVec 64)
    (pk edPt : Bytes) (signBit : UInt8) (Frame : SepProp)
    (hmont : P.montToEd pk signBit = some edPt) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 84#64) (hsp : s.sp = fsp) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 232#64) s
      (cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗ memRegion (fsp + 368#64) 32 ∗
       dalekMontToEdOutAt P (fsp + 800#64) pk signBit ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗
          ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗ memRegion (fsp + 800#64) 168 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 232#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hcomp := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.compress
  clear hH
  have hed_len : edPt.length = 160 := hWF.montToEd_len pk signBit edPt hmont
  have hed_bv_len : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hed_len]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
    hed_cells⟩ := exists_unpack64_of_length_160_eq hed_bv_len
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (dalekMontToEdOutAt_some P pk edPt signBit hmont hed_len (fsp + 800#64)))
    (by sep_frame)
  have hed_808 := hed_cells (fsp + 800#64 + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_808
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_808) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_808.symm) (by sep_frame)
  have hm168 := memRegion168_of_cell_and_bytes160 (fsp + 800#64) 1#64 hed_bv_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm168
  apply ProofLib.SepWP.replace_pre (hPQ := hm168) (by sep_frame)
  have hed_48 := (hed_cells (fsp + 48#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_48
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_48) (by sep_frame)
  have hed_208 := (hed_cells (fsp + 208#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_208
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_208) (by sep_frame)
  wp_call hcomp ⟨fsp + 48#64, edPt, fsp + 368#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.compress_len _), hsp, hsp_sf]
  have hm160_48 := pointsToBytes_entails_memRegion_n (fsp + 48#64) _ hed_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_48) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

/-- Segment 1c invalid-bits branch (`+232 .. +1096`, `sig[63] & 0x60 != 0`) of Block `204`. -/
theorem verifySig_seg1c_invalid_placed [LibsignalPlacement]
    (H : LibsignalHooks) (s : State) (sig : Bytes) (Frame : SepProp)
    (hinv : (sig.getD 63 0 &&& 0x60 == 0) = false) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 232#64)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 1096#64) s Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 1096#64 ∧ sm.sp = s.sp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  wp_steps
  rw [uint8_and7f_ule32_of_and60_eq_false (sig.getD 63 0) hinv]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨Entails.refl _, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
/-- Segment 1c valid branch (`+232 .. +320`, `EdwardsPoint::neg` & `.rodata` SHA-512 IV init)
    of Block `204` under `[LibsignalPlacement]`. -/
theorem verifySig_seg1c_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H) (s : State) (fsp sigPtr : BitVec 64)
    (edPt sig : Bytes) (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (lsmpl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (hedPt : edPt.length = 160) (hsig : sig.length = 64)
    (hvalid : (sig.getD 63 0 &&& 0x60 == 0) = true) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 232#64)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 (.gpr 19#5) = sigPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 320#64) s
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
        sm.pc = (blkPl_204).base + 320#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hedneg := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.edNeg
    (by set_option maxRecDepth 20000 in decide)
  clear hH
  have hsig32_bv : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  obtain ⟨r0, r1, r2, r3, _, hsig32_cells⟩ := exists_unpack64_of_length_32 hsig32_bv
  have hcapA_bv : (bytesToBv8 (P.compress edPt)).length = 32 := by
    simp [bytesToBv8, hWF.compress_len]
  obtain ⟨a0, a1, a2, a3, _, hcapA_cells⟩ := exists_unpack64_of_length_32 hcapA_bv
  rw [ProofLib.memRegion_four (fsp + 4#64), ProofLib.memRegion_one (fsp + 687#64)]
  cells_pre_unfold_fast
  wp_extract_exists
  apply SepWP.of_sepWP_sha512IV_placed hro (mid := (blkPl_204).base + 272#64)
  wp_step
  wp_step
  wp_step
  rw [uint8_and7f_ule32_of_and60_eq_true (sig.getD 63 0) hvalid]
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_steps
  wp_call hedneg ⟨fsp + 208#64, edPt, fsp + 400#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.edNeg_len _), truncate32_and7f_eq, hsp, hsp_sf]
  apply blkPC_204_pairStep_0x104 (blkPl_204).base H rfl (by wp_norm_goal) (by wp_norm_goal)
  wp_steps
  apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs)
  intro hro1
  apply SepWP.of_sepWP_sha512IV_placed hro1 (mid := (blkPl_204).base + 288#64)
  wp_step_ldp_ro (sha512IV_placed_quad0 hro1)
  wp_steps
  apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs)
  intro hro2
  wp_step_ldp_ro (sha512IV_placed_quad1 hro2)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig32_cells sigPtr)) (by sep_frame)
  have hcapA_368 := hcapA_cells (fsp + 368#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcapA_368
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_368) (by sep_frame)
  wp_steps
  have hsha_688 := sha512IV_cells_eq (fsp + 688#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsha_688
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsha_688) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig32_cells sigPtr).symm) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig).symm)
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_368.symm) (by sep_frame)
  have hsig_560 := (hsig32_cells (fsp + 560#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsig_560
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsig_560) (by sep_frame)
  have hcapA_592 := (hcapA_cells (fsp + 592#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcapA_592
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_592) (by sep_frame)
  have hmerge_560 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((fsp + 592#64) ↦ₛ bytesToBv8 (P.compress edPt)) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32 ++ P.compress edPt)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hsig32_bv, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge_560) (by sep_frame)
  have hedPt_bv : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hedPt]
  have hm160_208 := pointsToBytes_entails_memRegion_n (fsp + 208#64) _ hedPt_bv
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_208) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal⟩

/-! ## Block `204` Tail (`+548 .. retAddr`) -/

set_option maxHeartbeats 1600000 in
/-- Tail segment (`+548 .. retAddr`) of Block `204` (`verify_signature_for_multipart_message`)
    under `[LibsignalPlacement]`, sequencing `verifySig_seg3a_placed`, `verifySig_seg3b_placed`,
    and `verifySig_epilogue_placed`. -/
theorem verifySig_tail_from_548_placed [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks' P H) (s : State) (fsp sigPtr retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (edPt m sig tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (_hedPt : edPt.length = 160) (hsig : sig.length = 64) (htail97 : tail97.length = 97)
    (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hsha_eq : revWords64 (sha512CompressOutBytes P st
      (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)) =
        P.sha512 (sig.take 32 ++ P.compress edPt ++ m))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 548#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) retAddr s
      (memRegion fsp 4 ∗
       ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
       ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 (P.edNeg edPt)) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗
       ((fsp + 752#64) ↦₆₄ blkCnt) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗
       memRegion (fsp + 768#64) 32 ∗ memRegion (fsp + 800#64) 168 ∗
       memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
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
        sm.readReg64 (.gpr 19#5) = x19_0 ∧ sm.readReg64 (.gpr 20#5) = x20_0 ∧
        sm.readReg64 (.gpr 21#5) = x21_0 ∧ sm.readReg64 (.gpr 22#5) = x22_0 ∧
        sm.readReg64 (.gpr 23#5) = x23_0 ∧ sm.readReg64 (.gpr 24#5) = x24_0 ∧
        sm.readReg64 (.gpr 25#5) = x25_0 ∧ sm.readReg64 (.gpr 26#5) = x26_0 ∧
        sm.readReg64 (.gpr 27#5) = x27_0 ∧ sm.readReg64 (.gpr 28#5) = x28_0 ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (memRegion_800_seg3a_split fsp))
    (by sep_frame)
  apply verifySig_seq_seg_lscl hcl (verifySig_seg3a_placed P H hH s fsp tail97 st blkCnt L
    (memRegion fsp 4 ∗
     ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
     ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗
     memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
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
  intro s1 hpc1 hrun1 hcl1 ⟨_, _, hsp1, hx23_1, hx29_1, hv1, htr1⟩
  rw [hsha_eq, fitBv8_of_length_eq (hWF.scalarFromWide_len _)]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (seg3a_to_seg3b_split fsp)) (by sep_frame)
  have hnegA : (P.edNeg edPt).length = 160 := hWF.edNeg_len edPt
  have hh : (P.scalarFromWide (P.sha512 (sig.take 32 ++ P.compress edPt ++ m))).length = 32 :=
    hWF.scalarFromWide_len _
  apply verifySig_seq_seg (verifySig_seg3b_placed P H hWF hH s1 fsp sigPtr
    sig (P.edNeg edPt) (P.scalarFromWide (P.sha512 (sig.take 32 ++ P.compress edPt ++ m)))
    (memRegion fsp 4 ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗
     memRegion (fsp + 208#64) 160 ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 (P.compress edPt)) ∗
     cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗ memRegion (fsp + 960#64) 48 ∗
     memRegion (fsp + 1040#64) 96 ∗ memRegion (fsp + 1136#64) 16 ∗
     ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
     ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
     ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
     ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
     ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
     ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ Frame)
    hcl1 hsig hnegA hh hfsp_align hrun1 hpc1 hsp1 hx23_1 hx29_1)
    (Entails.of_eq (by ac_rfl))
  intro s2 hpc2 hrun2 ⟨_, _, hsp2, hx0_2, hv2, htr2⟩
  have hcapA : (P.compress edPt).length = 32 := hWF.compress_len edPt
  apply ProofLib.SepWP.replace_pre
    (hPQ := seg3b_to_epilogue_merge fsp
      (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32) sigPtr hcapA hnegA hh)
    (by sep_frame)
  apply verifySig_end_seg (verifySig_epilogue_placed H s2 fsp retAddr (s2.readReg64 (.gpr 0#5))
    x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
    ((sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
    hfsp_align hrun2 hpc2 hsp2 rfl)
    (Entails.of_eq (by ac_rfl))
  intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
    hv3, htr3⟩
  exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hrun3, hpc3, hsp3,
    hx0_3.trans hx0_2, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
    hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩

end CryptoVerification.E2E.Pqxdh.Shared
