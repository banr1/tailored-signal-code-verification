/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewModel
import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep

/-!
# PQXDH Handshake `acceptKeys` Bridges

Connects an accepting `SignalPqxdh.Model.acceptKeys` evaluation under `ModelAgree` and
`ExternContractsHoldCli` to X25519 base-key canonicality, non-low-order and torsion-free guards,
and byte-level `TR.pqxdhKdfBytes` key derivation.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF PreKeyFields pubBytes secretBytes kyberDecapsBytes)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli ModelAgree)
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.Cli

/-! ## Handshake Guards and Base-Key Validity -/

private theorem option_bind_guard (c : Prop) [Decidable c] {α : Type} (f : Unit → Option α) :
    Option.bind (_root_.guard c) f = if c then f () else none := by
  by_cases hc : c <;> simp [_root_.guard, Pure.pure, Alternative.failure, Option.bind, hc]

private theorem ite_none_eq_some_iff {c : Prop} [Decidable c] {α : Type} {x : Option α} {v : α} :
    (if c then x else none) = some v ↔ c ∧ x = some v := by
  by_cases hc : c <;> simp [hc]

theorem rpkNew_acceptKeys_some_guards {P : SignalPqxdh.Primitives}
    {inp : SignalPqxdh.AcceptKeysInput} {dk : SignalPqxdh.DRKey}
    (hacc : SignalPqxdh.Model.acceptKeys P inp = some dk) :
    P.isCanonical inp.hdr.ekAPk = true ∧
      P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0 := by
  unfold SignalPqxdh.Model.acceptKeys at hacc
  simp only [bind, option_bind_guard, ite_none_eq_some_iff] at hacc
  rcases hacc with ⟨_, _, _, _, hcanon, _, hdh2, _⟩
  exact ⟨hcanon, bne_iff_ne.mp hdh2⟩

/-- Base-key length, `< p25519` range, non-low-order, and torsion-freeness guarantees from an
accepting `SignalPqxdh.Model.acceptKeys` call. -/
theorem rpkNew_acceptKeys_baseKey_ok
    {interp : ExternInterpretation} {P : PEParams} {X : UnreachedPqxdhPrimitives} {r : ProtocolSetup}
    (hhooks : ModelAgree interp P)
    (hExt : ExternContractsHoldCli interp)
    (hwf : ProtocolSetupWF r)
    {inp : SignalPqxdh.AcceptKeysInput} {dk : SignalPqxdh.DRKey}
    {p : PreKeyFields} {bk32 : HwBytes}
    (hbk_len : bk32.length = 32)
    (hbk_take : p.baseKey.take 33 = 5#8 :: bk32)
    (hdr_ek : inp.hdr.ekAPk = toU8 bk32)
    (hdh2_eq : ofU8 ((modelPrims X P).x25519 inp.ikBSk inp.hdr.ekAPk) =
      TR.dhAgreeBytes interp (secretBytes r 1) bk32)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X P) inp = some dk) :
    ((p.baseKey.take 33).drop 1).length = 32 ∧
      DY.X25519.leValue (((p.baseKey.take 33).drop 1).map BitVec.toNat) < DY.X25519.p25519 ∧
      DY.X25519.isLowOrderKey (((p.baseKey.take 33).drop 1).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interp ((p.baseKey.take 33).drop 1) := by
  obtain ⟨hcanon, hdh2_ne⟩ := rpkNew_acceptKeys_some_guards hacc
  rw [hbk_take]
  dsimp only [List.drop]
  let bkV : List.Vector (BitVec 8) 32 := ⟨bk32, hbk_len⟩
  have hcanon_vec : (modelPrims X P).isCanonical (vecU8 bkV) = true := by
    change (modelPrims X P).isCanonical (toU8 bk32) = true
    rw [← hdr_ek]
    exact hcanon
  obtain ⟨hlt, htf⟩ := isCanonical_modelPrims_inv hhooks X bkV hcanon_vec
  have hsk1_len : (secretBytes r 1).length = 32 := (secretBytes_length_bob hwf).2.1
  have hclamp_len : (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 1)).length = 32 := by
    simp [DY.Libsignal.TripleRatchet.Refinement.clamp, hsk1_len]
  have hlow : DY.X25519.isLowOrderKey (bk32.map BitVec.toNat) = false := by
    cases hl : DY.X25519.isLowOrderKey (bk32.map BitVec.toNat)
    · rfl
    · exfalso
      have hz := (hExt.1.x25519_agreement_zero_iff_low_order
        (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 1)) bk32 hclamp_len hbk_len).mpr hl
      have hdh2_zero : ofU8 ((modelPrims X P).x25519 inp.ikBSk inp.hdr.ekAPk) =
          List.replicate 32 0#8 := by
        rw [hdh2_eq]
        simpa [TR.dhAgreeBytes] using hz
      have hdh2_u8 : (modelPrims X P).x25519 inp.ikBSk inp.hdr.ekAPk =
          List.replicate 32 0 := by
        have h := congrArg toU8 hdh2_zero
        rw [toU8_ofU8_id] at h
        simpa [toU8] using h
      exact hdh2_ne hdh2_u8
  exact ⟨hbk_len, hlt, hlow, htf⟩

theorem rpkNew_acceptKeys_baseKey_ok_of_idPriv
    {interp : ExternInterpretation} {P : PEParams} {X : UnreachedPqxdhPrimitives} {r : ProtocolSetup}
    (hhooks : ModelAgree interp P)
    (hExt : ExternContractsHoldCli interp)
    (hwf : ProtocolSetupWF r)
    {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {dk : SignalPqxdh.DRKey} {p : PreKeyFields}
    (hid : me.idPriv = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 1))
    (hbk_take : p.baseKey.take 33 = djbKey m.baseKey)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X P)
      (acceptInput P me k m) = some dk) :
    ((p.baseKey.take 33).drop 1).length = 32 ∧
      DY.X25519.leValue (((p.baseKey.take 33).drop 1).map BitVec.toNat) < DY.X25519.p25519 ∧
      DY.X25519.isLowOrderKey (((p.baseKey.take 33).drop 1).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interp ((p.baseKey.take 33).drop 1) := by
  have hsk1_len : (secretBytes r 1).length = 32 := (secretBytes_length_bob hwf).2.1
  have hdh2 : ofU8 ((modelPrims X P).x25519
      (acceptInput P me k m).ikBSk (acceptInput P me k m).hdr.ekAPk) =
      TR.dhAgreeBytes interp (secretBytes r 1) m.baseKey.toList := by
    change ofU8 ((modelPrims X P).x25519
      (vecU8 (keyPairOf P.C me.idPriv).privateKey.bytes) (vecU8 m.baseKey)) = _
    rw [hid]
    exact x25519_modelPrims_keyPairOf_bytesToVec hhooks X hsk1_len m.baseKey
  exact rpkNew_acceptKeys_baseKey_ok hhooks hExt hwf m.baseKey.toList_length hbk_take rfl hdh2 hacc

/-! ## SHA-256, HMAC, and HKDF Key Derivation Equivalence -/

private theorem ofU8_append_rpnc579 (xs ys : List UInt8) :
    ofU8 (xs ++ ys) = ofU8 xs ++ ofU8 ys := by
  simp [ofU8]

private theorem ofU8_replicate_rpnc579 (n : Nat) (b : UInt8) :
    ofU8 (List.replicate n b) = List.replicate n b.toBitVec := by
  simp [ofU8]

private theorem ofU8_length_rpnc579 (xs : List UInt8) :
    (ofU8 xs).length = xs.length := by
  simp [ofU8]

private theorem fitBytesRef_of_length_eq_local {n : Nat} {bs : List UInt8} (h : bs.length = n) :
    SignalPqxdh.fitBytesRef n bs = bs := by
  subst h
  unfold SignalPqxdh.fitBytesRef
  rw [Nat.sub_self, List.replicate_zero, List.append_nil, List.take_length]

private theorem sha256Ref_length_local (P : SignalPqxdh.Primitives) (msg : List UInt8) :
    (SignalPqxdh.sha256Ref P msg).length = 32 :=
  SignalPqxdh.fitBytesRef_length 32 _

private theorem beWord32_toBEBytes4_rpnc579 (w : BitVec 32) :
    beWord 32 (HMAC.toBEBytes 4 w) 0 = w := by
  ext i hi
  change (((((0#32 <<< 8 ||| (w.extractLsb' 24 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 16 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 8 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 0 8).zeroExtend 32))[i] = w[i]
  by_cases h8 : i < 8
  · simp [h8, hi, BitVec.getLsbD_eq_getElem]
  · by_cases h16 : i < 16
    · have h1 : 8 ≤ i := by omega
      have h2 : i - 8 < 8 := by omega
      have h5 : 8 + (i - 8) = i := by omega
      simp [h8, h1, h2, h5, hi, BitVec.getLsbD_eq_getElem]
    · by_cases h24 : i < 24
      · have h1 : 8 ≤ i := by omega
        have h2 : ¬ (i - 8 < 8) := by omega
        have h3 : 8 ≤ i - 8 := by omega
        have h4 : i - 8 - 8 < 8 := by omega
        have h6 : 16 + (i - 8 - 8) = i := by omega
        simp [h8, h1, h2, h3, h4, h6, hi, BitVec.getLsbD_eq_getElem]
      · have h1 : 8 ≤ i := by omega
        have h2 : ¬ (i - 8 < 8) := by omega
        have h3 : 8 ≤ i - 8 := by omega
        have h4 : ¬ (i - 8 - 8 < 8) := by omega
        have h5 : 8 ≤ i - 8 - 8 := by omega
        have h6 : i - 8 - 8 - 8 < 8 := by omega
        have h9 : 24 + (i - 8 - 8 - 8) = i := by omega
        simp [h8, h1, h2, h3, h4, h5, h6, h9, hi, BitVec.getLsbD_eq_getElem]

private theorem sha256StateBytes_length_rpnc579 : ∀ h : HMAC.ShaState, (sha256StateBytes h).length = 32
  | ⟨[_w0, _w1, _w2, _w3, _w4, _w5, _w6, _w7], _⟩ => rfl

private theorem fitBytesRef_32_sha256StateBytes (h : HMAC.ShaState) :
    SignalPqxdh.fitBytesRef 32 (sha256StateBytes h) = sha256StateBytes h :=
  fitBytesRef_of_length_eq_local (sha256StateBytes_length_rpnc579 h)

private theorem sha256StateOf_sha256StateBytes_rpnc579 : ∀ h : HMAC.ShaState,
    sha256StateOf (sha256StateBytes h) = h
  | ⟨[w0, w1, w2, w3, w4, w5, w6, w7], _⟩ => by
    apply Subtype.ext; unfold sha256StateOf sha256StateBytes; rw [ofU8_toU8_id]
    change [beWord 32 (HMAC.toBEBytes 4 w0) 0, beWord 32 (HMAC.toBEBytes 4 w1) 0,
      beWord 32 (HMAC.toBEBytes 4 w2) 0, beWord 32 (HMAC.toBEBytes 4 w3) 0,
      beWord 32 (HMAC.toBEBytes 4 w4) 0, beWord 32 (HMAC.toBEBytes 4 w5) 0,
      beWord 32 (HMAC.toBEBytes 4 w6) 0, beWord 32 (HMAC.toBEBytes 4 w7) 0] =
      [w0, w1, w2, w3, w4, w5, w6, w7]
    repeat rw [beWord32_toBEBytes4_rpnc579]

private theorem ofU8_sha256StateBytes_rpnc579 (h : HMAC.ShaState) :
    ofU8 (sha256StateBytes h) = h.toList.flatMap (HMAC.toBEBytes 4) := by
  unfold sha256StateBytes; exact ofU8_toU8_id _

private theorem sha256With_length_32 (F : HMAC.ShaState → HwBytes → HMAC.ShaState) (msg : HwBytes) :
    (HMAC.sha256With F msg).length = 32 := by
  unfold HMAC.sha256With
  rw [← ofU8_sha256StateBytes_rpnc579, ofU8_length_rpnc579]
  exact sha256StateBytes_length_rpnc579 _

theorem hmacWith_length_32 (F : HMAC.ShaState → HwBytes → HMAC.ShaState) (k msg : HwBytes) :
    (ByteSpecs.hmacWith F k msg).length = 32 :=
  sha256With_length_32 F _

private theorem sha256Step_sha256StateBytes {P : SignalPqxdh.Primitives}
    {F : HMAC.ShaState → HwBytes → HMAC.ShaState}
    (hsha : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (h : HMAC.ShaState) (blk : List UInt8) :
    SignalPqxdh.sha256Step P (sha256StateBytes h) blk = sha256StateBytes (F h (ofU8 blk)) := by
  unfold SignalPqxdh.sha256Step
  rw [fitBytesRef_32_sha256StateBytes, hsha, sha256StateOf_sha256StateBytes_rpnc579,
    fitBytesRef_32_sha256StateBytes]

private theorem foldl_sha256Step_sha256StateBytes {P : SignalPqxdh.Primitives}
    {F : HMAC.ShaState → HwBytes → HMAC.ShaState}
    (hsha : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (blks : List (List UInt8)) (h : HMAC.ShaState) :
    blks.foldl (SignalPqxdh.sha256Step P) (sha256StateBytes h) =
      sha256StateBytes ((blks.map ofU8).foldl F h) := by
  induction blks generalizing h with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [sha256Step_sha256StateBytes hsha, ih]

private theorem zeroPadLen_sha256_eq_rpnc579 (n : Nat) :
    (if (n + 9) % 64 == 0 then 0 else 64 - (n + 9) % 64) = (119 - n % 64) % 64 := by
  by_cases h0 : (n + 9) % 64 = 0 <;> simp [h0] <;> omega

private theorem setWidth8_ushift_and_ff (w : BitVec 64) (k : BitVec 64) (s : Nat)
    (hk : k.toNat = s) (hs : s + 8 ≤ 64) :
    (w >>> k &&& 0xFF#64).setWidth 8 = w.extractLsb' s 8 := by
  ext i hi
  have hff : (255#8)[i] = true := by revert i hi; decide
  have hlt : s + i < 64 := by omega
  simp [hk, hlt, hff]

private theorem ofU8_u64_be_rpnc579 (u : UInt64) :
    ofU8 [((u >>> 56) &&& 0xFF).toUInt8, ((u >>> 48) &&& 0xFF).toUInt8,
      ((u >>> 40) &&& 0xFF).toUInt8, ((u >>> 32) &&& 0xFF).toUInt8,
      ((u >>> 24) &&& 0xFF).toUInt8, ((u >>> 16) &&& 0xFF).toUInt8,
      ((u >>> 8) &&& 0xFF).toUInt8, (u &&& 0xFF).toUInt8] =
      HMAC.toBEBytes 8 u.toBitVec := by
  rcases u with ⟨w⟩
  simp only [ofU8, List.map, UInt64.toUInt8]
  change [(w >>> 56#64 &&& 0xFF#64).setWidth 8, (w >>> 48#64 &&& 0xFF#64).setWidth 8,
    (w >>> 40#64 &&& 0xFF#64).setWidth 8, (w >>> 32#64 &&& 0xFF#64).setWidth 8,
    (w >>> 24#64 &&& 0xFF#64).setWidth 8, (w >>> 16#64 &&& 0xFF#64).setWidth 8,
    (w >>> 8#64 &&& 0xFF#64).setWidth 8, (w &&& 0xFF#64).setWidth 8] =
    [w.extractLsb' 56 8, w.extractLsb' 48 8, w.extractLsb' 40 8, w.extractLsb' 32 8,
     w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]
  rw [setWidth8_ushift_and_ff w 56#64 56 rfl (by decide),
      setWidth8_ushift_and_ff w 48#64 48 rfl (by decide),
      setWidth8_ushift_and_ff w 40#64 40 rfl (by decide),
      setWidth8_ushift_and_ff w 32#64 32 rfl (by decide),
      setWidth8_ushift_and_ff w 24#64 24 rfl (by decide),
      setWidth8_ushift_and_ff w 16#64 16 rfl (by decide),
      setWidth8_ushift_and_ff w 8#64 8 rfl (by decide),
      show (w &&& 0xFF#64).setWidth 8 = (w >>> 0#64 &&& 0xFF#64).setWidth 8 by simp,
      setWidth8_ushift_and_ff w 0#64 0 rfl (by decide)]

private theorem ofU8_encodeBitLen64BE_rpnc579 (n : Nat) :
    ofU8 (SignalPqxdh.encodeBitLen64BE n) = HMAC.toBEBytes 8 (BitVec.ofNat 64 (8 * n)) := by
  unfold SignalPqxdh.encodeBitLen64BE; rw [ofU8_u64_be_rpnc579]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toBitVec_mul, Nat.toUInt64, BitVec.toNat_ofNat, Nat.mul_comm]

private theorem ofU8_sha256Pad_rpnc579 (msg : List UInt8) :
    ofU8 (SignalPqxdh.sha256Pad msg) = HMAC.sha256Pad (ofU8 msg) := by
  unfold SignalPqxdh.sha256Pad HMAC.sha256Pad; dsimp only
  rw [zeroPadLen_sha256_eq_rpnc579, ofU8_append_rpnc579, ofU8_append_rpnc579,
    ofU8_append_rpnc579, ofU8_replicate_rpnc579, ofU8_encodeBitLen64BE_rpnc579, ofU8_length_rpnc579]
  rfl

private theorem map_ofU8_chunkBlocks_64_rpnc579 (bs : List UInt8) :
    (SignalPqxdh.chunkBlocks 64 bs).map ofU8 = HMAC.chunks64 (ofU8 bs) := by
  unfold SignalPqxdh.chunkBlocks HMAC.chunks64
  apply List.ext_getElem
  · simp [ofU8_length_rpnc579]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      List.map_drop, List.map_take, ofU8, Nat.mul_comm]

private theorem ofU8_sha256Ref {P : SignalPqxdh.Primitives}
    {F : HMAC.ShaState → HwBytes → HMAC.ShaState}
    (hsha : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (msg : List UInt8) :
    ofU8 (SignalPqxdh.sha256Ref P msg) = HMAC.sha256With F (ofU8 msg) := by
  unfold SignalPqxdh.sha256Ref HMAC.sha256With; dsimp only
  have hinit : SignalPqxdh.sha256InitState = sha256StateBytes HMAC.sha256IV := rfl
  rw [hinit, foldl_sha256Step_sha256StateBytes hsha,
    fitBytesRef_32_sha256StateBytes, ofU8_sha256StateBytes_rpnc579,
    map_ofU8_chunkBlocks_64_rpnc579, ofU8_sha256Pad_rpnc579]

private theorem ofU8_fitBytesRef_of_le_rpnc579 {n : Nat} {bs : List UInt8} (h : bs.length ≤ n) :
    ofU8 (SignalPqxdh.fitBytesRef n bs) =
      ofU8 bs ++ List.replicate (n - (ofU8 bs).length) 0#8 := by
  unfold SignalPqxdh.fitBytesRef
  rw [List.take_of_length_le h, ofU8_append_rpnc579, ofU8_replicate_rpnc579, ofU8_length_rpnc579]
  rfl

private theorem ofU8_xorBytes_replicate_rpnc579 (xs : List UInt8) (b : UInt8) :
    ofU8 (SignalPqxdh.xorBytes xs (List.replicate xs.length b)) =
      (ofU8 xs).map (· ^^^ b.toBitVec) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨x⟩; rcases b with ⟨b⟩
    change (x ^^^ b) :: ofU8 (SignalPqxdh.xorBytes xs (List.replicate xs.length ⟨b⟩)) =
      (x ^^^ b) :: (ofU8 xs).map (· ^^^ b)
    rw [ih]

private theorem ofU8_xorBytes_replicate_of_length {xs : List UInt8} {k : Nat} (b : UInt8)
    (h : xs.length = k) :
    ofU8 (SignalPqxdh.xorBytes xs (List.replicate k b)) =
      (ofU8 xs).map (· ^^^ b.toBitVec) := by
  subst h; exact ofU8_xorBytes_replicate_rpnc579 xs b

private theorem ofU8_hmacSha256Ref {P : SignalPqxdh.Primitives}
    {F : HMAC.ShaState → HwBytes → HMAC.ShaState}
    (hsha : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (key msg : List UInt8) :
    ofU8 (SignalPqxdh.hmacSha256Ref P key msg) = ByteSpecs.hmacWith F (ofU8 key) (ofU8 msg) := by
  unfold SignalPqxdh.hmacSha256Ref ByteSpecs.hmacWith; dsimp only
  have hkpad_len :
      (SignalPqxdh.fitBytesRef 64 (if key.length > 64 then SignalPqxdh.sha256Ref P key else key)).length = 64 :=
    SignalPqxdh.fitBytesRef_length 64 _
  have hle : (if key.length > 64 then SignalPqxdh.sha256Ref P key else key).length ≤ 64 := by
    split
    · rw [sha256Ref_length_local]; decide
    · omega
  rw [ofU8_sha256Ref hsha, ofU8_append_rpnc579, ofU8_sha256Ref hsha, ofU8_append_rpnc579,
    ofU8_xorBytes_replicate_of_length 0x5c hkpad_len,
    ofU8_xorBytes_replicate_of_length 0x36 hkpad_len,
    ofU8_fitBytesRef_of_le_rpnc579 hle]
  split <;> rename_i hk
  · have hk' : 64 < (ofU8 key).length := by rwa [ofU8_length_rpnc579]
    simp only [hk', ↓reduceIte, ofU8_sha256Ref hsha]; rfl
  · have hk' : ¬ (64 < (ofU8 key).length) := by rwa [ofU8_length_rpnc579]
    simp only [hk', ↓reduceIte]; rfl

private theorem byteArray_toList_loop_aux (l : List UInt8) :
    ∀ (fuel i : Nat) (acc : List UInt8), l.length - i ≤ fuel →
      ByteArray.toList.loop ⟨⟨l⟩⟩ i acc = acc.reverse ++ l.drop i
  | 0, i, acc, hfuel => by
    unfold ByteArray.toList.loop
    split
    · rename_i hi
      have hlt : i < l.length := hi
      omega
    · have hlen : l.length ≤ i := by omega
      rw [List.drop_of_length_le hlen, List.append_nil]
  | fuel + 1, i, acc, hfuel => by
    unfold ByteArray.toList.loop
    split
    · rename_i hi
      have hlt : i < l.length := hi
      rw [byteArray_toList_loop_aux l fuel (i + 1) _ (by omega), List.reverse_cons,
        List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons hlt]
      congr 2
      exact getElem!_pos ({ toList := l } : Array UInt8) i hlt
    · rename_i hge
      have hlen : l.length ≤ i := Nat.not_lt.mp hge
      rw [List.drop_of_length_le hlen, List.append_nil]

private theorem ofU8_byteArray_toList (ba : ByteArray) :
    ofU8 ba.toList = ofByteArray ba := by
  rcases ba with ⟨⟨l⟩⟩
  unfold ByteArray.toList
  rw [byteArray_toList_loop_aux l l.length 0 [] (by omega)]
  rfl

private theorem ofU8_infoPqxdh : ofU8 SignalPqxdh.INFO_PQXDH = TR.pqxdhLabelBytes :=
  ofU8_byteArray_toList _

private theorem ofU8_discontinuity : ofU8 SignalPqxdh.F_X25519 = TR.discontinuityBytes := rfl

/-- Byte-level agreement between the root, chain, and PQR keys derived by
`SignalPqxdh.Model.acceptKeys` and `TR.pqxdhKdfBytes`. -/
theorem rpkNew_acceptKeys_eq_pqxdhKdfBytes
    {interp : ExternInterpretation} {P : PEParams} {X : UnreachedPqxdhPrimitives}
    (hhooks : ModelAgree interp P)
    {inp : SignalPqxdh.AcceptKeysInput} {dk : SignalPqxdh.DRKey}
    {r : ProtocolSetup} {p : PreKeyFields} {ct_wire : HwBytes}
    (hdh1 : ofU8 ((modelPrims X P).x25519 inp.spkBSk inp.hdr.ikAPk) =
      TR.dhAgreeBytes interp (secretBytes r 2) (pubBytes interp (secretBytes r 0)))
    (hdh2 : ofU8 ((modelPrims X P).x25519 inp.ikBSk inp.hdr.ekAPk) =
      TR.dhAgreeBytes interp (secretBytes r 1) (TR.ekBytes p))
    (hdh3 : ofU8 ((modelPrims X P).x25519 inp.spkBSk inp.hdr.ekAPk) =
      TR.dhAgreeBytes interp (secretBytes r 2) (TR.ekBytes p))
    (hopk : (p.preKeyId = none ∧ inp.hdr.opkId? = none ∧ inp.opkBSk? = none) ∨
      (∃ id1 id2 opkSk, p.preKeyId = some id1 ∧ inp.hdr.opkId? = some id2 ∧
        inp.opkBSk? = some opkSk ∧
        ofU8 ((modelPrims X P).x25519 opkSk inp.hdr.ekAPk) =
          TR.dhAgreeBytes interp (secretBytes r 6) (TR.ekBytes p)))
    (hkem : ((modelPrims X P).kemDecaps inp.pqspkBSk inp.hdr.kemCt).map ofU8 =
      some ((kyberDecapsBytes interp r ct_wire).getD []))
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X P) inp = some dk) :
    let F := sha256CompressFunction interp
    let ikABytes := pubBytes interp (secretBytes r 0)
    let ikBskBytes := secretBytes r 1
    let spkBytes := secretBytes r 2
    let ek := TR.ekBytes p
    let dh1 := TR.dhAgreeBytes interp spkBytes ikABytes
    let dh2 := TR.dhAgreeBytes interp ikBskBytes ek
    let dh3 := TR.dhAgreeBytes interp spkBytes ek
    let dh4 := p.preKeyId.map (fun _ => TR.dhAgreeBytes interp (secretBytes r 6) ek)
    let ss := (kyberDecapsBytes interp r ct_wire).getD []
    let (rk, ck, pqr) := TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
    ofU8 dk.rootKey = rk ∧
      ofU8 dk.chainKey = ck ∧
      ofU8 dk.pqrKey = pqr ∧
      rk.length = 32 ∧ ck.length = 32 ∧ pqr.length = 32 := by
  intro F ikABytes ikBskBytes spkBytes ek dh1 dh2 dh3 dh4 ss
  let MP := modelPrims X P
  have hsha : ∀ st blk, MP.sha256Compress st blk =
      sha256StateBytes (F (sha256StateOf st) (ofU8 blk)) := by
    intro st blk
    change sha256StateBytes (P.C.F (sha256StateOf st) (ofU8 blk)) = _
    rw [hhooks.1]
  have hhkdf : MP.hkdfDerive96 = SignalPqxdh.hkdfDerive96Ref MP := rfl
  change SignalPqxdh.Model.acceptKeys MP inp = some dk at hacc
  unfold SignalPqxdh.Model.acceptKeys at hacc
  simp only [bind, option_bind_guard, ite_none_eq_some_iff] at hacc
  rcases hacc with ⟨_, _, _, _, _, _, _, _, hacc⟩
  cases hkem_raw : MP.kemDecaps inp.pqspkBSk inp.hdr.kemCt with
  | none =>
    change (MP.kemDecaps inp.pqspkBSk inp.hdr.kemCt).map ofU8 = _ at hkem
    rw [hkem_raw] at hkem; simp at hkem
  | some ssRaw =>
    change (MP.kemDecaps inp.pqspkBSk inp.hdr.kemCt).map ofU8 = _ at hkem
    rw [hkem_raw] at hkem
    simp only [Option.map_some, Option.some.injEq] at hkem
    have hsecrets :
        ∃ dh4?,
          dk = MP.hkdfDerive96
            (SignalPqxdh.buildSecrets
              (MP.x25519 inp.spkBSk inp.hdr.ikAPk)
              (MP.x25519 inp.ikBSk inp.hdr.ekAPk)
              (MP.x25519 inp.spkBSk inp.hdr.ekAPk) dh4? ssRaw) ∧
          ofU8 (SignalPqxdh.buildSecrets
            (MP.x25519 inp.spkBSk inp.hdr.ikAPk)
            (MP.x25519 inp.ikBSk inp.hdr.ekAPk)
            (MP.x25519 inp.spkBSk inp.hdr.ekAPk) dh4? ssRaw) =
            TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss := by
      rcases hopk with ⟨hp0, hi0, hs0⟩ | ⟨id1, id2, opkSk, hp1, hi1, hs1, hdh4_eq⟩
      · simp only [hi0, hs0, hkem_raw, Option.bind, ite_none_eq_some_iff, Option.some.injEq] at hacc
        refine ⟨none, hacc.2.2.symm, ?_⟩
        dsimp only [SignalPqxdh.buildSecrets, TR.pqxdhIkmBytes, dh4, dh1, dh2, dh3, ss,
          ikABytes, ikBskBytes, spkBytes, ek, MP]
        rw [hp0]
        simp only [Option.map_none, ofU8_append_rpnc579, ofU8_discontinuity, hdh1, hdh2, hdh3, hkem,
          List.append_assoc]
      · simp only [hi1, hs1, hkem_raw, Option.bind, ite_none_eq_some_iff, Option.some.injEq] at hacc
        refine ⟨some (MP.x25519 opkSk inp.hdr.ekAPk), hacc.2.2.symm, ?_⟩
        dsimp only [SignalPqxdh.buildSecrets, TR.pqxdhIkmBytes, dh4, dh1, dh2, dh3, ss,
          ikABytes, ikBskBytes, spkBytes, ek, MP]
        rw [hp1]
        simp only [Option.map_some, ofU8_append_rpnc579, ofU8_discontinuity, hdh1, hdh2, hdh3, hdh4_eq, hkem,
          List.append_assoc]
    obtain ⟨dh4?, rfl, hikm⟩ := hsecrets
    rw [hhkdf]
    unfold SignalPqxdh.hkdfDerive96Ref SignalPqxdh.hkdfExpand96Ref SignalPqxdh.hkdfExtractRef
      TR.pqxdhKdfBytes TR.hkdfBlock1Bytes TR.hkdfBlock2Bytes TR.hkdfBlock3Bytes
    dsimp only
    set rawIkm := SignalPqxdh.buildSecrets (MP.x25519 inp.spkBSk inp.hdr.ikAPk)
      (MP.x25519 inp.ikBSk inp.hdr.ekAPk) (MP.x25519 inp.spkBSk inp.hdr.ekAPk) dh4? ssRaw
    set ikm := TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss
    set rawPrk := SignalPqxdh.hmacSha256Ref MP (List.replicate 32 0) rawIkm
    set prk := ByteSpecs.hmacWith F (List.replicate 32 0#8) ikm
    have hprk : ofU8 rawPrk = prk := by
      dsimp only [rawPrk, prk]
      rw [ofU8_hmacSha256Ref hsha, ofU8_replicate_rpnc579, hikm]; rfl
    have ht1 : ofU8 (SignalPqxdh.hmacSha256Ref MP rawPrk (SignalPqxdh.INFO_PQXDH ++ [0x01])) =
        ByteSpecs.hmacWith F prk (TR.pqxdhLabelBytes ++ [1#8]) := by
      rw [ofU8_hmacSha256Ref hsha, hprk, ofU8_append_rpnc579, ofU8_infoPqxdh]; rfl
    have ht2 : ofU8 (SignalPqxdh.hmacSha256Ref MP rawPrk
        (SignalPqxdh.hmacSha256Ref MP rawPrk (SignalPqxdh.INFO_PQXDH ++ [0x01]) ++
          SignalPqxdh.INFO_PQXDH ++ [0x02])) =
        ByteSpecs.hmacWith F prk (ByteSpecs.hmacWith F prk (TR.pqxdhLabelBytes ++ [1#8]) ++
          (TR.pqxdhLabelBytes ++ [2#8])) := by
      rw [ofU8_hmacSha256Ref hsha, hprk, ofU8_append_rpnc579, ofU8_append_rpnc579,
        ht1, ofU8_infoPqxdh, List.append_assoc]
      rfl
    have ht3 : ofU8 (SignalPqxdh.hmacSha256Ref MP rawPrk
        (SignalPqxdh.hmacSha256Ref MP rawPrk
          (SignalPqxdh.hmacSha256Ref MP rawPrk (SignalPqxdh.INFO_PQXDH ++ [0x01]) ++
            SignalPqxdh.INFO_PQXDH ++ [0x02]) ++ SignalPqxdh.INFO_PQXDH ++ [0x03])) =
        ByteSpecs.hmacWith F prk
          (ByteSpecs.hmacWith F prk (ByteSpecs.hmacWith F prk (TR.pqxdhLabelBytes ++ [1#8]) ++
            (TR.pqxdhLabelBytes ++ [2#8])) ++ (TR.pqxdhLabelBytes ++ [3#8])) := by
      rw [ofU8_hmacSha256Ref hsha, hprk, ofU8_append_rpnc579, ofU8_append_rpnc579,
        ht2, ofU8_infoPqxdh, List.append_assoc]
      rfl
    exact ⟨ht1, ht2, ht3, hmacWith_length_32 F _ _, hmacWith_length_32 F _ _, hmacWith_length_32 F _ _⟩

end Symbolic.Swarm.CREF.Cli.Slots
