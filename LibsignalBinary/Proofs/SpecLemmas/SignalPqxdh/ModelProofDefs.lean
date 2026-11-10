/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalPqxdh.Model

/-!
# Proof-Side PQXDH Key-Schedule Helpers and Handshake Round-Trip

Defines `DRKey.toBytes96`, `decodeEC`, `decodeKEM`, `WellFormedPrimitives`, and `fitBytes`, and
proves PQXDH handshake round-trip correctness (`pqxdh_handshake_roundtrip`, `wellFormed_pqxdhCorrect`).
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh

/-- Concatenates the three 32-byte slices of `DRKey` into a 96-byte buffer (`pqxdh.rs:70-92`). -/
def DRKey.toBytes96 (dk : DRKey) : Bytes :=
  dk.rootKey ++ dk.chainKey ++ dk.pqrKey

/-- Parses a 33-byte serialized Curve25519 public key (`<PublicKey>::try_from`). -/
def decodeEC (b : Bytes) : Option Bytes :=
  match b with
  | tag :: rest => if tag == TAG_EC_DJB && rest.length == 32 then some rest else none
  | [] => none

/-- Parses a 1569-byte serialized Kyber1024 public key (`<kem::Key<Public>>::try_from`). -/
def decodeKEM (b : Bytes) : Option Bytes :=
  match b with
  | tag :: rest => if tag == TAG_KYBER_1024 && rest.length == 1568 then some rest else none
  | [] => none

/-- Alias for `P.isCanonical` on 32-byte Curve25519 public keys (`pqxdh.rs:328`). -/
abbrev Primitives.isCanonicalEC (P : Primitives) : Bytes → Bool := P.isCanonical

theorem clampScalar25519_length (sk : Bytes) :
    (clampScalar25519 sk).length = 32 := by
  have hFit : (fitBytesRef 32 sk).length = 32 := fitBytesRef_length 32 sk
  simp [clampScalar25519, hFit]

private theorem xorByte_self_right (x y : UInt8) : (x ^^^ y) ^^^ y = x := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      apply congrArg UInt8.ofBitVec
      change (bx ^^^ by_) ^^^ by_ = bx
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xorBytes_self_right (a b : Bytes) (h : a.length = b.length) :
    xorBytes (xorBytes a b) b = a := by
  induction a generalizing b with
  | nil => simp [xorBytes]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [xorBytes, List.zipWith_cons_cons, xorByte_self_right]
      congr 1
      exact ih ys h

/-- Algebraic and structural well-formedness of `P : Primitives` with perfect KEM
    decapsulation correctness: `WellFormedPrimitivesδ P` (`Model.lean`) extended with `kem_corr`. -/
structure WellFormedPrimitives (P : Primitives) : Prop extends WellFormedPrimitivesδ P where
  kem_corr : ∀ seed r ss ct,
               P.kemEncaps (P.kemKeyGen seed).1 r = some (ss, ct) →
               P.kemDecaps (P.kemKeyGen seed).2 ct = some ss

/-- Derived non-zero DH law for arbitrary scalar byte slices `a, b : Bytes`, reducing via
    `x25519_clamp`, `x25519Base_clamp`, and `clampScalar25519_length` to 32-byte clamped scalars
    in `x25519_base_ne_zero`. -/
theorem WellFormedPrimitives.x25519_base_ne_zero_any (P : Primitives) (hWF : WellFormedPrimitives P)
    (a b : Bytes) : P.x25519 a (P.x25519Base b) ≠ List.replicate 32 0 := by
  rw [← hWF.x25519_clamp, ← hWF.x25519Base_clamp]
  exact hWF.x25519_base_ne_zero (clampScalar25519 a) (clampScalar25519 b)
    (clampScalar25519_length a) (clampScalar25519_length b)

/-- Handshake and first-message functional correctness (5-step key schedule):
    When Alice initiates against an authentic bundle of Bob (`ikB = x25519Base ikBSk`,
    `spkB = x25519Base spkBSk`, matching `opkB?`, valid `(pqspkB, pqspkBSk)`, valid signatures
    `spkSig` and `pqspkSig` under the single wire key `ikB`), and Bob accepts the resulting
    `PreKeyMsg` with `trustedPeer = true` and `replayOk = true`, both handshake-only
    `Model.initiateKeys`/`Model.acceptKeys` and full `Model.initiate`/`Model.accept` succeed,
    derive identical `(drKey, rk1, ck1_1)`, and recover `initInp.plaintext`. -/
theorem pqxdh_handshake_roundtrip
    (P : Primitives)
    (hX25519     : ∀ a b, P.x25519 a (P.x25519Base b) = P.x25519 b (P.x25519Base a))
    (hCanon      : ∀ e, P.isCanonical (P.x25519Base e) = true)
    (hBaseLen    : ∀ e, (P.x25519Base e).length = 32)
    (hBaseNeZero : ∀ a b, P.x25519 a (P.x25519Base b) ≠ List.replicate 32 0)
    (hAead       : ∀ mk ad pt, P.aeadDec mk ad (P.aeadEnc mk ad pt) = some pt)
    (initInp : InitiateInput) (accKeysInp : AcceptKeysInput)
    (hTrustA : initInp.trustedPeer = true)
    (hTrustB : accKeysInp.trustedPeer = true)
    (hReplay : accKeysInp.replayOk = true)
    (hSigSpk : P.sigVerify initInp.bundle.ikB (encodeEC initInp.bundle.spkB) initInp.bundle.spkSig = true)
    (hSigKem : P.sigVerify initInp.bundle.ikB (encodeKEM initInp.bundle.pqspkB) initInp.bundle.pqspkSig = true)
    (hIkA    : initInp.ikAPk = P.x25519Base initInp.ikASk)
    (hIkB    : initInp.bundle.ikB = P.x25519Base accKeysInp.ikBSk ∧ accKeysInp.ikBPk = initInp.bundle.ikB)
    (hSpkB   : initInp.bundle.spkB = P.x25519Base accKeysInp.spkBSk ∧ accKeysInp.spkBPk = initInp.bundle.spkB)
    (hOpkB   : initInp.bundle.opkB?.map Prod.snd = accKeysInp.opkBSk?.map P.x25519Base ∧
               initInp.bundle.opkB?.isSome = accKeysInp.opkBSk?.isSome)
    (ss kemCt : Bytes)
    (hEncaps : P.kemEncaps initInp.bundle.pqspkB initInp.kemCoins = some (ss, kemCt))
    (hDecaps : P.kemDecaps accKeysInp.pqspkBSk kemCt = some ss)
    (hCtLen  : kemCt.length = kyberCtLen)
    (hSpqr   : ∀ pqrKey stA salt? pqMsg,
                 P.spqrInitSend pqrKey initInp.spqrCoins = some (stA, salt?, pqMsg) →
                 ∃ stB, P.spqrInitRecv pqrKey pqMsg = some (stB, salt?))
    (hSpqrOk : (P.spqrInitSend (P.hkdfDerive96 (buildSecrets
                 (P.x25519 initInp.ikASk initInp.bundle.spkB)
                 (P.x25519 initInp.ekASk initInp.bundle.ikB)
                 (P.x25519 initInp.ekASk initInp.bundle.spkB)
                 (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk))
                 ss)).pqrKey initInp.spqrCoins).isSome = true) :
    ∃ drKey hdr rk1 ck1_1 msg,
      Model.initiateKeys P initInp.toInitiateKeysInput = some (drKey, hdr) ∧
      Model.acceptKeys P { accKeysInp with hdr := hdr } = some drKey ∧
      Model.initiate P initInp = some (drKey, rk1, ck1_1, msg) ∧
      Model.accept P { keysInp := { accKeysInp with hdr := hdr }, msg := msg } =
        some (drKey, rk1, ck1_1, initInp.plaintext) := by
  have hDh1 : P.x25519 accKeysInp.spkBSk initInp.ikAPk = P.x25519 initInp.ikASk initInp.bundle.spkB := by
    rw [hIkA, hSpkB.1, hX25519]
  have hDh2 : P.x25519 accKeysInp.ikBSk (P.x25519Base initInp.ekASk) =
      P.x25519 initInp.ekASk initInp.bundle.ikB := by
    rw [hIkB.1, hX25519]
  have hDh3 : P.x25519 accKeysInp.spkBSk (P.x25519Base initInp.ekASk) =
      P.x25519 initInp.ekASk initInp.bundle.spkB := by
    rw [hSpkB.1, hX25519]
  have hDhR : P.x25519 accKeysInp.spkBSk (P.x25519Base initInp.ephASk) =
      P.x25519 initInp.ephASk initInp.bundle.spkB := by
    rw [hSpkB.1, hX25519]
  have hIkALen : initInp.ikAPk.length = 32 := by rw [hIkA]; exact hBaseLen initInp.ikASk
  have hEkALen : (P.x25519Base initInp.ekASk).length = 32 := hBaseLen initInp.ekASk
  have hEphALen : (P.x25519Base initInp.ephASk).length = 32 := hBaseLen initInp.ephASk
  have hBaseNeZero' : ∀ a b, P.x25519 a (P.x25519Base b) ≠
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := hBaseNeZero
  have hDh1NeZero : P.x25519 initInp.ikASk initInp.bundle.spkB ≠
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [hSpkB.1]; exact hBaseNeZero _ _
  have hDh2NeZero : P.x25519 initInp.ekASk initInp.bundle.ikB ≠
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [hIkB.1]; exact hBaseNeZero _ _
  have hDh3NeZero : P.x25519 initInp.ekASk initInp.bundle.spkB ≠
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [hSpkB.1]; exact hBaseNeZero _ _
  have hDhRNeZero : P.x25519 initInp.ephASk initInp.bundle.spkB ≠
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [hSpkB.1]; exact hBaseNeZero _ _
  have hDh4NeZero :
      dhOptNonZero (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk)) = true := by
    rcases h1 : initInp.bundle.opkB? with _ | ⟨opkId, opkPk⟩ <;>
      rcases h2 : accKeysInp.opkBSk? with _ | opkSk
    · rfl
    · have := hOpkB.2; rw [h1, h2] at this; contradiction
    · have := hOpkB.2; rw [h1, h2] at this; contradiction
    · have hEq := hOpkB.1
      rw [h1, h2] at hEq
      injection hEq with hPk
      dsimp at hPk
      simp [dhOptNonZero, hPk, hBaseNeZero']
  revert hSpqrOk
  generalize hSend : P.spqrInitSend (P.hkdfDerive96 (buildSecrets
    (P.x25519 initInp.ikASk initInp.bundle.spkB)
    (P.x25519 initInp.ekASk initInp.bundle.ikB)
    (P.x25519 initInp.ekASk initInp.bundle.spkB)
    (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk))
    ss)).pqrKey initInp.spqrCoins = sendRes
  cases sendRes with
  | none => intro hContra; contradiction
  | some val =>
    rcases val with ⟨stA, salt?, pqMsg⟩
    intro _
    obtain ⟨stB, hRecv⟩ := hSpqr _ stA salt? pqMsg hSend
    have hInitKeys : Model.initiateKeys P initInp.toInitiateKeysInput =
        some (P.hkdfDerive96 (buildSecrets
          (P.x25519 initInp.ikASk initInp.bundle.spkB)
          (P.x25519 initInp.ekASk initInp.bundle.ikB)
          (P.x25519 initInp.ekASk initInp.bundle.spkB)
          (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk))
          ss), {
            ikAPk   := initInp.ikAPk
            ekAPk   := P.x25519Base initInp.ekASk
            spkId   := initInp.bundle.spkId
            opkId?  := initInp.bundle.opkB?.map Prod.fst
            pqspkId := initInp.bundle.pqspkId
            kemCt   := kemCt
          }) := by
      simp [Model.initiateKeys, hTrustA, hSigSpk, hSigKem, hEncaps, hDh1NeZero, hDh2NeZero, hDh3NeZero, hDh4NeZero, guard, bind, pure]
    have hAccKeys : Model.acceptKeys P { accKeysInp with hdr := {
          ikAPk   := initInp.ikAPk
          ekAPk   := P.x25519Base initInp.ekASk
          spkId   := initInp.bundle.spkId
          opkId?  := initInp.bundle.opkB?.map Prod.fst
          pqspkId := initInp.bundle.pqspkId
          kemCt   := kemCt
        } } = some (P.hkdfDerive96 (buildSecrets
          (P.x25519 initInp.ikASk initInp.bundle.spkB)
          (P.x25519 initInp.ekASk initInp.bundle.ikB)
          (P.x25519 initInp.ekASk initInp.bundle.spkB)
          (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk))
          ss)) := by
      rcases h1 : initInp.bundle.opkB? with _ | ⟨opkId, opkPk⟩ <;>
        rcases h2 : accKeysInp.opkBSk? with _ | opkSk
      · simp [Model.acceptKeys, dhOptNonZero, hTrustB, hReplay, hIkALen, hEkALen, hCanon, hCtLen, kyberCtLen, hDecaps, hDh1, hDh2, hDh3, hDh1NeZero, hDh2NeZero, hDh3NeZero, guard, bind, pure]
      · have := hOpkB.2; rw [h1, h2] at this; contradiction
      · have := hOpkB.2; rw [h1, h2] at this; contradiction
      · have hEq := hOpkB.1
        rw [h1, h2] at hEq
        injection hEq with hPk
        dsimp at hPk
        simp [Model.acceptKeys, dhOptNonZero, hTrustB, hReplay, hIkALen, hEkALen, hCanon, hCtLen, kyberCtLen, hDecaps, hDh1, hDh2, hDh3, hDh1NeZero, hDh2NeZero, hDh3NeZero, hPk, hX25519, hBaseNeZero', guard, bind, pure]
    let drKey := P.hkdfDerive96 (buildSecrets
          (P.x25519 initInp.ikASk initInp.bundle.spkB)
          (P.x25519 initInp.ekASk initInp.bundle.ikB)
          (P.x25519 initInp.ekASk initInp.bundle.spkB)
          (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk))
          ss)
    let hdr : HandshakeHdr := {
      ikAPk   := initInp.ikAPk
      ekAPk   := P.x25519Base initInp.ekASk
      spkId   := initInp.bundle.spkId
      opkId?  := initInp.bundle.opkB?.map Prod.fst
      pqspkId := initInp.bundle.pqspkId
      kemCt   := kemCt
    }
    let ephAPk := P.x25519Base initInp.ephASk
    let dhRatchet := P.x25519 initInp.ephASk initInp.bundle.spkB
    let rk1 := (P.rootCreateChain drKey.rootKey dhRatchet).1
    let ck1_0 := (P.rootCreateChain drKey.rootKey dhRatchet).2
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let deriveMessageKeys := P.deriveMsgKeys mkSeed salt?
    let ad := firstMsgAD initInp.ikAPk initInp.bundle.ikB ephAPk pqMsg
    let aeadCt := P.aeadEnc deriveMessageKeys ad initInp.plaintext
    let msg : PreKeyMsg := {
      hdr          := hdr
      ephAPk       := ephAPk
      pqRatchetMsg := pqMsg
      aeadCt       := aeadCt
    }
    refine ⟨drKey, hdr, rk1, ck1_1, msg, hInitKeys, hAccKeys, ?_, ?_⟩
    · simp [Model.initiate, hInitKeys, hDhRNeZero, hSend, drKey, hdr, ephAPk, dhRatchet, rk1, ck1_0, mkSeed, ck1_1, deriveMessageKeys, ad, aeadCt, msg, guard, bind]
    · dsimp only [Model.accept, hdr, msg]
      rw [hAccKeys]
      simp [hEphALen, hDhR, hDhRNeZero, hRecv, hIkB.2, hAead, drKey, ephAPk, dhRatchet, rk1, ck1_0, mkSeed, ck1_1, deriveMessageKeys, ad, aeadCt, guard, bind]

/-- Well-formed primitives satisfy `PqxdhCorrect`. -/
theorem wellFormed_pqxdhCorrect (P : Primitives) (hWF : WellFormedPrimitives P) :
    PqxdhCorrect P := by
  intro initInp accKeysInp ss kemCt hTrustA hTrustB hReplay hSigSpk hSigKem hIkA hIkB hSpkB hOpkB hEncaps hDecaps hSpqrOk
  exact pqxdh_handshake_roundtrip P hWF.x25519_comm hWF.canon_base hWF.x25519Base_len hWF.x25519_base_ne_zero_any hWF.aead_corr
    initInp accKeysInp hTrustA hTrustB hReplay hSigSpk hSigKem hIkA hIkB hSpkB hOpkB
    ss kemCt hEncaps hDecaps (hWF.kemEncaps_len _ _ _ _ hEncaps).2
    (fun pqrKey stA salt? pqMsg hS => hWF.spqr_corr pqrKey initInp.spqrCoins stA salt? pqMsg hS) hSpqrOk

/-- Pad or truncate a `Bytes` list to exactly `n` bytes with trailing `0`s. -/
def fitBytes (n : Nat) (bs : Bytes) : Bytes :=
  bs.take n ++ List.replicate (n - bs.length) 0

end SignalPqxdh
