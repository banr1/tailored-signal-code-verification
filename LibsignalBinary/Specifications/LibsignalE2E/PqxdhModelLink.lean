/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.SignalPqxdh.Model

/-!
# Bridge from End-to-End Primitives to `SignalPqxdh.Primitives` (`modelPrims`)

**Trusted: the statement.** Instantiates `SignalPqxdh.Primitives` (`SignalPqxdh/Model.lean`) from
the session primitives `C : Crypto`, the PQXDH hooks `Q : PqxdhPrims`, and the unreached model
operations `X : UnreachedPqxdhPrimitives`:
* Block-level primitives (`blockLevelPrims`) adapt byte and endianness encodings (big-endian SHA
  words, little-endian AES keys/blocks, clamped X25519 scalars, and length-checked Kyber inputs).
* Derived primitives (`modelPrims`) use the pure model's reference constructions (`sha512Ref`,
  `xeddsaVerifyRef`, `isCanonicalRef`, `hkdfDerive96Ref`, chain KDFs, and AEAD).
* Unused SPQR fields in `SignalPqxdh.Primitives` are stubs; V1 SPQR runs in the session model
  (`pqxdhSpqrSession`, DEV-PQ3).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession

/-! ## Byte conversions -/

/-- A model byte string (`List UInt8`) as a machine vector of `n` bytes: `fitVec n ∘ ofU8`. -/
def u8Vec (n : Nat) (bs : List UInt8) : List.Vector (BitVec 8) n := fitVec n (ofU8 bs)

/-- A machine vector as a model byte string. -/
def vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : List UInt8 := toU8 v.toList

/-- The `k`-th big-endian `w`-bit word of `bs` (bytes `k·(w/8) .. (k+1)·(w/8) − 1`, missing bytes
zero). -/
def beWord (w : Nat) (bs : List (BitVec 8)) (k : Nat) : BitVec w :=
  ((bs.drop (k * (w / 8))).take (w / 8)).foldl (fun acc b => (acc <<< 8) ||| b.zeroExtend w) 0

/-- A 32-byte SHA-256 chaining state (FIPS 180-4's `H` as big-endian bytes) as eight words. -/
def sha256StateOf (bs : List UInt8) : HMAC.ShaState :=
  List.Vector.ofFn fun i : Fin 8 => beWord 32 (ofU8 bs) i.val

/-- A 64-byte SHA-512 chaining state as eight words. -/
def sha512StateOf (bs : List UInt8) : Sha512State :=
  List.Vector.ofFn fun i : Fin 8 => beWord 64 (ofU8 bs) i.val

/-- A SHA-256 chaining state as its 32 big-endian bytes. -/
def sha256StateBytes (h : HMAC.ShaState) : List UInt8 := toU8 (h.toList.flatMap (HMAC.toBEBytes 4))

/-- A SHA-512 chaining state as its 64 big-endian bytes. -/
def sha512StateBytesBE (h : Sha512State) : List UInt8 := toU8 (h.toList.flatMap (HMAC.toBEBytes 8))

/-! ## The fields with no binary counterpart -/

/-- **The model's primitives that no handshake entry reaches**: XEdDSA public-key derivation and
signing, scalar multiplication and addition mod ℓ, Kyber key generation, and the security
model's cofactor projection and DDH predicate. Universally quantified in the statement. -/
structure UnreachedPqxdhPrimitives where
  /-- `sigPkGen` (the model's law says it is `x25519Base`; free here, not reached). -/
  sigPkGen : List UInt8 → List UInt8
  /-- `sigSign`. -/
  sigSign : List UInt8 → List UInt8 → List UInt8 → List UInt8
  /-- `scalarMul`. -/
  scalarMul : List UInt8 → List UInt8 → List UInt8
  /-- `scalarAdd`. -/
  scalarAdd : List UInt8 → List UInt8 → List UInt8
  /-- `kemKeyGen`. -/
  kemKeyGen : List UInt8 → List UInt8 × List UInt8
  /-- `pow8`. -/
  pow8 : List UInt8 → List UInt8
  /-- `isValidDhTriple`. -/
  isValidDhTriple : List UInt8 → List UInt8 → List UInt8 → Bool

/-! ## The primitives -/

/-- **The block-level primitives** at `(X, W)`; the derived fields are placeholders, replaced in
`modelPrims`. `kemEncaps` and `kemDecaps` reject inputs whose byte length differs from
`SignalPqxdh.kyberPkLen` and `SignalPqxdh.kyberCtLen`, matching `PublicKey` and `Ciphertext`
deserialization in `rust/protocol/src/kem.rs`. -/
def blockLevelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) : SignalPqxdh.Primitives where
  x25519 a pk := vecU8 (W.C.X (Ratchet.clampScalar (u8Vec 32 a)) (u8Vec 32 pk))
  x25519Base a := vecU8 (W.C.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
  isCanonical _ := false
  sigPkGen := X.sigPkGen
  sigSign := X.sigSign
  sigVerify _ _ _ := false
  sha512 _ := []
  scalarMul := X.scalarMul
  scalarAdd := X.scalarAdd
  scalarFromBytesModOrder b := vecU8 (W.Q.scalarMod (u8Vec 32 b))
  scalarFromWide b := vecU8 (W.Q.scalarWide (u8Vec 64 b))
  montToEd u s := (W.Q.montToEd (u8Vec 32 u) s.toBitVec).map vecU8
  isTorsionFree p := W.Q.isTorsionFree (u8Vec 160 p)
  edNeg p := vecU8 (W.Q.edNeg (u8Vec 160 p))
  doubleScalarMulBasepoint h a s :=
    vecU8 (W.Q.dsmb (u8Vec 32 h) (u8Vec 160 a) (u8Vec 32 s))
  compress p := vecU8 (W.Q.compress (u8Vec 160 p))
  kemKeyGen := X.kemKeyGen
  kemEncaps pk r :=
    if pk.length == SignalPqxdh.kyberPkLen then
      let (ct, ss) := W.Q.encaps (u8Vec SignalPqxdh.kyberPkLen pk) (u8Vec 32 r)
      some (vecU8 ss, vecU8 ct)
    else none
  kemDecaps sk ct :=
    if ct.length == SignalPqxdh.kyberCtLen then
      some (vecU8 (W.Q.decaps (u8Vec 3168 sk) (u8Vec SignalPqxdh.kyberCtLen ct)))
    else none
  hkdfDerive96 _ := default
  rootCreateChain _ _ := ([], [])
  chainKdfSeed _ := []
  chainKdfNext _ := []
  spqrInitSend _ _ := some ([], none, [])
  spqrInitRecv _ _ := some ([], none)
  deriveMsgKeys _ _ := default
  aeadEnc _ _ _ := []
  aeadDec _ _ _ := none
  pow8 := X.pow8
  isValidDhTriple := X.isValidDhTriple
  sha256Compress st blk := sha256StateBytes (W.C.F (sha256StateOf st) (ofU8 blk))
  sha512Compress st blk := sha512StateBytesBE (W.Q.F512 (sha512StateOf st) (ofU8 blk))
  aesEncBlock k blk := toU8 (LibsignalAesCbc.blockToBytes
    (W.C.E (LibsignalAesCbc.bytesToKey (ofU8 (SignalPqxdh.fitBytesRef 32 k)))
      (CBC.bytesToBlock (ofU8 (SignalPqxdh.fitBytesRef 16 blk)))))
  aesDecBlock k blk := toU8 (LibsignalAesCbc.blockToBytes
    (W.C.D (LibsignalAesCbc.bytesToKey (ofU8 (SignalPqxdh.fitBytesRef 32 k)))
      (CBC.bytesToBlock (ofU8 (SignalPqxdh.fitBytesRef 16 blk)))))

/-- **The PQXDH model's primitives at `(X, W)`**: `blockLevelPrims` with every derived field replaced by
the model's reference construction over the block-level fields. -/
def modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) : SignalPqxdh.Primitives :=
  let B := blockLevelPrims X W
  let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
  { B1 with
    sigVerify := SignalPqxdh.xeddsaVerifyRef B1
    isCanonical := SignalPqxdh.isCanonicalRef B1
    hkdfDerive96 := SignalPqxdh.hkdfDerive96Ref B1
    rootCreateChain := SignalPqxdh.rootCreateChainRef B1
    chainKdfSeed := SignalPqxdh.chainKdfSeedRef B1
    chainKdfNext := SignalPqxdh.chainKdfNextRef B1
    deriveMsgKeys := SignalPqxdh.deriveMsgKeysRef B1
    aeadEnc := SignalPqxdh.aes256CbcHmacEncRef B1
    aeadDec := SignalPqxdh.aes256CbcHmacDecRef B1 }

end CryptoVerification.E2E
