/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance
public import Symbolic.Specifications.Refinement.WireFormat
public import Symbolic.Specifications.Concrete.ExternInterpretation

/-!
# Term Concretization

Maps symbolic `DY.Bytes` terms of the 12-theory composed model to concrete `HwBytes` (`gamma`),
paired with each term's structural `shape` and non-opaque subterm `memo` (`gamma'`). Algebraic
constructors evaluate as transparent `node`s via `ExternInterpretation`; SPQR, KEM public keys,
non-32-byte KEM shared secrets, and signatures evaluate via `OpaqueSymbolSemantics` as `opaqueNode`s
with literal shapes `litOf v`. Kyber implicit rejection (`RejKey`) is evaluated as a transparent
`node` (`S.kemDecap (S.kemPk s.bytes) c.bytes`) so `KdfExtract` memo entries distinguish implicit
rejection from attacker-chosen byte literals.
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (encodeWith EncodingVariation WireFields FieldItem
  PbValue canonicalVariation encodeField trItemEncode honestTrItems trFields trWireBytes
  x25519PublicKeySymbol x25519AgreementSymbol aesCbcEncryptSymbol sha256CompressFunction
  torsionShift)
export DY.Libsignal.Refinement (trItemEncode honestTrItems trFields trWireBytes)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)

/-- Byte `i` of RFC 7748 scalar clamping (`b[0] &= 0xF8`, `b[31] &= 0x7F`, `b[31] |= 0x40`). -/
def clampByte (i : Nat) (b : BitVec 8) : BitVec 8 :=
  if i = 0 then b &&& 0xF8#8 else if i = 31 then (b &&& 0x7F#8) ||| 0x40#8 else b

/-- RFC 7748 scalar clamping on 32-byte scalars (identity on other lengths). -/
def clamp (k : HwBytes) : HwBytes := if k.length = 32 then k.mapIdx clampByte else k

def x25519UCoord (b : HwBytes) : Nat := DY.X25519.uCoord (b.map BitVec.toNat)

/-- `w` encoded as `n` little-endian bytes. -/
def leBytes : Nat → Nat → HwBytes
  | 0, _ => []
  | n + 1, w => BitVec.ofNat 8 w :: leBytes n (w / 256)

/-- Concrete 32-byte encoding of `x25519Variant` selector `v` applied to `b`. -/
def variantBytes (b : HwBytes) (v : Fin 4) : HwBytes :=
  if b.length = 32 then
    let u := x25519UCoord b
    let u' := if v.val / 2 = 1 ∧ u + DY.X25519.p25519 < 2 ^ 255 then u + DY.X25519.p25519 else u
    leBytes 32 (if v.val % 2 = 1 then u' + 2 ^ 255 else u')
  else b

def ofByteArray (b : ByteArray) : HwBytes := b.data.toList.map UInt8.toBitVec

/-- Symbolic literal term carrying `v`. -/
def litOf (v : HwBytes) : DY.Bytes :=
  ({ lit := ⟨(v.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack

/-- Concrete byte-level semantics for opaque symbolic primitives (SPQR transitions and keys,
Kyber-1024 public keys and decapsulation, and XEdDSA verification keys and signatures), fixed ahead
of the trace. -/
structure OpaqueSymbolSemantics where
  init : HwBytes → HwBytes → HwBytes
  chainKey : HwBytes → HwBytes → HwBytes → HwBytes
  sendState : HwBytes → HwBytes → HwBytes
  sendKey : HwBytes → HwBytes → HwBytes
  sendMsg : HwBytes → HwBytes → HwBytes
  recvState : HwBytes → HwBytes → HwBytes
  recvKey : HwBytes → HwBytes → HwBytes
  kemPk : HwBytes → HwBytes
  kemDecap : HwBytes → HwBytes → HwBytes
  vk : HwBytes → HwBytes
  sign : HwBytes → HwBytes → HwBytes → HwBytes

/-- Per-trace ghost interpretation assigning concrete bytes `σ timestamp size` to fresh `Random`
terms and protobuf field-6 `addresses` bytes `addr` to `trWireMsg` terms. -/
structure Ghost where
  σ : Nat → Nat → HwBytes
  addr : DY.Bytes → HwBytes

/-- Concretized evaluation of a symbolic term: concrete `bytes`, `shape` (with opaque subterms
replaced by `litOf` literals), and `memo` of `(subterm, shape, bytes)` for transparent subterms. -/
structure ConcretizedTerm where
  bytes : HwBytes
  shape : DY.Bytes
  memo : List (DY.Bytes × DY.Bytes × HwBytes)

section Fold

variable (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

def node (v : HwBytes) (self sh : DY.Bytes) (cs : List ConcretizedTerm) : ConcretizedTerm :=
  { bytes := v, shape := sh, memo := (self, sh, v) :: cs.flatMap (·.memo) }

def opaqueNode (v : HwBytes) (cs : List ConcretizedTerm) : ConcretizedTerm :=
  { bytes := v, shape := litOf v, memo := cs.flatMap (·.memo) }

/-- Zero-pad or truncate an SPQR message key `k` to the 32-byte HKDF salt (`[]` yields 32 zeros). -/
def spqrKeyBytes (k : HwBytes) : HwBytes := (k ++ List.replicate 32 0).take 32

def spqrKeyNode (v : HwBytes) (cs : List ConcretizedTerm) : ConcretizedTerm := opaqueNode (spqrKeyBytes v) cs

def concretizeRandom : DY.Bytes.PartialFunction DY.Random.Random ConcretizedTerm :=
  fun x _ => if x.size = 0 then { bytes := [], shape := litOf [], memo := [] }
    else node (g.σ x.timestamp x.size) x.pack x.pack []
def concretizeLit : DY.Bytes.PartialFunction DY.Literal.Literal.SubF ConcretizedTerm :=
  fun x _ => node (ofByteArray x.lit) x.pack x.pack []
def concretizeConcat : DY.Bytes.PartialFunction DY.Concat.Concat.SubF ConcretizedTerm :=
  fun x rec => let l := rec x.lhs; let r := rec x.rhs
    node (l.bytes ++ r.bytes) x.pack ({ x with lhs := l.shape, rhs := r.shape }).pack [l, r]
def concretizeDhPk : DY.Bytes.PartialFunction DY.DiffieHellman.DhPk.SubF ConcretizedTerm :=
  fun x rec => let s := rec x.sk
    node ((interpretation x25519PublicKeySymbol [clamp s.bytes]).getD []) x.pack
      ({ x with sk := s.shape }).pack [s]
def concretizeDh : DY.Bytes.PartialFunction DY.DiffieHellman.Dh.SubF ConcretizedTerm :=
  fun x rec => let p := rec x.pk; let s := rec x.sk
    node ((interpretation x25519AgreementSymbol [clamp s.bytes, p.bytes]).getD []) x.pack
      ({ x with pk := p.shape, sk := s.shape }).pack [p, s]
def concretizeKdf : DY.Bytes.PartialFunction DY.KdfExtract.KdfExtract.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.salt; let b := rec x.ikm
    node (hmacWith (sha256CompressFunction interpretation) a.bytes b.bytes) x.pack
      ({ x with salt := a.shape, ikm := b.shape }).pack [a, b]
def concretizeSym : DY.Bytes.PartialFunction DY.SymEnc.Enc.SubF ConcretizedTerm :=
  fun x rec =>
    let k := rec x.key; let i := rec x.iv; let m := rec x.msg
    node ((interpretation aesCbcEncryptSymbol [m.bytes, k.bytes, i.bytes.take 16]).getD []) x.pack
      ({ x with key := k.shape, iv := i.shape, msg := m.shape }).pack [k, i, m]
def concretizeTrunc : DY.Bytes.PartialFunction DY.Trunc.Trunc8.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.input
    node (a.bytes.take 8) x.pack ({ x with input := a.shape }).pack [a]
def concretizeVariant : DY.Bytes.PartialFunction DY.X25519.Variant.SubF ConcretizedTerm :=
  fun x rec => let k := rec x.key
    node (variantBytes (torsionShift interpretation k.bytes x.torsion) x.variation) x.pack
      ({ x with key := k.shape }).pack [k]
def concretizeTrWire : DY.Bytes.PartialFunction DY.TrWire.TrWireMsg.SubF ConcretizedTerm :=
  fun x rec =>
    let rk := rec x.senderRatchetKey; let ct := rec x.ciphertext; let pq := rec x.pqRatchet
    let ev := { x.encodingVariation with
      fields := .extra 6 (.bytes (g.addr x.pack)) 0 0 :: x.encodingVariation.fields }
    node (trWireBytes (g.addr x.pack) x.encodingVariation
        { version := x.version.toNat, ratchetKey := rk.bytes, counter := x.counter.toNat,
          previousCounter := x.previousCounter.toNat, ciphertext := ct.bytes } pq.bytes)
      x.pack
      ({ x with senderRatchetKey := rk.shape, ciphertext := ct.shape, pqRatchet := pq.shape,
                encodingVariation := ev }).pack
      [rk, ct, pq]

def concretizeKemPk : DY.Bytes.PartialFunction DY.PQKem.Pk.SubF ConcretizedTerm :=
  fun x rec => let s := rec x.sk; opaqueNode (S.kemPk s.bytes) [s]
def concretizeKemEncap : DY.Bytes.PartialFunction DY.PQKem.Encap.SubF ConcretizedTerm :=
  fun x rec =>
    let p := rec x.pk; let e := rec x.entropy
    if e.bytes.length = 32 then
      node (((interpretation kyberEncapsSymbol [p.bytes, e.bytes]).getD []).take 1568)
        x.pack ({ x with pk := p.shape, entropy := e.shape }).pack [p, e]
    else opaqueNode [] [p, e]
def concretizeKemSS : DY.Bytes.PartialFunction DY.PQKem.SharedSecret.SubF ConcretizedTerm :=
  fun x rec =>
    let p := rec x.pk; let e := rec x.entropy
    if e.bytes.length = 32 then
      node (((interpretation kyberEncapsSymbol [p.bytes, e.bytes]).getD []).drop 1568)
        x.pack ({ x with pk := p.shape, entropy := e.shape }).pack [p, e]
    else opaqueNode (S.kemDecap p.bytes e.bytes) [p, e]
def concretizeKemRej : DY.Bytes.PartialFunction DY.PQKem.RejKey.SubF ConcretizedTerm :=
  fun x rec =>
    let s := rec x.sk; let c := rec x.cipher
    node (S.kemDecap (S.kemPk s.bytes) c.bytes)
      x.pack ({ x with sk := s.shape, cipher := c.shape }).pack [s, c]
def concretizeVk : DY.Bytes.PartialFunction DY.Signature.Vk.SubF ConcretizedTerm :=
  fun x rec => let s := rec x.sk; opaqueNode (S.vk s.bytes) [s]
def concretizeSign : DY.Bytes.PartialFunction DY.Signature.Sign.SubF ConcretizedTerm :=
  fun x rec => let s := rec x.sk; let n := rec x.nonce; let m := rec x.msg
    opaqueNode (S.sign s.bytes n.bytes m.bytes) [s, n, m]
def concretizeSpqrInit : DY.Bytes.PartialFunction DY.Spqr.InitState.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.authKey; let p := rec x.params; opaqueNode (S.init a.bytes p.bytes) [a, p]
def concretizeSpqrSendState : DY.Bytes.PartialFunction DY.Spqr.SendState.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.st; let b := rec x.coins; opaqueNode (S.sendState a.bytes b.bytes) [a, b]
def concretizeSpqrSendKey : DY.Bytes.PartialFunction DY.Spqr.SendKey.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.st; let b := rec x.coins; spqrKeyNode (S.sendKey a.bytes b.bytes) [a, b]
def concretizeSpqrSendMsg : DY.Bytes.PartialFunction DY.Spqr.SendMsg.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.st; let b := rec x.coins; opaqueNode (S.sendMsg a.bytes b.bytes) [a, b]
def concretizeSpqrRecvState : DY.Bytes.PartialFunction DY.Spqr.RecvState.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.st; let b := rec x.msg; opaqueNode (S.recvState a.bytes b.bytes) [a, b]
def concretizeSpqrRecvKey : DY.Bytes.PartialFunction DY.Spqr.RecvKey.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.st; let b := rec x.msg; spqrKeyNode (S.recvKey a.bytes b.bytes) [a, b]
def concretizeSpqrChainKey : DY.Bytes.PartialFunction DY.Spqr.ChainKey.SubF ConcretizedTerm :=
  fun x rec => let a := rec x.authKey; let p := rec x.params; let i := rec x.idx
    spqrKeyNode (S.chainKey a.bytes p.bytes i.bytes) [a, p, i]

def litFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Literal.SubF.internal id) ConcretizedTerm
  | 0 => concretizeLit
def concatFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Concat.SubF.internal id) ConcretizedTerm
  | 0 => concretizeConcat
def dhFuns : (id : Fin 2) → DY.Bytes.PartialFunction (DY.DiffieHellman.SubF.internal id) ConcretizedTerm
  | 0 => concretizeDhPk interpretation
  | 1 => concretizeDh interpretation
def kdfFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.KdfExtract.SubF.internal id) ConcretizedTerm
  | 0 => concretizeKdf interpretation
def symFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.SymEnc.SubF.internal id) ConcretizedTerm
  | 0 => concretizeSym interpretation
def truncFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.Trunc.SubF.internal id) ConcretizedTerm
  | 0 => concretizeTrunc
def x25519Funs : (id : Fin 1) → DY.Bytes.PartialFunction (DY.X25519.SubF.internal id) ConcretizedTerm
  | 0 => concretizeVariant interpretation
def kemFuns : (id : Fin 4) → DY.Bytes.PartialFunction (DY.PQKem.SubF.internal id) ConcretizedTerm
  | 0 => concretizeKemPk S
  | 1 => concretizeKemEncap interpretation
  | 2 => concretizeKemSS interpretation S
  | 3 => concretizeKemRej S
def sigFuns : (id : Fin 2) → DY.Bytes.PartialFunction (DY.Signature.SubF.internal id) ConcretizedTerm
  | 0 => concretizeVk S
  | 1 => concretizeSign S
def spqrFuns : (id : Fin 7) → DY.Bytes.PartialFunction (DY.Spqr.SubF.internal id) ConcretizedTerm
  | 0 => concretizeSpqrInit S
  | 1 => concretizeSpqrSendState S
  | 2 => concretizeSpqrSendKey S
  | 3 => concretizeSpqrSendMsg S
  | 4 => concretizeSpqrRecvState S
  | 5 => concretizeSpqrRecvKey S
  | 6 => concretizeSpqrChainKey S
def trWireFuns : (id : Fin 1) → DY.Bytes.PartialFunction (DY.TrWire.SubF.internal id) ConcretizedTerm
  | 0 => concretizeTrWire g

def allFuns : (id : Fin 12) →
    DY.Bytes.PartialFunction (DY.Libsignal.Composed.SubF.internal id) ConcretizedTerm
  | 0 => concretizeRandom g
  | 1 => DY.Bytes.PartialFunction.combine litFuns
  | 2 => DY.Bytes.PartialFunction.combine concatFuns
  | 3 => DY.Bytes.PartialFunction.combine (dhFuns interpretation)
  | 4 => DY.Bytes.PartialFunction.combine (kdfFuns interpretation)
  | 5 => DY.Bytes.PartialFunction.combine (symFuns interpretation)
  | 6 => DY.Bytes.PartialFunction.combine truncFuns
  | 7 => DY.Bytes.PartialFunction.combine (x25519Funs interpretation)
  | 8 => DY.Bytes.PartialFunction.combine (kemFuns interpretation S)
  | 9 => DY.Bytes.PartialFunction.combine (sigFuns S)
  | 10 => DY.Bytes.PartialFunction.combine (spqrFuns S)
  | 11 => DY.Bytes.PartialFunction.combine (trWireFuns g)

def concretizeAll : DY.Bytes.Function ConcretizedTerm := DY.Bytes.PartialFunction.combine (allFuns interpretation S g)

/-- Concretization of `b` returning `(bytes, shape, memo)`. -/
def gamma' (b : DY.Bytes) : ConcretizedTerm := b.rec (concretizeAll interpretation S g)

/-- Concrete `HwBytes` of symbolic term `b`. -/
def gamma (b : DY.Bytes) : HwBytes := (gamma' interpretation S g b).bytes

end Fold

end DY.Libsignal.Composed.Refinement
