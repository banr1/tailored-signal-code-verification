/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Game
public import ToMathlib.MeasureTheory.DiscreteInstances
public import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.ModelProofDefs
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Concrete Well-Formed PQXDH Primitives

Concrete toy `Primitives` instances (`idealRoundtripPrimitives` and `cwfPrimitives`) witnessing
`WellFormedPrimitives` and the KEM public-key collision bound without importing test modules.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace SpecTests.SignalPqxdh

open _root_.SignalPqxdh

@[simp] theorem fitBytes_length (n : Nat) (bs : Bytes) : (fitBytes n bs).length = n := by
  simp [fitBytes]
  omega

theorem fitBytes_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) : fitBytes n bs = bs := by
  subst h
  simp [fitBytes]

def clamp32 (bs : Bytes) : Bytes :=
  (fitBytes 32 bs).map (fun b => b &&& 0x7F)

def isCanonical32 (pk : Bytes) : Bool :=
  pk.length == 32 && scalarIsInRange pk

def reduceCanon32 (bs : Bytes) : Bytes :=
  if isCanonical32 bs then bs else clamp32 bs

theorem xorBytes_comm (a b : Bytes) : xorBytes a b = xorBytes b a := by
  unfold xorBytes
  induction a generalizing b with
  | nil =>
    cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp [List.zipWith, UInt8.xor_comm, ih ys]

def testPrimitivesBase : Primitives where
  x25519 := fun sk pk => xorBytes (clamp32 sk) (clamp32 pk)
  x25519Base := clamp32
  isCanonical := isCanonical32
  sigPkGen := clamp32
  sigSign := fun sk msg _rand =>
    clamp32 (xorBytes (clamp32 msg) (clamp32 sk)) ++ List.replicate 32 0
  sigVerify := fun _ _ _ => false
  sha512 := fun m => clamp32 (m.drop 64) ++ List.replicate 32 0
  scalarMul := fun a b => xorBytes (clamp32 a) (clamp32 b)
  scalarAdd := fun a b => xorBytes (clamp32 a) (clamp32 b)
  scalarFromBytesModOrder := clamp32
  scalarFromWide := fun b => clamp32 (b.take 32)
  montToEd := fun u s =>
    if s == 0 && isCanonical32 u then some (u ++ List.replicate 128 0) else none
  isTorsionFree := fun pt => isCanonical32 (pt.take 32)
  edNeg := fun pt => fitBytes 160 (clamp32 (pt.take 32))
  doubleScalarMulBasepoint := fun h a _s =>
    fitBytes 160 (clamp32 (xorBytes (clamp32 h) (clamp32 (a.take 32))))
  compress := fun pt => clamp32 (pt.take 32)
  kemKeyGen := fun seed => (fitBytes 1568 (seed.take 32), fitBytes 3168 seed)
  kemEncaps := fun pk coins =>
    some (fitBytes 32 (pk.take 4 ++ coins.take 4),
          fitBytes kyberCtLen ([0xC0, 0x01] ++ fitBytes 4 pk ++ fitBytes 4 coins))
  kemDecaps := fun sk ct =>
    if ct.length == kyberCtLen && ct.take 2 == [0xC0, 0x01] then
      some (fitBytes 32 (fitBytes 4 sk ++ (ct.drop 6).take 4))
    else none
  hkdfDerive96 := fun secrets =>
    let body := secrets.drop 32
    { rootKey  := [0x10] ++ body
    , chainKey := [0x20] ++ body
    , pqrKey   := [0x30] ++ body }
  rootCreateChain := fun rk0 dh =>
    ([0x41] ++ rk0 ++ dh, [0x42] ++ rk0 ++ dh)
  chainKdfSeed := fun ck => ck ++ [0x01]
  chainKdfNext := fun ck => ck ++ [0x02]
  spqrInitSend := fun pqrKey coins =>
    some (pqrKey ++ coins, some (pqrKey ++ [0x51]), [0x52] ++ coins)
  spqrInitRecv := fun pqrKey pqMsg =>
    if pqMsg.take 1 == [0x52] then
      some (pqrKey ++ pqMsg.drop 1, some (pqrKey ++ [0x51]))
    else none
  deriveMsgKeys := fun seed salt? =>
    let s := salt?.getD []
    { cipherKey := [0x61] ++ seed ++ s
    , macKey    := [0x62] ++ seed ++ s
    , iv        := [0x63] ++ s }
  aeadEnc := fun mk ad pt =>
    mk.cipherKey ++ ad ++ [0xEE] ++ pt
  aeadDec := fun mk ad ct =>
    let pfx := mk.cipherKey ++ ad ++ [0xEE]
    if ct.take pfx.length == pfx then some (ct.drop pfx.length) else none
  sha256Compress := fun st blk => fitBytes 32 (xorBytes (fitBytes 32 st) (fitBytes 32 blk))
  sha512Compress := fun st blk => fitBytes 64 (xorBytes (fitBytes 64 st) (fitBytes 64 blk))
  aesEncBlock := fun k blk => xorBytes (fitBytes 16 k) (fitBytes 16 blk)
  aesDecBlock := fun k blk => xorBytes (fitBytes 16 k) (fitBytes 16 blk)
  pow8 := reduceCanon32
  isValidDhTriple := fun x y z =>
    reduceCanon32 z == reduceCanon32 (xorBytes (clamp32 x) (clamp32 y))

/-- Clamps a byte to bits 3–4 with bit 3 set (`(b &&& 0x18) ||| 0x08`), invariant under RFC 7748
scalar clamping, non-zero, and canonical (`< 237`). -/
def clampIdealByte (b : UInt8) : UInt8 :=
  (b &&& 0x18) ||| 0x08

def clampIdeal32 (bs : Bytes) : Bytes :=
  (fitBytes 32 bs).map clampIdealByte

def reduceCanonIdeal32 (bs : Bytes) : Bytes :=
  if isCanonical32 bs then bs else clampIdeal32 bs

def idealX25519 (sk pk : Bytes) : Bytes :=
  clampIdeal32 (xorBytes (clampIdeal32 sk) (clampIdeal32 pk))

theorem clampIdealByte_idem (b : UInt8) :
    clampIdealByte (clampIdealByte b) = clampIdealByte b := by
  revert b; decide

theorem clampIdealByte_and_7f (b : UInt8) :
    clampIdealByte b &&& 0x7F = clampIdealByte b := by
  revert b; decide

theorem clampIdealByte_and_80 (b : UInt8) :
    clampIdealByte b &&& 0x80 = 0 := by
  revert b; decide

theorem clampIdeal32_length (bs : Bytes) : (clampIdeal32 bs).length = 32 := by
  simp [clampIdeal32, fitBytes_length]

theorem map_clampIdealByte_idem (bs : Bytes) :
    (bs.map clampIdealByte).map clampIdealByte = bs.map clampIdealByte := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [clampIdealByte_idem, ih]

theorem clampIdeal32_idem (bs : Bytes) : clampIdeal32 (clampIdeal32 bs) = clampIdeal32 bs := by
  unfold clampIdeal32
  rw [fitBytes_of_length_eq (by simp [fitBytes_length])]
  exact map_clampIdealByte_idem (fitBytes 32 bs)

theorem getD_31_clampIdeal32_and_80 (bs : Bytes) :
    ((clampIdeal32 bs).getD 31 0 &&& 0x80) = 0 := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 31 < (fitBytes 32 bs).length := by omega
  unfold clampIdeal32
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  exact clampIdealByte_and_80 _

def idealLeafPrimitives : Primitives :=
  { testPrimitivesBase with
    x25519 := idealX25519
    x25519Base := clampIdeal32
    isCanonical := isCanonical32
    sigPkGen := clampIdeal32
    sigSign := fun sk msg _rand =>
      let r := clampIdeal32 (xorBytes (clampIdeal32 msg) (clampIdeal32 sk))
      r ++ r
    scalarMul := fun a b => xorBytes (clampIdeal32 a) (clampIdeal32 b)
    scalarAdd := fun a b => xorBytes (clampIdeal32 a) (clampIdeal32 b)
    scalarFromBytesModOrder := clampIdeal32
    scalarFromWide := fun b => clampIdeal32 (b.take 32)
    montToEd := fun u s =>
      if s == 0 && isCanonical32 u then some (u ++ List.replicate 128 0) else none
    isTorsionFree := fun pt => isCanonical32 (pt.take 32)
    edNeg := fun pt => fitBytes 160 (clampIdeal32 (pt.take 32))
    doubleScalarMulBasepoint := fun _h _a s => fitBytes 160 (clampIdeal32 s)
    compress := fun pt => clampIdeal32 (pt.take 32)
    kemKeyGen := fun seed => (fitBytes 1568 (seed.take 32), fitBytes 3168 seed)
    kemEncaps := fun _pk coins =>
      let ss := fitBytes 32 coins
      some (ss, ss ++ List.replicate 1536 0)
    kemDecaps := fun _sk ct => some (fitBytes 32 (ct.take 32))
    spqrInitSend := fun pqrKey coins => some (pqrKey, some (fitBytes 32 pqrKey), coins)
    spqrInitRecv := fun pqrKey _pqMsg => some (pqrKey, some (fitBytes 32 pqrKey))
    sha256Compress := fun st blk => fitBytes 32 (xorBytes (fitBytes 32 st) (fitBytes 32 blk))
    sha512Compress := fun st blk => fitBytes 64 (xorBytes (fitBytes 64 st) (fitBytes 64 blk))
    aesEncBlock := fun k blk => xorBytes (fitBytes 16 k) (fitBytes 16 blk)
    aesDecBlock := fun k blk => xorBytes (fitBytes 16 k) (fitBytes 16 blk)
    pow8 := reduceCanonIdeal32
    isValidDhTriple := fun x y z =>
      (clampIdeal32 x == x || clampIdeal32 y == y) &&
        reduceCanonIdeal32 z == reduceCanonIdeal32 (idealX25519 x y) }

/-- Ideal roundtrip primitives with composite KDF, AEAD, SHA-512, and XEdDSA fields tied to their
`Model` reference constructions over `idealLeafPrimitives`. -/
def idealRoundtripPrimitives : Primitives :=
  let P1 : Primitives := { idealLeafPrimitives with
    sha512          := sha512Ref idealLeafPrimitives
    hkdfDerive96    := hkdfDerive96Ref idealLeafPrimitives
    rootCreateChain := rootCreateChainRef idealLeafPrimitives
    chainKdfSeed    := chainKdfSeedRef idealLeafPrimitives
    chainKdfNext    := chainKdfNextRef idealLeafPrimitives
    deriveMsgKeys   := deriveMsgKeysRef idealLeafPrimitives
    aeadEnc         := aes256CbcHmacEncRef idealLeafPrimitives
    aeadDec         := aes256CbcHmacDecRef idealLeafPrimitives }
  { P1 with sigVerify := xeddsaVerifyRef P1 }

theorem clampIdealByte_and_60 (b : UInt8) :
    clampIdealByte b &&& 0x60 = 0 := by
  revert b; decide

theorem getD_31_clampIdeal32_and_60 (bs : Bytes) :
    ((clampIdeal32 bs).getD 31 0 &&& 0x60) = 0 := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 31 < (fitBytes 32 bs).length := by omega
  unfold clampIdeal32
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  exact clampIdealByte_and_60 _

theorem clampIdeal32_clamped31 (bs : Bytes) :
    clampIdeal32 ((clampIdeal32 bs).take 31 ++ [(clampIdeal32 bs).getD 31 0 &&& 0x7F]) =
      clampIdeal32 bs := by
  have hlen : (fitBytes 32 bs).length = 32 := fitBytes_length 32 bs
  have hlt : 31 < (fitBytes 32 bs).length := by omega
  have h7f : (clampIdeal32 bs).getD 31 0 &&& 0x7F = (clampIdeal32 bs).getD 31 0 := by
    unfold clampIdeal32
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.getD_some]
    exact clampIdealByte_and_7f _
  rw [h7f]
  have hclLen : (clampIdeal32 bs).length = 32 := clampIdeal32_length bs
  have hdrop31 : (clampIdeal32 bs).drop 31 = [(clampIdeal32 bs).getD 31 0] := by
    have hcons := List.drop_eq_getElem_cons (by omega : 31 < (clampIdeal32 bs).length)
    have hdrop32 : (clampIdeal32 bs).drop (31 + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : 31 < (clampIdeal32 bs).length)]
    simp only [Option.getD_some]
    rw [hcons, hdrop32]
  rw [← hdrop31, List.take_append_drop]
  exact clampIdeal32_idem bs

private theorem xorByte_comm_cancel_left (x y : UInt8) : x ^^^ (x ^^^ y) = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      apply congrArg UInt8.ofBitVec
      change bx ^^^ (bx ^^^ by_) = by_
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem xorBytes_cancel_left (a b : Bytes) (h : a.length = b.length) :
    xorBytes a (xorBytes a b) = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [xorBytes, List.zipWith_cons_cons, xorByte_comm_cancel_left]
      congr 1
      exact ih ys h

theorem idealAesBlock_corr (k blk : Bytes) (_hk : k.length = 32) (hb : blk.length = 16) :
    idealRoundtripPrimitives.aesDecBlock k (idealRoundtripPrimitives.aesEncBlock k blk) = blk := by
  dsimp only [idealRoundtripPrimitives, idealLeafPrimitives]
  have h16k : (fitBytes 16 k).length = 16 := fitBytes_length 16 k
  have h16b : fitBytes 16 blk = blk := fitBytes_of_length_eq hb
  rw [h16b]
  have hxorLen : (xorBytes (fitBytes 16 k) blk).length = 16 := by
    rw [xorBytes_length, h16k, hb, Nat.min_self]
  rw [fitBytes_of_length_eq hxorLen]
  exact xorBytes_cancel_left (fitBytes 16 k) blk (by rw [h16k, hb])

def cwfMask (i : Nat) : UInt8 := if i = 0 then 0xF8 else if i = 31 then 0x3F else 0xFF

def cwfFix (i : Nat) : UInt8 := if i = 0 then 0x01 else 0x00

def cwfByte (i : Nat) (b : UInt8) : UInt8 := (b &&& cwfMask i) ||| cwfFix i

/-- Projects a byte string to 32 canonical bytes preserving RFC 7748 clamped bits (size-32 fibres
over uniform 32-byte inputs). -/
def cwfC (bs : Bytes) : Bytes :=
  List.ofFn (fun i : Fin 32 => cwfByte i.val ((fitBytes 32 bs).getD i.val 0))

theorem cwfByte_cases (i : Nat) :
    (cwfMask i = 0xF8 ∧ cwfFix i = 0x01) ∨ (cwfMask i = 0x3F ∧ cwfFix i = 0) ∨
      (cwfMask i = 0xFF ∧ cwfFix i = 0) := by
  unfold cwfMask cwfFix; by_cases h0 : i = 0 <;> by_cases h31 : i = 31 <;> simp_all

theorem cwfByte_idem (i : Nat) (b : UInt8) : cwfByte i (cwfByte i b) = cwfByte i b := by
  unfold cwfByte
  rcases cwfByte_cases i with ⟨hm, hf⟩ | ⟨hm, hf⟩ | ⟨hm, hf⟩ <;> rw [hm, hf] <;> revert b <;> decide

theorem cwfByte_mask (i : Nat) (b : UInt8) : cwfByte i b &&& cwfMask i = b &&& cwfMask i := by
  unfold cwfByte
  rcases cwfByte_cases i with ⟨hm, hf⟩ | ⟨hm, hf⟩ | ⟨hm, hf⟩ <;> rw [hm, hf] <;> revert b <;> decide

theorem uint8_and_xor (a b m : UInt8) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply UInt8.toBitVec_inj.1
  show (a.toBitVec ^^^ b.toBitVec) &&& m.toBitVec =
    (a.toBitVec &&& m.toBitVec) ^^^ (b.toBitVec &&& m.toBitVec)
  ext j hj
  simp only [BitVec.getElem_and, BitVec.getElem_xor]
  cases a.toBitVec[j] <;> cases b.toBitVec[j] <;> cases m.toBitVec[j] <;> rfl

theorem cwfByte_eq_iff (i : Nat) (a b : UInt8) :
    cwfByte i a = cwfByte i b ↔ a &&& cwfMask i = b &&& cwfMask i := by
  constructor
  · intro h; rw [← cwfByte_mask i a, ← cwfByte_mask i b, h]
  · intro h; unfold cwfByte; rw [h]

theorem cwfByte_xor_inj (i : Nat) (x p q : UInt8) (h : cwfByte i (x ^^^ p) = cwfByte i (x ^^^ q)) :
    cwfByte i p = cwfByte i q := by
  rw [cwfByte_eq_iff, uint8_and_xor, uint8_and_xor, UInt8.xor_right_inj] at h
  exact (cwfByte_eq_iff i p q).2 h

theorem cwfC_length (bs : Bytes) : (cwfC bs).length = 32 := by simp [cwfC]

theorem cwfC_getD (bs : Bytes) (i : Nat) (hi : i < 32) :
    (cwfC bs).getD i 0 = cwfByte i ((fitBytes 32 bs).getD i 0) := by
  unfold cwfC
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi)]
  simp only [List.getElem_ofFn, Option.getD_some]

theorem bytes32_ext {a b : Bytes} (ha : a.length = 32) (hb : b.length = 32)
    (h : ∀ i, i < 32 → a.getD i 0 = b.getD i 0) : a = b := by
  apply List.ext_getElem (by rw [ha, hb])
  intro i h1 h2
  have := h i (by omega)
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem cwfC_idem (bs : Bytes) : cwfC (cwfC bs) = cwfC bs := by
  apply bytes32_ext (cwfC_length _) (cwfC_length _)
  intro i hi
  rw [cwfC_getD _ i hi, fitBytes_of_length_eq (cwfC_length _), cwfC_getD _ i hi, cwfByte_idem]

theorem cwfC_ne_zero (bs : Bytes) : cwfC bs ≠ List.replicate 32 0 := by
  intro h
  have h0 := congrArg (fun xs : Bytes => xs.getD 0 0) h
  rw [cwfC_getD _ 0 (by omega)] at h0
  change cwfByte 0 _ = (0 : UInt8) at h0
  revert h0; generalize (fitBytes 32 bs).getD 0 0 = b; revert b
  unfold cwfByte cwfMask cwfFix; decide

def cwfClampByte (i : Nat) (b : UInt8) : UInt8 :=
  if i = 0 then b &&& 0xF8 else if i = 31 then (b &&& 0x7F) ||| 0x40 else b

theorem clampScalar25519_getD (sk : Bytes) (i : Nat) (hi : i < 32) :
    (clampScalar25519 sk).getD i 0 = cwfClampByte i ((fitBytes 32 sk).getD i 0) := by
  have hr : fitBytesRef 32 sk = fitBytes 32 sk := rfl
  have hs := fitBytes_length 32 sk
  simp only [clampScalar25519, hr]
  generalize fitBytes 32 sk = s at hs ⊢
  interval_cases i <;>
    simp [cwfClampByte, List.getD_eq_getElem?_getD, hs]

theorem cwfByte_clampByte (i : Nat) (b : UInt8) : cwfByte i (cwfClampByte i b) = cwfByte i b := by
  unfold cwfByte cwfClampByte cwfMask cwfFix
  by_cases h0 : i = 0
  · simp only [h0, ↓reduceIte]; revert b; decide
  · by_cases h31 : i = 31
    · simp only [h31, ↓reduceIte]; revert b; decide
    · simp only [h0, h31, ↓reduceIte]

theorem cwfC_clamp (sk : Bytes) : cwfC (clampScalar25519 sk) = cwfC sk := by
  apply bytes32_ext (cwfC_length _) (cwfC_length _)
  intro i hi
  rw [cwfC_getD _ i hi, cwfC_getD _ i hi, fitBytes_of_length_eq (clampScalar25519_length sk),
    clampScalar25519_getD sk i hi, cwfByte_clampByte]

def cwfX25519 (sk pk : Bytes) : Bytes := cwfC (xorBytes (cwfC sk) (cwfC pk))

def cwfCanon (pk : Bytes) : Bool := pk.length == 32 && cwfC pk == pk

theorem cwfX25519_comm (a b : Bytes) : cwfX25519 a b = cwfX25519 b a := by
  unfold cwfX25519; rw [xorBytes_comm]

theorem cwfX25519_idem_left (a pk : Bytes) : cwfX25519 (cwfC a) pk = cwfX25519 a pk := by
  unfold cwfX25519; rw [cwfC_idem]

theorem cwfX25519_idem_right (a pk : Bytes) : cwfX25519 a (cwfC pk) = cwfX25519 a pk := by
  unfold cwfX25519; rw [cwfC_idem]

theorem cwfCanon_cwfC (bs : Bytes) : cwfCanon (cwfC bs) = true := by
  simp [cwfCanon, cwfC_length, cwfC_idem]

theorem cwfCanon_spec {pk : Bytes} (h : cwfCanon pk = true) : pk.length = 32 ∧ cwfC pk = pk := by
  simpa [cwfCanon] using h

theorem xorBytes_getD (a b : Bytes) (i : Nat) (ha : i < a.length) (hb : i < b.length) :
    (xorBytes a b).getD i 0 = a.getD i 0 ^^^ b.getD i 0 := by
  simp [xorBytes, List.getD_eq_getElem?_getD, ha, hb]

theorem cwfX25519_inj (a pk1 pk2 : Bytes) (h : cwfX25519 a pk1 = cwfX25519 a pk2) :
    cwfC pk1 = cwfC pk2 := by
  apply bytes32_ext (cwfC_length _) (cwfC_length _)
  intro i hi
  have hi' := congrArg (fun xs : Bytes => xs.getD i 0) h
  simp only [cwfX25519] at hi'
  have hl1 : (xorBytes (cwfC a) (cwfC pk1)).length = 32 := by simp [cwfC_length]
  have hl2 : (xorBytes (cwfC a) (cwfC pk2)).length = 32 := by simp [cwfC_length]
  rw [cwfC_getD _ i hi, cwfC_getD _ i hi, fitBytes_of_length_eq hl1, fitBytes_of_length_eq hl2,
    xorBytes_getD _ _ i (by rw [cwfC_length]; exact hi) (by rw [cwfC_length]; exact hi),
    xorBytes_getD _ _ i (by rw [cwfC_length]; exact hi) (by rw [cwfC_length]; exact hi)] at hi'
  have := cwfByte_xor_inj i _ _ _ hi'
  rw [cwfC_getD _ i hi, cwfC_getD _ i hi] at this ⊢
  rw [← cwfC_getD _ i hi, ← cwfC_getD _ i hi] at this
  rw [← cwfC_getD _ i hi, ← cwfC_getD _ i hi]
  have e1 : (cwfC pk1).getD i 0 = cwfByte i ((fitBytes 32 (cwfC pk1)).getD i 0) := by
    rw [← cwfC_getD _ i hi, cwfC_idem]
  have e2 : (cwfC pk2).getD i 0 = cwfByte i ((fitBytes 32 (cwfC pk2)).getD i 0) := by
    rw [← cwfC_getD _ i hi, cwfC_idem]
  rw [fitBytes_of_length_eq (cwfC_length _)] at e1 e2
  rw [e1, e2]; exact this

def cwfZero : Bytes := List.replicate 32 0

def cwfGood (p : Bytes) : Bool := p.length == 32 && p != cwfZero

def cwfP8 (p : Bytes) : Bytes := if cwfGood p then cwfC p else cwfZero

def cwfX (sk pk : Bytes) : Bytes := if cwfGood pk then cwfX25519 sk pk else cwfZero

def cwfDh (x y : Bytes) : Bytes := if cwfGood x && cwfGood y then cwfX25519 x y else cwfZero

theorem cwfGood_cwfC (bs : Bytes) : cwfGood (cwfC bs) = true := by
  simpa [cwfGood, cwfC_length, cwfZero] using cwfC_ne_zero bs

theorem cwfGood_len {p : Bytes} (h : cwfGood p = true) : p.length = 32 := by
  simp only [cwfGood, Bool.and_eq_true, beq_iff_eq] at h; exact h.1

theorem cwfP8_cwfC (bs : Bytes) : cwfP8 (cwfC bs) = cwfC bs := by
  simp [cwfP8, cwfGood_cwfC, cwfC_idem]

theorem cwfP8_bad {p : Bytes} (h : cwfGood p = false) : cwfP8 p = cwfZero := by
  simp [cwfP8, h]

theorem cwfP8_good {p : Bytes} (h : cwfGood p = true) : cwfP8 p = cwfC p := by
  simp [cwfP8, h]

theorem cwfGood_zero : cwfGood cwfZero = false := by
  simp [cwfGood]

theorem cwfP8_idem (p : Bytes) : cwfP8 (cwfP8 p) = cwfP8 p := by
  cases h : cwfGood p
  · rw [cwfP8_bad h, cwfP8_bad cwfGood_zero]
  · rw [cwfP8_good h, cwfP8_cwfC]

theorem cwfP8_length (p : Bytes) : (cwfP8 p).length = 32 := by
  unfold cwfP8; split <;> simp [cwfC_length, cwfZero]

theorem cwfGood_of_P8_eq {p q : Bytes} (h : cwfP8 p = cwfP8 q) : cwfGood p = cwfGood q := by
  cases hp : cwfGood p <;> cases hq : cwfGood q <;> try rfl
  · rw [cwfP8_bad hp, cwfP8_good hq] at h; exact absurd h.symm (cwfC_ne_zero _)
  · rw [cwfP8_good hp, cwfP8_bad hq] at h; exact absurd h (cwfC_ne_zero _)

theorem cwfX_ne_zero_of_good {sk pk : Bytes} (h : cwfGood pk = true) : cwfX sk pk ≠ cwfZero := by
  simp only [cwfX, h, ite_true, cwfX25519]; exact cwfC_ne_zero _

theorem cwfX_cwfC (sk bs : Bytes) : cwfX sk (cwfC bs) = cwfX25519 sk bs := by
  simp [cwfX, cwfGood_cwfC, cwfX25519_idem_right]

theorem cwfX_pow8_congr (a pk1 pk2 : Bytes) (h : cwfP8 pk1 = cwfP8 pk2) :
    cwfX a pk1 = cwfX a pk2 := by
  have hg := cwfGood_of_P8_eq h
  unfold cwfX
  cases hp : cwfGood pk1
  · rw [← hg, hp]; rfl
  · rw [← hg, hp]
    simp only [ite_true]
    rw [cwfP8_good hp, cwfP8_good (hg ▸ hp)] at h
    rw [← cwfX25519_idem_right a pk1, h, cwfX25519_idem_right]

theorem cwfX_inj (a pk1 pk2 : Bytes) (h : cwfX a pk1 = cwfX a pk2) : cwfP8 pk1 = cwfP8 pk2 := by
  cases h1 : cwfGood pk1 <;> cases h2 : cwfGood pk2
  · rw [cwfP8_bad h1, cwfP8_bad h2]
  · exact absurd (h.symm.trans (by simp [cwfX, h1])) (cwfX_ne_zero_of_good h2)
  · exact absurd (h.trans (by simp [cwfX, h2])) (cwfX_ne_zero_of_good h1)
  · rw [cwfP8_good h1, cwfP8_good h2]
    simp only [cwfX, h1, h2, ite_true] at h
    exact cwfX25519_inj a pk1 pk2 h

theorem cwfX_length (sk pk : Bytes) : (cwfX sk pk).length = 32 := by
  unfold cwfX cwfX25519; split <;> simp [cwfC_length, cwfZero]

theorem cwfX_zero_iff (sk pk : Bytes) : cwfX sk pk = List.replicate 32 0 ↔ cwfGood pk = false := by
  cases h : cwfGood pk
  · simp [cwfX, h, cwfZero]
  · simpa [cwfZero] using cwfX_ne_zero_of_good (sk := sk) h

theorem cwfDh_cwfC_left (a pk : Bytes) : cwfDh (cwfC a) pk = cwfX a pk := by
  unfold cwfDh cwfX
  cases cwfGood pk <;> simp [cwfGood_cwfC, cwfX25519_idem_left]

theorem cwfDh_comm (x y : Bytes) : cwfDh x y = cwfDh y x := by
  unfold cwfDh; rw [Bool.and_comm, cwfX25519_comm]

def cwfLeafPrimitives : Primitives :=
  { idealLeafPrimitives with
    x25519 := cwfX
    x25519Base := cwfC
    isCanonical := cwfCanon
    sigPkGen := cwfC
    montToEd := fun u s => if s == 0 && cwfCanon u then some (u ++ List.replicate 128 0) else none
    isTorsionFree := fun pt => cwfCanon (pt.take 32)
    kemEncaps := fun pk coins =>
      if pk.length == kyberPkLen then
        let ss := fitBytes 32 coins
        some (ss, ss ++ List.replicate 1536 0)
      else none
    kemDecaps := fun _sk ct =>
      if ct.length == kyberCtLen then some (fitBytes 32 (ct.take 32)) else none
    pow8 := cwfP8
    isValidDhTriple := fun x y z =>
      cwfGood x && cwfGood y && (cwfC x == x || cwfC y == y) && cwfP8 z == cwfP8 (cwfDh x y) }

/-- Concrete `CryptoWellFormedPrimitives` witness over `cwfLeafPrimitives`. -/
def cwfPrimitives : Primitives :=
  let P1 : Primitives := { cwfLeafPrimitives with
    sha512          := sha512Ref cwfLeafPrimitives
    hkdfDerive96    := hkdfDerive96Ref cwfLeafPrimitives
    rootCreateChain := rootCreateChainRef cwfLeafPrimitives
    chainKdfSeed    := chainKdfSeedRef cwfLeafPrimitives
    chainKdfNext    := chainKdfNextRef cwfLeafPrimitives
    deriveMsgKeys   := deriveMsgKeysRef cwfLeafPrimitives
    aeadEnc         := aes256CbcHmacEncRef cwfLeafPrimitives
    aeadDec         := aes256CbcHmacDecRef cwfLeafPrimitives }
  { P1 with sigVerify := xeddsaVerifyRef P1 }

theorem cwfC_and_80 (bs : Bytes) : ((cwfC bs).getD 31 0 &&& 0x80) = 0 := by
  rw [cwfC_getD _ 31 (by omega)]
  generalize (fitBytes 32 bs).getD 31 0 = b; revert b; unfold cwfByte cwfMask cwfFix; decide

theorem cwfC_scalarIsInRange (bs : Bytes) : scalarIsInRange (cwfC bs) = true := by
  have h31 : (cwfC bs).getD 31 0 &&& 0x7F ≠ 0x7F := by
    rw [cwfC_getD _ 31 (by omega)]
    generalize (fitBytes 32 bs).getD 31 0 = b; revert b; unfold cwfByte cwfMask cwfFix; decide
  have hb : ((cwfC bs).getD 31 0 &&& 0x7F == 0x7F) = false := by simpa using h31
  unfold scalarIsInRange
  rw [cwfC_and_80, hb]
  simp

theorem cwfPrimitives_isCanonical_eq_isCanonicalRef (pk : Bytes) :
    cwfPrimitives.isCanonical pk = isCanonicalRef cwfPrimitives pk := by
  dsimp only [cwfPrimitives, cwfLeafPrimitives, isCanonicalRef]
  by_cases hc : cwfCanon pk = true
  · obtain ⟨hlen, hfix⟩ := cwfCanon_spec hc
    have h80 : (pk.getD 31 0 &&& 0x80) = 0 := by rw [← hfix]; exact cwfC_and_80 pk
    have hr : scalarIsInRange pk = true := by rw [← hfix]; exact cwfC_scalarIsInRange pk
    have htake : (pk ++ List.replicate 128 0).take 32 = pk := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hc, hlen, h80, hr]
    simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, htake, hc]
  · have hfalse : cwfCanon pk = false := Bool.eq_false_iff.mpr hc
    simp [hfalse]

theorem cwfPrimitives_sig_corr (sk msg r : Bytes) :
    cwfPrimitives.sigVerify (cwfPrimitives.sigPkGen sk) msg
      (cwfPrimitives.sigSign sk msg r) = true := by
  dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives, xeddsaVerifyRef]
  have hpk_len : (cwfC sk).length = 32 := cwfC_length sk
  have hpk_canon : cwfCanon (cwfC sk) = true := cwfCanon_cwfC sk
  set capR := clampIdeal32 (xorBytes (clampIdeal32 msg) (clampIdeal32 sk))
  have hcapR_len : capR.length = 32 := clampIdeal32_length _
  have hsig_len : (capR ++ capR).length = 64 := by
    rw [List.length_append, hcapR_len]
  have hget63 : (capR ++ capR).getD 63 0 = capR.getD 31 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    rw [List.getD_eq_getElem?_getD, hcapR_len]
  have he0 : ((capR ++ capR).getD 63 0 &&& 0x60) = 0 := by
    rw [hget63]
    exact getD_31_clampIdeal32_and_60 _
  have h80 : ((capR ++ capR).getD 63 0 &&& 0x80) = 0 := by
    rw [hget63]
    exact getD_31_clampIdeal32_and_80 _
  have htake_sig : (capR ++ capR).take 32 = capR :=
    List.take_left' hcapR_len
  have hdrop_sig : (capR ++ capR).drop 32 = capR :=
    List.drop_left' hcapR_len
  have hcond1 :
      ((cwfC sk).length == 32 && (capR ++ capR).length == 64 &&
        ((capR ++ capR).getD 63 0 &&& 0x60 == 0)) = true := by
    rw [hpk_len, hsig_len, he0]; decide
  have hcond2 : (((capR ++ capR).getD 63 0 &&& 0x80) >>> 7 == 0 &&
      cwfCanon (cwfC sk)) = true := by
    rw [h80, hpk_canon]; decide
  have hsScalar : clampIdeal32 (capR.take 31 ++ [capR.getD 31 0 &&& 0x7F]) = capR :=
    clampIdeal32_clamped31 _
  have hfit_take : (fitBytes 160 capR).take 32 = capR := by
    unfold fitBytes
    rw [List.take_append_of_le_length (by rw [List.length_take, hcapR_len]; omega)]
    rw [List.take_take, Nat.min_eq_left (by decide)]
    exact List.take_of_length_le (by omega)
  have hclamp_capR : clampIdeal32 capR = capR := clampIdeal32_idem _
  rw [hcond1, hcond2]
  simp only [↓reduceIte, htake_sig, hdrop_sig, hsScalar, hclamp_capR, hfit_take, beq_self_eq_true]

theorem cwfPrimitives_onCurveKey_iff (pk : Bytes) :
    onCurveKey cwfPrimitives pk ↔ cwfGood pk = true := by
  show (cwfCanon pk = true ∨ ∃ e, e.length = 32 ∧ cwfP8 pk = cwfP8 (cwfC e)) ↔ cwfGood pk = true
  constructor
  · rintro (hc | ⟨e, _, hpow⟩)
    · rw [← (cwfCanon_spec hc).2]; exact cwfGood_cwfC pk
    · rw [cwfGood_of_P8_eq hpow]; exact cwfGood_cwfC e
  · intro hg
    exact Or.inr ⟨cwfC pk, cwfC_length pk, by rw [cwfP8_good hg, cwfP8_cwfC, cwfC_idem]⟩

theorem cwfPrimitives_isValidDhTriple_ref (X Y Z : Bytes) :
    cwfPrimitives.isValidDhTriple X Y Z = true ↔ isValidDhTripleRef cwfPrimitives X Y Z := by
  unfold isValidDhTripleRef
  rw [cwfPrimitives_onCurveKey_iff, cwfPrimitives_onCurveKey_iff]
  show (cwfGood X && cwfGood Y && (cwfC X == X || cwfC Y == Y) &&
      cwfP8 Z == cwfP8 (cwfDh X Y)) = true ↔
    cwfGood X = true ∧ cwfGood Y = true ∧
      ((∃ a, X = cwfC a ∧ cwfP8 Z = cwfP8 (cwfX a Y)) ∨
        (∃ b, Y = cwfC b ∧ cwfP8 Z = cwfP8 (cwfX b X)))
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨hgX, hgY⟩, hX | hY⟩, hZ⟩
    · refine ⟨hgX, hgY, Or.inl ⟨X, hX.symm, ?_⟩⟩
      rw [← cwfDh_cwfC_left, hX]; exact hZ
    · refine ⟨hgX, hgY, Or.inr ⟨Y, hY.symm, ?_⟩⟩
      rw [← cwfDh_cwfC_left, hY, cwfDh_comm]; exact hZ
  · rintro ⟨hgX, hgY, ⟨a, rfl, hZ⟩ | ⟨b, rfl, hZ⟩⟩
    · exact ⟨⟨⟨hgX, hgY⟩, Or.inl (cwfC_idem a)⟩, by rw [cwfDh_cwfC_left]; exact hZ⟩
    · exact ⟨⟨⟨hgX, hgY⟩, Or.inr (cwfC_idem b)⟩, by rw [cwfDh_comm, cwfDh_cwfC_left]; exact hZ⟩

theorem cwfPrimitives_wellFormed : WellFormedPrimitives cwfPrimitives where
  isValidDhTriple_eq_ref := cwfPrimitives_isValidDhTriple_ref
  x25519_comm := by
    intro a b
    show cwfX a (cwfC b) = cwfX b (cwfC a)
    rw [cwfX_cwfC, cwfX_cwfC, cwfX25519_comm]
  canon_base := cwfCanon_cwfC
  canon_x25519 := by
    intro a pk _ h
    change cwfCanon pk = true at h
    show cwfCanon (cwfX a pk) = true
    rw [← (cwfCanon_spec h).2, cwfX_cwfC]
    exact cwfCanon_cwfC _
  sigPkGen_eq_x25519Base := rfl
  pow8_idemp := cwfP8_idem
  pow8_x25519_comm := by
    intro a b
    show cwfP8 (cwfX a (cwfC b)) = cwfP8 (cwfX b (cwfC a))
    rw [cwfX_cwfC, cwfX_cwfC, cwfX25519_comm]
  ddh_consistent := by
    intro a b z
    show (cwfGood (cwfC a) && cwfGood (cwfC b) &&
        (cwfC (cwfC a) == cwfC a || cwfC (cwfC b) == cwfC b) &&
        cwfP8 z == cwfP8 (cwfDh (cwfC a) (cwfC b))) = true ↔
      cwfP8 z = cwfP8 (cwfX a (cwfC b))
    simp only [cwfGood_cwfC, cwfC_idem, cwfDh_cwfC_left, beq_self_eq_true, Bool.true_or,
      Bool.true_and, beq_iff_eq]
  ddh_consistent_left := by
    intro a pk z hon
    have hg : cwfGood pk = true := (cwfPrimitives_onCurveKey_iff pk).mp hon
    show (cwfGood (cwfC a) && cwfGood pk &&
        (cwfC (cwfC a) == cwfC a || cwfC pk == pk) &&
        cwfP8 z == cwfP8 (cwfDh (cwfC a) pk)) = true ↔
      cwfP8 z = cwfP8 (cwfX a pk)
    simp only [cwfGood_cwfC, hg, cwfC_idem, cwfDh_cwfC_left, beq_self_eq_true, Bool.true_or,
      Bool.true_and, beq_iff_eq]
  x25519_congr_of_base_eq := by
    intro a1 a2 pk _ _ _ h
    change cwfC a1 = cwfC a2 at h
    show cwfX a1 pk = cwfX a2 pk
    unfold cwfX cwfX25519
    rw [h]
  ddh_symm := by
    intro pk1 pk2 z
    show (cwfGood pk1 && cwfGood pk2 && (cwfC pk1 == pk1 || cwfC pk2 == pk2) &&
        cwfP8 z == cwfP8 (cwfDh pk1 pk2)) =
      (cwfGood pk2 && cwfGood pk1 && (cwfC pk2 == pk2 || cwfC pk1 == pk1) &&
        cwfP8 z == cwfP8 (cwfDh pk2 pk1))
    rw [Bool.and_comm (cwfGood pk1) (cwfGood pk2), Bool.or_comm, cwfDh_comm]
  x25519_pow8_congr := fun a pk1 pk2 _ _ h => cwfX_pow8_congr a pk1 pk2 h
  canon_pow8_inj := by
    intro pk1 pk2 h1 h2 hpow
    change cwfCanon pk1 = true at h1
    change cwfCanon pk2 = true at h2
    change cwfP8 pk1 = cwfP8 pk2 at hpow
    rw [← (cwfCanon_spec h1).2, cwfP8_cwfC, ← (cwfCanon_spec h2).2, cwfP8_cwfC] at hpow
    rw [← (cwfCanon_spec h1).2, ← (cwfCanon_spec h2).2]
    exact hpow
  x25519_len := cwfX_length
  x25519Base_len := cwfC_length
  pow8_len := cwfP8_length
  sha512_len := sha512Ref_length cwfLeafPrimitives
  scalarMul_len := by
    intro a b
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, clampIdeal32_length, clampIdeal32_length]
    rfl
  scalarAdd_len := by
    intro a b
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, clampIdeal32_length, clampIdeal32_length]
    rfl
  scalarFromBytesModOrder_len := clampIdeal32_length
  scalarFromWide_len := fun b => clampIdeal32_length (b.take 32)
  montToEd_len := by
    intro u s pt h
    dsimp only [cwfPrimitives, cwfLeafPrimitives] at h
    split at h <;> rename_i hcond
    · injection h with hpt
      subst hpt
      rw [Bool.and_eq_true] at hcond
      have hu : u.length = 32 := (cwfCanon_spec hcond.2).1
      rw [List.length_append, hu, List.length_replicate]
    · contradiction
  edNeg_len := fun pt => fitBytes_length 160 (clampIdeal32 (pt.take 32))
  doubleScalarMulBasepoint_len := fun _h _a s =>
    fitBytes_length 160 (clampIdeal32 s)
  compress_len := fun pt => clampIdeal32_length (pt.take 32)
  sigVerify_eq_xeddsaVerifyRef := fun _ _ _ => rfl
  isCanonical_eq_isCanonicalRef := cwfPrimitives_isCanonical_eq_isCanonicalRef
  kemKeyGen_valid := fun seed =>
    ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  kemEncaps_len := by
    intro pk r ss ct hEnc
    dsimp only [cwfPrimitives, cwfLeafPrimitives] at hEnc
    split at hEnc
    · injection hEnc with hPair
      injection hPair with hSs hCt
      subst hSs
      subst hCt
      refine ⟨fitBytes_length 32 r, ?_⟩
      rw [List.length_append, fitBytes_length, List.length_replicate]
    · contradiction
  kemDecaps_len := by
    intro _sk ct ss hDec
    dsimp only [cwfPrimitives, cwfLeafPrimitives] at hDec
    split at hDec
    · injection hDec with hSs
      subst hSs
      exact fitBytes_length 32 (ct.take 32)
    · contradiction
  spqrInitSend_some := fun _ _ => rfl
  aead_corr := fun mk ad pt =>
    aes256CbcHmac_roundtrip cwfPrimitives
      (fun k b => by
        dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives]
        rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl)
      (fun k blk hk hb => idealAesBlock_corr k blk hk hb) mk ad pt
  kem_corr := by
    intro seed r ss ct hEnc
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives] at hEnc ⊢
    have hpk : ((fitBytes 1568 (seed.take 32)).length == kyberPkLen) = true := by
      simp [fitBytes_length, kyberPkLen]
    rw [hpk] at hEnc
    simp only [↓reduceIte] at hEnc
    injection hEnc with hPair
    injection hPair with hSs hCt
    subst hSs
    subst hCt
    have hct : ((fitBytes 32 r ++ List.replicate 1536 0).length == kyberCtLen) = true := by
      rw [List.length_append, fitBytes_length, List.length_replicate]; rfl
    rw [hct]
    simp only [↓reduceIte]
    congr 1
    have hlen : (fitBytes 32 r).length = 32 := fitBytes_length 32 r
    have htake : (fitBytes 32 r ++ List.replicate 1536 0).take 32 = fitBytes 32 r := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [htake, fitBytes_of_length_eq hlen]
  sig_corr := cwfPrimitives_sig_corr
  spqr_corr := by
    intro pqrKey coins stA salt? pqMsg hSend
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives] at hSend ⊢
    injection hSend with hTuple
    injection hTuple with hSt hRest
    injection hRest with hSalt _
    exact ⟨pqrKey, by rw [← hSalt]⟩
  spqrInitRecv_salt_len := by
    intro pqrKey pqMsg stB salt hRecv
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives] at hRecv
    injection hRecv with hTuple
    injection hTuple with _ hSalt
    injection hSalt with hSalt
    rw [← hSalt]; simp
  sha256Compress_len := fun st blk => fitBytes_length 32 _
  sha512Compress_len := fun st blk => fitBytes_length 64 _
  aesEncBlock_len := fun k blk => by
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl
  aesDecBlock_len := fun k blk => by
    dsimp only [cwfPrimitives, cwfLeafPrimitives, idealLeafPrimitives]
    rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl
  aesBlock_corr := fun k blk hk hb => idealAesBlock_corr k blk hk hb
  sha512_eq_ref := fun _ => rfl
  hkdfDerive96_eq_ref := fun _ => rfl
  rootCreateChain_eq_ref := fun _ _ => rfl
  chainKdfSeed_eq_ref := fun _ => rfl
  chainKdfNext_eq_ref := fun _ => rfl
  deriveMsgKeys_eq_ref := fun _ _ => rfl
  aeadEnc_eq_ref := fun _ _ _ => rfl
  aeadDec_eq_ref := fun _ _ _ => rfl
  x25519_clamp := by
    intro sk pk
    show cwfX (clampScalar25519 sk) pk = cwfX sk pk
    unfold cwfX cwfX25519
    rw [cwfC_clamp]
  x25519Base_clamp := cwfC_clamp
  x25519_base_ne_zero := fun _ _ _ _ => cwfX_ne_zero_of_good (cwfGood_cwfC _)
  x25519_zero_iff := fun a1 a2 pk _ _ _ => by
    show cwfX a1 pk = List.replicate 32 0 ↔ cwfX a2 pk = List.replicate 32 0
    rw [cwfX_zero_iff, cwfX_zero_iff]
  kemDecaps_isSome := fun _ ct _ hct => by
    dsimp only [cwfPrimitives, cwfLeafPrimitives]; simp [hct, kyberCtLen]
  kemEncaps_isSome := fun pk _ hpk _ => by
    dsimp only [cwfPrimitives, cwfLeafPrimitives]; simp [hpk, kyberPkLen]

theorem word256ToBytes_length (w : BitVec 256) : (word256ToBytes w).length = 32 := by
  simp [word256ToBytes]

theorem word256ToBytes_getD (w : BitVec 256) (i : Nat) (hi : i < 32) :
    (word256ToBytes w).getD i 0 = UInt8.ofNat ((w.toNat >>> (8 * i)) % 256) := by
  unfold word256ToBytes
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi)]
  simp only [List.getElem_ofFn, Option.getD_some]

theorem word_byte_testBit (n i k : Nat) (hk : k < 8) :
    (UInt8.ofNat ((n >>> (8 * i)) % 256)).toNat.testBit k = n.testBit (8 * i + k) := by
  have h1 : (UInt8.ofNat ((n >>> (8 * i)) % 256)).toNat = (n >>> (8 * i)) % 2 ^ 8 := by
    simp
  rw [h1, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hk]

theorem cwfMask_testBit (j : Nat) (h1 : 3 ≤ j) (h2 : j < 254) :
    (cwfMask (j / 8)).toNat.testBit (j % 8) = true := by
  have : ∀ j : Fin 254, 3 ≤ j.val → (cwfMask (j.val / 8)).toNat.testBit (j.val % 8) = true := by
    decide
  exact this ⟨j, h2⟩ h1

theorem cwfC_word_testBit (w w' : BitVec 256)
    (h : cwfC (word256ToBytes w) = cwfC (word256ToBytes w')) (j : Nat) (h1 : 3 ≤ j)
    (h2 : j < 254) : w.toNat.testBit j = w'.toNat.testBit j := by
  have hi : j / 8 < 32 := by omega
  have hfit : ∀ v : BitVec 256, fitBytes 32 (word256ToBytes v) = word256ToBytes v := by
    intro v
    simp [fitBytes, word256ToBytes_length]
  have hb := congrArg (fun l => l.getD (j / 8) 0) h
  simp only [cwfC_getD _ _ hi, hfit, word256ToBytes_getD _ _ hi] at hb
  have hb2 := congrArg (fun x : UInt8 => x.toNat.testBit (j % 8)) ((cwfByte_eq_iff _ _ _).1 hb)
  simp only [UInt8.toNat_and, Nat.testBit_and, cwfMask_testBit j h1 h2, Bool.and_true,
    word_byte_testBit _ _ _ (Nat.mod_lt _ (by decide : 8 > 0))] at hb2
  have hj : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
  rw [hj] at hb2
  exact hb2

theorem cwfC_word_eq (w w' : BitVec 256)
    (h : cwfC (word256ToBytes w) = cwfC (word256ToBytes w'))
    (hlo : w.toNat % 8 = w'.toNat % 8) (hhi : w.toNat / 2 ^ 254 = w'.toNat / 2 ^ 254) :
    w = w' := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj1 : j < 3
  · have := congrArg (fun n => n.testBit j) hlo
    simp only [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, hj1, decide_true,
      Bool.true_and] at this
    exact this
  by_cases hj2 : j < 254
  · exact cwfC_word_testBit w w' h j (by omega) hj2
  by_cases hj3 : j < 256
  · have := congrArg (fun n => n.testBit (j - 254)) hhi
    simp only [Nat.testBit_div_two_pow] at this
    rwa [show j - 254 + 254 = j by omega] at this
  · rw [Nat.testBit_lt_two_pow
        (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le w'.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem uniform256_map_bool_le (f : BitVec 256 → Bool) (k : Nat)
    (hk : (Finset.univ.filter (fun w => f w = true)).card ≤ k) :
    (𝒟[f <$> ($ᵗ BitVec 256)] {true}).toReal ≤ (k : ℝ) / 2 ^ 256 := by
  rw [evalDist_map_apply_of_discrete _ _ (measurableSet_singleton true)]
  change (𝒟[$ᵗ BitVec 256] {w | f w = true}).toReal ≤ _
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card (BitVec 256) : ENNReal) = 2 ^ 256 := by
    simp only [Fintype.card_bitVec]
    norm_num
  rw [hcard, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  gcongr

theorem word256ToBytes_inj (w w' : BitVec 256) (h : word256ToBytes w = word256ToBytes w') :
    w = w' := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 256
  · have hi : j / 8 < 32 := by omega
    have hb := congrArg (fun l => (l.getD (j / 8) 0).toNat.testBit (j % 8)) h
    simp only [word256ToBytes_getD _ _ hi,
      word_byte_testBit _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)), Nat.div_add_mod j 8] at hb
    exact hb
  · rw [Nat.testBit_lt_two_pow
        (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le w'.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem cwfPrimitives_kemKeyGen_fst (seed : Bytes) :
    (cwfPrimitives.kemKeyGen seed).1 = fitBytes 1568 (seed.take 32) := by
  rfl

theorem uniform256_probEvent_le (p : BitVec 256 → Prop) [DecidablePred p] (k : Nat)
    (hk : (Finset.univ.filter p).card ≤ k) :
    (𝒟[$ᵗ BitVec 256] {w | p w}).toReal ≤ (k : ℝ) / 2 ^ 256 := by
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card (BitVec 256) : ENNReal) = 2 ^ 256 := by
    simp only [Fintype.card_bitVec]
    norm_num
  rw [hcard, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  gcongr

theorem fitBytes_kem_take32 (x y : Bytes) (hx : x.length = 32) :
    (fitBytes 1568 ((x ++ y).take 32)).take 32 = x := by
  have hxy : (x ++ y).take 32 = x := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [hxy]
  unfold fitBytes
  rw [List.take_append_of_le_length (by simp; omega), List.take_take,
    show min 32 1568 = 32 from rfl, List.take_of_length_le (by omega)]

theorem cwfPrimitives_kem_coll_bound (targetPk : Bytes) :
      (𝒟[do let (pk, _) ← sampleKemKeyGen cwfPrimitives; pure (pk == targetPk)] {true}).toReal
        ≤ 1 / (2 : ℝ) ^ 255 := by
  simp only [sampleKemKeyGen, sampleRandom64, sampleBytes32, bind_assoc, pure_bind,
    bind_map_left]
  have hle :
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun w => do
          let x_1 ← word256ToBytes <$> ($ᵗ BitVec 256)
          pure ((cwfPrimitives.kemKeyGen (word256ToBytes w ++ x_1)).1 == targetPk)] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun w =>
          (pure (decide (word256ToBytes w = targetPk.take 32)) : ProbComp Bool)] {true} := by
    refine evalDist_bind_apply_mono_of_discrete _ _ _ (measurableSet_singleton true) ?_
    intro w
    by_cases hw : word256ToBytes w = targetPk.take 32
    · refine le_trans (evalDist_apply_le_one _ _) ?_
      simp [hw]
    · have hf : ∀ y, ((cwfPrimitives.kemKeyGen (word256ToBytes w ++ y)).1 == targetPk) =
          false := by
        intro y
        rw [cwfPrimitives_kemKeyGen_fst, beq_eq_false_iff_ne]
        intro heq
        apply hw
        rw [← heq, fitBytes_kem_take32 _ y (word256ToBytes_length w)]
      simp [hf]
  refine le_trans (ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (evalDist_apply_le_one _ _)) hle) ?_
  rw [bind_pure_comp, evalDist_map_apply_of_discrete _ _ (measurableSet_singleton true)]
  have hset : (fun w => decide (word256ToBytes w = targetPk.take 32)) ⁻¹' {true} =
      {w | word256ToBytes w = targetPk.take 32} := by
    ext w
    simp
  rw [hset]
  refine le_trans (uniform256_probEvent_le (fun w => word256ToBytes w = targetPk.take 32) 1 ?_)
    (by norm_num)
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact word256ToBytes_inj a b (ha.trans hb.symm)

end SpecTests.SignalPqxdh
