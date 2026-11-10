/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames
public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# Legacy PQXDH `ReductionDsl` Compatibility Tables

**Checked by Lean.** Proof-only `ReductionDsl` signature `pqSig`, operation table `pqxdhOps`,
uniform sampler table `pqSamplers`, challenger interfaces, and game codecs (`keyIndCodec`,
`authCodec`), bridged to the shared atomic tables via `AtomicLift.lean`.
-/

@[expose] public section

namespace SignalPqxdh.LegacyCosted

open _root_.ReductionDsl OracleSpec OracleComp

/-! ## Sorts -/

/-- PQXDH abstract sorts: byte strings of nominal width `w`, and 32-bit key identifiers. -/
inductive PSort
  | bytes (w : ℕ+)
  | u32

@[reducible] def PSort.den : PSort → Type
  | .bytes _ => Bytes
  | .u32 => UInt32

/-- Size of a base value in blocks of its sort's width: `⌈len / w⌉` for bytes, `1` for `u32`. -/
def PSort.blocks : (s : PSort) → s.den → ℕ
  | .bytes w, x => (x.length + w - 1) / w
  | .u32, _ => 1

@[reducible] def pqSig : Sig where
  Base := PSort
  den := PSort.den
  sz := PSort.blocks

local notation "PT" => Ty pqSig

@[reducible] def B (w : ℕ+) : PT := .base (.bytes w)

@[reducible] def U32 : PT := .base .u32

/-- Nominal byte width of the base leaves of a value type (`u32` counts as 4 bytes). -/
def Ty.wd : PT → ℕ
  | .base (.bytes w) => w
  | .base .u32 => 4
  | .unit | .bool | .nat => 0
  | .opt t | .list t | .tbl t => Ty.wd t
  | .prod t u | .sum t u => Ty.wd t + Ty.wd u

@[reducible] def drKeyT : PT := .prod (B 32) (.prod (B 32) (B 32))

@[reducible] def msgKeysT : PT := .prod (B 32) (.prod (B 32) (B 16))

def drKeyV (k : DRKey) : drKeyT.denote := (k.rootKey, k.chainKey, k.pqrKey)

def msgKeysV (k : MessageKeys) : msgKeysT.denote := (k.cipherKey, k.macKey, k.iv)
def msgKeysOfV (v : msgKeysT.denote) : MessageKeys := ⟨v.1, v.2.1, v.2.2⟩

/-! ## Byte-string operations -/

inductive BOp
  | lit (w : ℕ+) (v : Bytes)
  | cat (m n : ℕ+)
  | cons (b : UInt8) (w : ℕ+)
  | widen (w d : ℕ+)
  | takeK (w k : ℕ+)
  | take (w : ℕ+)
  | drop (w : ℕ+)
  | len (w : ℕ+)
  | eq (m n : ℕ+)
  | varint

/-- Byte-string operation table; each operation's cost bounds the nominal widths read and written. -/
@[reducible] def pqBytesOps : Ops pqSig where
  Op := BOp
  dom := fun
    | .lit _ _ => .unit
    | .cat m n => .prod (B m) (B n)
    | .cons _ w | .widen w _ | .takeK w _ | .len w => B w
    | .take w | .drop w => .prod .nat (B w)
    | .eq m n => .prod (B m) (B n)
    | .varint => .nat
  cod := fun
    | .lit w _ => B w
    | .cat m n => B (m + n)
    | .cons _ w => B (w + 1)
    | .widen w d => B (w + d)
    | .takeK _ k => B k
    | .take w | .drop w => B w
    | .len _ => .nat
    | .eq _ _ => .bool
    | .varint => B 10
  eval := fun
    | .lit _ v, _ => v
    | .cat _ _, (x, y) => x ++ y
    | .cons b _, x => b :: x
    | .widen _ _, x => x
    | .takeK _ k, x => x.take k
    | .take _, (n, x) => x.take n
    | .drop _, (n, x) => x.drop n
    | .len _, x => x.length
    | .eq _ _, (x, y) => x == y
    | .varint, n => pbVarint n
  cost := fun
    | .lit w v => w + v.length
    | .cat m n => m + n
    | .cons _ w => w + 1
    | .widen w d => w + d
    | .takeK w k => w + k
    | .take w | .drop w => w + 1
    | .len w => bits w
    | .eq m n => m + n
    | .varint => 10

/-! ## Key-identifier operations -/

inductive UOp
  | lit (k : UInt32)
  | ofNat
  | toNat
  | eq

@[reducible] def pqU32Ops : Ops pqSig where
  Op := UOp
  dom := fun | .lit _ => .unit | .ofNat => .nat | .toNat => U32 | .eq => .prod U32 U32
  cod := fun | .lit _ | .ofNat => U32 | .toNat => .nat | .eq => .bool
  eval := fun
    | .lit k, _ => k
    | .ofNat, n => UInt32.ofNat n
    | .toNat, k => k.toNat
    | .eq, (a, b) => a == b
  cost := fun | .lit _ | .ofNat | .eq => 1 | .toNat => 32

/-- Combined byte-string and `UInt32` operation table for PQXDH reductions. -/
@[reducible] def pqxdhOps : Ops pqSig := Ops.sum pqBytesOps pqU32Ops

/-! ## Primitive-oracle tags -/

/-- Primitive-oracle query tags parameterized by nominal variable-field byte widths. -/
inductive PTag
  | x25519 | x25519Base | isCanonical | pow8 | sigPkGen
  | sigSign (m : ℕ+) | sigVerify (m : ℕ+)
  | kemKeyGen | kemEncaps | kemDecaps
  | hkdfDerive96 (w : ℕ+)
  | rootCreateChain | chainKdfSeed | chainKdfNext
  | spqrInitSend (p c : ℕ+) | spqrInitRecv (p c : ℕ+)
  | deriveMsgKeys (s : ℕ+)
  | aeadEnc (a m c : ℕ+) | aeadDec (a c m : ℕ+)

@[reducible] def PTag.dom : PTag → PT
  | .x25519 => .prod (B 32) (B 32)
  | .x25519Base | .isCanonical | .pow8 | .sigPkGen => B 32
  | .sigSign m => .prod (B 32) (.prod (B m) (B 64))
  | .sigVerify m => .prod (B 32) (.prod (B m) (B 64))
  | .kemKeyGen => B 64
  | .kemEncaps => .prod (B 1568) (B 32)
  | .kemDecaps => .prod (B 3168) (B 1568)
  | .hkdfDerive96 w => B w
  | .rootCreateChain => .prod (B 32) (B 32)
  | .chainKdfSeed | .chainKdfNext => B 32
  | .spqrInitSend _ _ => .prod (B 32) (B 32)
  | .spqrInitRecv _ c => .prod (B 32) (B c)
  | .deriveMsgKeys s => .prod (B 32) (.opt (B s))
  | .aeadEnc a m _ => .prod msgKeysT (.prod (B a) (B m))
  | .aeadDec a c _ => .prod msgKeysT (.prod (B a) (B c))

@[reducible] def PTag.cod : PTag → PT
  | .x25519 | .x25519Base | .pow8 | .sigPkGen | .chainKdfSeed | .chainKdfNext => B 32
  | .isCanonical | .sigVerify _ => .bool
  | .sigSign _ => B 64
  | .kemKeyGen => .prod (B 1568) (B 3168)
  | .kemEncaps => .opt (.prod (B 32) (B 1568))
  | .kemDecaps => .opt (B 32)
  | .hkdfDerive96 _ => drKeyT
  | .rootCreateChain => .prod (B 32) (B 32)
  | .spqrInitSend p c => .opt (.prod (B p) (.prod (.opt (B 32)) (B c)))
  | .spqrInitRecv p _ => .opt (.prod (B p) (.opt (B 32)))
  | .deriveMsgKeys _ => msgKeysT
  | .aeadEnc _ _ c => B c
  | .aeadDec _ _ m => .opt (B m)

def PTag.enc : (t : PTag) → t.dom.denote → PrimQuery
  | .x25519, (sk, pk) => .x25519 sk pk
  | .x25519Base, sk => .x25519Base sk
  | .isCanonical, pk => .isCanonical pk
  | .pow8, pk => .pow8 pk
  | .sigPkGen, sk => .sigPkGen sk
  | .sigSign _, (sk, m, r) => .sigSign sk m r
  | .sigVerify _, (pk, m, s) => .sigVerify pk m s
  | .kemKeyGen, seed => .kemKeyGen seed
  | .kemEncaps, (pk, r) => .kemEncaps pk r
  | .kemDecaps, (sk, ct) => .kemDecaps sk ct
  | .hkdfDerive96 _, ikm => .hkdfDerive96 ikm
  | .rootCreateChain, (rk, dh) => .rootCreateChain rk dh
  | .chainKdfSeed, ck => .chainKdfSeed ck
  | .chainKdfNext, ck => .chainKdfNext ck
  | .spqrInitSend _ _, (p, r) => .spqrInitSend p r
  | .spqrInitRecv _ _, (p, m) => .spqrInitRecv p m
  | .deriveMsgKeys _, (k, s) => .deriveMsgKeys k s
  | .aeadEnc _ _ _, (k, ad, pt) => .aeadEnc (msgKeysOfV k) ad pt
  | .aeadDec _ _ _, (k, ad, ct) => .aeadDec (msgKeysOfV k) ad ct

def PTag.dec : (t : PTag) → (x : t.dom.denote) → primSpec (t.enc x) → t.cod.denote
  | .x25519, _, r | .x25519Base, _, r | .isCanonical, _, r | .pow8, _, r
  | .sigPkGen, _, r | .sigSign _, _, r | .sigVerify _, _, r | .kemKeyGen, _, r
  | .kemEncaps, _, r | .kemDecaps, _, r | .rootCreateChain, _, r | .chainKdfSeed, _, r
  | .chainKdfNext, _, r | .spqrInitSend _ _, _, r | .spqrInitRecv _ _, _, r
  | .aeadEnc _ _ _, _, r | .aeadDec _ _ _, _, r => r
  | .hkdfDerive96 _, _, r => drKeyV r
  | .deriveMsgKeys _, _, r => msgKeysV r

/-! ## Uniform samplers -/

inductive PSamp
  | bool | bytes32 | random64 | drKey96 | msgKeys80
  | index (N : ℕ)

@[reducible] def PSamp.ty : PSamp → PT
  | .bool => .bool
  | .bytes32 => B 32
  | .random64 => B 64
  | .drKey96 => drKeyT
  | .msgKeys80 => msgKeysT
  | .index _ => .nat

def sampleIndex (N : ℕ) : ProbComp ℕ :=
  if h : 0 < N then
    letI : NeZero N := ⟨Nat.ne_of_gt h⟩
    do let x ← $ᵗ (Fin N); return x.val
  else return 0

def PSamp.run : (s : PSamp) → ProbComp s.ty.denote
  | .bool => $ᵗ Bool
  | .bytes32 => sampleBytes32
  | .random64 => sampleRandom64
  | .drKey96 => drKeyV <$> sampleDRKey96
  | .msgKeys80 => msgKeysV <$> sampleMessageKeys80
  | .index N => sampleIndex N

def PSamp.cost : PSamp → ℕ
  | .index N => bits N + 1
  | s => 1 + Ty.wd s.ty

/-- Uniform sampler table shared across legacy PQXDH interfaces. -/
def pqSamplers : Samplers pqSig where
  Samp := PSamp
  sDom := fun _ => .unit
  sTy := PSamp.ty
  samp := fun s _ => s.run
  sCost := PSamp.cost

/-! ## Challenger interfaces -/

/-- Primitive-oracle `ReductionDsl` interface over `PrimBaseSpec`. -/
def pqPrimIface : Iface pqSig PrimBaseSpec where
  fwdU := fun n => query (spec := PrimBaseSpec) (.inl n)
  uCost := 1
  Tag := PTag
  dom := PTag.dom
  cod := PTag.cod
  enc := fun t x => .inr (t.enc x)
  dec := fun t x r => t.dec x r
  qCost := fun t => 1 + Ty.wd t.dom + Ty.wd t.cod
  smp := pqSamplers

/-- Typed tag encoding and cost parameters for a challenger oracle. -/
structure ChallengerOracle where
  ι : Type
  spec : OracleSpec.{0, 0} ι
  Tag : Type
  dom : Tag → PT
  cod : Tag → PT
  enc : (t : Tag) → (dom t).denote → ι
  dec : (t : Tag) → (x : (dom t).denote) → spec (enc t x) → (cod t).denote
  encCost : ℕ

def ChallengerOracle.qCost (C : ChallengerOracle) (t : C.Tag) : ℕ :=
  1 + Ty.wd (C.dom t) + C.encCost + Ty.wd (C.cod t)

def pqChalIface (C : ChallengerOracle) : Iface pqSig (PrimBaseSpec + C.spec) where
  fwdU := fun n => query (spec := PrimBaseSpec + C.spec) (.inl (.inl n))
  uCost := 1
  Tag := PTag ⊕ C.Tag
  dom := fun | .inl t => t.dom | .inr t => C.dom t
  cod := fun | .inl t => t.cod | .inr t => C.cod t
  enc := fun | .inl t, x => .inl (.inr (t.enc x)) | .inr t, x => .inr (C.enc t x)
  dec := fun | .inl t, x, r => t.dec x r | .inr t, x, r => C.dec t x r
  qCost := fun | .inl t => 1 + Ty.wd t.dom + Ty.wd t.cod | .inr t => C.qCost t
  smp := pqSamplers

/-- Combined XEdDSA signing and X25519 DDH challenger oracle (`sigAndDdhSpec`). -/
def sigAndDdhOracle : ChallengerOracle where
  ι := SigQuery ⊕ DdhQuery
  spec := sigAndDdhSpec
  Tag := ℕ+ ⊕ Unit
  dom := fun
    | .inl m => B m
    | .inr () => .prod (B 32) (.prod (B 32) (B 32))
  cod := fun
    | .inl _ => B 64
    | .inr () => .bool
  enc := fun
    | .inl _, msg => .inl (.sign msg)
    | .inr (), x => .inr x
  dec := fun
    | .inl _, _, r => r
    | .inr (), _, r => r
  encCost := 0

abbrev pqSigAndDdhIface := pqChalIface sigAndDdhOracle

/-! ## Game codecs -/

def drKeyOfV (v : drKeyT.denote) : DRKey := ⟨v.1, v.2.1, v.2.2⟩

@[reducible] def bundleT : PT :=
  .prod (B 32) (.prod U32 (.prod (B 32) (.prod (B 64)
    (.prod (.opt (.prod U32 (B 32))) (.prod U32 (.prod (B 1568) (B 64)))))))

def bundleV (b : PreKeyBundleInput) : bundleT.denote :=
  (b.ikB, (b.spkId, (b.spkB, (b.spkSig, (b.opkB?, (b.pqspkId, (b.pqspkB, b.pqspkSig)))))))
def bundleOfV (v : bundleT.denote) : PreKeyBundleInput :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2⟩

@[reducible] def hdrT : PT :=
  .prod (B 32) (.prod (B 32) (.prod U32 (.prod (.opt U32) (.prod U32 (B 1568)))))

def hdrV (h : HandshakeHdr) : hdrT.denote :=
  (h.ikAPk, (h.ekAPk, (h.spkId, (h.opkId?, (h.pqspkId, h.kemCt)))))
def hdrOfV (v : hdrT.denote) : HandshakeHdr :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩

@[reducible] def sidT : PT :=
  .sum (.prod .nat .nat) (.sum (.prod .nat .nat)
    (.sum (.prod .nat (.prod .nat .nat)) (.prod .nat (.prod .nat .nat))))

def sidV {S : Setup} : SessionId S → sidT.denote
  | .sendOPK u i => .inl (u.val, i.val)
  | .sendNoOPK u i => .inr (.inl (u.val, i.val))
  | .recvOPK k j o => .inr (.inr (.inl (k.val, (j.val, o.val))))
  | .recvNoOPK k j l => .inr (.inr (.inr (k.val, (j.val, l.val))))

@[reducible] def dhSecretsT : PT :=
  .prod (.list (B 32)) (.prod (.list (B 32)) (.prod (.list (B 32)) (.list (B 32))))

@[reducible] def keyIndQT : PT :=
  .sum .nat (.sum .nat (.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat))
  (.sum (.prod .nat (.prod .nat bundleT)) (.sum (.prod .nat (.prod .nat bundleT))
  (.sum (.prod .nat (.prod .nat (.prod .nat hdrT)))
  (.sum (.prod .nat (.prod .nat (.prod .nat hdrT)))
  (.sum sidT (.sum (B 192) (.sum .unit (.sum sidT (.sum (B 32) (.prod .nat .nat)))))))))))))

def keyIndQenc {S : Setup} : KeyIndQuery S → keyIndQT.denote
  | .initPrin u => .inl u.val
  | .corruptIK u => .inr (.inl u.val)
  | .genSPK u j => .inr (.inr (.inl (u.val, j.val)))
  | .genOPK u j o => .inr (.inr (.inr (.inl (u.val, (j.val, o.val)))))
  | .initiateOPK u i b => .inr (.inr (.inr (.inr (.inl (u.val, (i.val, bundleV b))))))
  | .initiateNoOPK u i b =>
    .inr (.inr (.inr (.inr (.inr (.inl (u.val, (i.val, bundleV b)))))))
  | .acceptOPK k j o h =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inl (k.val, (j.val, (o.val, hdrV h)))))))))
  | .acceptNoOPK k j l h =>
    .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inl (k.val, (j.val, (l.val, hdrV h))))))))))
  | .testSession sid =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sidV sid)))))))))
  | .roQuery sec =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec)))))))))
  | .revealDhSecrets =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | .revealSessionKey sid =>
    .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr (.inr (.inr (.inr (.inl (sidV sid))))))))))))
  | .registerKey sk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sk))))))))))))
  | .revealSpkSk u j =>
    .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (u.val, j.val)))))))))))))

@[reducible] def keyIndRT : PT :=
  .sum .unit (.sum (.prod (B 32) (B 32)) (.sum (B 32) (.sum (.prod (B 32) (B 32))
  (.sum bundleT (.sum hdrT (.sum (.prod drKeyT hdrT)
  (.sum .unit (.sum drKeyT (.sum dhSecretsT (B 32))))))))))

def keyIndRdec : keyIndRT.denote → KeyIndResponse
  | .inl () => .noneResp
  | .inr (.inl (ik, s)) => .initPrinResp ik s
  | .inr (.inr (.inl pk)) => .pkResp pk
  | .inr (.inr (.inr (.inl (ik, s)))) => .corrResp ik s
  | .inr (.inr (.inr (.inr (.inl b)))) => .bundleResp (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inl h))))) => .hdrResp (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (dk, h))))))) =>
    .initUnfreshResp (drKeyOfV dk) (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => .acceptFreshResp
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk)))))))) => .drKeyResp (drKeyOfV dk)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l1, (l2, (l3, l4)))))))))))) =>
    .dhSecretsResp l1 l2 l3 l4
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk))))))))) => .spkSkResp sk

/-- `ReductionDsl` game codec for `keyIndSpec S`. -/
def keyIndCodec (S : Setup) : GameCodec pqSig (keyIndSpec S) where
  Q := keyIndQT
  R := keyIndRT
  qenc := keyIndQenc
  rdec := fun _ r => keyIndRdec r
  codecCost := 32

/-! ## Two-key and authentication interfaces -/

def eufCmaSignOracle : ChallengerOracle where
  ι := SigQuery
  spec := sigOracleSpec
  Tag := ℕ+
  dom := fun m => B m
  cod := fun _ => B 64
  enc := fun _ msg => .sign msg
  dec := fun _ _ r => r
  encCost := 0

def gapDhDdhOracle : ChallengerOracle where
  ι := DdhQuery
  spec := gapDhOracleSpec
  Tag := Unit
  dom := fun _ => .prod (B 32) (.prod (B 32) (B 32))
  cod := fun _ => .bool
  enc := fun _ x => x
  dec := fun _ _ r => r
  encCost := 0

/-- Maps the reduction's optional raw SPQR salt to the 32-byte `PrfMsgKeys` salt key
(`effectiveHkdfSaltBytes`, DEV-LS25). -/
def saltKeyEnc (salt? : Option Bytes) : PrfMsgKeysQuery := .derive (effectiveHkdfSaltBytes salt?)

def saltKeyEncCost : ℕ := 32

def msgKeyPrfOracle : ChallengerOracle where
  ι := PrfMsgKeysQuery
  spec := prfMsgKeysSpec
  Tag := ℕ+
  dom := fun s => .opt (B s)
  cod := fun _ => msgKeysT
  enc := fun _ salt? => saltKeyEnc salt?
  dec := fun _ _ r => msgKeysV r
  encCost := saltKeyEncCost

def hmacPrfOracle : ChallengerOracle where
  ι := PrfHmacQuery
  spec := prfHmacSpec
  Tag := ℕ+
  dom := fun m => B m
  cod := fun _ => B 32
  enc := fun _ msg => .eval msg
  dec := fun _ _ r => r
  encCost := 0

abbrev pqxdhEufCmaIface := pqChalIface eufCmaSignOracle
abbrev pqGapDhIface := pqChalIface gapDhDdhOracle
abbrev pqPrfMkIface := pqChalIface msgKeyPrfOracle
abbrev pqPrfHmacIface := pqChalIface hmacPrfOracle

@[reducible] def preKeyMsgT : PT := .prod hdrT (.prod (B 32) (.prod (B 32) (B 32)))

def preKeyMsgV (m : PreKeyMsg) : preKeyMsgT.denote :=
  (hdrV m.hdr, (m.ephAPk, (m.pqRatchetMsg, m.aeadCt)))
def preKeyMsgOfV (v : preKeyMsgT.denote) : PreKeyMsg :=
  ⟨hdrOfV v.1, v.2.1, v.2.2.1, v.2.2.2⟩

@[reducible] def authQT : PT :=
  .sum .nat (.sum .nat (.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat))
  (.sum (.prod .nat (.prod .nat (.prod bundleT (.prod (B 32) (B 32)))))
  (.sum (.prod .nat (.prod .nat (.prod bundleT (.prod (B 32) (B 32)))))
  (.sum (.prod .nat (.prod .nat (.prod .nat preKeyMsgT)))
  (.sum (.prod .nat (.prod .nat (.prod .nat preKeyMsgT)))
  (.sum (B 192) (.sum (.prod (B 32) (B 32)) (.sum .unit (B 32)))))))))))

def authQenc {S : Setup} : AuthQuery S → authQT.denote
  | .initPrin u => .inl u.val
  | .corruptIK u => .inr (.inl u.val)
  | .genSPK u j => .inr (.inr (.inl (u.val, j.val)))
  | .genOPK u j o => .inr (.inr (.inr (.inl (u.val, (j.val, o.val)))))
  | .sendOPK u i b m0 m1 =>
    .inr (.inr (.inr (.inr (.inl (u.val, (i.val, (bundleV b, (m0, m1))))))))
  | .sendNoOPK u i b m0 m1 =>
    .inr (.inr (.inr (.inr (.inr (.inl (u.val, (i.val, (bundleV b, (m0, m1)))))))))
  | .recvOPK k j o msg =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inl (k.val, (j.val, (o.val, preKeyMsgV msg)))))))))
  | .recvNoOPK k j l msg =>
    .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inl (k.val, (j.val, (l.val, preKeyMsgV msg))))))))))
  | .roQuery sec =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))
  | .roRootQuery rk dh =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (rk, dh))))))))))
  | .revealDhSecrets =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | .registerKey sk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk))))))))))

@[reducible] def authRT : PT :=
  .sum .unit (.sum (.prod (B 32) (B 32)) (.sum (B 32) (.sum (.prod (B 32) (B 32))
  (.sum bundleT (.sum preKeyMsgT
  (.sum (.prod drKeyT (.prod (B 32) (.prod (B 32) preKeyMsgT)))
  (.sum .unit (.sum (.prod drKeyT (.prod (B 32) (.prod (B 32) (B 32))))
  (.sum drKeyT (.sum (.prod (B 32) (B 32)) dhSecretsT))))))))))

def authRdec : authRT.denote → AuthResponse
  | .inl () => .noneResp
  | .inr (.inl (ik, s)) => .initPrinResp ik s
  | .inr (.inr (.inl pk)) => .pkResp pk
  | .inr (.inr (.inr (.inl (ik, s)))) => .corrResp ik s
  | .inr (.inr (.inr (.inr (.inl b)))) => .bundleResp (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inl m))))) => .sendFreshResp (preKeyMsgOfV m)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (dk, (rk, (ck, m))))))))) =>
    .sendUnfreshResp (drKeyOfV dk) rk ck (preKeyMsgOfV m)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => .recvHonestResp
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (dk, (rk, (ck, pt))))))))))) =>
    .recvUnfreshResp (drKeyOfV dk) rk ck pt
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk))))))))) =>
    .drKeyResp (drKeyOfV dk)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (rk, ck))))))))))) =>
    .rootKdfResp rk ck
  | .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr (.inr (.inr (.inr (l1, (l2, (l3, l4))))))))))))) =>
    .dhSecretsResp l1 l2 l3 l4

/-- `ReductionDsl` game codec for `authSpec S`. -/
def authCodec (S : Setup) : GameCodec pqSig (authSpec S) where
  Q := authQT
  R := authRT
  qenc := authQenc
  rdec := fun _ r => authRdec r
  codecCost := 32

/-! ## Legacy cost and block-size bounds -/

def stepCostBudget (S : Setup) (b : QueryBudget) : Nat :=
  2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2

def outputSizeBudget (S : Setup) (b : QueryBudget) (ℓ : Nat) : Nat :=
  2 * stepCostBudget S b * (ℓ + 1) + 2 * (b.q_total + 1) * ℓ

export _root_.ReductionDsl (ValFits)

abbrev PqOpsSizeHonest {S : Sig} (O : Ops S) : Prop :=
  ∀ (o : O.Op) (x : (O.dom o).denote) (B : ℕ),
    ValFits B (O.dom o) x → ValFits (B + O.cost o) (O.cod o) (O.eval o x)

abbrev PqSampSizeHonest {S : Sig} (X : Samplers S) : Prop :=
  ∀ (s : X.Samp) (x : (X.sDom s).denote) (B : ℕ),
    ValFits B (X.sDom s) x →
    ∀ y ∈ support (X.samp s x), ValFits (B + X.sCost s) (X.sTy s) y

/-- Legacy output block-size bound for a one-stage `CostedReduction` over `pqxdhOps`. -/
def GRedBlockBounded {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn out : Ty pqSig}
    (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqxdhOps I G C rIn .unit .bool out) : Prop :=
  (∀ g x u, ValFits ℓ (I.cod g) (I.dec g x u)) →
  (∀ t, ValFits ℓ C.Q (C.qenc t)) →
  ∀ (A : Unit → OracleComp (unifSpec + G) Bool),
    (∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total) →
    ∀ (x : rIn.denote), ValFits ℓ rIn x →
      ∀ y ∈ support (R.eval A x), ValFits (outputSizeBudget S b ℓ) out y

/-- Legacy output block-size bound for a two-stage `TwoStageCostedReduction` over `pqxdhOps`. -/
def GRed2BlockBounded {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn ch rIn2 out : Ty pqSig}
    (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : TwoStageCostedReduction pqxdhOps I G C rIn .unit .bool ch rIn2 out) : Prop :=
  (∀ g x u, ValFits ℓ (I.cod g) (I.dec g x u)) →
  (∀ t, ValFits ℓ C.Q (C.qenc t)) →
  ∀ (A : Unit → OracleComp (unifSpec + G) Bool) (x : rIn.denote), ValFits ℓ rIn x →
    ∀ cm ∈ support (R.eval1 A x b.q_total false),
      ValFits (outputSizeBudget S b ℓ) ch cm.1 ∧
      ∀ (y : rIn2.denote), ValFits ℓ rIn2 y →
        ∀ z ∈ support (R.eval2 cm.2 y b.q_total false),
          ValFits (outputSizeBudget S b ℓ) out z

def primIfacePrimQueryWeight : PTag → ℕ := fun _ => 1

def chalIfacePrimQueryWeight {C : ChallengerOracle} : PTag ⊕ C.Tag → ℕ
  | .inl _ => 1
  | .inr _ => 0

def chalIfaceSigQueryWeight : PTag ⊕ (ℕ+ ⊕ Unit) → ℕ
  | .inr (.inl _) => 1
  | _ => 0

def chalIfaceDdhQueryWeight : PTag ⊕ (ℕ+ ⊕ Unit) → ℕ
  | .inr (.inr ()) => 1
  | _ => 0

def chalIfaceChalQueryWeight {C : ChallengerOracle} : PTag ⊕ C.Tag → ℕ
  | .inl _ => 0
  | .inr _ => 1

def samplerZeroQueryWeight : PSamp → ℕ := fun _ => 0

end SignalPqxdh.LegacyCosted
