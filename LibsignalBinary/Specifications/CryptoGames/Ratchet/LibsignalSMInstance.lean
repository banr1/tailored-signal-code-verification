/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith

/-!
# The Fig. 8 instance with public message components, and the libsignal session as an `SMSchemeR`

**Trusted in part.** The theorems of `Computational/Theorems/` use only 26 definitions of this file,
listed in `Computational/docs/TRUSTED_BASE.md` §3: read them. Everything else here is checked by
Lean.

Instantiates ACD19 Fig. 8 on libsignal's primitives (`lFig8` over `lFS`, `lChainPRG`, `lAead`,
`lAeadK`, `lAeadR`, `lIdeal`, `lPubOf`, `lWire`, `lHeader`, `lIds`, `dummyKey`, `Salt32`,
`LibsignalCiphertextWithSalt32`, `LibsignalMsgPublicPart`, DEV-LS8, DEV-LS13, DEV-LS14), wraps the
session model with given epoch-0 keys as an `SMSchemeR` (`libsignalSessionSchemeFromEpoch0Keys`,
DEV-LS26, DEV-LS27), and defines the game configuration (`ratchetKeyAdmissible`, `configR1OnCurve`,
DEV-LS1, DEV-LS3, DEV-LS4, DEV-LS5, DEV-LS6, DEV-LS7), the DH realization predicate
(`X25519RealizesDh`, DEV-LS29), and the salt-PRF / wire-OT-CCA reductions and forgery bound
(`lSaltPRF32`, `lSaltRed`, `lRandSaltBias`, `LibsignalWireOracleSpec`, `lWireRed`,
`macForgeryProb`, `SaltSlotSt`, `slotKeyOf`, `isSlotChalSalt`, `slotSaltImpl`, `slotSaltImplNF`,
`slotSaltRed`, `slotWireRed`, DEV-LS23, DEV-LS25, DEV-LS31).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalInst

open HMAC HKDF CBC LibsignalAead SM.Construction CKA LibsignalSession AEADScheme MACScheme

/-- The salt carried by the Fig. 8 instance: the **32-byte effective HKDF salt** of the SPQR
message key (`effectiveHkdfSalt32`: a missing salt is `0^32`). HKDF-Extract keyed by an absent salt and by
`0^32` computes the same function (`msgKeys_effSalt`), so the instance carries the key HKDF
actually uses: a PRF over salts is then a PRF over `{0,1}^256` (BBGS'23 Thm 11). -/
abbrev Salt32 := List.Vector (BitVec 8) 32

/-- The ciphertext of the per-message AEAD: the wire `(serialized message, 8-byte tag)` and the
salt attached to it (not on the wire). -/
abbrev LibsignalCiphertextWithSalt32 := (List (BitVec 8) × BitVec 64) × Salt32

/-- Public message components (`previous_counter`, SPQR wire message, effective HKDF salt, and
address blob).

**DEV-LS13 (libsignal): public message parts.** libsignal sends `previous_counter`, the SPQR
message, and unacknowledged addresses in the clear (MACed) and derives message keys with the SPQR
salt; challenges in `lFig8` must agree on `LibsignalMsgPublicPart` (`EqualPubChalls`). -/
structure LibsignalMsgPublicPart where
  pn : BitVec 32
  /-- SPQR wire message (`pq_ratchet`). -/
  pqmsg : List (BitVec 8)
  /-- Effective 32-byte HKDF salt of the message keys (ghost, not on the wire). -/
  salt : Salt32
  addrs : Option (List (BitVec 8))
  deriving DecidableEq

instance decEqHeaderLPub {Pt : Type} [DecidableEq Pt] : DecidableEq (Header Pt × LibsignalMsgPublicPart) :=
  instDecidableEqProd

instance decEqFig8C {Pt : Type} [DecidableEq Pt] :
    DecidableEq (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :=
  instDecidableEqProd

/-- Placeholder public key (`0xff^32`, non-canonical `u ≥ 2²⁵⁵ - 19` outside `encT`'s image) used
for Fig. 8's unused epoch-0 header `(0, none)`. -/
def dummyKey : PublicKey := ⟨List.Vector.replicate 32 0xff⟩

/-- The identity keys MACed in epoch `t`: sender's then receiver's (`A` sends in odd epochs). -/
def lIds (idOf : Party → IdentityKey) (t : ℕ) : SerializedIdentityKeys :=
  macIds (idOf (Party.senderOf t)) (idOf (Party.senderOf t).other)

/-- The wire header of the message with index `i` (1-based), Fig. 8 header `(t, T)`, public part
`p`: version 4, ratchet key `encT T`, counter `i − 1`, `pn`, `pqmsg`, `addrs`. -/
def lHeader {Pt : Type} (encT : Pt → PublicKey) (i : ℕ) (h : Header Pt) (p : LibsignalMsgPublicPart) : SignalHeader :=
  ⟨currentVersion, (h.2.map encT).getD dummyKey, BitVec.ofNat 32 (i - 1), p.pn, p.pqmsg, p.addrs⟩

/-- The wire AEAD (`libsignalWireAead`) with libsignal's codec and plaintext length `ℓ`, no address check. -/
abbrev lWire (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) :=
  libsignalWireAead C.E C.D C.F ℓ (signalWireCodec codec) (fun _ => none) none

/-- The per-message AEAD keyed by the message keys themselves (no salt check): `lAead` after
`deriveMessageKeys F (some salt) seed`. -/
def lAeadK {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    AEADScheme DerivedMessageKeys ((ℕ × Header Pt) × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32 where
  enc mk a m := ((lWire C codec ℓ).enc mk (lIds idOf a.1.2.1) (lHeader encT a.1.1 a.1.2 a.2) m, a.2.salt)
  dec mk a c :=
    match (lWire C codec ℓ).dec mk (lIds idOf a.1.2.1) c.1 with
    | none => none
    | some (h, m) => if h = lHeader encT a.1.1 a.1.2 a.2 then some (padOrTruncatePlain ℓ m) else none

/-- **The per-message AEAD** with AD `((i, (t, T)), (pn, pqmsg, salt, addrs))` (see the module doc):
the salt must equal the AD's; keys `deriveMessageKeys F (some salt) seed`; then `lAeadK`. -/
def lAead {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    AEADScheme (BitVec 256) ((ℕ × Header Pt) × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32 where
  enc seed a m := (lAeadK C codec ℓ encT idOf).enc
    (deriveMessageKeys C.F (some a.2.salt) (keyToBytes32 seed)) a m
  dec seed a c :=
    if c.2 ≠ a.2.salt then none else
    (lAeadK C codec ℓ encT idOf).dec (deriveMessageKeys C.F (some a.2.salt) (keyToBytes32 seed)) a c

/-- The public part of a ciphertext: `(pn, pqmsg)` parsed from the wire, the attached salt. -/
def lPubOf (codec : SignalMessageProtoCodec) (c : LibsignalCiphertextWithSalt32) : Option LibsignalMsgPublicPart :=
  ((signalWireCodec codec).parse c.1.1).map fun hb =>
    ⟨hb.1.previousCounter, hb.1.pqRatchet, c.2, hb.1.addresses⟩

/-- The chain PRG: `ck ↦ (HMAC(ck, 0x02), HMAC(ck, 0x01))` (next chain key, message-key seed). The
SPQR salt enters only in `lAead` (unlike `Ratchet.chainPRG F salts`).

**DEV-LS14 (libsignal): message keys from a chain step and a salted HKDF.** ACD19 Fig. 6 uses one
PRG `G : W → W × K`. libsignal's chain step yields the next chain key and a 32-byte seed, and the
AEAD key is `HKDF(salt, seed, "WhisperMessageKeys", 80)` (AES key, MAC key, IV), computed per
message inside `lAead`. The IV is derived, not random. Effect: none (one-time keys). -/
def lChainPRG (F : ShaState → List (BitVec 8) → ShaState) (_p : ℕ) :
    PRGScheme (BitVec 256) (BitVec 256 × BitVec 256) :=
  ⟨fun ck => ((hmacPRF F).tag ck chainKeySeed, (hmacPRF F).tag ck messageKeySeed)⟩

/-- **The FS-AEAD of the instance**: Fig. 6 with `lAead.movePubPartToAD lPubOf` (messages `LibsignalMsgPublicPart × Plain ℓ`). -/
def lFS {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (maxSkip : ℕ) :=
  FSAEAD.fromAEADPRG ((lAead C codec ℓ encT idOf).movePubPartToAD (lPubOf codec)) (lChainPRG C.F) maxSkip

/-- **The Fig. 8 instance** attacked by the reduction `sim` (messages `LibsignalMsgPublicPart × Plain ℓ`). -/
def lFig8 {Pt : Type} [Zero Pt] (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) :=
  scheme (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip) lam

/-- `lAead` with its AD re-associated as `(i, ((t, T), pub))`, the form of Theorem 5. -/
def lAeadR {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    AEADScheme (BitVec 256) (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32 where
  enc k a m := (lAead C codec ℓ encT idOf).enc k ((a.1, a.2.1), a.2.2) m
  dec k a c := (lAead C codec ℓ encT idOf).dec k ((a.1, a.2.1), a.2.2) c

/-- The ideal ciphertext of `lAeadR` for AD `(i, ((t, T), pub))`: the wire AEAD's ideal wire for the
header (uniform body and tag), with the AD's salt attached. -/
def lIdeal {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) : ProbComp LibsignalCiphertextWithSalt32 := do
  let w ← (lWire C codec ℓ).idealEnc (lHeader encT a.1 a.2.1 a.2.2)
  return (w, a.2.2.salt)

/-- The libsignal session as an `SMSchemeR` with the epoch-0 root and chain keys given (the key's
`k_root` is ignored): the distinguisher `epoch0Distinguisher` of the epoch-0 term runs the R1 game
on it. -/
def libsignalSessionSchemeFromEpoch0Keys {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ) (rk0 : RootKey)
    (ck0 : BitVec 256) :
    SMSchemeR (RootKey × BitVec 256 × BitVec 256 × BitVec 256) (GhostState PQ) (Plain ℓ) PQC
      (BitVec 256) (List (BitVec 8)) where
  initA k := P.initA ⟨rk0, ck0, k.2.1, k.2.2.1, k.2.2.2⟩
  initB k := P.initB ⟨rk0, ck0, k.2.1, k.2.2.1, k.2.2.2⟩
  send g m r := P.send g m.toList r
  receive g c rc := (P.receive g c rc).map fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)

/-- The wire's ratchet key is the encoding of a group element and a parseable wire has fewer than
`2³²` bytes (or the wire does not parse): the admissibility predicate of injections in the
libsignal game.

**DEV-LS5 (libsignal): only injections with on-curve ratchet keys and `< 2³²`-byte parseable wires.**
ACD19 Fig. 2 accepts any injected ciphertext. libsignal accepts any 32 bytes as a public key (twist
points, mixed-order and non-canonical encodings), which the Fig. 8 instance cannot express, since
its CKA messages are group elements. So the game refuses an injection whose ratchet key is not
`encT` of a group element, or whose parseable wire has `2³²` or more bytes (already excluded by
`shortCiphertext` in the binary harness `bhInjOK`). Effect: restricts the adversary. -/
def ratchetKeyAdmissible {Pt : Type} (codec : SignalMessageProtoCodec) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    [DecidableEq PublicKey] (w : List (BitVec 8)) : Bool :=
  if w.length < 9 then true else
  match (signalWireCodec codec).parse (w.take (w.length - 8)) with
  | none => true
  | some (h, _) =>
    decide (w.length < 2 ^ 32) &&
      match decT h.senderRatchetKey with
      | some T => decide (encT T = h.senderRatchetKey)
      | none => false

/-- **The libsignal game**: `configR1` (ACD19 App. A's H1 with DEV-LS1–DEV-LS4 and DEV-LS6) with
injections restricted to on-curve ratchet keys (DEV-LS5).

**DEV-LS7 (formalization): rules inherited from the generic restricted game.** The restricted game
of `SM/LibsignalGame.lean` keeps the generic game's own deviations from ACD19 Fig. 2 (the `DEV-SM`
entries): `corr-P` also waits until no uncompromised record of the other party is in transit, the
epoch cap `qep`, and `tL` only grows. The Fig. 8 side runs with epoch cap `qep + 1`, because a
window reduction's hidden `transmit` can open one more epoch. Effect: restricts the adversary. -/
def configR1OnCurve {St Msg : Type} (onImage : List (BitVec 8) → Bool) : SM.ConfigR St Msg (List (BitVec 8)) :=
  { SM.configR1 with injOK := onImage }

/-- **The salt PRF**: seed ↦ 32-byte salt ↦ message keys, `deriveMessageKeys F (some salt) seed`
(HKDF-Extract keyed by the seed in its message slot, then Expand). Its value at `s` is exactly the key `lAead` uses for a
ciphertext carrying `s`.

**DEV-LS25 (libsignal): one seed, several salts.** In ACD19 Fig. 6 each message key is used once.
libsignal takes the salt from the unauthenticated SPQR message before it checks the MAC, so an
active adversary can make the receiver expand one seed under several salts. The proof treats
`seed ↦ salt ↦ keys` as a PRF over 32-byte salts (the dual-PRF use of HMAC, BBGS'23 Thm 11 with
`S = {0,1}^256`), bounds non-challenge-salt decryptions by `macForgeryTerm` before the wire
reduction, and reduces the challenge salt (`j = 0`) to `lWire`. Effect: constants (a salt-PRF term
per slot). -/
def lSaltPRF32 (F : ShaState → List (BitVec 8) → ShaState) : MACScheme (BitVec 256) Salt32 DerivedMessageKeys :=
  ⟨fun seed salt => deriveMessageKeys F (some salt) (keyToBytes32 seed)⟩

/-- **The salt-PRF reduction** (used by `LibsignalSM.Inst.lAeadR_otcca`, the step that replaces
the salt PRF by a random function): plays `lAeadR`'s OT-CCA game for `B` with its own hidden bit
`b`, getting the message keys of every salt from the PRF oracle; outputs `b == b'`. Real PRF =
the OT-CCA game of `lAeadR` (ideal `lIdeal`); random function = independent keys per salt. -/
def lSaltRed {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    PRFAdversary Salt32 DerivedMessageKeys :=
  show OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys) Bool from do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys) Bool)
  let ae := lAeadK C codec ℓ encT idOf
  let impl : QueryImpl (unifSpec + otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32))
        (OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys))) := fun q => match q with
    | .inl n => StateT.lift (query (spec := unifSpec + prfSpec Salt32 DerivedMessageKeys) (.inl n))
    | .inr (.inl ⟨a, m⟩) => do
      if (← get).isSome then return none
      let mk ← StateT.lift (evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) a.2.2.salt)
      let e ← if b then StateT.lift (liftM (lIdeal C codec ℓ encT a))
        else pure (ae.enc mk ((a.1, a.2.1), a.2.2) m)
      set (some (a, e))
      return some e
    | .inr (.inr ⟨a, e⟩) => do
      if b || (← get) == some (a, e) || e.2 ≠ a.2.2.salt then return none
      let mk ← StateT.lift (evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) a.2.2.salt)
      return ae.dec mk ((a.1, a.2.1), a.2.2) e
  let b' ← (simulateQ impl B).run' none
  return b == b'

/-- The OT-CCA bias of `B` when every salt's message keys are independent and uniform (the
random-function branch of `lSaltRed`); the wire step of the proof (`lRandSaltBias_le_short`)
bounds it by the wire AEAD's OT-CCA terms. -/
noncomputable def lRandSaltBias {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    ℝ≥0∞ :=
  𝒟[MACScheme.branch (lSaltPRF32 C.F) true (lSaltRed C codec ℓ encT idOf B)].boolBias

/-- The oracle interface of the wire AEAD's game for the instance (header `SignalHeader`). -/
abbrev LibsignalWireOracleSpec (ℓ : ℕ) :=
  unifSpec + WireAEAD.wireSpec SerializedIdentityKeys SignalHeader (Plain ℓ) (List (BitVec 8)) (BitVec 64)

/-- **The wire reduction** from the random-salt experiment (`lRandSaltBias`) to the wire AEAD's
OT-CCA game (guess `j`: the challenge's salt is the `j`-th distinct salt `B` uses). Salts other
than the guessed one get lazily sampled independent message keys (the random-function world); a
second encryption query is answered `none` (as in `lSaltRed`); the guessed salt's encryption /
decryption go to the wire AEAD's game (header and AD checked as in `lAeadK`); if `B`'s encryption
salt is not the `j`-th, the reduction outputs a uniform bit, and also if `B` made no encryption
query and `j ≠ 0`. Pre-challenge
decryptions and decryptions under non-guessed salts return `none` directly (in the `b = true` world
they are rejected; in the `b = false` world the difference is paid once by `qd * macForgeryProb`
before the reduction, so the challenge encryption always lands at `j = 0`). -/
def lWireRed {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    WireAEAD.WireAdversary SerializedIdentityKeys SignalHeader (Plain ℓ) (List (BitVec 8)) (BitVec 64) :=
  show OracleComp (LibsignalWireOracleSpec ℓ) Bool from do
  let _ := (C, codec)
  let impl : QueryImpl (unifSpec + otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (List Salt32 × List (Salt32 × DerivedMessageKeys) × Bool × Bool) (OracleComp (LibsignalWireOracleSpec ℓ))) :=
      fun q =>
    let slot (salt : Salt32) :
        StateT (List Salt32 × List (Salt32 × DerivedMessageKeys) × Bool × Bool) (OracleComp (LibsignalWireOracleSpec ℓ)) ℕ := do
      let st ← get
      match st.1.idxOf? salt with
      | some n => return n
      | none => set (st.1 ++ [salt], st.2.1, st.2.2.1, st.2.2.2); return st.1.length
    match q with
    | .inl n => StateT.lift (query (spec := LibsignalWireOracleSpec ℓ) (.inl n))
    | .inr (.inl ⟨a, m⟩) => do
      if (← get).2.2.2 then return none
      let n ← slot a.2.2.salt
      modify fun st => (st.1, st.2.1, st.2.2.1, true)
      if n ≠ j then
        modify fun st => (st.1, st.2.1, true, st.2.2.2)
        return none
      let r ← StateT.lift (query (spec := LibsignalWireOracleSpec ℓ)
        (.inr (.inl (lIds idOf a.2.1.1, lHeader encT a.1 a.2.1 a.2.2, m))))
      return r.map fun w => (w, a.2.2.salt)
    | .inr (.inr ⟨a, e⟩) => do
      if !(← get).2.2.2 || e.2 ≠ a.2.2.salt then return none
      let n ← slot a.2.2.salt
      if n = j then
        let r ← StateT.lift (query (spec := LibsignalWireOracleSpec ℓ) (.inr (.inr (lIds idOf a.2.1.1, e.1))))
        return match r with
          | none => none
          | some (h, m) => if h = lHeader encT a.1 a.2.1 a.2.2 then some (padOrTruncatePlain ℓ m) else none
      else
        return none
  let (b', st) ← (simulateQ impl B).run ([], [], false, false)
  if st.2.2.1 || (!st.2.2.2 && j ≠ 0) then (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (LibsignalWireOracleSpec ℓ) Bool) else return b'

/-- Worst-case probability over identity keys, `< 2³²`-byte serialized messages, and 8-byte tags
that a fixed wire `(ser, tag)` verifies under uniform `DerivedMessageKeys` (bounded in length to
avoid Borel–Cantelli vacuity; reflects pointwise key-regularity of `F` in `hmacWith F`).

**DEV-LS23 (libsignal): the 8-byte MAC tag and the forgery term.** libsignal truncates the HMAC tag
to 8 bytes (`≥ 2⁻⁶⁴` forgery probability), so `macForgeryProb` enters `fsShortBound` as a
bounded-length non-uniform supremum over concrete tests of `F` (DEV-LS31). -/
noncomputable def macForgeryProb (F : ShaState → List (BitVec 8) → ShaState) : ℝ≥0∞ :=
  ⨆ (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (_ : ser.length < 2 ^ 32)
    (tag : BitVec 64),
    𝒟[(do let mk ← ($ᵗ DerivedMessageKeys : ProbComp DerivedMessageKeys)
          return ((hmacScheme F).tag mk.2 (ids.toList ++ ser) == tag) : ProbComp Bool)] {true}

/-- A byte list as a 32-byte vector (zero-padded / truncated; identity on 32-byte lists). -/
def vec32 (bs : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  ⟨(bs ++ List.replicate 32 0).take 32, by simp⟩

/-- Per-slot state of the random-salt experiment (`slotSaltImpl` / `slotSaltImplNF`): the recorded
challenge `(AD, ciphertext)` and the lazy salt-to-message-key table. -/
structure SaltSlotSt (Pt : Type) where
  chal : Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32) := none
  table : List (Salt32 × DerivedMessageKeys) := []

/-- Look up or lazily sample the uniform message key for `salt` in `SaltSlotSt`. -/
def slotKeyOf {Pt : Type} (salt : Salt32) : StateT (SaltSlotSt Pt) ProbComp DerivedMessageKeys :=
  StateT.mk fun st =>
    match st.table.lookup salt with
    | some k => pure (k, st)
    | none => (fun k => (k, { st with table := (salt, k) :: st.table })) <$> ($ᵗ DerivedMessageKeys)

/-- Whether `salt` equals the challenge query's salt (or `false` before the challenge query). -/
def isSlotChalSalt {Pt : Type}
    (chal : Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32))
    (salt : Salt32) : Bool :=
  match chal with
  | none => false
  | some (a₀, _) => salt == a₀.2.2.salt

/-- Per-slot oracle implementation of the random-salt experiment (the random-function branch of
`lSaltRed`). -/
def slotSaltImpl {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) :
    QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32) (StateT (SaltSlotSt Pt) ProbComp)
  | .inl n => (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SaltSlotSt Pt) ProbComp) n
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).chal.isSome then return none
    let mk ← slotKeyOf a.2.2.salt
    let e ← if b then StateT.lift (lIdeal C codec ℓ encT a)
      else pure ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)
    modify fun st => { st with chal := some (a, e) }
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    if b || (← get).chal == some (a, e) then return none
    let mk ← slotKeyOf a.2.2.salt
    return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e

/-- Variant of `slotSaltImpl` in which all decryptions on non-challenge salts
(`!isSlotChalSalt st.chal a.2.2.salt`, including all pre-challenge decryptions) return `none`. -/
def slotSaltImplNF {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) :
    QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32) (StateT (SaltSlotSt Pt) ProbComp)
  | .inl n => (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SaltSlotSt Pt) ProbComp) n
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).chal.isSome then return none
    let mk ← slotKeyOf a.2.2.salt
    let e ← if b then StateT.lift (lIdeal C codec ℓ encT a)
      else pure ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)
    modify fun st => { st with chal := some (a, e) }
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    if b || !(isSlotChalSalt (← get).chal a.2.2.salt) || (← get).chal == some (a, e) then return none
    let mk ← slotKeyOf a.2.2.salt
    return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e

/-- **Single-slot salt-PRF reduction wrapper** at step `k` (`0 ≤ k < N`): forwards slot `k + 1` of a
multi-slot `OTCCAAdversary` `B` to the external single-slot `IndexedOtccaSpec` oracle, simulates slots
`1 ≤ i ≤ k` with `slotSaltImpl false` (independent random message keys per salt), and simulates all
remaining slots with `otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)` (`b = false`). -/
def slotSaltRed {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32 :=
  show OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) Bool from do
  let K₀ ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (BitVec 256))
  let ks ← (liftM (FSAEAD.Thm5.sampleKeys (MK := BitVec 256) N) :
    OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (List (BitVec 256)))
  Prod.fst <$> (simulateQ
    (FSAEAD.Thm5.slotRedImpl
      (FSAEAD.Thm5.otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
      (slotSaltImpl C codec ℓ encT idOf false) k) B).run
    (FSAEAD.Thm5.initOStM false K₀ ks, fun _ => {})

/-- **Single-slot wire-OT-CCA reduction wrapper** at step `k`: forwards slot `k + 1` of a
multi-slot `OTCCAAdversary` `B` to the external single-slot `IndexedOtccaSpec` oracle, simulates slots
`1 ≤ i ≤ k` with `slotSaltImpl true` (ideal ciphertexts), and simulates all remaining slots with
`slotSaltImplNF false` (real ciphertexts with non-challenge-salt decryptions rejected). -/
def slotWireRed {Pt : Type} [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32 :=
  show OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) Bool from
  Prod.fst <$> (simulateQ
    (FSAEAD.Thm5.slotRedImpl
      (slotSaltImplNF C codec ℓ encT idOf false)
      (slotSaltImpl C codec ℓ encT idOf true) k) B).run
    (fun _ => {}, fun _ => {})

/-- **The byte-level X25519 of the model realizes the abstract DH function** `Dh`
(`CKA.X25519Model` for the list lifts of `C.X`, `C.pubKey`), and `encT` is the public key of
`encPt`.

**DEV-LS29 (formalization): an abstract DH group.** ACD19 §4.1.2's CKA is over a prime-order group
with DDH. The CKA and PRF-PRNG terms of the theorem are over an abstract `Dh : DHFun (BitVec 256)
Pt`, tied to the model's byte-level X25519 by this hypothesis; clamping and x-only points are
absorbed into the DDH assumption for the X25519 function as used. Effect: none (nothing here is a
proof about real Curve25519). -/
def X25519RealizesDh {Pt : Type} [Zero Pt] (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) : Prop :=
  CKA.X25519Model Dh encPt (fun x u => (C.X (vec32 x) (vec32 u)).toList)
      (fun x => (C.pubKey (vec32 x)).toList)
    ∧ ∀ P, (encT P).bytes = vec32 (encPt P)

end LibsignalInst
end Ratchet
end CryptoGames
