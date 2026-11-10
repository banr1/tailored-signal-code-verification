/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs

/-!
# PQXDH and SPQR V1 Primitive Hooks

**Trusted: the statement.** External-call hooks for the PQXDH and SPQR V1 cryptographic primitives
(SHA-512 block compression, `curve25519-dalek` Edwards/scalar operations for XEdDSA, Kyber1024
encapsulation/decapsulation, incremental ML-KEM-768, and `libcrux_hmac::hmac`), assembled into
`spqrHookTable` and `pqxdhHookTable`. See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc (toLEBytes returnToLinkRegister)
open CryptoVerification.LibsignalSpqrV1
  (MlKem mlkemFromSeedName mlkemPk1Name mlkemPk2Name mlkemEncaps1Name mlkemEncaps2Name
   mlkemDecapsName mlkemValidatePkName libcruxHmacName)

/-! ## Stub names -/

/-- `sha2::sha512::compress512(state = x0, blocks = x1, n = x2)`. -/
abbrev compress512Name : String := "sha2::sha512::compress512"
/-- `MontgomeryPoint::to_edwards(&self = x0, sign = w1) -> Option<EdwardsPoint>` (sret `x8`). -/
abbrev toEdwardsName : String := "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
/-- `EdwardsPoint::compress(&self = x0) -> CompressedEdwardsY` (sret `x8`). -/
abbrev compressName : String := "<curve25519_dalek::edwards::EdwardsPoint>::compress"
/-- `<EdwardsPoint as Neg>::neg(self = x0) -> EdwardsPoint` (sret `x8`). -/
abbrev edNegName : String :=
  "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg"
/-- `EdwardsPoint::is_torsion_free(&self = x0) -> bool`. -/
abbrev torsionFreeName : String := "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint(a = x0, A = x1, b = x2)` (sret `x8`). -/
abbrev dsmbName : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"
/-- `Scalar::from_bytes_mod_order(bytes = x0) -> Scalar` (sret `x8`). -/
abbrev scalarModName : String := "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"
/-- `Scalar::from_bytes_mod_order_wide(bytes = x0) -> Scalar` (sret `x8`). -/
abbrev scalarWideName : String := "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"
/-- `mlkem1024::kyber::encapsulate(pk = x0, randomness = x1) -> (ct, ss)` (sret `x8`). -/
abbrev kemEncapsName : String := "libcrux_ml_kem::mlkem1024::kyber::encapsulate"
/-- `mlkem1024::kyber::decapsulate(sk = x0, ct = x1) -> ss` (sret `x8`). -/
abbrev kemDecapsName : String := "libcrux_ml_kem::mlkem1024::kyber::decapsulate"

/-! ## The hooks -/

/-- The `n` bytes at `a`, as a vector. -/
def readVecN (m : Memory) (a : BitVec 64) (n : Nat) : List.Vector (BitVec 8) n :=
  ⟨m.readBytes a n, Memory.readBytes_length m a n⟩

/-- The SHA-512 chaining state stored at `a`: eight native little-endian `u64` words
(`sha2`'s `[u64; 8]`). -/
def readSha512State (m : Memory) (a : BitVec 64) : Sha512State :=
  List.Vector.ofFn fun i : Fin 8 => m.read64 (a + BitVec.ofNat 64 (8 * i.val))

/-- The 64 bytes of a SHA-512 chaining state as stored (each word little-endian). -/
def sha512StateBytesLE (h : Sha512State) : List (BitVec 8) :=
  h.toList.flatMap (toLEBytes 8)

/-- The 128-byte blocks of `bs` (a trailing partial block is dropped; the hook reads exactly
`128 n` bytes and `sha512Pad`'s output is a multiple of 128, so there is none). As `HMAC.chunks64`. -/
def chunks128 (bs : List (BitVec 8)) : List (List (BitVec 8)) :=
  List.ofFn fun i : Fin (bs.length / 128) => (bs.drop (128 * i.val)).take 128

/-- `sha2::sha512::compress512(state = x0, blocks.ptr = x1, blocks.len = x2)`: with `st` the eight
LE words at `x0` and `bs` the `128 · x2` bytes at `x1`,
`mem[x0 .. x0+64] := sha512StateBytesLE ((chunks128 bs).foldl F512 st)` (all inputs read before
writing); `pc := lr`. As `LibsignalHmac.compress256Hook` for SHA-256. -/
def compress512Hook (F512 : Sha512State → List (BitVec 8) → Sha512State) (s : State) :
    State :=
  let st := readSha512State s.mem (s.readReg64 .x0)
  let bs := s.mem.readBytes (s.readReg64 .x1) (128 * (s.readReg64 .x2).toNat)
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (sha512StateBytesLE ((chunks128 bs).foldl F512 st))))

/-- `MontgomeryPoint::to_edwards(&u = x0, sign = w1)` with `Option<EdwardsPoint>` at the sret `x8`:
`some p` = tag `1` (u64) @0 and the 160 bytes of `p` @8; `none` = tag `0` @0, the other bytes
unchanged. The sign bit is `w1 & 1` (`tbz w1, #0`; callers pass `sig[63] >> 7` or `0`). The callers
test only `tag == 1` (`ldr x8, [sret]; cmp x8, #1`). -/
def toEdwardsHook
    (montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160))
    (s : State) : State :=
  let r := s.readReg64 .x8
  let m := match montToEd (readVecN s.mem (s.readReg64 .x0) 32) ((s.readReg64 .x1).setWidth 8 &&& 1#8) with
    | some p => (s.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList
    | none => s.mem.write64 r 0#64
  returnToLinkRegister (s.setMem m)

/-- `EdwardsPoint::compress(&p = x0)`: `mem[x8 .. +32] := compress mem[x0 .. +160]`; `pc := lr`. -/
def compressHook (compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32) (s : State) :
    State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (compress (readVecN s.mem (s.readReg64 .x0) 160)).toList))

/-- `<EdwardsPoint as Neg>::neg(&p = x0)`: `mem[x8 .. +160] := edNeg mem[x0 .. +160]`;
`pc := lr`. -/
def edNegHook (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) (s : State) :
    State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (edNeg (readVecN s.mem (s.readReg64 .x0) 160)).toList))

/-- `EdwardsPoint::is_torsion_free(&p = x0) -> bool`: `x0 := 1` if `isTorsionFree mem[x0 .. +160]`,
else `0`; `pc := lr`. -/
def torsionFreeHook (isTorsionFree : List.Vector (BitVec 8) 160 → Bool) (s : State) : State :=
  returnToLinkRegister (s.writeReg64 .x0
    (if isTorsionFree (readVecN s.mem (s.readReg64 .x0) 160) then 1#64 else 0#64))

/-- `vartime_double_scalar_mul_basepoint(&a = x0, &A = x1, &b = x2)`:
`mem[x8 .. +160] := dsmb mem[x0 .. +32] mem[x1 .. +160] mem[x2 .. +32]`, the double scalar
multiplication `a·A + b·B` with the basepoint `B` (XEdDSA passes `h`, `-A`, `s`); `pc := lr`. -/
def dsmbHook (dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160) (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (dsmb (readVecN s.mem (s.readReg64 .x0) 32) (readVecN s.mem (s.readReg64 .x1) 160)
      (readVecN s.mem (s.readReg64 .x2) 32)).toList))

/-- `Scalar::from_bytes_mod_order(&b = x0)`: `mem[x8 .. +32] := scalarMod mem[x0 .. +32]`;
`pc := lr`. -/
def scalarModHook (scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32) (s : State) :
    State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (scalarMod (readVecN s.mem (s.readReg64 .x0) 32)).toList))

/-- `Scalar::from_bytes_mod_order_wide(&b = x0)`: `mem[x8 .. +32] := scalarWide mem[x0 .. +64]`;
`pc := lr`. -/
def scalarWideHook (scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32)
    (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (scalarWide (readVecN s.mem (s.readReg64 .x0) 64)).toList))

/-- `kyber::encapsulate(&pk = x0, randomness = x1)` with `(ct, ss)` at the sret `x8`: the 1568-byte
ciphertext @0 and the 32-byte shared secret @`0x620` of `encaps mem[x0 .. +1568] mem[x1 .. +32]`;
`pc := lr`. The caller (`initialize_alice_session::<PqxdhRng>`) fills the 32 coin bytes from 32
`next_u32` calls, keeping the low byte of each (so coin `i` is tape byte `4 i` of that segment). -/
def kemEncapsHook (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32) (s : State) : State :=
  let r := s.readReg64 .x8
  let o := encaps (readVecN s.mem (s.readReg64 .x0) 1568) (readVecN s.mem (s.readReg64 .x1) 32)
  returnToLinkRegister (s.setMem ((s.mem.writeBytes r o.1.toList).writeBytes (r + 0x620#64) o.2.toList))

/-- `kyber::decapsulate(&sk = x0, &ct = x1)`: `mem[x8 .. +32] := decaps mem[x0 .. +3168]
mem[x1 .. +1568]`; `pc := lr`. -/
def kemDecapsHook (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 →
    List.Vector (BitVec 8) 32) (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (decaps (readVecN s.mem (s.readReg64 .x0) 3168)
      (readVecN s.mem (s.readReg64 .x1) 1568)).toList))

/-! ## The SPQR V1 hooks -/

/-- `<KeyPairCompressedBytes>::from_seed(&seed = x0)` with sret `x8`: writes the 2400-byte
compressed keypair `(K.fromSeed mem[x0 .. +64]).2.2` at `x8`. -/
def mlkemFromSeedHook (K : MlKem) : State → State :=
  retHook fun s =>
    s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (K.fromSeed (readVecN s.mem (s.readReg64 .x0) 64)).2.2.toList)

/-- `<KeyPairCompressedBytes>::pk1(&kp = x0) -> &[u8; 64]`: returns `x0 + 2304#64`. -/
def mlkemPk1Hook : State → State :=
  retHook fun s => s.writeReg64 .x0 (s.readReg64 .x0 + 2304#64)

/-- `<KeyPairCompressedBytes>::pk2(&kp = x0) -> &[u8; 1152]`: returns `x0 + 1152#64`. -/
def mlkemPk2Hook : State → State :=
  retHook fun s => s.writeReg64 .x0 (s.readReg64 .x0 + 1152#64)

/-- `mlkem768::incremental::encapsulate1(pk1 = (x0, x1), &rand = x2, es = (x3, x4), ss = (x5, x6))`
with sret `x8`: if `es.len < 2080` (`x4`) or `ss.len < 32` (`x6`), writes
`Err(Error::InvalidOutputLength)` (`[1#8, 1#8]`) at `x8` leaving `es` and `ss` untouched;
otherwise on `some (ct1, es, ss)`, writes `0#8 :: ct1` at `x8`, `es` at `x3`, and `ss` at `x5`;
on `none`, writes `1#8` at `x8`. -/
def mlkemEncaps1Hook (K : MlKem) : State → State :=
  retHook fun s =>
    let ret := s.readReg64 .x8
    if (s.readReg64 .x4).toNat < 2080 || (s.readReg64 .x6).toNat < 32 then
      s.setMem (s.mem.writeBytes ret [1#8, 1#8])
    else
      let hdr := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
      let rand := readVecN s.mem (s.readReg64 .x2) 32
      let esA := s.readReg64 .x3
      let ssA := s.readReg64 .x5
      let m := match K.encaps1 hdr rand with
        | some (ct1, es, ss) =>
          ((s.mem.writeBytes ret (0#8 :: ct1.toList)).writeBytes esA es.toList).writeBytes
            ssA ss.toList
        | none =>
          s.mem.writeBytes ret [1#8]
      s.setMem m

/-- `mlkem768::incremental::encapsulate2(&es = x0, &ek = x1)` with sret `x8`: writes the 128-byte
`ct2 = K.encaps2 mem[x0 .. +2080] mem[x1 .. +1152]` at `x8`. -/
def mlkemEncaps2Hook (K : MlKem) : State → State :=
  retHook fun s =>
    let es := readVecN s.mem (s.readReg64 .x0) 2080
    let ek := readVecN s.mem (s.readReg64 .x1) 1152
    s.setMem (s.mem.writeBytes (s.readReg64 .x8) (K.encaps2 es ek).toList)

/-- `mlkem768::incremental::decapsulate_compressed_key(&dk = x0, &ct1 = x1, &ct2 = x2)` with sret
`x8`: writes the 32-byte `K.decaps mem[x0 .. +2400] mem[x1 .. +960] mem[x2 .. +128]` at `x8`. -/
def mlkemDecapsHook (K : MlKem) : State → State :=
  retHook fun s =>
    let dk := readVecN s.mem (s.readReg64 .x0) 2400
    let ct1 := readVecN s.mem (s.readReg64 .x1) 960
    let ct2 := readVecN s.mem (s.readReg64 .x2) 128
    s.setMem (s.mem.writeBytes (s.readReg64 .x8) (K.decaps dk ct1 ct2).toList)

/-- `mlkem768::incremental::validate_pk_bytes(hdr = (x0, x1), ek = (x2, x3))`: returns `0xff#64`
in `x0` when `K.validPkBytes hdr ek = true`, and `0#64` otherwise. -/
def mlkemValidatePkHook (K : MlKem) : State → State :=
  retHook fun s =>
    let hdr := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
    let ek := s.mem.readBytes (s.readReg64 .x2) (s.readReg64 .x3).toNat
    s.writeReg64 .x0 (if K.validPkBytes hdr ek then 0xff#64 else 0#64)

/-- `libcrux_hmac::hmac(alg = w0, key = (x1, x2), data = (x3, x4), tag_len = (w5, x6))` with sret
`x8`: fails closed (`Exception`) when `alg != Algorithm::Sha256` (`w0 != 0#32`); panics when
`key.len() ≥ 2^32` or `data.len() ≥ 2^32`; otherwise allocates a 32-byte `Vec<u8>` (`cap = 32`) at
`x8` holding `HMAC.hmacWith F key data`, truncated (`Vec::truncate`) to `min x6 32` when
`tag_len` is `Some` (`w5 & 1 != 0`). -/
noncomputable def libcruxHmacHook (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState)
    (s : State) : State :=
  if (s.readReg64 .x0).setWidth 32 != 0#32 then
    s.setStatus (.Exception "libcrux_hmac::hmac: alg != Sha256")
  else
    let keyLen := (s.readReg64 .x2).toNat
    let dataLen := (s.readReg64 .x4).toNat
    if keyLen < 2 ^ 32 ∧ dataLen < 2 ^ 32 then
      let key := s.mem.readBytes (s.readReg64 .x1) keyLen
      let data := s.mem.readBytes (s.readReg64 .x3) dataLen
      let tag := HMAC.hmacWith F key data
      let outLen :=
        if (s.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then
          min (s.readReg64 .x6).toNat tag.length
        else
          tag.length
      bumpThen tag.length 1
        (fun s p =>
          retHook (fun s =>
            s.setMem (writeVecHeader (s.mem.writeBytes p tag) (s.readReg64 .x8)
              (BitVec.ofNat 64 tag.length) p (BitVec.ofNat 64 outLen))) s)
        allocPanicHook s
    else
      Rust.panicked s

/-! ## The table -/

/-- **The SPQR V1 rows** (8): the contracts' stubs (`SpqrHooks`), each with its hook above. -/
noncomputable def spqrHookTable (C : Crypto) (K : MlKem) : List (String × (State → State)) :=
  [(mlkemFromSeedName,   mlkemFromSeedHook K),
   (mlkemPk1Name,        mlkemPk1Hook),
   (mlkemPk2Name,        mlkemPk2Hook),
   (mlkemEncaps1Name,    mlkemEncaps1Hook K),
   (mlkemEncaps2Name,    mlkemEncaps2Hook K),
   (mlkemDecapsName,     mlkemDecapsHook K),
   (mlkemValidatePkName, mlkemValidatePkHook K),
   (libcruxHmacName,     libcruxHmacHook C.F)]

/-- **The PQXDH + SPQR rows of the hook table**: the eighteen hooks above. The first rows of
`cliHookTablePlaced` (`SignalSession/CliBinaryPq.lean`, as `cliPqxdhHookTablePlaced`) are these
rows under mangled symbol names, with `libcruxHmacHookMallocng` for `libcrux_hmac::hmac`. -/
noncomputable def pqxdhHookTable (C : Crypto) (Q : PqxdhPrims) : List (String × (State → State)) :=
  [(compress512Name,     compress512Hook Q.F512),
   (toEdwardsName,       toEdwardsHook Q.montToEd),
   (compressName,        compressHook Q.compress),
   (edNegName,           edNegHook Q.edNeg),
   (torsionFreeName,     torsionFreeHook Q.isTorsionFree),
   (dsmbName,            dsmbHook Q.dsmb),
   (scalarModName,       scalarModHook Q.scalarMod),
   (scalarWideName,      scalarWideHook Q.scalarWide),
   (kemEncapsName,       kemEncapsHook Q.encaps),
   (kemDecapsName,       kemDecapsHook Q.decaps)] ++ spqrHookTable C Q.K

end CryptoVerification.E2E
