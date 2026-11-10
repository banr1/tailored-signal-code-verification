/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf -- shake: keep
import all Init.Data.Range.Basic

/-!
# SPQR V1: Authenticator (`spqr/src/authenticator.rs`, `src/authenticator/serialize.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `compare_prefix`, `Authenticator.verifyCt_prefix`, `Authenticator.verifyHdr_prefix` and the
test vectors in `Tests`, which are checked by Lean (see `Computational/docs/TRUSTED_BASE.md`).

Models SPQR's epoch authenticator (`Mac`, `AuthError`, `Authenticator` with `macSize`, `new`,
`update`, `intoPb`, `fromPb`), panic-explicit HMAC-SHA256 tag computation and constant-time
verification (`macCt`, `verifyCt`, `verifyCtError`, `macHdr`, `verifyHdr`, `verifyHdrError`,
`hmacU32UnwrapPanic`), and unchecked helpers (`macCtUnchecked`, `macHdrUnchecked`,
`verifyCt_eq_ok_prefix`, `verifyHdr_eq_ok_prefix`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HMAC

/-! ## Unchecked prefix-comparison helper and `sha256With`/`hmacWith` length lemmas -/

/-- Unchecked prefix-comparing helper for `spqr::util::compare` (`src/util.rs:25–33`): accumulates
bitwise XOR differences over `lhs.zip rhs` without the `lhs.length ≤ rhs.length` bounds check. -/
def compare_prefix (lhs rhs : Bytes) : BitVec 8 :=
  isNonZero ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) 0#8)

theorem compare_eq_ok_prefix {lhs rhs : Bytes} (h : lhs.length ≤ rhs.length) :
    compare lhs rhs = .ok (compare_prefix lhs rhs) := by
  simp [compare, compare_prefix, h]

@[simp]
theorem length_sha256With (F : ShaState → List (BitVec 8) → ShaState) (m : Bytes) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize (chunks64 (sha256Pad m)).foldl F sha256IV = s
  rcases s with ⟨l, hl⟩
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | rfl | cases hl

@[simp]
theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState) (k m : Bytes) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith
  exact length_sha256With F _

/-! ## Types and constants (`spqr/src/authenticator.rs`) -/

abbrev Mac := Bytes

/-- Panic site in `libcrux-hmac 0.0.8` (`src/impl_hacl.rs:12,14`): `u32` length unwrap when
`key.length ≥ 2^32` or `data.length ≥ 2^32`. -/
abbrev hmacU32UnwrapPanic : SpqrPanic :=
  .site "libcrux-hmac impl_hacl.rs:12/14 u32 unwrap"

/-- `spqr::authenticator::Error` (`src/authenticator.rs:11–24`). -/
inductive AuthError where
  | invalidCtMac
  | invalidHdrMac
  | authenticatorRootKeyPresent
  | authenticatorRootKeyMissing
  | authenticatorMacKeyPresent
  | authenticatorMacKeyMissing
  deriving DecidableEq, Repr, Inhabited

/-- `impl From<authenticator::Error> for Error` (`src/lib.rs:144–147`). -/
def AuthError.toError : AuthError → Error := fun _ => .macVerifyFailed

/-- `spqr::authenticator::Authenticator` (`src/authenticator.rs:27–30`). -/
structure Authenticator where
  rootKey : Mac
  macKey : Mac
  deriving DecidableEq, Repr, Inhabited

namespace Authenticator

abbrev macSize : ℕ := 32

def updateLabel : Bytes :=
  "Signal_PQCKA_V1_MLKEM768:Authenticator Update".toList.map fun c => BitVec.ofNat 8 c.toNat

def ctLabel : Bytes :=
  "Signal_PQCKA_V1_MLKEM768:ciphertext".toList.map fun c => BitVec.ofNat 8 c.toNat

def hdrLabel : Bytes :=
  "Signal_PQCKA_V1_MLKEM768:ekheader".toList.map fun c => BitVec.ofNat 8 c.toNat

/-- `Authenticator::update` (`src/authenticator.rs:44–54`): derives `(rootKey, macKey)` via 64-byte
HKDF-SHA256 from `rootKey ++ k` and `updateLabel ++ ep.to_be_bytes()` under a 32-byte zero salt. -/
def update (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (k : Bytes) : Authenticator :=
  let ikm := self.rootKey ++ k
  let info := updateLabel ++ toBEBytes 8 ep
  let kdfOut := hkdfToVecUnchecked F (List.replicate 32 0) ikm info 64
  { rootKey := kdfOut.take 32
    macKey := kdfOut.drop 32 }

/-- `Authenticator::new` (`src/authenticator.rs:35–42`). -/
def new (F : ShaState → List (BitVec 8) → ShaState) (rootKey : Bytes) (ep : Epoch) : Authenticator :=
  let result : Authenticator := { rootKey := List.replicate 32 0, macKey := List.replicate 32 0 }
  result.update F ep rootKey

def macCtUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) : Mac :=
  let ctMacData := ctLabel ++ toBEBytes 8 ep ++ ct
  (hmacWith F self.macKey ctMacData).take macSize

@[simp]
theorem length_macCtUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    (self.macCtUnchecked F ep ct).length = 32 := by
  simp [macCtUnchecked, macSize]

/-- `Authenticator::mac_ct` (`src/authenticator.rs:66–79`): HMAC-SHA256 tag over
`ctLabel ++ ep.to_be_bytes() ++ ct`, panicking with `hmacU32UnwrapPanic` if key or input length
reaches `2^32`. -/
def macCt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) : Except SpqrPanic Mac :=
  let ctMacData := ctLabel ++ toBEBytes 8 ep ++ ct
  if self.macKey.length < 2 ^ 32 ∧ ctMacData.length < 2 ^ 32 then
    .ok (self.macCtUnchecked F ep ct)
  else
    .error hmacU32UnwrapPanic

theorem macCt_of_lt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32) :
    self.macCt F ep ct = .ok (self.macCtUnchecked F ep ct) := by
  simp only [macCt, hk, hd, and_self, ↓reduceIte]

def verifyCt_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) : Except AuthError Unit :=
  if compare_prefix expectedMac (self.macCtUnchecked F ep ct) != 0#8 then
    .error .invalidCtMac
  else
    .ok ()

/-- `Authenticator::verify_ct` (`src/authenticator.rs:57–63`): checks `expectedMac` against
`macCt F ep ct` via `Core.compare` (which compares `0..expectedMac.length` and panics if
`expectedMac.length > 32`). -/
def verifyCt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) :
      Except SpqrPanic (Except AuthError Unit) := do
  let mac ← self.macCt F ep ct
  let c ← compare expectedMac mac
  return if c != 0#8 then .error .invalidCtMac else .ok ()

def verifyCtError (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) :
      Except SpqrPanic (Except Error Unit) :=
  (self.verifyCt F ep ct expectedMac).map (Except.mapError AuthError.toError)

theorem verifyCt_eq_ok_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32)
    (hm : expectedMac.length ≤ 32) :
    self.verifyCt F ep ct expectedMac = .ok (self.verifyCt_prefix F ep ct expectedMac) := by
  have hm' : expectedMac.length ≤ (self.macCtUnchecked F ep ct).length := by
    simpa [length_macCtUnchecked] using hm
  simp [verifyCt, macCt_of_lt F self ep ct hk hd, compare_eq_ok_prefix hm', verifyCt_prefix,
     Bind.bind, Except.bind, pure, Except.pure]

def macHdrUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) : Mac :=
  let ctMacData := hdrLabel ++ toBEBytes 8 ep ++ hdr
  (hmacWith F self.macKey ctMacData).take macSize

@[simp]
theorem length_macHdrUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    (self.macHdrUnchecked F ep hdr).length = 32 := by
  simp [macHdrUnchecked, macSize]

/-- `Authenticator::mac_hdr` (`src/authenticator.rs:91–104`): HMAC-SHA256 tag over
`hdrLabel ++ ep.to_be_bytes() ++ hdr`, panicking with `hmacU32UnwrapPanic` if key or input length
reaches `2^32`. -/
def macHdr (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) : Except SpqrPanic Mac :=
  let ctMacData := hdrLabel ++ toBEBytes 8 ep ++ hdr
  if self.macKey.length < 2 ^ 32 ∧ ctMacData.length < 2 ^ 32 then
    .ok (self.macHdrUnchecked F ep hdr)
  else
    .error hmacU32UnwrapPanic

theorem macHdr_of_lt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32) :
    self.macHdr F ep hdr = .ok (self.macHdrUnchecked F ep hdr) := by
  simp only [macHdr, hk, hd, and_self, ↓reduceIte]

def verifyHdr_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) : Except AuthError Unit :=
  if compare_prefix expectedMac (self.macHdrUnchecked F ep hdr) != 0#8 then
    .error .invalidHdrMac
  else
    .ok ()

/-- `Authenticator::verify_hdr` (`src/authenticator.rs:82–88`): checks `expectedMac` against
`macHdr F ep hdr` via `Core.compare` (panicking if `expectedMac.length > 32`). -/
def verifyHdr (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) :
      Except SpqrPanic (Except AuthError Unit) := do
  let mac ← self.macHdr F ep hdr
  let c ← compare expectedMac mac
  return if c != 0#8 then .error .invalidHdrMac else .ok ()

def verifyHdrError (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) :
      Except SpqrPanic (Except Error Unit) :=
  (self.verifyHdr F ep hdr expectedMac).map (Except.mapError AuthError.toError)

theorem verifyHdr_eq_ok_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32)
    (hm : expectedMac.length ≤ 32) :
    self.verifyHdr F ep hdr expectedMac = .ok (self.verifyHdr_prefix F ep hdr expectedMac) := by
  have hm' : expectedMac.length ≤ (self.macHdrUnchecked F ep hdr).length := by
    simpa [length_macHdrUnchecked] using hm
  simp [verifyHdr, macHdr_of_lt F self ep hdr hk hd, compare_eq_ok_prefix hm', verifyHdr_prefix,
    Bind.bind, Except.bind, pure, Except.pure]

def intoPb (self : Authenticator) : ProtoAuthenticator :=
  { rootKey := self.rootKey, macKey := self.macKey }

def fromPb (pb : ProtoAuthenticator) : Authenticator :=
  { rootKey := pb.rootKey, macKey := pb.macKey }

@[simp]
theorem fromPb_intoPb (a : Authenticator) : fromPb (intoPb a) = a := rfl

@[simp]
theorem intoPb_fromPb (pb : ProtoAuthenticator) : intoPb (fromPb pb) = pb := rfl

end Authenticator

/-! ## Test vectors -/

namespace Tests

open Authenticator

def asciiBytes (s : String) : Bytes := s.toList.map fun c => BitVec.ofNat 8 c.toNat

def auth1 : Authenticator :=
  Authenticator.new sha256Compress (List.replicate 32 42#8) 1#64

def auth1Expected : Authenticator :=
  { rootKey := hexBytes 32 0x7023c8902b246ef746fe7919e81358d3521ab6c3d230a4cfe835a94d33ed34b6
    macKey := hexBytes 32 0xba0a9d05de50e05e41a6575065f7a4117b44011cb25b1714a3c5df4e658b06dc }

theorem auth1_eq : auth1 = auth1Expected := by
  decide +kernel

theorem auth1_macCt :
    auth1.macCt sha256Compress 1#64 (asciiBytes "123") =
      .ok (hexBytes 32 0xfdb33c78925a8084806f8870db6a0b0db5ee38365e1fb749cb2aa5386a47a611) := by
  rw [auth1_eq]
  decide +kernel

theorem auth1_macHdr :
    auth1.macHdr sha256Compress 1#64 (asciiBytes "hdr") =
      .ok (hexBytes 32 0xdfbf9eef463c7e430228a3e90cb35b94030700d00e80c130c634339fecf4f05e) := by
  rw [auth1_eq]
  decide +kernel

#guard
  let pb := auth1.intoPb
  let auth1' := Authenticator.fromPb pb
  let ctMac := hexBytes 32 0xfdb33c78925a8084806f8870db6a0b0db5ee38365e1fb749cb2aa5386a47a611
  let hdrMac := hexBytes 32 0xdfbf9eef463c7e430228a3e90cb35b94030700d00e80c130c634339fecf4f05e
  auth1'.verifyCt sha256Compress 1#64 (asciiBytes "123") ctMac == .ok (.ok ()) &&
  auth1'.verifyCt sha256Compress 1#64 (asciiBytes "124") ctMac == .ok (.error .invalidCtMac) &&
  auth1'.verifyHdr sha256Compress 1#64 (asciiBytes "hdr") hdrMac == .ok (.ok ()) &&
  auth1'.verifyHdr sha256Compress 2#64 (asciiBytes "hdr") hdrMac == .ok (.error .invalidHdrMac) &&
  auth1'.verifyCt sha256Compress 1#64 (asciiBytes "123") (ctMac ++ [0#8]) ==
    .error .compareBounds &&
  auth1'.verifyHdr sha256Compress 1#64 (asciiBytes "hdr") (hdrMac ++ [0#8]) ==
    .error .compareBounds

def v0Auth0 : Authenticator :=
  Authenticator.new sha256Compress
    (hexBytes 32 0x78774a186003cdaf73dfefce516edeaccb6e387de1e6234aa45f4df00a8b62ad)
    0#64

def v0Auth0Expected : Authenticator :=
  { rootKey := hexBytes 32 0x6f17ae608e0a647ba4c8e26ca69007ca0bce4fe756872a4b5cc57c3b993e7c72
    macKey := hexBytes 32 0x0f47989a07f32bdee23aaaffecb65516d585a575dd2074472b1ad007cf7dddfe }

theorem v0_update_vec0 : v0Auth0 = v0Auth0Expected := by
  decide +kernel

def v0Auth1 : Authenticator :=
  v0Auth0Expected.update sha256Compress 1#64
    (hexBytes 64 0x0796cb28571102ff06ea2ad26933a17e8225858a085270d721d028432b824e84dd68cc02a794b617cb883d1953aa48911071bd565a6969c7b0343beaedb0f174)

def v0Auth1Expected : Authenticator :=
  { rootKey := hexBytes 32 0x225dbcbf59f81c7940dd44c2cd412d6b640ef592afb095d5f265f356c415d004
    macKey := hexBytes 32 0x0a0cff9d796e2a136a13ec272d91326d2d1788366f1e8057a9882f2ed8a47b73 }

#guard v0Auth1 == v0Auth1Expected

#guard
  let hdrMac0 := hexBytes 32 0x2341be5136e673c4d507b81289afdcc449acb540d1dd1a42bce1f7c598ca18e2
  let ctMac0 := hexBytes 32 0xecb80f01872a6da42b3e4b546ec5e7b1432ac2d152fb9f62278225810051af27
  let hdrMac1 := hexBytes 32 0x8b399dda14797ca03f63f4cbf14bf2ef75f1580cac9b2de23045eb09959755e1
  let ctMac1 := hexBytes 32 0x9f67b76175d994eb47c118ad71d3b1b98dcc692b0f807048b26a35c706435ea2
  v0Auth0Expected.macHdr sha256Compress 1#64 [] == .ok hdrMac0 &&
  v0Auth0Expected.macCt sha256Compress 1#64 [] == .ok ctMac0 &&
  v0Auth0Expected.verifyHdr sha256Compress 1#64 [] hdrMac0 == .ok (.ok ()) &&
  v0Auth0Expected.verifyCt sha256Compress 1#64 [] hdrMac0 == .ok (.error .invalidCtMac) &&
  v0Auth1Expected.macHdr sha256Compress 2#64 [0x4d#8] == .ok hdrMac1 &&
  v0Auth1Expected.macCt sha256Compress 2#64 [0x4d#8] == .ok ctMac1 &&
  v0Auth1Expected.verifyHdr sha256Compress 2#64 [0x4d#8] ctMac1 == .ok (.error .invalidHdrMac) &&
  v0Auth1Expected.verifyCt sha256Compress 2#64 [0x4d#8] ctMac1 == .ok (.ok ())

#guard
  let auth : Authenticator :=
    { rootKey := hexBytes 32 0xd38780574384246b6394504c59a9e6b316702aac717eb2b231f0528ef978f44b
      macKey := hexBytes 32 0xcc6bd1971de07b4fd2ed7337ca000e6c3af0152ae96fc15e572d6a53606d2765 }
  let payload :=
    hexBytes 160 0xa7b63fca122f7febec1342caeb57add54f064c92f48723519085bfc46b71250e4980a6e77bd73b647fbfdfb49f21ac8d2e53d4f792bf500776cc3ca3c1d9c96900c7ddd7440ebe711aadf7311ddd68b8aa94bac83f4987c8088c801e43eeb642b50940260316b6de01b566f9943810d5e8731980c4e860971fae2b75a7adfe1849db4899838fb8dbac64fc19c61b01425e3c40e33c71e6f583889a1bc545b064
  let hdrMac := hexBytes 32 0x45254a6f05eef93020dff06e747a5e4a4386896c5e6515df21e805708f12eb5f
  let ctMac := hexBytes 32 0xb7d0f71eeafdbd2601d3fc7ac97ccda2981500f763079a96f6aebc9b8af11561
  let candidateMac := hexBytes 32 0x45254a6f05eeb93020dff06e747a5e4a4386896c5e6515df21e805708f12eb5f
  auth.macHdr sha256Compress 0x27#64 payload == .ok hdrMac &&
  auth.macCt sha256Compress 0x27#64 payload == .ok ctMac &&
  auth.verifyHdr sha256Compress 0x27#64 payload hdrMac == .ok (.ok ()) &&
  auth.verifyHdr sha256Compress 0x27#64 payload candidateMac == .ok (.error .invalidHdrMac) &&
  auth.verifyCt sha256Compress 0x27#64 payload candidateMac == .ok (.error .invalidCtMac)

end Tests

end CryptoVerification.LibsignalSpqrV1
