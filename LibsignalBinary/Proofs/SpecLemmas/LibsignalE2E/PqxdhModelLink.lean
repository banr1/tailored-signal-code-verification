/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.SecurityWith
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.SignalPqxdh.Model

@[expose] public section

set_option autoImplicit false

/-!
# Definitional Unfoldings for `PqxdhModelLink.modelPrims`

**Checked by Lean.**

Proves the ten `modelPrims_*_eq_ref` equations relating the derived fields of `modelPrims X W`
(`sha512`, `xeddsaVerify`, `isCanonical`, `hkdfDerive96`, `rootCreateChain`, `chainKdfSeed`,
`chainKdfNext`, `deriveMsgKeys`, `aes256CbcHmacEnc`, `aes256CbcHmacDec`) to their reference
constructions over `blockLevelPrims X W`.
-/

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession
theorem modelPrims_sha512_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (m : List UInt8) :
    (modelPrims X W).sha512 m = SignalPqxdh.sha512Ref (modelPrims X W) m := rfl

theorem modelPrims_sigVerify_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk m sig : List UInt8) :
    (modelPrims X W).sigVerify pk m sig = SignalPqxdh.xeddsaVerifyRef (modelPrims X W) pk m sig := rfl

theorem modelPrims_isCanonical_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : List UInt8) :
    (modelPrims X W).isCanonical pk = SignalPqxdh.isCanonicalRef (modelPrims X W) pk := rfl

theorem modelPrims_hkdfDerive96_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (s : List UInt8) :
    (modelPrims X W).hkdfDerive96 s = SignalPqxdh.hkdfDerive96Ref (modelPrims X W) s := rfl

theorem modelPrims_rootCreateChain_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (rk dh : List UInt8) :
    (modelPrims X W).rootCreateChain rk dh =
      SignalPqxdh.rootCreateChainRef (modelPrims X W) rk dh := rfl

theorem modelPrims_chainKdfSeed_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (ck : List UInt8) :
    (modelPrims X W).chainKdfSeed ck = SignalPqxdh.chainKdfSeedRef (modelPrims X W) ck := rfl

theorem modelPrims_chainKdfNext_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (ck : List UInt8) :
    (modelPrims X W).chainKdfNext ck = SignalPqxdh.chainKdfNextRef (modelPrims X W) ck := rfl

theorem modelPrims_deriveMsgKeys_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (s : List UInt8)
    (salt? : Option (List UInt8)) :
    (modelPrims X W).deriveMsgKeys s salt? = SignalPqxdh.deriveMsgKeysRef (modelPrims X W) s salt? := rfl

theorem modelPrims_aeadEnc_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (mk : SignalPqxdh.MessageKeys)
    (ad pt : List UInt8) :
    (modelPrims X W).aeadEnc mk ad pt = SignalPqxdh.aes256CbcHmacEncRef (modelPrims X W) mk ad pt := rfl

theorem modelPrims_aeadDec_eq_ref (X : UnreachedPqxdhPrimitives) (W : PEParams) (mk : SignalPqxdh.MessageKeys)
    (ad ct : List UInt8) :
    (modelPrims X W).aeadDec mk ad ct = SignalPqxdh.aes256CbcHmacDecRef (modelPrims X W) mk ad ct := rfl

end CryptoVerification.E2E
