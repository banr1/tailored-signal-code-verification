/-
Copyright 2020 Signal Messenger, LLC.
SPDX-License-Identifier: AGPL-3.0-only

Copied from Signal Messenger's libsignal (https://github.com/signalapp/libsignal), tag `v0.105.4`,
commit `b2a5c30f3245c1bcad04b27b1e752a38321c793d`: the values below are the byte arrays `seed`,
`message_key`, `mac_key` and `next_chain_key` of upstream's test `test_chain_key_derivation`
(`rust/protocol/src/ratchet/keys.rs`, lines 231-277), each written as one big-endian hex literal.
Full license text: `third_party/libsignal/LICENSE`. See `third_party/libsignal/README.md`.
-/

module

/-!
# libsignal `test_chain_key_derivation` vectors

The known-answer vectors of libsignal v0.105.4's `test_chain_key_derivation`
(`rust/protocol/src/ratchet/keys.rs:231-277`), as 32-byte big-endian `Nat` literals (read them with
`CryptoGames.HMAC.Tests.hex 32`). Imported by `Computational/Tests/AEAD/HKDFTest.lean` and
`Computational/Tests/Binary/SessionRunTest.lean`.
-/

@[expose] public section

namespace LibsignalTestVectors.ChainKeyDerivation

/-- `seed`: the chain key, at index `0`. -/
def seed : Nat := 0x8ab72d6f4cc5ac0d387eaf463378ddb28edd07385b1cb01250c715982e7ad48f

/-- `message_key`: the cipher key of `seed`'s message keys (`message_keys().generate_keys(None)`,
`cipher_key()`). -/
def cipherKey : Nat := 0xbf51e9d75e0e31031051f82a2491ffc084fa298b7793bd9db620056febf45217

/-- `mac_key`: the MAC key of `seed`'s message keys. -/
def macKey : Nat := 0xc6c77d6a73a354337a56435e34607dfe48e3ace14e77314dc6abc172e7a7030b

/-- `next_chain_key`: the key of `seed`'s next chain key (`next_chain_key().key()`). -/
def nextChainKey : Nat := 0x28e8f8fee54b801eef7c5cfb2f17f32c7b334485bbb70fac6ec10342a246d15d

end LibsignalTestVectors.ChainKeyDerivation
