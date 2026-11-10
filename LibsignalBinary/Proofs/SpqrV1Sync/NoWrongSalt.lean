/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
public import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
public import LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge
public import LibsignalBinary.Proofs.SpqrV1.KemFailFindFacts
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch
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
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import ProofLib

set_option warningAsError false

/-!
# SPQR V1 No-Wrong-Salt along Honest Traces

Umbrella module re-exporting the SPQR V1 synchronization stack for the injection-free
no-wrong-salt trace theorem:

* **Chain receive preservation**: `Chain.addEpoch` and `Chain.sendKey` preserve the `recv` state of
  every kept epoch link (dropping only links prior to `sendEpoch - 1`, which `recvKey` rejects with
  `.epochOutOfRange`).
* **Draw-local ML-KEM non-failure (`StepKemFailFree`)**: requires
  `K.honestExchangeFails s (encRandOf r) = false` only on CT-side `.headerReceived` sends that
  actually draw encapsulation randomness `encRandOf r` against the peer's seed `s` (`DrawsEnc`).
* **Counter window bound (`DEV-LS36`)**: SPQR's chain uses `u32` counters with out-of-order window
  `MAX_MESSAGE_KEYS = 2000` (`dparams.maxOooKeysOrDefault = 2000#32`), guarding against `u32`
  addition overflow on `at + max_ooo` and `ctr + max_ooo`. Bounding total sends by `q` with
  `q + 2000 ≤ 2 ^ 32` keeps all sent indices and receive counters below the `2 ^ 32 - 2000`
  overflow threshold.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.NoWrongSalt

end CryptoVerification.SpqrV1Sync.NoWrongSalt
