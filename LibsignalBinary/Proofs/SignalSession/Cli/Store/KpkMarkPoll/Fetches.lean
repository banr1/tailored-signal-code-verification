/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

gen_decodes CryptoVerification.libsignalSessionCode_tree cliKpkMarkPollBin
  [(ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") →
   (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 1112)]

gen_decodes CryptoVerification.libsignalSessionCode_tree cliKpkConcatBin
  [(ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") →
   (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" + 364)]

gen_decodes CryptoVerification.libsignalSessionCode_tree cliKpkReserveBin
  [(ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") →
   (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" + 136)]

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
