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

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 400000

gen_decodes libsignalSessionCode_tree libsignalSessionBin [raw (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"), (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 4) → (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 76), raw (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 80),
    (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 84) → (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 240), raw (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 244), (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 248) → (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 288), raw (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 292), raw (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 296), (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 300) → (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}" + 508)]
end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
