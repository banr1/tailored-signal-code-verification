/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux

/-!
# CLI `SegSave` Instruction Decodes and Panic Helpers

Instruction decode tables (`+0x2150..+0x21b0`, `+0x2334..+0x2388`, `+0x23c8..+0x23dc`) and
allocation-panic outcome helpers for `SegSave`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet


open CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decode lemmas -/

gen_decodes libsignalSessionCode_tree segSaveBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8528) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8620), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9012) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9092), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9160) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9176)]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave.panic_outcome_of_allocFailedIn {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace)
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) :
    SubroutineOutcome (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV Spec.inImage
  dsimp only
  apply Entails.pure_left
  rintro ⟨haf, htr⟩
  refine Entails.pure_right ⟨htr0.trans htr, Or.inl (allocFailedIn_trans htr0 haf)⟩ (Entails.refl _)

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
