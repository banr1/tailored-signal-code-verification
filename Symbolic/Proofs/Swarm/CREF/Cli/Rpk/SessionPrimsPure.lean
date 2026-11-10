/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PinCoinsPure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Proofs.Swarm.SHARED.HookAuthPure

/-!
# Machine-Free Session and SPQR Primitives

Defines machine-free counterparts of `drawsCoins`, `DecryptCoinsOk`,
`pureSaltOfKeyBytes?`, and `Spqr HwBytes HwBytes` instances without `SpqrModel`
projections.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open CryptoGames CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSpqrV1
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Coin-draw predicate for `tryDecryptWithStateW`. -/
def pureDrawsCoins {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey) : Bool :=
  st.remoteIdentity.isSome &&
    match RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their with
    | .ok none =>
      match st.senderChain with
      | some sc =>
        match rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with
        | .ok _ => true
        | .error _ => false
      | none => false
    | _ => false

/-- Ghost-coin tie for decrypt operations (`pureDrawsCoins = false` with zero coins, or
`pureDrawsCoins = true` with 32 random bytes). -/
def PureDecryptCoinsOk (C : Crypto) (st : SessionState HwBytes) (their : PublicKey)
    (coins : BitVec 256) : Prop :=
  (pureDrawsCoins C st their = false ∧ coins = 0#256) ∨
  (pureDrawsCoins C st their = true ∧ ∃ bs : HwBytes, bs.length = 32 ∧ coins = RpkCli.pureCoinsOf bs)

theorem pureCoinsOf_take_32 (rest : HwBytes) (h : 32 ≤ rest.length) :
    RpkCli.pureCoinsOf (rest.take 32) = RpkCli.pureCoinsOf rest := by
  unfold RpkCli.pureCoinsOf
  congr 1
  have hlen : (rest.take 32).length = 32 := by
    rw [List.length_take, min_eq_left h]
  have h1 : (rest.take 32 ++ List.replicate 32 0#8).take 32 = rest.take 32 := by
    rw [List.take_append_of_le_length (le_of_eq hlen.symm)]
    exact List.take_take.trans (by rw [min_self])
  have h2 : (rest ++ List.replicate 32 0#8).take 32 = rest.take 32 :=
    List.take_append_of_le_length h
  rw [h1, h2]

theorem pureDecryptCoinsOk_of_draws_true (C : Crypto) (st : SessionState HwBytes)
    (their : PublicKey) (rest : HwBytes) (hdraws : pureDrawsCoins C st their = true)
    (hrest : 32 ≤ rest.length) :
    PureDecryptCoinsOk C st their (RpkCli.pureCoinsOf rest) :=
  Or.inr ⟨hdraws, rest.take 32, by rw [List.length_take, min_eq_left hrest],
    (pureCoinsOf_take_32 rest hrest).symm⟩

theorem pureDecryptCoinsOk_of_draws_false (C : Crypto) (st : SessionState HwBytes)
    (their : PublicKey) (hdraws : pureDrawsCoins C st their = false) :
    PureDecryptCoinsOk C st their 0#256 :=
  Or.inl ⟨hdraws, rfl⟩

/-- Maps a 32-byte key `some k` (`k.length = 32`) to `some ⟨k, h⟩` and any other option to `none`. -/
def pureSaltOfKeyBytes? (k? : Option HwBytes) : Option (List.Vector (BitVec 8) 32) :=
  match k? with
  | some k => if h : k.length = 32 then some ⟨k, h⟩ else none
  | none => none

/-- Constructs a `Spqr HwBytes HwBytes` directly from `D : SpqrApiDeps` and `hkdf : HkdfFn`. -/
def pureSpqrFromDeps (D : SpqrApiDeps) (hkdf : HkdfFn) : Spqr HwBytes HwBytes where
  init := fun _ _ => []
  send := fun stateBytes tape =>
    match (CryptoVerification.LibsignalSpqrV1.send D hkdf stateBytes tape).1 with
    | .ok s =>
      match messageKeyToSalt? s.key with
      | some salt => some (s.state, salt, s.msg)
      | none => none
    | .error _ => none
  recv := fun stateBytes msgBytes =>
    match CryptoVerification.LibsignalSpqrV1.recv D hkdf stateBytes msgBytes with
    | .ok r =>
      match recvKeyToSalt? r.key with
      | some salt => .ok (r.state, salt)
      | none => .error false
    | .error (.err e) => .error e.isStateDecode
    | .error (.panic _) => .error false
  sendPanics := fun stateBytes tape => sendPanicsPureB D hkdf stateBytes tape
  recvPanics := fun stateBytes msgBytes => recvPanicsB D hkdf stateBytes msgBytes

/-- Pure `Spqr HwBytes HwBytes` induced by `i : ExternInterpretation`. -/
def pureSpqrOf (i : ExternInterpretation) : Spqr HwBytes HwBytes :=
  pureSpqrFromDeps
    (Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac
      (sha256CompressFunction i)
      (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
      (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i))
    (spqrHkdfWith (sha256CompressFunction i))

/-- Pure `Spqr HwBytes HwBytes` mapping receive keys through `pureSaltOfKeyBytes?`. -/
def pureSpqrEmptyAsNone (F : ShaCompress) (K : MlKem)
    (H : Symbolic.Swarm.SHARED.HookAuth.HmacFn) : Spqr HwBytes HwBytes where
  init := fun _ _ => []
  send := fun stateBytes tape =>
    match (CryptoVerification.LibsignalSpqrV1.send
      (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K H) (spqrHkdfWith F) stateBytes tape).1 with
    | .ok s =>
      match messageKeyToSalt? s.key with
      | some salt => some (s.state, salt, s.msg)
      | none => none
    | .error _ => none
  recv := fun s m =>
    match (Symbolic.Swarm.SHARED.HookAuth.spqrV1RecvWithMac F K H).recv s m with
    | .ok (st', key?) => .ok (st', pureSaltOfKeyBytes? key?)
    | .error b => .error b
  sendPanics := fun stateBytes tape =>
    sendPanicsPureB (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K H) (spqrHkdfWith F)
      stateBytes tape
  recvPanics := fun stateBytes msgBytes =>
    recvPanicsB (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K H) (spqrHkdfWith F)
      stateBytes msgBytes

end Symbolic.Swarm.CREF.CliPure
