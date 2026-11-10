/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks

/-!
# CLI Self-Identity Answer Relations

Pure answer relations (`cliKpRel`, `cliRegIdRel`) and `Ok`/`Err`/totality characterizations
relating `<IdentityFiles as IdentityKeyStore>::get_identity_key_pair` and
`get_local_registration_id` results to `IdGhost.keyPair` and `IdGhost.regId`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli

open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)

/-- `IdGhost.keyPair` reads only `g.own`, ignoring `peers`. -/
theorem IdGhost.keyPair_mk_own {g : IdGhost} {p : DirGhost} {rd : ReadRule} {F0 : FsFiles} :
    (IdGhost.mk g.own p).keyPair rd F0 = g.keyPair rd F0 := rfl

/-- `IdGhost.regId` reads only `g.own`, ignoring `peers`. -/
theorem IdGhost.regId_mk_own {g : IdGhost} {p : DirGhost} {rd : ReadRule} {F0 : FsFiles} :
    (IdGhost.mk g.own p).regId rd F0 = g.regId rd F0 := rfl

end CryptoVerification.SignalSession.Cli

namespace CryptoVerification.SignalSession.Cli.KitInst.SelfRel

open Arm64
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)

namespace IdGhost
export CryptoVerification.SignalSession.Cli.IdGhost (keyPair_mk_own regId_mk_own)
end IdGhost

/-- Answer relation for `get_identity_key_pair`, matching `Ok`/`Err` status against
`IdGhost.keyPair`. -/
def cliKpRel {E : Type} (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (ans : Except E IdentityKeyPair) : Prop :=
  match ans, g.keyPair rd F0 with
  | .ok kp, .ok kp' => kp = kp'
  | .error _, .error () => True
  | _, _ => False

/-- Answer relation for `get_local_registration_id`, matching `Ok`/`Err` status against
`IdGhost.regId`. -/
def cliRegIdRel {E : Type} (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (ans : Except E (BitVec 32)) : Prop :=
  match ans, g.regId rd F0 with
  | .ok reg, .ok reg' => reg = reg'
  | .error _, .error () => True
  | _, _ => False

theorem cliKpRel_error_iff {E : Type} (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (e : E) :
    cliKpRel rd F0 g (.error e) ↔ g.keyPair rd F0 = .error () := by
  dsimp only [cliKpRel]
  cases g.keyPair rd F0 with
  | error u => cases u; exact ⟨fun _ => rfl, fun _ => trivial⟩
  | ok _ => exact ⟨False.elim, fun h => nomatch h⟩

theorem cliKpRel_ok_iff {E : Type} (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (kp : IdentityKeyPair) :
    cliKpRel (E := E) rd F0 g (.ok kp) ↔ g.keyPair rd F0 = .ok kp := by
  dsimp only [cliKpRel]
  cases g.keyPair rd F0 with
  | error _ => exact ⟨False.elim, fun h => nomatch h⟩
  | ok _ => exact ⟨fun h => congrArg Except.ok h.symm, fun h => (Except.ok.inj h).symm⟩

theorem cliRegIdRel_error_iff {E : Type} (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (e : E) :
    cliRegIdRel rd F0 g (.error e) ↔ g.regId rd F0 = .error () := by
  dsimp only [cliRegIdRel]
  cases g.regId rd F0 with
  | error u => cases u; exact ⟨fun _ => rfl, fun _ => trivial⟩
  | ok _ => exact ⟨False.elim, fun h => nomatch h⟩

theorem cliRegIdRel_ok_iff {E : Type} (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (reg : BitVec 32) :
    cliRegIdRel (E := E) rd F0 g (.ok reg) ↔ g.regId rd F0 = .ok reg := by
  dsimp only [cliRegIdRel]
  cases g.regId rd F0 with
  | error _ => exact ⟨False.elim, fun h => nomatch h⟩
  | ok _ => exact ⟨fun h => congrArg Except.ok h.symm, fun h => (Except.ok.inj h).symm⟩

theorem cliKpRel_opened_error_iff {E : Type} (F : FsFiles) (e : E) :
    cliKpRel cliIo.rd F StoresGhost.opened.identity (.error e) ↔
      StoresGhost.opened.identity.keyPair cliIo.rd F = .error () :=
  cliKpRel_error_iff cliIo.rd F StoresGhost.opened.identity e

theorem cliRegIdRel_opened_error_iff {E : Type} (F : FsFiles) (e : E) :
    cliRegIdRel cliIo.rd F StoresGhost.opened.identity (.error e) ↔
      StoresGhost.opened.identity.regId cliIo.rd F = .error () :=
  cliRegIdRel_error_iff cliIo.rd F StoresGhost.opened.identity e

theorem cliKpRel_total {E : Type} (e0 : E) (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) :
    ∃ ans : Except E IdentityKeyPair, cliKpRel rd F0 g ans :=
  match h : g.keyPair rd F0 with
  | .error () => ⟨.error e0, (cliKpRel_error_iff rd F0 g e0).2 h⟩
  | .ok kp => ⟨.ok kp, (cliKpRel_ok_iff rd F0 g kp).2 h⟩

theorem cliRegIdRel_total {E : Type} (e0 : E) (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) :
    ∃ ans : Except E (BitVec 32), cliRegIdRel rd F0 g ans :=
  match h : g.regId rd F0 with
  | .error () => ⟨.error e0, (cliRegIdRel_error_iff rd F0 g e0).2 h⟩
  | .ok reg => ⟨.ok reg, (cliRegIdRel_ok_iff rd F0 g reg).2 h⟩

end CryptoVerification.SignalSession.Cli.KitInst.SelfRel
