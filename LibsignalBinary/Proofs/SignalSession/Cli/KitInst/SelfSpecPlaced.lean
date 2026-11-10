/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpecPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI Self-Identity Store Specification

Relocatable `[LibsignalPlacement]` instantiation of `cliIdentitySelfSpec` at base `0#64`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel

/-- Relocatable `IdentitySelfStoreSpec` at base `0#64` over any `ikit : IdentityStoreSpec A 0#64`
with `ikit.IdState = IdGhost`. -/
def cliIdentitySelfSpecOfPlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) (hSt : ikit.IdState = IdGhost)
    (rd : ReadRule) (F0 : FsFiles)
    (kpShimStk kpPollStk regIdShimStk regIdPollStk : Nat) :
    IdentitySelfStoreSpec ikit where
  fdsOk := fun fs => FdsGe3Closed fs
  KpErr := CliSelfSpeErr
  RegIdErr := CliSelfSpeErr
  kpErr := cliSelfSpeErrSpec A
  regIdErr := cliSelfSpeErrSpec A
  kpRel := hSt ▸ cliKpRel rd F0
  regIdRel := hSt ▸ cliRegIdRel rd F0
  kpEvs := fun _ => []
  regIdEvs := fun _ => []
  kpShimOff := lsmpl.base 602
  kpFutVtOff := lsρ idKeyPairFutVtSym
  kpPollOff := lsmpl.base 567
  kpFutDropOff := lsDropOffPlaced
  regIdShimOff := lsmpl.base 603
  regIdFutVtOff := lsρ idRegIdFutVtSym
  regIdPollOff := lsmpl.base 568
  regIdFutDropOff := lsDropOffPlaced
  kpBoxSize := 16
  regIdBoxSize := 16
  kpShimStack := kpShimStk
  kpPollStack := kpPollStk
  regIdShimStack := regIdShimStk
  regIdPollStack := regIdPollStk
  kpBoxAt := idOwnFutBoxAt
  regIdBoxAt := idOwnFutBoxAt
  kpBoxAt_memRegion := idOwnFutBoxAt_memRegion
  regIdBoxAt_memRegion := idOwnFutBoxAt_memRegion
  kpBoxSize_ne_zero := by decide
  regIdBoxSize_ne_zero := by decide
  kpBoxSize_lt := by decide
  regIdBoxSize_lt := by decide
  kpFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
  regIdFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero

/-- Relocatable `IdentitySelfStoreSpec` over `cliIdentityStoreSpecPlaced`. -/
abbrev cliIdentitySelfSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat}
    (kpShimStk kpPollStk regIdShimStk regIdPollStk : Nat) :
    IdentitySelfStoreSpec (cliIdentityStoreSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4) where
  fdsOk := fun fs => FdsGe3Closed fs
  KpErr := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).KpErr
  RegIdErr := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).RegIdErr
  kpErr := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).kpErr
  regIdErr := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).regIdErr
  kpRel := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).kpRel
  regIdRel := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).regIdRel
  kpEvs := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).kpEvs
  regIdEvs := (cliIdentitySelfSpec A 0#64 rd F0 pathOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) kpShimStk kpPollStk regIdShimStk regIdPollStk).regIdEvs
  kpShimOff := lsmpl.base 602
  kpFutVtOff := lsρ idKeyPairFutVtSym
  kpPollOff := lsmpl.base 567
  kpFutDropOff := lsDropOffPlaced
  regIdShimOff := lsmpl.base 603
  regIdFutVtOff := lsρ idRegIdFutVtSym
  regIdPollOff := lsmpl.base 568
  regIdFutDropOff := lsDropOffPlaced
  kpBoxSize := 16
  regIdBoxSize := 16
  kpShimStack := kpShimStk
  kpPollStack := kpPollStk
  regIdShimStack := regIdShimStk
  regIdPollStack := regIdPollStk
  kpBoxAt := idOwnFutBoxAt
  regIdBoxAt := idOwnFutBoxAt
  kpBoxAt_memRegion := idOwnFutBoxAt_memRegion
  regIdBoxAt_memRegion := idOwnFutBoxAt_memRegion
  kpBoxSize_ne_zero := by decide
  regIdBoxSize_ne_zero := by decide
  kpBoxSize_lt := by decide
  regIdBoxSize_lt := by decide
  kpFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
  regIdFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero

theorem cliIdentitySelfSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} :
    (cliIdentitySelfSpecPlaced A rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).Quiet :=
  ⟨fun _ => by simp [cliIdentitySelfSpec, NoFsEv],
    fun _ => by simp [cliIdentitySelfSpec, NoFsEv]⟩

theorem cliIdentitySelf_kpRel_total_placed [LibsignalPlacement] {A : RustAlloc} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).kpRel g ans :=
  cliKpRel_total cliSelfSpeErrWitness cliIo.rd F0 g

theorem cliIdentitySelf_regIdRel_total_placed [LibsignalPlacement] {A : RustAlloc} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).regIdRel g ans :=
  cliRegIdRel_total cliSelfSpeErrWitness cliIo.rd F0 g

theorem cliIdentitySelf_kpRel_eq_placed [LibsignalPlacement] {A : RustAlloc} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) :
    (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).kpRel =
      cliKpRel cliIo.rd F0 :=
  rfl

theorem cliIdentitySelf_regIdRel_eq_placed [LibsignalPlacement] {A : RustAlloc} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) :
    (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).regIdRel =
      cliRegIdRel cliIo.rd F0 :=
  rfl

theorem cliIdentitySelf_kpErr_layout_placed [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (out : BitVec 64) :
    ((∃∗ e, kpPollOutAt
      (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e)) ⊢
      idKeyPairOutAt A out (.error ())) ∧
    (idKeyPairOutAt A out (.error ()) ⊢
      (∃∗ e, kpPollOutAt
        (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
          (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e))) := by
  obtain ⟨hfwd, hrev⟩ := cliSelfSpeErrAt_biEntails A (out + 8#64)
  dsimp only [kpPollOutAt, idKeyPairOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
  constructor
  · refine Entails.sepExists_elim fun e => ?_
    have he : speErrAt (cliSelfSpeErrSpec A) (out + 8#64) e ⊢
        SepProp.sepExists fun k : RunDrop.SpeOwned => RunDrop.speOwnedAt A (out + 8#64) k :=
      Entails.trans (Entails.sepExists_right e (Entails.refl _)) hfwd
    exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono he (Entails.refl _)))
  · have hpull :
        (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
          SepProp.sepExists (fun k : RunDrop.SpeOwned => RunDrop.speOwnedAt A (out + 8#64) k) ∗
          memRegion (out + 0x38#64) 16 =
        SepProp.sepExists (fun k : RunDrop.SpeOwned => RunDrop.speOwnedAt A (out + 8#64) k) ∗
          ((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ memRegion (out + 0x38#64) 16) := by
      ac_rfl
    rw [hpull]
    refine Entails.trans (sepConj_mono_left hrev) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun e => ?_
    refine Entails.sepExists_right e ?_
    exact Entails.of_eq (by ac_rfl)

theorem cliIdentitySelf_regIdErr_layout_placed [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (out : BitVec 64) :
    ((∃∗ e, regIdPollOutAt
      (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e)) ⊢
      idRegIdOutAt A out (.error ())) ∧
    (idRegIdOutAt A out (.error ()) ⊢
      (∃∗ e, regIdPollOutAt
        (cliIdentitySelfSpecPlaced A cliIo.rd F0 cliWrOk peer
          (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e))) := by
  dsimp only [regIdPollOutAt, idRegIdOutAt, cliIdentitySelfSpecPlaced, cliIdentitySelfSpec]
  exact cliSelfSpeErrAt_biEntails A out

end CryptoVerification.SignalSession.Cli.KitInst
