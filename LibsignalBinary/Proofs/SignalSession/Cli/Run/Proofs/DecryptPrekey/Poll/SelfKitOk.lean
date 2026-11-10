/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli

/-!
# CLI Self-Identity and Full Identity Store Kit

Extends `cliIdentityStoreSpec` with `CliIdOwnInv` on `g.own` (`cliIdStoreSpecFull` and
`cliIdSelfSpecFull`) so that peer callbacks (`IdentityStoreKitOkIE`) and self-identity callbacks
(`IdentitySelfStoreKitOkI`) share a single `IdentityStoreSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
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
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel

/-! ## 1. Self-Directory Invariant (`CliIdOwnInv`) & Full `IdentityStoreSpec` -/

/-- Pure invariant on `g.own` (`IdentityFiles.own`) needed by `idKeyPairPollSpec` and
`idRegIdPollSpec`. Preserved across `save_identity` and `is_trusted_identity` because neither
callback modifies `g.own`. -/
structure CliIdOwnInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (own : DirGhost) : Prop where
  ownPathLt : own.path.length < 2 ^ 32
  kpPathOk : pathOk (pathOf own.path (utf8 "identity-key-pair"))
  regPathOk : pathOk (pathOf own.path (utf8 "registration-id"))
  kpSizeOk : ∀ bs, own.get rd F0 (utf8 "identity-key-pair") = .ok bs → bs.length < 2 ^ 32

/-- Full `IdentityFiles` store predicate combining `CliIdOwnInv` on `g.own` with `cliIdStoreAt`. -/
def cliIdStoreAtFull (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost) (self : BitVec 64) (g : IdGhost) :
    SepProp :=
  ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ cliIdStoreAt A rd F0 pathOk peer self g

/-- Full `IdentityStoreSpec` equipping `cliIdentityStoreSpec` with `cliIdStoreAtFull`. -/
def cliIdStoreSpecFull (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat) : IdentityStoreSpec A b :=
  { cliIdentityStoreSpec A b rd F0 pathOk peer trustShimStk trustPollStk saveShimStk savePollStk with
    identityAt := cliIdStoreAtFull A rd F0 pathOk peer }

/-- Full `IdentitySelfStoreSpec` over `cliIdStoreSpecFull`. -/
def cliIdSelfSpecFull (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat}
    (kpShimStk kpPollStk regIdShimStk regIdPollStk : Nat) :
    IdentitySelfStoreSpec (cliIdStoreSpecFull A b rd F0 pathOk peer t1 t2 t3 t4) where
  fdsOk := fun fs => FdsGe3Closed fs
  KpErr := CliSelfSpeErr
  RegIdErr := CliSelfSpeErr
  kpErr := cliSelfSpeErrSpec A
  regIdErr := cliSelfSpeErrSpec A
  kpRel := cliKpRel rd F0
  regIdRel := cliRegIdRel rd F0
  kpEvs := fun _ => []
  regIdEvs := fun _ => []
  kpShimOff := cliIdKpShimOff
  kpFutVtOff := idKeyPairFutVtOff
  kpPollOff := cliIdKpPollOff
  kpFutDropOff := cliIdFutDropOff
  regIdShimOff := cliIdRegIdShimOff
  regIdFutVtOff := idRegIdFutVtOff
  regIdPollOff := cliIdRegIdPollOff
  regIdFutDropOff := cliIdFutDropOff
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
  kpFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  regIdFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

/-! ## 2. Vtables, Quietness, & Totality on `cliIdStoreSpecFull` / `cliIdSelfSpecFull` -/

section VtablesAndProps

variable {A : RustAlloc} {img : Obj.Image} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}

theorem cliIdStoreSpecFull_offsets :
    CliIdKitOffsets img (cliIdStoreSpecFull A img.base rd F0 pathOk peer t1 t2 t3 t4) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cliIdStoreSpecFull_vtablesOk (himg : Obj.Loads libsignalSessionImage img) :
    IdentityVtablesOk img (cliIdStoreSpecFull A img.base rd F0 pathOk peer t1 t2 t3 t4) :=
  cliIdentityVtablesOk himg cliIdStoreSpecFull_offsets

theorem cliIdStoreSpecFull_quiet :
    (cliIdStoreSpecFull A img.base rd F0 pathOk peer t1 t2 t3 t4).Quiet :=
  ⟨fun _ _ _ _ => by simp [cliIdStoreSpecFull, cliIdentityStoreSpec, NoFsEv],
    fun _ _ _ => by simp [cliIdStoreSpecFull, cliIdentityStoreSpec, NoFsEv]⟩

theorem cliIdSelfSpecFull_vtablesOk (himg : Obj.Loads libsignalSessionImage img) :
    IdentitySelfVtablesOk img
      (cliIdStoreSpecFull A img.base rd F0 pathOk peer t1 t2 t3 t4)
      (cliIdSelfSpecFull A img.base rd F0 pathOk peer k1 k2 k3 k4) where
  kpSlot := cliIdKpSlot_ok himg
  regIdSlot := cliIdRegIdSlot_ok himg
  kpFutDrop := cliIdKpFutDrop_ok himg
  kpFutSize := cliIdKpFutSize_ok himg
  kpFutAlign := cliIdKpFutAlign_ok himg
  kpFutPoll := cliIdKpFutPoll_ok himg
  regIdFutDrop := cliIdRegIdFutDrop_ok himg
  regIdFutSize := cliIdRegIdFutSize_ok himg
  regIdFutAlign := cliIdRegIdFutAlign_ok himg
  regIdFutPoll := cliIdRegIdFutPoll_ok himg

theorem cliIdSelfSpecFull_quiet :
    (cliIdSelfSpecFull A img.base rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).Quiet :=
  ⟨fun _ => by simp [cliIdSelfSpecFull, NoFsEv],
    fun _ => by simp [cliIdSelfSpecFull, NoFsEv]⟩

theorem cliIdSelfSpecFull_kpRel_total (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdSelfSpecFull A img.base cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).kpRel g ans :=
  cliKpRel_total cliSelfSpeErrWitness cliIo.rd F0 g

theorem cliIdSelfSpecFull_regIdRel_total (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdSelfSpecFull A img.base cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).regIdRel g ans :=
  cliRegIdRel_total cliSelfSpeErrWitness cliIo.rd F0 g

end VtablesAndProps

/-! ## 3. Lifting Peer `IdentityStoreKitOkIE` & Self `IdentitySelfStoreKitOkI` -/

private theorem panic_absorb_extra {φ : Prop} {extra R : SepProp} {m : Memory}
    (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (extra ∗ R)) :
    m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  have h1 : m ⊨ ⌜φ⌝ ∗ ((anyHeap ∗ extra) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h1
  have h2 : m ⊨ ⌜φ⌝ ∗ (anyHeap ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨h1.1, Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ extra))) h1.2⟩
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h2

private theorem saveUpd_own (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (addr : AddrVal) (key : IdentityKey) :
    (IdGhost.saveUpd rd F0 g addr key).own = g.own := by
  unfold IdGhost.saveUpd
  cases IdGhost.peer rd F0 g addr <;> rfl

theorem cliIdKitOkIE_full {A : RustAlloc} {img : Obj.Image} {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {t1 t2 t3 t4 : Nat}
    (hBase : IdentityStoreKitOkIE img
      (cliIdentityStoreSpec A img.base rd F0 pathOk peer t1 t2 t3 t4) ext) :
    IdentityStoreKitOkIE img
      (cliIdStoreSpecFull A img.base rd F0 pathOk peer t1 t2 t3 t4) ext where
  trustShim := hBase.trustShim
  trustFutDrop := hBase.trustFutDrop
  saveShim := hBase.saveShim
  saveFutDrop := hBase.saveFutDrop
  trustPoll := by
    refine subroutine_ok_map_panic hBase.trustPoll ?_
    rintro ⟨x, d, self, g⟩ R s0 hpre
    change IdGhost at g
    dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE,
      kitTrustPollSpec, withEnvPre, cliIdStoreSpecFull, cliIdStoreAtFull] at hpre
    have hpre' : s0.mem ⊨
        (kitTrustPollSpecI img
          (cliIdentityStoreSpec A img.base rd F0 pathOk peer t1 t2 t3 t4)).pre
            (x, d, self, g) s0 ∗
        (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE,
        kitTrustPollSpec, withEnvPre]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    refine ⟨(x, d, self, g), ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R, hpre', ?_,
      fun _ hpan => panic_absorb_extra hpan⟩
    intro sf hpost
    dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE,
      kitTrustPollSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreSpecFull,
      cliIdStoreAtFull] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨ans, hm⟩ := hpost
    exact ⟨ans, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
  savePoll := by
    refine subroutine_ok_map_panic hBase.savePoll ?_
    rintro ⟨x, self, g⟩ R s0 hpre
    change IdGhost at g
    dsimp only [kitSavePollSpecI, Spec.inImage, withLogOff, kitSavePollSpecE,
      kitSavePollSpec, withEnvPre, cliIdStoreSpecFull, cliIdStoreAtFull] at hpre
    have hpre' : s0.mem ⊨
        (kitSavePollSpecI img
          (cliIdentityStoreSpec A img.base rd F0 pathOk peer t1 t2 t3 t4)).pre
            (x, self, g) s0 ∗
        (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [kitSavePollSpecI, Spec.inImage, withLogOff, kitSavePollSpecE,
        kitSavePollSpec, withEnvPre]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    refine ⟨(x, self, g), ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R, hpre', ?_,
      fun _ hpan => panic_absorb_extra hpan⟩
    intro sf hpost
    dsimp only [kitSavePollSpecI, Spec.inImage, withLogOff, kitSavePollSpecE,
      kitSavePollSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreSpecFull,
      cliIdStoreAtFull] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨ans, hm⟩ := hpost
    rw [saveUpd_own]
    exact ⟨ans, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩

/-- CLI instance of `IdentityStoreKitOkIE` on `cliIdStoreSpecFull` at `E2E.HooksE.A0` and
`cliExterns W`. -/
theorem cliIdKitOkIE_cli_full (W : CliHooks) {img : Obj.Image} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : IdKit.trustShimNeed ≤ s1) (hs2 : IdKit.trustPollNeed readStk ≤ s2)
    (hs3 : IdKit.saveShimNeed ≤ s3) (hs4 : IdKit.savePollNeed readStk ≤ s4) :
    IdentityStoreKitOkIE img
      (cliIdStoreSpecFull E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      (cliExterns W) :=
  cliIdKitOkIE_full (cliIdKitOkIE_cli W himg hs1 hs2 hs3 hs4)

/-- Generic `ext` instance of `IdentityStoreKitOkIE` on `cliIdStoreSpecFull` from `RunHooks`,
`read_file`, and `PublicKeyEqOkExt`. -/
theorem cliIdKitOkIE_ext_full {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hs1 : IdKit.trustShimNeed ≤ s1) (hs2 : IdKit.trustPollNeed readStk ≤ s2)
    (hs3 : IdKit.saveShimNeed ≤ s3) (hs4 : IdKit.savePollNeed readStk ≤ s4) :
    IdentityStoreKitOkIE img
      (cliIdStoreSpecFull A img.base rd F0 cliWrOk peer s1 s2 s3 s4) ext :=
  cliIdKitOkIE_full (IdKit.cliIdKitOkIE himg hh hRead hEq hs1 hs2 hs3 hs4)

/-- Contract-backed `IdentityStoreKitOkIE` on `cliIdStoreSpecFull` from `RunHooksExt`,
`read_file`, and `PublicKeyEqOkExt32` (32-byte stack frame for `subtle::black_box::<u8>`). -/
theorem cliIdKitOkIE_ext32_full {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hs1 : IdKit.trustShimNeed ≤ s1) (hs2 : IdKit.trustPollNeed readStk ≤ s2)
    (hs3 : IdKit.saveShimNeed ≤ s3) (hs4 : IdKit.savePollNeed readStk ≤ s4) :
    IdentityStoreKitOkIE img
      (cliIdStoreSpecFull A img.base rd F0 cliWrOk peer s1 s2 s3 s4) ext :=
  cliIdKitOkIE_full (IdKit.cliIdKitOkIE_ext32 himg hh hRead hEq hs1 hs2 hs3 hs4)

/-- Contract-backed `IdentityStoreKitOkIE` on `cliIdStoreSpecFull` at `cliExternsWith ext` from
`CliExternsOk P A ext`. -/
theorem cliIdKitOkIE_ext_of_externsOk_full {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : IdKit.trustShimNeed ≤ s1) (hs2 : IdKit.trustPollNeed readStk ≤ s2)
    (hs3 : IdKit.saveShimNeed ≤ s3) (hs4 : IdKit.savePollNeed readStk ≤ s4)
    (hread : extHookStack ≤ readStk := by decide) :
    IdentityStoreKitOkIE img
      (cliIdStoreSpecFull A img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      (cliExternsWith ext) :=
  cliIdKitOkIE_full (IdKit.cliIdKitOkIE_ext hOk himg hs1 hs2 hs3 hs4 hread)

/-- Assemble `IdentitySelfStoreKitOkI` over `cliIdStoreSpecFull` and `cliIdSelfSpecFull` from the
four self-identity hop contracts (`idOwnShimSpec`, `idKeyPairPollSpec`, `idRegIdPollSpec`) and
`futDropSpec`. -/
theorem cliSelfKitOkI_of_hops {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {F0 : FsFiles} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}
    (hKpShim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idKeyPairShimName)
      (idOwnShimSpec idKeyPairFutVtOff A img k1))
    (hKpPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idKeyPairPollName)
      (idKeyPairPollSpec cliIo.rd cliWrOk A img k2))
    (hRegIdShim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdShimName)
      (idOwnShimSpec idRegIdFutVtOff A img k3))
    (hRegIdPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdPollName)
      (idRegIdPollSpec cliIo.rd cliWrOk A img k4))
    (hFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + cliIdFutDropOff) futDropSpec) :
    IdentitySelfStoreKitOkI img
      (cliIdStoreSpecFull A img.base cliIo.rd F0 cliWrOk peer t1 t2 t3 t4)
      (cliIdSelfSpecFull A img.base cliIo.rd F0 cliWrOk peer k1 k2 k3 k4) ext where
  kpShim := by
    rw [cliIdKpShimOff_eq] at hKpShim
    exact hKpShim
  kpFutDrop := hFutDrop
  regIdShim := by
    rw [cliIdRegIdShimOff_eq] at hRegIdShim
    exact hRegIdShim
  regIdFutDrop := hFutDrop
  kpPoll := by
    rw [cliIdKpPollOff_eq] at hKpPoll
    refine subroutine_ok_map_panic hKpPoll ?_
    rintro ⟨fut, out, self, g⟩ R s0 hpre
    change IdGhost at g
    let skit := cliIdSelfSpecFull A img.base cliIo.rd F0 cliWrOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    dsimp only [kitKpPollSpecI, Spec.inImage, withLogOff, kitKpPollSpecE,
      kitKpPollSpec, withEnvPre, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt, cliIdSelfSpecFull] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A self g.own ∗
          memRegion out 72 ∗ logOff img ∗ A.pool ∗ stackAt s0.sp k2 ∗
          (dirAt A (self + 0x28#64) g.peers ∗ R)))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    let frameKpCore : SepProp :=
      ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      dirAt A (self + 0x28#64) g.peers
    have hhop_pure :
        s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
          ∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32 :=
      ⟨hx0, hx8, hown.ownPathLt, hown.kpPathOk, fun bs hbs =>
        hown.kpSizeOk bs (hfiles ▸ hbs)⟩
    have hm_hop :
        s0.mem ⊨ (idKeyPairPollSpec cliIo.rd cliWrOk A img k2).pre ⟨fut, out, self, g.own⟩ s0 ∗
          (frameKpCore ∗ R) := by
      dsimp only [idKeyPairPollSpec, Spec.inImage, frameKpCore]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            g.own.path.length < 2 ^ 32 ∧
            cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
            ∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
              bs.length < 2 ^ 32⌝ ∗
          (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
          (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
          (idOwnFutBoxAt fut self 0#8 ∗ dirAt A self g.own ∗
            memRegion out 72 ∗ logOff img ∗ A.pool ∗ stackAt s0.sp k2 ∗
            (dirAt A (self + 0x28#64) g.peers ∗ R))))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hinv, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, g.own⟩, frameKpCore ∗ R, hm_hop, ?_, fun sf hpan => by
      dsimp only [idKeyPairPollSpec, kitKpPollSpecI, Spec.inImage, withLogOff,
        kitKpPollSpecE, kitKpPollSpec, withEnvPre] at hpan ⊢
      exact panic_absorb_extra hpan⟩
    intro sf hpost
    dsimp only [idKeyPairPollSpec, Spec.inImage, frameKpCore] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨ans0, ⟨hans0, htr⟩, hm⟩ := hpost
    rw [hfiles, IdGhost.keyPair_mk_own] at hans0
    dsimp only [kitKpPollSpecI, Spec.inImage, withLogOff, kitKpPollSpecE,
      kitKpPollSpec, withEnvPre, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt, cliIdSelfSpecFull]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    cases ans0 with
    | ok kp =>
      have hrel : cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) :=
        (cliKpRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g kp).2 hans0.symm
      refine ⟨.ok kp, ?_⟩
      dsimp only [kpPollOutAt, idKeyPairOutAt] at hm ⊢
      have hgoal : sf.mem ⊨
          ⌜cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) ∧ sf.trace = s0.trace ++ []⌝ ∗
          (idKeyPairOutAt A out (.ok kp) ∗ idOwnFutBoxAt fut self 1#8 ∗
            dirAt A self g.own ∗ logOff img ∗ A.pool ∗ stackAt s0.sp k2 ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A (self + 0x28#64) g.peers ∗ R) := by
        dsimp only [idKeyPairOutAt]
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hm⟩
      dsimp only [idKeyPairOutAt] at hgoal
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
    | error u =>
      cases u
      have herr_ent :
          idKeyPairOutAt A out (.error ()) ⊢
            ∃∗ e : skit.KpErr, kpPollOutAt skit out (.error e) :=
        (cliIdentitySelf_kpErr_layout A img F0
          (peer := peer) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4)
          (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) out).2
      have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
      obtain ⟨e, hme⟩ := hm'
      have hrel : cliKpRel cliIo.rd F0 g (.error e) :=
        (cliKpRel_error_iff cliIo.rd F0 g e).2 hans0.symm
      refine ⟨.error e, ?_⟩
      dsimp only [skit, cliIdSelfSpecFull, kpPollOutAt] at hme ⊢
      have hgoal : sf.mem ⊨
          ⌜cliKpRel cliIo.rd F0 g (.error e) ∧ sf.trace = s0.trace ++ []⌝ ∗
          (((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
              speErrAt (cliSelfSpeErrSpec A) (out + 8#64) e ∗
              memRegion (out + 0x38#64) 16) ∗
            idOwnFutBoxAt fut self 1#8 ∗
            dirAt A self g.own ∗ logOff img ∗ A.pool ∗ stackAt s0.sp k2 ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A (self + 0x28#64) g.peers ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hme⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  regIdPoll := by
    rw [cliIdRegIdPollOff_eq] at hRegIdPoll
    refine subroutine_ok_map_panic hRegIdPoll ?_
    rintro ⟨fut, out, self, g⟩ R s0 hpre
    change IdGhost at g
    let skit := cliIdSelfSpecFull A img.base cliIo.rd F0 cliWrOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4
    dsimp only [kitRegIdPollSpecI, Spec.inImage, withLogOff, kitRegIdPollSpecE,
      kitRegIdPollSpec, withEnvPre, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt, cliIdSelfSpecFull] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt A self g.own ∗
          memRegion out 48 ∗ A.pool ∗ stackAt s0.sp k4 ∗
          (dirAt A (self + 0x28#64) g.peers ∗ logOff img ∗ R)))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    let frameRegCore : SepProp :=
      ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      dirAt A (self + 0x28#64) g.peers ∗ logOff img
    have hhop_pure :
        s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "registration-id")) :=
      ⟨hx0, hx8, hown.ownPathLt, hown.regPathOk⟩
    have hm_hop :
        s0.mem ⊨ (idRegIdPollSpec cliIo.rd cliWrOk A img k4).pre ⟨fut, out, self, g.own⟩ s0 ∗
          (frameRegCore ∗ R) := by
      dsimp only [idRegIdPollSpec, Spec.inImage, frameRegCore]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
            g.own.path.length < 2 ^ 32 ∧
            cliWrOk (pathOf g.own.path (utf8 "registration-id"))⌝ ∗
          (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
          (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
          (idOwnFutBoxAt fut self 0#8 ∗ dirAt A self g.own ∗
            memRegion out 48 ∗ A.pool ∗ stackAt s0.sp k4 ∗
            (dirAt A (self + 0x28#64) g.peers ∗ logOff img ∗ R))))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hinv, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨fut, out, self, g.own⟩, frameRegCore ∗ R, hm_hop, ?_, fun sf hpan => by
      dsimp only [idRegIdPollSpec, kitRegIdPollSpecI, Spec.inImage, withLogOff,
        kitRegIdPollSpecE, kitRegIdPollSpec, withEnvPre] at hpan ⊢
      exact panic_absorb_extra hpan⟩
    intro sf hpost
    dsimp only [idRegIdPollSpec, Spec.inImage, frameRegCore] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨ans0, ⟨hans0, htr⟩, hm⟩ := hpost
    rw [hfiles, IdGhost.regId_mk_own] at hans0
    dsimp only [kitRegIdPollSpecI, Spec.inImage, withLogOff, kitRegIdPollSpecE,
      kitRegIdPollSpec, withEnvPre, cliIdStoreSpecFull, cliIdStoreAtFull,
      cliIdentityStoreSpec, cliIdStoreAt, cliIdSelfSpecFull]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    cases ans0 with
    | ok reg =>
      have hrel : cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) :=
        (cliRegIdRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g reg).2 hans0.symm
      refine ⟨.ok reg, ?_⟩
      dsimp only [regIdPollOutAt, idRegIdOutAt] at hm ⊢
      have hgoal : sf.mem ⊨
          ⌜cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) ∧ sf.trace = s0.trace ++ []⌝ ∗
          (((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
              memRegion (out + 12#64) 36) ∗
            idOwnFutBoxAt fut self 1#8 ∗
            dirAt A self g.own ∗ A.pool ∗ stackAt s0.sp k4 ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A (self + 0x28#64) g.peers ∗ logOff img ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
    | error u =>
      cases u
      have herr_ent :
          idRegIdOutAt A out (.error ()) ⊢
            ∃∗ e : skit.RegIdErr, regIdPollOutAt skit out (.error e) :=
        (cliIdentitySelf_regIdErr_layout A img F0
          (peer := peer) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4)
          (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) out).2
      have hm' := Satisfies.mono (sepConj_mono_left herr_ent) hm
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
      obtain ⟨e, hme⟩ := hm'
      have hrel : cliRegIdRel cliIo.rd F0 g (.error e) :=
        (cliRegIdRel_error_iff cliIo.rd F0 g e).2 hans0.symm
      refine ⟨.error e, ?_⟩
      dsimp only [skit, cliIdSelfSpecFull, regIdPollOutAt] at hme ⊢
      have hgoal : sf.mem ⊨
          ⌜cliRegIdRel cliIo.rd F0 g (.error e) ∧ sf.trace = s0.trace ++ []⌝ ∗
          (speErrAt (cliSelfSpeErrSpec A) out e ∗ idOwnFutBoxAt fut self 1#8 ∗
            dirAt A self g.own ∗ A.pool ∗ stackAt s0.sp k4 ∗
            ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
            ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
            dirAt A (self + 0x28#64) g.peers ∗ logOff img ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hme⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
