/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.Core
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCli
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt

/-!
# Tight-Panic Token-Framed CLI `decrypt_signal` (`WithStoresVT`)

Specializes `WithStoresVT.Core` (`withStoresDecSpecVTP` and `withStoresDecSpecVT`, framing
`TokenInit img` under `RecordInScopeP` and `IdOrDistinctSid`) to `trTrapProgAt`, concrete CLI
externs (`cliExterns W`), and parametric contract-backed externs (`cliExternsWith ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (ScopePq SessionOnlyKitOkSE decryptRecord)
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

export WithStoresVT (
  region_ok_of_trapsOnly
  IdOrDistinctSid
  idOrDistinctSid_of_distinctSid
  idOrDistinctSid_of_scopeIn
  withStoresDecSpecVT
  withStoresDecSpecVTP
  msgDecryptMemcpySpec4K
  AllocContracts4K
  PublicKeyEqOkExtX
  DecFsCtxExt
  DecHypsExt
  DecHypsExtX
  DecHypsExt4K
  DecCalleesTPExt
  DecCalleesTExt
  withStoresDec_reachVTP_fs_ext
  withStoresDec_reachVTP_fs_ext4K
  withStoresDec_okVTP_fs_ext
  withStoresDec_okVTP_fs_ext4K
  withStoresDec_okVTP_distinct_fs_ext
  withStoresDec_okVTP_distinct_fs_ext4K
  withStoresDec_okVTP_ext
  withStoresDec_okVTP_ext4K
  withStoresDec_okVT_fs_ext
  withStoresDec_okVT_fs_ext4K
  withStoresDec_okVT_ext
  withStoresDec_okVT_ext4K
)

/-! ## Region and entry-address helpers -/

/-- Lifts an unconditional `region_ok` proof to `spec.restrictPre (fun _ => True)`. -/
theorem region_ok_restrictPre_true {α : Type} {P : Program} {entry exit : BitVec 64}
    {spec : Spec α} (h : region_ok P entry exit spec) :
    region_ok P entry exit (spec.restrictPre (fun _ => True)) := by
  intro x R s0 hpc hrun hpre hL
  dsimp only [Spec.restrictPre] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.2 hL

/-- Identifies `wsEntryPC img` with `(tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName` under `Obj.Loads`. -/
theorem wsEntryPC_eq_fnAddr_ext {img : Obj.Image}
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    wsEntryPC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName :=
  entryOf_eq_tripleRatchetProgAtExt ext himg
    CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName

/-! ## Trap-program specializations (`trTrapProgAt`) -/

/-- Weak-precondition (`RecordInScopeP`) hypothesis bundle at `trTrapProgAt img.base C abs`. -/
abbrev DecHypsP_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (ss : SessionStoreSpec A img.base)
    (id : IdentityStoreSpec A img.base)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsExt img C A parse S encRecord (trTrapExterns C abs) ss id st0 Scope

/-- Tight-panic, weak-precondition callee bundle at `trTrapProgAt img.base C abs`. -/
abbrev DecCalleesTP_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPExt img C A ctl S (trTrapExterns C abs) Q

/-- `TokenInit`-framed `recordDecryptSpecT` callee bundle at `trTrapProgAt img.base C abs`. -/
abbrev DecCalleesT_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTExt img C A ctl S (trTrapExterns C abs) Q

/-- Constructs `DecCalleesTP_trap` at `Q := fun _ => True` from an unconditional region proof. -/
theorem DecCalleesTP_trap.of_uncond {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hreg : region_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).withVRegs)
    (hrem : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img))
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      img.base A (trTrapExterns C abs)) :
    DecCalleesTP_trap img C A ctl S abs (fun _ => True) where
  region := region_ok_restrictPre_true hreg
  remoteIk := hrem
  dropSs := hdrop

theorem withStoresDec_reachVTP_fs_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsP_trap img C A uuidTryParse S encRecord abs kit ikit st0 Scope)
    (hC : DecCalleesTP_trap img C A ctl S abs Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPC img)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtx_trap kit ikit C abs s0 s0) :
    reaches_outcome (trTrapProgAt img.base C abs)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s0 :=
  withStoresDec_reachVTP_fs_ext hH hC hQ x R s0 hid hpc hrun hpre hal hfs

theorem withStoresDec_okVTP_fs_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsP_trap img C A uuidTryParse S encRecord abs kit ikit st0 Scope)
    (hC : DecCalleesTP_trap img C A ctl S abs Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (wsEntryPC img)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_ext hH hC hQ hKitFs

theorem withStoresDec_okVTP_distinct_fs_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsP_trap img C A uuidTryParse S encRecord abs kit ikit st0 Scope)
    (hC : DecCalleesTP_trap img C A ctl S abs Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (wsEntryPC img)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_ext hH hC hQ hKitFs

theorem withStoresDec_okVTP_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsP_trap img C A uuidTryParse S encRecord abs kit ikit st0 Scope)
    (hC : DecCalleesTP_trap img C A ctl S abs Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (wsEntryPC img)
      ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
        (IdOrDistinctSid uuidTryParse kit st0 Scope)) :=
  withStoresDec_okVTP_ext hH hC hQ htriv

theorem withStoresDec_okVT_fs_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsV_trap img C A uuidTryParse S encRecord abs kit ikit st0 Scope)
    (hC : DecCalleesT_trap img C A ctl S abs Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (wsEntryPC img)
      (withEnvPre (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVT_fs_ext (DecHypsExt.of_trap hH) hH.scopeIn hC hQ hKitFs

theorem withStoresDec_okVT_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsV_trap img C A uuidTryParse S encRecord abs kit ikit st0 Scope)
    (hC : DecCalleesT_trap img C A ctl S abs Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (wsEntryPC img)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  withStoresDec_okVT_ext (DecHypsExt.of_trap hH) hH.scopeIn hC hQ htriv

/-! ## Concrete CLI extern specializations (`cliExterns W`) -/

/-- Constructs `DecHypsExt` from `RunSkeleton.RunHooks` and the session/identity store-kit bundles. -/
theorem DecHypsExt.of_runHooks {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {ss : SessionStoreSpec A img.base} {id : IdentityStoreSpec A img.base}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooks img A ext)
    (hkit : SessionOnlyKitOkSE ss Scope encRecord ext)
    (hikit : StoreKit.Identity.IdentityStoreKitOkIE img id ext)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExt img C A parse S encRecord ext ss id st0 Scope where
  loads := himg
  alloc := hh.allocContracts
  kit := hkit
  ikit := hikit
  scopeInP := hscopeInP
  recOk := hrecOk

/-- Discharges `KitFsOk` for `cliSessionStoreSpec` and `cliIdentityStoreSpec` on any `TraceFsSound` program. -/
theorem cliFilesKits_fsOk {A : RustAlloc} {img : Obj.Image} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 is1 is2 is3 is4 : Nat} {P : Program}
    (hfs : TraceFsSound P) :
    KitFsOk
      (fun f =>
        (cliSessionStoreSpec A img.base rd F0 pathOk Scope peer s1 s2 s3 s4).envOk f ∧
        (cliIdentityStoreSpec A img.base rd F0 pathOk peer is1 is2 is3 is4).envOk f)
      ((cliSessionStoreSpec A img.base rd F0 pathOk Scope peer s1 s2 s3 s4).Quiet ∧
        (cliIdentityStoreSpec A img.base rd F0 pathOk peer is1 is2 is3 is4).Quiet)
      P :=
  KitFsOk.of_sound
    ⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
      ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩
    hfs

/-- Constructs `DecHypsExt` for `cliSessionStoreSpec` and `cliIdentityStoreSpec` at `A0` and `cliExterns W`. -/
theorem DecHypsExt.of_cli (W : CliHooks) {img : Obj.Image} {S : SpqrModel} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {st0 : DirGhost} {readStk s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope CryptoVerification.E2E.HooksE.A0 img))
    (hs1 : SessKit.loadShimNeed ≤ s1) (hs2 : SessKit.loadPollNeed readStk ≤ s2)
    (hs3 : SessKit.storeShimNeed ≤ s3) (hs4 : SessKit.storePollNeedX ≤ s4)
    (his1 : IdKit.trustShimNeed ≤ is1) (his2 : IdKit.trustPollNeed readStk ≤ is2)
    (his3 : IdKit.saveShimNeed ≤ is3) (his4 : IdKit.savePollNeed readStk ≤ is4)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).addrOk x.rem.val →
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).RecOk rec') :
    DecHypsExt img W.C CryptoVerification.E2E.HooksE.A0 uuidTryParse S
      CryptoVerification.E2E.Record.encodeRecord (cliExterns W)
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4)
      (cliIdentityStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer
        is1 is2 is3 is4)
      st0 Scope :=
  DecHypsExt.of_runHooks himg (RunSkeleton.RunHooks.cli W img)
    (SessKit.cliSessKitOkSE_cli W himg hDeser hs1 hs2 hs3 hs4)
    (IdKit.cliIdKitOkIE_cli W himg his1 his2 his3 his4)
    hscopeInP hrecOk

/-- CLI `decrypt_signal` (`withStoresDecSpecVTP`, `IdOrDistinctSid`) at `cliExterns W` for arbitrary store kits. -/
theorem decryptSignalWithStores_okVTP_fs_cli (W : CliHooks) {img : Obj.Image} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img W.C A uuidTryParse S encRecord (cliExterns W) kit ikit st0 Scope)
    (hC : DecCalleesTP_trap img W.C A ctl S (cliExterns W) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExterns W))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP W.C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  rw [← wsEntryPC_eq_fnAddr_ext (cliExterns W) hH.loads]
  exact withStoresDec_okVTP_fs_ext hH (DecCalleesTPExt.of_trTrap_cli W hC) hQ hKitFs

/-- CLI `decrypt_signal` (`withStoresDecSpecVTP`, `DistinctSid`) at `cliExterns W` for arbitrary store kits. -/
theorem decryptSignalWithStores_okVTP_distinct_fs_cli (W : CliHooks) {img : Obj.Image}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img W.C A uuidTryParse S encRecord (cliExterns W) kit ikit st0 Scope)
    (hC : DecCalleesTP_trap img W.C A ctl S (cliExterns W) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExterns W))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP W.C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  rw [← wsEntryPC_eq_fnAddr_ext (cliExterns W) hH.loads]
  exact withStoresDec_okVTP_distinct_fs_ext hH (DecCalleesTPExt.of_trTrap_cli W hC) hQ hKitFs

/-- CLI `decrypt_signal` (`withStoresDecSpecVT`, `Scope ⊆ RecordInScope`) at `cliExterns W` for arbitrary store kits. -/
theorem decryptSignalWithStores_okVT_fs_cli (W : CliHooks) {img : Obj.Image} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img W.C A uuidTryParse S encRecord (cliExterns W) kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesT_trap img W.C A ctl S (cliExterns W) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExterns W))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre (withStoresDecSpecVT W.C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  rw [← wsEntryPC_eq_fnAddr_ext (cliExterns W) hH.loads]
  exact withStoresDec_okVT_fs_ext hH hscopeIn (DecCalleesTExt.of_trTrap_cli W hC) hQ hKitFs

/-- Concrete file-kit CLI `decrypt_signal` (`withStoresDecSpecVTP`, `IdOrDistinctSid`) at `A0` and `cliExterns W`. -/
theorem cliDecryptSignalWithStores_okVTP_fs_cli (W : CliHooks) {img : Obj.Image}
    {ctl : BitVec 64} {S : SpqrModel} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {peer : AddrGhost} {st0 : DirGhost} {ist0 : IdGhost}
    {readStk s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope CryptoVerification.E2E.HooksE.A0 img))
    (hs1 : SessKit.loadShimNeed ≤ s1) (hs2 : SessKit.loadPollNeed readStk ≤ s2)
    (hs3 : SessKit.storeShimNeed ≤ s3) (hs4 : SessKit.storePollNeedX ≤ s4)
    (his1 : IdKit.trustShimNeed ≤ is1) (his2 : IdKit.trustPollNeed readStk ≤ is2)
    (his3 : IdKit.saveShimNeed ≤ is3) (his4 : IdKit.savePollNeed readStk ≤ is4)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).addrOk x.rem.val →
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).RecOk rec')
    (hC : DecCalleesTP_trap img W.C CryptoVerification.E2E.HooksE.A0 ctl S (cliExterns W) Q)
    (hQ : ScopePq
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4)
      st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S
          CryptoVerification.E2E.Record.encodeRecord img
          (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
            peer s1 s2 s3 s4)
          (cliIdentityStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer
            is1 is2 is3 is4)
          st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse
            (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
              peer s1 s2 s3 s4)
            st0 Scope))
        fun s =>
          (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
            peer s1 s2 s3 s4).envOk s.fs.files ∧
          (cliIdentityStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer
            is1 is2 is3 is4).envOk s.fs.files) :=
  decryptSignalWithStores_okVTP_fs_cli W
    (DecHypsExt.of_cli W himg hDeser hs1 hs2 hs3 hs4 his1 his2 his3 his4 hscopeInP hrecOk)
    hC hQ (cliFilesKits_fsOk (RunSkeleton.RunHooks.cli W img).fs)

/-- Concrete file-kit CLI `decrypt_signal` (`withStoresDecSpecVTP`, `DistinctSid`) at `A0` and `cliExterns W`. -/
theorem cliDecryptSignalWithStores_okVTP_distinct_fs_cli (W : CliHooks) {img : Obj.Image}
    {ctl : BitVec 64} {S : SpqrModel} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {peer : AddrGhost} {st0 : DirGhost} {ist0 : IdGhost}
    {readStk s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope CryptoVerification.E2E.HooksE.A0 img))
    (hs1 : SessKit.loadShimNeed ≤ s1) (hs2 : SessKit.loadPollNeed readStk ≤ s2)
    (hs3 : SessKit.storeShimNeed ≤ s3) (hs4 : SessKit.storePollNeedX ≤ s4)
    (his1 : IdKit.trustShimNeed ≤ is1) (his2 : IdKit.trustPollNeed readStk ≤ is2)
    (his3 : IdKit.saveShimNeed ≤ is3) (his4 : IdKit.savePollNeed readStk ≤ is4)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).addrOk x.rem.val →
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4).RecOk rec')
    (hC : DecCalleesTP_trap img W.C CryptoVerification.E2E.HooksE.A0 ctl S (cliExterns W) Q)
    (hQ : ScopePq
      (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
        peer s1 s2 s3 s4)
      st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S
          CryptoVerification.E2E.Record.encodeRecord img
          (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
            peer s1 s2 s3 s4)
          (cliIdentityStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer
            is1 is2 is3 is4)
          st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s =>
          (cliSessionStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope
            peer s1 s2 s3 s4).envOk s.fs.files ∧
          (cliIdentityStoreSpec CryptoVerification.E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer
            is1 is2 is3 is4).envOk s.fs.files) :=
  decryptSignalWithStores_okVTP_distinct_fs_cli W
    (DecHypsExt.of_cli W himg hDeser hs1 hs2 hs3 hs4 his1 his2 his3 his4 hscopeInP hrecOk)
    hC hQ (cliFilesKits_fsOk (RunSkeleton.RunHooks.cli W img).fs)

/-! ## Parametric contract-backed CLI program (`cliExternsWith ext`) -/

/-- Constructs `DecCalleesTPExt` at `Q := fun _ => True` directly from unconditional `tripleRatchetProgAtExt` proofs. -/
theorem DecCalleesTPExt.of_uncond {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hreg : region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).withVRegs)
    (hrem : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img))
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      img.base A ext) :
    DecCalleesTPExt img C A ctl S ext (fun _ => True) where
  region := region_ok_restrictPre_true hreg
  remoteIk := hrem
  dropSs := hdrop

/-- Lifts `CliExternsOk P A ext` to `AllocContracts4K b A (cliExternsWith ext)`. -/
theorem AllocContracts4K.of_cliExternsOk {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    AllocContracts4K b A (cliExternsWith ext) where
  alloc := by
    have h : subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
        ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr allocName + BitVec.ofNat 64 0)
        (rustAllocSpec A) :=
      hook_ok_at (hname := "__rustc::__rust_alloc")
        (stub := libsignalSessionCode.fnOff "__rustc::__rust_alloc") (k := 0)
        rfl (Nat.add_zero _)
        (by rw [(ls_stub% "__rustc::__rust_alloc")]; decide)
        (fun H => by
          rw [(ls_stub% "__rustc::__rust_alloc")]
          exact (ls_hook% "__rustc::__rust_alloc") H)
        (by simp [Rust.isPanicSymbol])
        (Slots.ext_allocHooks hOk).alloc
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  dealloc := by
    have h : subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
        ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr deallocName + BitVec.ofNat 64 0)
        (rustDeallocSpec A) :=
      hook_ok_at (hname := "__rustc::__rust_dealloc")
        (stub := libsignalSessionCode.fnOff "__rustc::__rust_dealloc") (k := 0)
        rfl (Nat.add_zero _)
        (by rw [(ls_stub% "__rustc::__rust_dealloc")]; decide)
        (fun H => by
          rw [(ls_stub% "__rustc::__rust_dealloc")]
          exact (ls_hook% "__rustc::__rust_dealloc") H)
        (by simp [Rust.isPanicSymbol])
        (Slots.ext_allocHooks hOk).dealloc
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  realloc := by
    have h : subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
        ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr reallocName + BitVec.ofNat 64 0)
        (rustReallocSpec A) :=
      hook_ok_at (hname := "__rustc::__rust_realloc")
        (stub := libsignalSessionCode.fnOff "__rustc::__rust_realloc") (k := 0)
        rfl (Nat.add_zero _)
        (by rw [(ls_stub% "__rustc::__rust_realloc")]; decide)
        (fun H => by
          rw [(ls_stub% "__rustc::__rust_realloc")]
          exact (ls_hook% "__rustc::__rust_realloc") H)
        (by simp [Rust.isPanicSymbol])
        (Slots.ext_allocHooks hOk).realloc
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  shim := by
    have h : subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
        ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr shimName + BitVec.ofNat 64 0)
        sessionShimSpec :=
      hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
        (stub := libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") (k := 0)
        rfl (Nat.add_zero _)
        (by rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]; decide)
        (fun H => by
          rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]
          exact (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") H)
        (by simp [Rust.isPanicSymbol])
        (Slots.ext_shim hOk)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  memcpy := by
    have hSat : HookSat (cliExternsWith ext) "memcpy" msgDecryptMemcpySpec4K :=
      Slots.hookSat_map (Slots.ext_memcpy hOk) fun f hok x R s0 hrun hp hsp => by
        have hp' : s0.mem ⊨ CliExt.memcpySpec.pre x s0 ∗ R := by
          simpa only [CliExt.memcpySpec, libcMemcpySpec, msgDecryptMemcpySpec4K,
            CliExt.memHookStack, allocHookStack, sepConj_assoc] using hp
        obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hp' hsp
        refine ⟨hkf, hsym, ?_⟩
        rcases hout with ⟨hr, hc, hq⟩ | ⟨hs, hq⟩ | ⟨c, hs, hq⟩ | ⟨hs, hq⟩
        · refine Or.inl ⟨hr, hc, ?_⟩
          simpa only [CliExt.memcpySpec, msgDecryptMemcpySpec4K,
            CliExt.memHookStack, allocHookStack, sepConj_assoc] using hq
        · exact Or.inr (Or.inl ⟨hs, hq⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨c, hs, hq⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hs, hq⟩))
    have h : subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
        ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr memcpyName + BitVec.ofNat 64 0)
        msgDecryptMemcpySpec4K :=
      hook_ok_at (hname := "memcpy")
        (stub := libsignalSessionCode.fnOff "memcpy") (k := 0)
        rfl (Nat.add_zero _)
        (by rw [(ls_stub% "memcpy")]; decide)
        (fun H => by
          rw [(ls_stub% "memcpy")]
          exact (ls_hook% "memcpy") H)
        (by simp [Rust.isPanicSymbol])
        hSat
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

/-- Constructs `DecHypsExt4K` from `CliExternsOk P A ext` and the session/identity store-kit bundles. -/
theorem DecHypsExt4K.of_cliExternsOk {P : CryptoVerification.E2E.PEParams} {img : Obj.Image}
    {A : RustAlloc} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {ss : SessionStoreSpec A img.base} {id : IdentityStoreSpec A img.base}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hkit : SessionOnlyKitOkSE ss Scope encRecord (cliExternsWith ext))
    (hikit : StoreKit.Identity.IdentityStoreKitOkIE img id (cliExternsWith ext))
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord P.C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExt4K img P.C A parse S encRecord (cliExternsWith ext) ss id st0 Scope where
  loads := himg
  alloc := AllocContracts4K.of_cliExternsOk img.base hOk
  kit := hkit
  ikit := hikit
  scopeInP := hscopeInP
  recOk := hrecOk

/-- Constructs `DecHypsExt4K` for `cliSessionStoreSpec` and `cliIdentityStoreSpec` under `CliExternsOk P A ext`. -/
theorem DecHypsExt4K.of_cli_ext {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {S : SpqrModel} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {st0 : DirGhost} {readStk s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hs1 : SessKit.loadShimNeed ≤ s1) (hs2 : SessKit.loadPollNeed readStk ≤ s2)
    (hs3 : SessKit.storeShimNeed ≤ s3) (hs4 : SessKit.storePollNeedX ≤ s4)
    (his1 : IdKit.trustShimNeed ≤ is1) (his2 : IdKit.trustPollNeed readStk ≤ is2)
    (his3 : IdKit.saveShimNeed ≤ is3) (his4 : IdKit.savePollNeed readStk ≤ is4)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).addrOk x.rem.val →
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).ScopeAt
        Scope st0 x.rem.val rec →
      decryptRecord P.C S uuidTryParse x rec = .ok (pt, rec') →
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).RecOk rec')
    (hreadStk : extHookStack ≤ readStk := by decide) :
    DecHypsExt4K img P.C A uuidTryParse S
      CryptoVerification.E2E.Record.encodeRecord (cliExternsWith ext)
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      (cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer is1 is2 is3 is4)
      st0 Scope :=
  DecHypsExt4K.of_cliExternsOk hOk himg
    (SessKit.cliSessKitOkSE_ext hOk himg hDeser hs1 hs2 hs3 hs4 hreadStk)
    (IdKit.cliIdKitOkIE_ext hOk himg his1 his2 his3 his4 hreadStk)
    hscopeInP hrecOk

/-- Contract-backed `decrypt_signal` (`withStoresDecSpecVTP`, `IdOrDistinctSid`) at `cliExternsWith ext` for arbitrary store kits. -/
theorem decryptSignalWithStores_okVTP_fs_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord (cliExternsWith ext) kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S (cliExternsWith ext) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExternsWith ext))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  rw [← wsEntryPC_eq_fnAddr_ext (cliExternsWith ext) hH.loads]
  exact withStoresDec_okVTP_fs_ext4K hH hC hQ hKitFs

/-- Contract-backed `decrypt_signal` (`withStoresDecSpecVTP`, `DistinctSid`) at `cliExternsWith ext` for arbitrary store kits. -/
theorem decryptSignalWithStores_okVTP_distinct_fs_ext {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord (cliExternsWith ext) kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S (cliExternsWith ext) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExternsWith ext))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  rw [← wsEntryPC_eq_fnAddr_ext (cliExternsWith ext) hH.loads]
  exact withStoresDec_okVTP_distinct_fs_ext4K hH hC hQ hKitFs

/-- Contract-backed `decrypt_signal` (`withStoresDecSpecVT`, `Scope ⊆ RecordInScope`) at `cliExternsWith ext` for arbitrary store kits. -/
theorem decryptSignalWithStores_okVT_fs_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord (cliExternsWith ext) kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTExt img C A ctl S (cliExternsWith ext) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExternsWith ext))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  rw [← wsEntryPC_eq_fnAddr_ext (cliExternsWith ext) hH.loads]
  exact withStoresDec_okVT_fs_ext4K hH hscopeIn hC hQ hKitFs

/-- Concrete file-kit `decrypt_signal` (`withStoresDecSpecVTP`, `IdOrDistinctSid`) under `CliExternsOk P A ext`. -/
theorem cliDecryptSignalWithStores_okVTP_fs_ext {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    {ctl : BitVec 64} {S : SpqrModel} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {peer : AddrGhost} {st0 : DirGhost} {ist0 : IdGhost}
    {readStk s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hs1 : SessKit.loadShimNeed ≤ s1) (hs2 : SessKit.loadPollNeed readStk ≤ s2)
    (hs3 : SessKit.storeShimNeed ≤ s3) (hs4 : SessKit.storePollNeedX ≤ s4)
    (his1 : IdKit.trustShimNeed ≤ is1) (his2 : IdKit.trustPollNeed readStk ≤ is2)
    (his3 : IdKit.saveShimNeed ≤ is3) (his4 : IdKit.savePollNeed readStk ≤ is4)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).addrOk x.rem.val →
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).ScopeAt
        Scope st0 x.rem.val rec →
      decryptRecord P.C S uuidTryParse x rec = .ok (pt, rec') →
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).RecOk rec')
    (hC : DecCalleesTPExt img P.C A ctl S (cliExternsWith ext) Q)
    (hQ : ScopePq
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hreadStk : extHookStack ≤ readStk := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP P.C A ctl uuidTryParse S
          CryptoVerification.E2E.Record.encodeRecord img
          (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
          (cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer is1 is2 is3 is4)
          st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse
            (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
            st0 Scope))
        fun s =>
          (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).envOk s.fs.files ∧
          (cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer is1 is2 is3 is4).envOk s.fs.files) :=
  decryptSignalWithStores_okVTP_fs_ext
    (DecHypsExt4K.of_cli_ext hOk himg hDeser hs1 hs2 hs3 hs4 his1 his2 his3 his4 hscopeInP hrecOk hreadStk)
    hC hQ (cliFilesKits_fsOk (Slots.ext_traceFsSound hOk img.base))

/-- Concrete file-kit `decrypt_signal` (`withStoresDecSpecVTP`, `DistinctSid`) under `CliExternsOk P A ext`. -/
theorem cliDecryptSignalWithStores_okVTP_distinct_fs_ext {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    {ctl : BitVec 64} {S : SpqrModel} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {peer : AddrGhost} {st0 : DirGhost} {ist0 : IdGhost}
    {readStk s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hs1 : SessKit.loadShimNeed ≤ s1) (hs2 : SessKit.loadPollNeed readStk ≤ s2)
    (hs3 : SessKit.storeShimNeed ≤ s3) (hs4 : SessKit.storePollNeedX ≤ s4)
    (his1 : IdKit.trustShimNeed ≤ is1) (his2 : IdKit.trustPollNeed readStk ≤ is2)
    (his3 : IdKit.saveShimNeed ≤ is3) (his4 : IdKit.savePollNeed readStk ≤ is4)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).addrOk x.rem.val →
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).ScopeAt
        Scope st0 x.rem.val rec →
      decryptRecord P.C S uuidTryParse x rec = .ok (pt, rec') →
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).RecOk rec')
    (hC : DecCalleesTPExt img P.C A ctl S (cliExternsWith ext) Q)
    (hQ : ScopePq
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hreadStk : extHookStack ≤ readStk := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
      (withEnvPre
        ((withStoresDecSpecVTP P.C A ctl uuidTryParse S
          CryptoVerification.E2E.Record.encodeRecord img
          (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
          (cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer is1 is2 is3 is4)
          st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s =>
          (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4).envOk s.fs.files ∧
          (cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer is1 is2 is3 is4).envOk s.fs.files) :=
  decryptSignalWithStores_okVTP_distinct_fs_ext
    (DecHypsExt4K.of_cli_ext hOk himg hDeser hs1 hs2 hs3 hs4 his1 his2 his3 his4 hscopeInP hrecOk hreadStk)
    hC hQ (cliFilesKits_fsOk (Slots.ext_traceFsSound hOk img.base))

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
