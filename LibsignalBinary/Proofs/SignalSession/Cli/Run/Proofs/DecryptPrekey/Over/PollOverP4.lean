/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.S_d2c
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Store
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P3/P4 Kit and Pure Step Glue

Decomposes `overScratch` inside `stageP3StackFrameAt`, instantiates the 2-session (`Prev1`) CLI
session-store kit (`cliPollSessPrev1Kit`, `cliPollStorePrev1Ops`, `cliPollSess_prev1KitOkSE`), and
proves pure `decPkDefD2c` Path C step lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `overScratch` Decomposition Inside `stageP3StackFrameAt` -/

/-- `Over.overScratch sp` equals the trailing `memRegion (sp + 0x538#64) 24 ∗ spHighGapsAt sp`
slice of `stageP3StackFrameAt`. -/
theorem overScratch_eq_sp538_spHighGaps (sp : BitVec 64) :
    Over.overScratch sp = memRegion (sp + 0x538#64) 24 ∗ spHighGapsAt sp := by
  unfold Over.overScratch spHighGapsAt
  rw [memRegion_split (sp + 0x538#64) 24 992 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Stack slots in `stageP3StackFrameAt` outside `Over.overScratch sp` (framed across
`StageP3Prev1VRegsStmt`). -/
def stageP3OverStackFrameAt (sp remoteIkPtr remAddrPtr : BitVec 64) : SepProp :=
  (sp ↦₆₄ 0#64) ∗
  spLowGapsAt sp ∗
  ((sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ remAddrPtr) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  memRegion (sp + 0xd8#64) 376 ∗
  memRegion (sp + 0x264#64) 12 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
  memRegion (sp + 0x2b0#64) 192 ∗
  memRegion (sp + 0x394#64) 12 ∗
  memRegion (sp + 0x3a8#64) 4 ∗
  memRegion (sp + 0x3ad#64) 27

theorem stageP3StackFrameAt_eq_over (sp remoteIkPtr remAddrPtr : BitVec 64) :
    stageP3StackFrameAt sp remoteIkPtr remAddrPtr =
      stageP3OverStackFrameAt sp remoteIkPtr remAddrPtr ∗ Over.overScratch sp := by
  unfold stageP3StackFrameAt stageP3OverStackFrameAt
  rw [overScratch_eq_sp538_spHighGaps sp]
  ac_rfl

/-! ## 2. `Prev1` CLI Session-Store Kit (`cliPollSessPrev1Kit`, `cliPollStorePrev1Ops`) -/

/-- Pure directory invariant preserved across `SessionFiles::store_session` on a 2-session
(`Prev1`) record: retains peer-name and `changed`-vector length bounds without requiring
1-session `SessFileWf`. -/
structure CliSessPrev1Inv (peer : AddrGhost) (d : DirGhost) : Prop where
  nameLt : peer.name.bytes.length < 2 ^ 32
  changedLt : d.changed.length < 2 ^ 32 ∧
    (d.changed.length + 1 < 2 ^ 32 ∨ Cli.addressText peer.val ∈ d.changed.map Prod.fst)

/-- Spatial store predicate for `cliPollSessPrev1Kit` (named `def` so `sep_frame` cancels it as an
atom without exposing pure `⌜...⌝` conjuncts in equation mode). -/
def cliSessPrev1StoreAt (A : RustAlloc) (peer : AddrGhost) (self : BitVec 64)
    (d : DirGhost) : SepProp :=
  ⌜CliSessPrev1Inv peer d⌝ ∗ dirAt A self d

/-- Stage P4 `SessionStoreSpec` for Path C (`Prev1`), sharing `StoreState := DirGhost` and all
vtables, stack budgets, `addrOk`, `envOk`, and `Quiet` fields with `cliPollSessKit` (`rfl`). -/
abbrev cliPollSessPrev1Kit (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) : SessionStoreSpec A b :=
  { cliPollSessKit A b F0 Slots.scopeKit peer σ with
    storeAt := cliSessPrev1StoreAt A peer }

/-- `StorePrev1Ops` on `cliPollSessPrev1Kit`: `store_session` serializes `(sess, [enc])` to
`Over.encodeRecordPrev1 sess enc` and buffers it in `d.put (Cli.addressText rem) ...` with `[]`
trace events. -/
def cliPollStorePrev1Ops {A : RustAlloc} {b : BitVec 64} {F0 : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} :
    Over.StorePrev1Ops (cliPollSessPrev1Kit A b F0 peer σ) where
  RecPrev1Ok := fun G sess enc =>
    E2E.Record.Serialization.CanonSession G sess ∧
    (Over.encodeRecordPrev1 sess enc).length < 2 ^ 32
  storeRelPrev1 := fun _ _ _ _ _ ans => ans = .ok ()
  storeUpdatePrev1 := fun d rem _ sess enc _ =>
    d.put (Cli.addressText rem) (Over.encodeRecordPrev1 sess enc)
  storeEvsPrev1 := fun _ _ _ _ _ => []

theorem cliPollSessKit_storeAt_entails_prev1 {A : RustAlloc} {b : BitVec 64} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {σ : DpKitStk}
    (self : BitVec 64) (d : DirGhost) :
    (cliPollSessKit A b F0 Scope peer σ).storeAt self d ⊢
      (cliPollSessPrev1Kit A b F0 peer σ).storeAt self d := by
  dsimp only [cliPollSessKit, cliSessionStoreSpec, cliPollSessPrev1Kit, cliSessPrev1StoreAt]
  exact Entails.pure_left fun h => Entails.pure_right ⟨h.nameLt, h.changedLt⟩ (Entails.refl _)

theorem cliPollSessPrev1Kit_storeAt_entails_dirAt {A : RustAlloc} {b : BitVec 64} {F0 : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (self : BitVec 64) (d : DirGhost) :
    (cliPollSessPrev1Kit A b F0 peer σ).storeAt self d ⊢ dirAt A self d := by
  dsimp only [cliPollSessPrev1Kit, cliSessPrev1StoreAt]
  exact Entails.pure_left fun _ => Entails.refl _

theorem cliPollSess_prev1VtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    SessionOnlyVtablesOk img (cliPollSessPrev1Kit A img.base F0 peer σ) :=
  cliSessionOnlyVtablesOk himg ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem extract_prev1_pure3 {p1 p2 p3 : Prop} {box dir rest R : SepProp} {m : Memory}
    (hm : m ⊨ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ∗ R) :
    p1 ∧ p2 ∧ p3 := by
  have hperm :
      (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ∗ R =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest ∗ R))) := by
    ac_rfl
  rw [hperm, satisfies_pure_sepConj] at hm
  obtain ⟨hp1, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  obtain ⟨hp2, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  exact ⟨hp1, hp2, hm.1⟩

private theorem extract_prev1_storePoll_pure {fl p1 p2 p3 : Prop}
    {box dir rest R : SepProp} {m : Memory}
    (hm : m ⊨ (⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest))) ∗ R) :
    p1 ∧ p2 ∧ p3 := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact extract_prev1_pure3 hm.2

private theorem prev1_storePoll_pre_entails {fl p1 p2 p3 q : Prop} {box dir rest : SepProp}
    (hq : p1 → p2 → p3 → q) :
    ⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest)) ⊢
      ⌜fl⌝ ∗ (⌜q⌝ ∗ box ∗ dir ∗ rest) := by
  apply Entails.pure_left; intro hfl
  refine Entails.pure_right hfl ?_
  have hperm :
      ⌜p1⌝ ∗ (⌜p2⌝ ∗ box ∗ (⌜p3⌝ ∗ dir) ∗ rest) =
        ⌜p1⌝ ∗ (⌜p2⌝ ∗ (⌜p3⌝ ∗ (box ∗ dir ∗ rest))) := by
    ac_rfl
  rw [hperm]
  apply Entails.pure_left; intro hp1
  apply Entails.pure_left; intro hp2
  apply Entails.pure_left; intro hp3
  exact Entails.pure_right (hq hp1 hp2 hp3) (Entails.refl _)

private theorem prev1_storePoll_post_sat {p : Prop} {q : Except Unit Unit → Prop} {inv' : Prop}
    {box1 dir0 outA outB tail R : SepProp}
    {storeAt' outAt' : Except Unit Unit → SepProp} {m : Memory}
    (hq : p → q (.ok ())) (hinv' : inv')
    (hstore : storeAt' (.ok ()) = ⌜inv'⌝ ∗ dir0)
    (hout : outAt' (.ok ()) = outA ∗ outB)
    (hm : m ⊨ (⌜p⌝ ∗ box1 ∗ dir0 ∗ outA ∗ outB ∗ tail) ∗ R) :
    m ⊨ (∃∗ ans : Except Unit Unit,
          ⌜q ans⌝ ∗ box1 ∗ storeAt' ans ∗ outAt' ans ∗ tail) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hp, hm⟩ := hm
  refine Satisfies.sepExists_intro (.ok ()) ?_
  rw [hstore, hout, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hq hp, Arm64.Satisfies.mono (sepConj_mono_left ?_) hm⟩
  rw [← sepConj_assoc outA outB tail]
  exact sepConj_mono_right (sepConj_mono_left (Entails.pure_right hinv' (Entails.refl dir0)))

theorem cliPollSess_prev1KitOkSE (W : CliHooks) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) (F0 : FsFiles)
    (peer : AddrGhost) (B : RunBudgets) :
    Over.SessionPrev1KitOkSE
      (cliPollSessPrev1Kit E2E.HooksE.A0 img.base F0 peer (cliKitStk B))
      cliPollStorePrev1Ops (cliExterns W) where
  storeShim := Store.StoreSessionPrev1.sessStoreShim_cli_at W himg
    (by dsimp only [cliPollSessPrev1Kit, cliPollSessKit, cliSessionStoreSpec, cliKitStk]; decide)
  storePollPrev1 := by
    have h := Store.StoreSessionPrev1.sessStorePollPrev1_cli_at W himg
      (stk := (cliKitStk B).sessStorePoll)
      (by dsimp only [cliKitStk]; decide)
    refine subroutine_ok_map_panic h ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    obtain ⟨_, ⟨_, _, _hrec, haddr⟩, hinv⟩ := extract_prev1_storePoll_pure hpre
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    let x : Store.StoreSessionPrev1.SessStorePollPrev1Ghost :=
      ⟨call.fut, self, call.out, call.addrA, call.addr, call.recA,
       call.prevCap, call.prevPtr, call.G, call.sess, call.enc, d⟩
    refine ⟨x, R, ?_, ?_, fun _ hpan => hpan⟩
    · exact Arm64.Satisfies.mono
        (sepConj_mono_left
          (prev1_storePoll_pre_entails fun _ ⟨hx0, hx8, ⟨hcan, hlen⟩, _⟩ hinv' =>
            ⟨hx0, hx8, hname ▸ hinv'.nameLt, hcan, hlen, hinv'.changedLt.1⟩))
        hpre
    · intro sf hpost
      have hinv_put : CliSessPrev1Inv peer
          (d.put (Cli.addressText call.addr.val) (Over.encodeRecordPrev1 call.sess call.enc)) := by
        rw [haddr]
        exact ⟨hinv.nameLt,
          Store.StoreSessionPrev1.changedLt_put_self
            (Over.encodeRecordPrev1 call.sess call.enc) hinv.changedLt⟩
      exact prev1_storePoll_post_sat
        (fun htr => ⟨rfl, by
          show sf.trace = s0.trace ++ []
          rw [List.append_nil]
          exact htr⟩)
        hinv_put rfl rfl hpost
  storeFutDrop := Store.StoreSessionPrev1.sessStoreFutDrop_cli_at W img

/-- `(P : PEParams) (A : RustAlloc)` contract-backed `SessionPrev1KitOkSE` on `cliExternsWith ext`
from `CliExternsOk P A ext`. -/
theorem cliPollSess_prev1KitOkSE_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) (F0 : FsFiles)
    (peer : AddrGhost) (B : RunBudgets) :
    Over.SessionPrev1KitOkSE
      (cliPollSessPrev1Kit A img.base F0 peer (cliKitStk B))
      cliPollStorePrev1Ops (cliExternsWith ext) where
  storeShim := Store.StoreSessionPrev1.sessStoreShim_ext_at hOk himg
    (by dsimp only [cliPollSessPrev1Kit, cliPollSessKit, cliSessionStoreSpec, cliKitStk]; decide)
  storePollPrev1 := by
    have h := Store.StoreSessionPrev1.sessStorePollPrev1_ext_at hOk himg
      (stk := (cliKitStk B).sessStorePoll)
      (by dsimp only [cliKitStk]; decide)
    refine subroutine_ok_map_panic h ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    obtain ⟨_, ⟨_, _, _hrec, haddr⟩, hinv⟩ := extract_prev1_storePoll_pure hpre
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    let x : Store.StoreSessionPrev1.SessStorePollPrev1Ghost :=
      ⟨call.fut, self, call.out, call.addrA, call.addr, call.recA,
       call.prevCap, call.prevPtr, call.G, call.sess, call.enc, d⟩
    refine ⟨x, R, ?_, ?_, fun _ hpan => hpan⟩
    · exact Arm64.Satisfies.mono
        (sepConj_mono_left
          (prev1_storePoll_pre_entails fun _ ⟨hx0, hx8, ⟨hcan, hlen⟩, _⟩ hinv' =>
            ⟨hx0, hx8, hname ▸ hinv'.nameLt, hcan, hlen, hinv'.changedLt.1⟩))
        hpre
    · intro sf hpost
      have hinv_put : CliSessPrev1Inv peer
          (d.put (Cli.addressText call.addr.val) (Over.encodeRecordPrev1 call.sess call.enc)) := by
        rw [haddr]
        exact ⟨hinv.nameLt,
          Store.StoreSessionPrev1.changedLt_put_self
            (Over.encodeRecordPrev1 call.sess call.enc) hinv.changedLt⟩
      exact prev1_storePoll_post_sat
        (fun htr => ⟨rfl, by
          show sf.trace = s0.trace ++ []
          rw [List.append_nil]
          exact htr⟩)
        hinv_put rfl rfl hpost
  storeFutDrop := Store.StoreSessionPrev1.sessStoreFutDrop_ext_at hOk img

/-! ## 3. Pure `decPkDefD2c` Path C Agreement Lemmas -/

/-- Because `Slots.loadRec (fun _ => False) F peer` can never return `.ok (some r)`,
`DecPkOkD2c W Scope F peer me pm` implies `DecPkOk₀ W (fun _ => False) F peer me pm`,
unlocking all `Scope`-independent inner decryption lemmas on Path C. -/
theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.DecPkOkD2c.toDecPkOk₀_emptyScope
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (h : DecPkOkD2c W Scope F peer me pm) :
    DecPkOk₀ W (fun _ => False) F peer me pm :=
  h.toDecPkOk₀_vacuous

theorem decPkDefD2c_pathC_lookup_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))} {m : PreKeyMessageFields}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpm : pkToE? pm = some m)
    (herr : pkStoreKeys F m = none ∨
      StoresGhost.opened.identity.keyPair cliIo.rd F = .error () ∨
      StoresGhost.opened.identity.regId cliIo.rd F = .error ()) :
    decPkDefD2c X W Scope F peer me pm coins = some none := by
  rw [decPkDefD2c_of_not_match X W Scope F peer me pm coins hload hcur htrust hnot]
  dsimp only [decPkAcceptWith]
  rw [hpm]
  dsimp only
  rcases herr with hk | hkp | hreg
  · rw [hk]
  · rcases pkStoreKeys F m with _ | k
    · rfl
    · rw [hkp]
  · rcases pkStoreKeys F m with _ | k
    · rfl
    · rcases StoresGhost.opened.identity.keyPair cliIo.rd F with _ | kp
      · rfl
      · rw [hreg]

theorem decPkDefD2c_pathC_accept_none (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpm : pkToE? pm = some m)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = none) :
    decPkDefD2c X W Scope F peer me pm coins = some none := by
  rw [decPkDefD2c_of_not_match X W Scope F peer me pm coins hload hcur htrust hnot]
  dsimp only [decPkAcceptWith]
  rw [hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_none X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]

theorem decPkDefD2c_pathC_ver_ne (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
      pm.message.messageVersion.zeroExtend 32) :
    decPkDefD2c X W Scope F peer me pm coins = some none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : pm.message = i := hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1
  rw [hmsg] at hver
  rw [decPkDefD2c_of_not_match X W Scope F peer me pm coins hload hcur htrust hnot]
  dsimp only [decPkAcceptWith]
  rw [hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ k m i
      (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc,
    tryDecryptFromRecord_preKey_ver_ne hver]

theorem decPkDefD2c_pathC_panic (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hpan : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error .panic) :
    decPkDefD2c X W Scope F peer.val me.val pm coins = none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  rw [decPkDefD2c_of_not_match X W Scope F peer.val me.val pm coins hload hcur htrust hnot]
  dsimp only [decPkAcceptWith]
  rw [hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  rw [hmsg, tryDecryptFromRecord_preKey_ver_eq hd.toDecPkOk₀_emptyScope hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) with ⟨res, st'⟩
  rw [hm] at hpan
  dsimp only at hpan
  subst hpan
  rfl

theorem decPkDefD2c_pathC_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {e : SignalProtocolError}
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (herr : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e)
    (hne : e ≠ .panic) :
    decPkDefD2c X W Scope F peer.val me.val pm coins = some none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  rw [decPkDefD2c_of_not_match X W Scope F peer.val me.val pm coins hload hcur htrust hnot]
  dsimp only [decPkAcceptWith]
  rw [hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  rw [hmsg, tryDecryptFromRecord_preKey_ver_eq hd.toDecPkOk₀_emptyScope hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) with ⟨res, st'⟩
  rw [hm] at herr
  dsimp only at herr
  subst herr
  dsimp only
  have hne' : SessionState.recordError .preKey e ≠ .panic :=
    mt (recordError_eq_panic_iff .preKey e).mp hne
  cases hr : SessionState.recordError .preKey e <;> first | exact absurd hr hne' | rfl

theorem decPkDefD2c_pathC_mark_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)} {st' : SessionState (List (BitVec 8))}
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).1 =
      .error ()) :
    decPkDefD2c X W Scope F peer.val me.val pm coins = some none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  rw [decPkDefD2c_of_not_match X W Scope F peer.val me.val pm coins hload hcur htrust hnot]
  dsimp only [decPkAcceptWith]
  rw [hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  rw [hmsg, tryDecryptFromRecord_preKey_ver_eq hd.toDecPkOk₀_emptyScope hver, hok]
  dsimp only
  rcases hmk : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
    ⟨r_mk, kyber'⟩
  rw [hmk] at hmark
  dsimp only at hmark
  subst hmark
  rfl

theorem decPkDefD2c_pathC_ok (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))} {kyber' : KyberGhost}
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s_old pm)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey =
      (.ok (), kyber')) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let prevEnc := E2E.Record.encSession (Over.clearPending s_old)
    let oneTime' := match pm.preKeyId with
      | none => StoresGhost.opened.oneTime
      | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
    let g' : StoresGhost :=
      { StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := oneTime'
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (Over.encodeRecordPrev1 ses' prevEnc) }
    decPkDefD2c X W Scope F peer.val me.val pm coins = some (some (g', pt)) ∧
      (∀ pw ∈ g'.writes, cliWrOk pw.1) := by
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  have htry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) (pathAInitState W meE k m dk) = (.ok pt, st') := by
    rw [tryDecryptFromRecord_preKey_ver_eq hd.toDecPkOk₀_emptyScope hver, hok]
  have hPendFalse : st'.pendingPreKey = false :=
    (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) htry).1
  have hEncEq : E2E.Record.encodeRecord
      ⟨some { pathAInitSession W meE k m dk with
              state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩ =
      encodeRecordUnderExtras (fun _ => responderRecordExtras meE m) ⟨initParty peer.val, st', 1, [1]⟩ :=
    DecPkS0.encodeRecord_cleared_eq_encodeRecordX (responderRecordExtras meE m)
      ⟨initParty peer.val, pathAInitState W meE k m dk, 1, [1]⟩ st' hPendFalse
  have hPrev1Eq :
      encodeRecordUnderExtras (fun _ => responderRecordExtras meE m) ⟨initParty peer.val, st', 1, [1]⟩ ++
        E2E.Record.lenField 2 (E2E.Record.encSession (Over.clearPending s_old)) =
      Over.encodeRecordPrev1
        { pathAInitSession W meE k m dk with
          state := st', pendingPreKey := none, pendingKyberPreKey := none }
        (E2E.Record.encSession (Over.clearPending s_old)) := by
    rw [← hEncEq]
    rfl
  have hDec : decPkDefD2c X W Scope F peer.val me.val pm coins =
      some (some ({ StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := match pm.preKeyId with
          | none => StoresGhost.opened.oneTime
          | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (Over.encodeRecordPrev1
            { pathAInitSession W meE k m dk with
              state := st', pendingPreKey := none, pendingKyberPreKey := none }
            (E2E.Record.encSession (Over.clearPending s_old))) }, pt)) := by
    rw [decPkDefD2c_of_not_match X W Scope F peer.val me.val pm coins hload hcur htrust hnot]
    dsimp only [decPkAcceptWith]
    rw [hpm]
    dsimp only
    rw [hk, hkp, hreg]
    dsimp only
    rw [recvPrekeyState_of_accept_some X W (initParty peer.val) meE k m i
      (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
    rw [hmsg, htry]
    dsimp only
    rw [hmark]
    dsimp only
    rw [hPrev1Eq]
    rfl
  have hky' : kyber' =
      (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).2 := by
    rw [hmark]
  have hWr : ∀ pw ∈ ({ StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := match pm.preKeyId with
          | none => StoresGhost.opened.oneTime
          | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (Over.encodeRecordPrev1
            { pathAInitSession W meE k m dk with
              state := st', pendingPreKey := none, pendingKyberPreKey := none }
            (E2E.Record.encSession (Over.clearPending s_old))) } :
        StoresGhost).writes, cliWrOk pw.1 := by
    rw [hky']
    exact storesWrOk_pathA hf
  exact ⟨hDec, hWr⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll



