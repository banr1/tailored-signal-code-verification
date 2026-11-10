/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAlice
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link

/-!
# CLI Poll Stage P2 V1 Store Canonicality and Model Agreement

Provides `SepWPp` step/pure-extraction combinators, pre-key store canonicality bridges under
`PreKeyFilesWf`, and pure Path A `acceptKeys`, `p2BobInitSessionV1`, and `SessionExtraRel`
agreement lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue initialStateValue_libsignal')
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. `SepWPp` Step & Pure-Fact Extraction Combinators -/

/-- Thread `Steps prog s1 sf` into both `Q` and `Qp` of `SepWPp`. -/
theorem sepWPp_with_steps {prog : Program} {ret : BitVec 64} {s1 : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s1 P (fun sf Pf => Steps prog s1 sf → Q sf Pf)
      (fun sf Pf => Steps prog s1 sf → Qp sf Pf)) :
    SepWPp prog ret s1 P Q Qp := by
  intro R hPR hcode
  obtain ⟨sf, hsteps, hbranch⟩ := h R hPR hcode
  refine ⟨sf, hsteps, ?_⟩
  rcases hbranch with ⟨hpc, hrun, Pf, hmem, hQ⟩ | ⟨hpan, Pf, hmem, hQp⟩ | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmem, hQ hsteps⟩
  · exact Or.inr (Or.inl ⟨hpan, Pf, hmem, hQp hsteps⟩)
  · exact Or.inr (Or.inr hoom)

/-- Discharge the threaded `Steps prog s1 sf` obligation from an intermediate `Steps prog s1 s2`. -/
theorem sepWPp_drop_steps {prog : Program} {ret : BitVec 64} {s2 : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {s1 : State}
    (_h12 : Steps prog s1 s2)
    (h : SepWPp prog ret s2 P Q Qp) :
    SepWPp prog ret s2 P (fun sf Pf => Steps prog s1 sf → Q sf Pf)
      (fun sf Pf => Steps prog s1 sf → Qp sf Pf) := by
  intro R hPR hcode
  obtain ⟨sf, hsteps, hbranch⟩ := h R hPR hcode
  refine ⟨sf, hsteps, ?_⟩
  rcases hbranch with ⟨hpc, hrun, Pf, hmem, hQ⟩ | ⟨hpan, Pf, hmem, hQp⟩ | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmem, fun _ => hQ⟩
  · exact Or.inr (Or.inl ⟨hpan, Pf, hmem, fun _ => hQp⟩)
  · exact Or.inr (Or.inr hoom)

private theorem dup_pure_sepConj_right {φ : Prop} {A B : SepProp}
    (h : B ⊢ ⌜φ⌝ ∗ B) : A ∗ B ⊢ ⌜φ⌝ ∗ (A ∗ B) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem dup_pure_sepConj_left {φ : Prop} {A B : SepProp}
    (h : A ⊢ ⌜φ⌝ ∗ A) : A ∗ B ⊢ ⌜φ⌝ ∗ (A ∗ B) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

/-- Duplicate `⌜g.kyberPtr ≠ 0#64⌝` out of `pathAMsgRemInnerAtExt`. -/
theorem pathAMsgRemInnerAt_dup_kyberPtr_ext (A : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    pathAMsgRemInnerAtExt A g msgA m i ⊢
      ⌜g.kyberPtr ≠ 0#64⌝ ∗ pathAMsgRemInnerAtExt A g msgA m i := by
  unfold pathAMsgRemInnerAtExt
  refine Entails.pure_left fun hp => ?_
  have hne : g.kyberPtr ≠ 0#64 := hp.1
  rw [pure_sepConj_of_true hne, pure_sepConj_of_true hp]
  exact Entails.refl _

/-- Duplicate `⌜g.kyberPtr ≠ 0#64⌝` out of `pathAMsgRemInnerAt`. -/
theorem pathAMsgRemInnerAt_dup_kyberPtr (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    pathAMsgRemInnerAt g msgA m i ⊢
      ⌜g.kyberPtr ≠ 0#64⌝ ∗ pathAMsgRemInnerAt g msgA m i :=
  pathAMsgRemInnerAt_dup_kyberPtr_ext E2E.HooksE.A0 g msgA m i

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFrameExt`. -/
theorem pathAInnerFrame_dup_kyberPtr_ext {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFrameExt img y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFrameExt img y m i rngPtr sp := by
  unfold pathAInnerFrameExt
  repeat (first
    | exact dup_pure_sepConj_left (pathAMsgRemInnerAt_dup_kyberPtr_ext A y.g.msgG y.g.msgA m i)
    | refine dup_pure_sepConj_right ?_)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFrame`. -/
theorem pathAInnerFrame_dup_kyberPtr {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFrame img y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFrame img y m i rngPtr sp :=
  pathAInnerFrame_dup_kyberPtr_ext img y m i rngPtr sp

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` to the front of `stageP2PreAt... (pathAInnerFrameExt...)`. -/
theorem stageP2PreAt_dup_kyberPtr_ext {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PreAt A img
      (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFrameExt img y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAt A img
      (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFrameExt img y m i rngPtr sp) := by
  unfold stageP2PreAt
  repeat (first
    | exact pathAInnerFrame_dup_kyberPtr_ext img y m i rngPtr sp
    | exact dup_pure_sepConj_left (pathAInnerFrame_dup_kyberPtr_ext img y m i rngPtr sp)
    | refine dup_pure_sepConj_right ?_)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` to the front of `stageP2PreAt... (pathAInnerFrame...)`. -/
theorem stageP2PreAt_dup_kyberPtr {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PreAt E2E.HooksE.A0 img
      (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFrame img y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAt E2E.HooksE.A0 img
      (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFrame img y m i rngPtr sp) :=
  stageP2PreAt_dup_kyberPtr_ext img y m i w s0 sp fp rngPtr v_a8 v_b8 v_d0

/-! ## 2. Store Canonicality & Self-Kit Relations -/

theorem cliPollSelf_kpRel_ok {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {kp : IdentityKeyPair}
    (h : (cliPollSelfKit A b F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp :=
  (KitInst.SelfRel.cliKpRel_ok_iff cliIo.rd F StoresGhost.opened.identity kp).mp h

theorem cliPollSelf_kpRel_err {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {e : (cliPollSelfKit A b F peer σ).KpErr}
    (h : (cliPollSelfKit A b F peer σ).kpRel StoresGhost.opened.identity (.error e)) :
    StoresGhost.opened.identity.keyPair cliIo.rd F = .error () :=
  (KitInst.SelfRel.cliKpRel_opened_error_iff F e).mp h

theorem cliPollSelf_regIdRel_ok {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {reg : BitVec 32}
    (h : (cliPollSelfKit A b F peer σ).regIdRel StoresGhost.opened.identity (.ok reg)) :
    StoresGhost.opened.identity.regId cliIo.rd F = .ok reg :=
  (KitInst.SelfRel.cliRegIdRel_ok_iff cliIo.rd F StoresGhost.opened.identity reg).mp h

theorem cliPollSelf_regIdRel_err {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {e : (cliPollSelfKit A b F peer σ).RegIdErr}
    (h : (cliPollSelfKit A b F peer σ).regIdRel StoresGhost.opened.identity (.error e)) :
    StoresGhost.opened.identity.regId cliIo.rd F = .error () :=
  (KitInst.SelfRel.cliRegIdRel_opened_error_iff F e).mp h

private theorem bytesToBv8_inj : ∀ {xs ys : SignalPqxdh.Bytes},
    bytesToBv8 xs = bytesToBv8 ys → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [bytesToBv8, List.map_cons, List.cons.injEq] at h
    have hxy : x = y := UInt8.eq_of_toBitVec_eq (by simpa [UInt8.toBitVec] using h.1)
    rw [hxy, bytesToBv8_inj h.2]

private theorem toU8_vecToList_eq_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    toU8 v.toList = E2E.vecU8 v := by
  apply bytesToBv8_inj
  rw [bytesToBv8_toU8, bytesToBv8_vecU8]

private theorem clampBv8List_vec32_eq (v : List.Vector (BitVec 8) 32) :
    clampBv8List v.toList = (Ratchet.clampScalar v).toList := by
  rcases v with ⟨bs, hbs⟩
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, bs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hbs)
  rcases bs with _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, bs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hbs)
  rcases bs with _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23, bs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hbs)
  rcases bs with _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, bs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hbs)
  rcases bs with _ | ⟨_, _⟩
  · rfl
  · simp at hbs

/-- Private key inside `IdentityKeyPair` decoded from `StoresGhost.opened.identity.keyPair` is
already clamped (`Ratchet.clampScalar`), so `keyPairOf` leaves `.privateKey.bytes` unchanged. -/
theorem idKeyPair_keyPairOf_privateKey {C : Crypto} {F : FsFiles} {kp : IdentityKeyPair}
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    (keyPairOf C kp.privateKey.bytes).privateKey.bytes = kp.privateKey.bytes := by
  unfold IdGhost.keyPair at hkp
  cases hg : StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") with
  | error e => simp [hg, Except.bind] at hkp
  | ok bs =>
    simp only [hg, Except.bind] at hkp
    unfold IdentityKeyPair.tryFrom at hkp
    cases hp : IdentityKeyPairStructure.decode bs with
    | none => simp [hp] at hkp
    | some s =>
      simp only [hp] at hkp
      cases hpub : decodeIdentityKey s.publicKey with
      | error e => simp [hpub, Bind.bind, Except.bind] at hkp
      | ok ik =>
        cases hpriv : deserializePrivateKey s.privateKey with
        | error e => simp [hpub, hpriv, Bind.bind, Except.bind] at hkp
        | ok sk =>
          simp only [hpub, hpriv, Bind.bind, Except.bind, Pure.pure, Except.pure,
            Except.ok.injEq] at hkp
          subst hkp
          unfold deserializePrivateKey at hpriv
          split at hpriv
          · injection hpriv with hsk
            subst hsk
            exact Reach.clampScalar_idem _
          · contradiction

/-- SPK canonicality (`hspk_wf`) on `cliPollSpkKit` under `PreKeyFilesWf` (allocator-polymorphic). -/
theorem cliPollSpk_wf_of_preKeysWf_ext {W : PEParams} {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {spkId : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : SignedPreKeyRecord)
    (hrel : (cliPollSpkKit A b F spkId σ).getRel StoresGhost.opened.signed spkId (.ok r)) :
    ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
      spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧
      r.signedPreKey.privateKey = spkPrivBytes := by
  have hget : getSignedPreKey cliIo.rd F StoresGhost.opened.signed spkId = .ok r :=
    (cliSpk_getRel_ok_iff cliIo.rd F cliWrOk spkId _ _ StoresGhost.opened.signed spkId r).mp hrel
  obtain ⟨k, hr, _⟩ := signed_canonical_of_preKeysWf hwf hget
  subst hr
  exact ⟨(keyPairOf W.C k.priv).publicKey.bytes.toList, k.priv.toList,
    List.Vector.toList_length _, List.Vector.toList_length _, rfl, rfl⟩

/-- SPK canonicality (`hspk_wf`) on `cliPollSpkKit` under `PreKeyFilesWf`. -/
theorem cliPollSpk_wf_of_preKeysWf {W : PEParams} {b : BitVec 64} {F : FsFiles}
    {spkId : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : SignedPreKeyRecord)
    (hrel : (cliPollSpkKit E2E.HooksE.A0 b F spkId σ).getRel StoresGhost.opened.signed spkId (.ok r)) :
    ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
      spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧
      r.signedPreKey.privateKey = spkPrivBytes :=
  cliPollSpk_wf_of_preKeysWf_ext hwf r hrel

/-- KPK canonicality (`hkpk_wf`) on `cliPollKpkKit` under `PreKeyFilesWf` (allocator-polymorphic). -/
theorem cliPollKpk_wf_of_preKeysWf_ext {W : PEParams} {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {kpkId spkId : BitVec 32} {kbk : PublicKey} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : KyberPreKeyRecord)
    (hrel : (cliPollKpkKit A b F kpkId spkId kbk σ).getRel
      StoresGhost.opened.kyber kpkId (.ok r)) :
    ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
      kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes := by
  have hget : StoresGhost.opened.kyber.get cliIo.rd F kpkId = .ok r :=
    (cliKpk_getRel_ok_iff (A := A) cliIo.rd F cliWrOk kpkId
      StoresGhost.opened.kyber kpkId r).mp hrel
  obtain ⟨k, hr, _, _⟩ := kyber_canonical_of_preKeysWf hwf hget
  subst hr
  exact ⟨k.pub.toList, k.sec.toList,
    List.Vector.toList_length _, List.Vector.toList_length _, rfl, rfl⟩

/-- KPK canonicality (`hkpk_wf`) on `cliPollKpkKit` under `PreKeyFilesWf`. -/
theorem cliPollKpk_wf_of_preKeysWf {W : PEParams} {b : BitVec 64} {F : FsFiles}
    {kpkId spkId : BitVec 32} {kbk : PublicKey} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : KyberPreKeyRecord)
    (hrel : (cliPollKpkKit E2E.HooksE.A0 b F kpkId spkId kbk σ).getRel
      StoresGhost.opened.kyber kpkId (.ok r)) :
    ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
      kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes :=
  cliPollKpk_wf_of_preKeysWf_ext hwf r hrel

/-- OPK canonicality (`hpk_wf`) on `cliPollPkKit` under `PreKeyFilesWf` (allocator-polymorphic). -/
theorem cliPollPk_wf_of_preKeysWf_ext {W : PEParams} {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {opkWord id : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : PreKeyRecord)
    (hrel : (cliPollPkKit A b F opkWord σ).getRel
      StoresGhost.opened.oneTime id (.ok r)) :
    ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
      opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
      r.preKey.publicKey = 5#8 :: opkPubBytes ∧
      r.preKey.privateKey = opkPrivBytes := by
  have hget : getPreKey cliIo.rd F StoresGhost.opened.oneTime id = .ok r :=
    (cliPk_getRel_ok_iff cliIo.rd F cliWrOk opkWord _ _ _ _
      StoresGhost.opened.oneTime id r).mp hrel
  obtain ⟨sk, hr, _⟩ := oneTime_canonical_of_preKeysWf hwf hget
  subst hr
  exact ⟨(keyPairOf W.C sk).publicKey.bytes.toList, sk.toList,
    List.Vector.toList_length _, List.Vector.toList_length _, rfl, rfl⟩

/-- OPK canonicality (`hpk_wf`) on `cliPollPkKit` under `PreKeyFilesWf`. -/
theorem cliPollPk_wf_of_preKeysWf {W : PEParams} {b : BitVec 64} {F : FsFiles}
    {opkWord id : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : PreKeyRecord)
    (hrel : (cliPollPkKit E2E.HooksE.A0 b F opkWord σ).getRel
      StoresGhost.opened.oneTime id (.ok r)) :
    ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
      opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
      r.preKey.publicKey = 5#8 :: opkPubBytes ∧
      r.preKey.privateKey = opkPrivBytes :=
  cliPollPk_wf_of_preKeysWf_ext hwf r hrel

/-! ## 3. Pure Path A Model Agreement -/

/-- Under successful SPK, KPK, OPK, and identity-keypair loads, `pkStoreKeys F m = some k` and
`mkP2AcceptKeysInput` equals `ofSignalPqxdhAcceptKeysInput (acceptInput...)` (`PEParams` /
allocator-polymorphic). -/
theorem pathA_acceptInput_agree_ext {W : PEParams} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {b : BitVec 64} {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} {opkWord : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)}
    {kp : IdentityKeyPair} {ikBSk ikBPk : SignalPqxdh.Bytes}
    (hdecOk : DecPkOk₀ W Scope F peer me pm)
    (hspkRel : (cliPollSpkKit A b F m.spkId σ).getRel
      StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKit A b F m.kpkId m.spkId pm.baseKey σ).getRel
      StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKit A b F opkWord σ)
      StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hikBSk : ikBSk = E2E.vecU8 kp.privateKey.bytes)
    (hikBPk : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes) :
    ∃ k : ResponderPreKeySecrets,
      pkStoreKeys F m = some k ∧
      spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList ∧
      spkPrivBytes = k.spkPriv.toList ∧
      (∀ reg : BitVec 32,
        mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes =
        ofSignalPqxdhAcceptKeysInput
          (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m)) := by
  have hspkGet : getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId = .ok spkRec :=
    (cliSpk_getRel_ok_iff cliIo.rd F cliWrOk m.spkId _ _ StoresGhost.opened.signed m.spkId spkRec).mp
      hspkRel
  have hkpkGet : StoresGhost.opened.kyber.get cliIo.rd F m.kpkId = .ok kpkRec :=
    (cliKpk_getRel_ok_iff (A := A) cliIo.rd F cliWrOk m.kpkId
      StoresGhost.opened.kyber m.kpkId kpkRec).mp hkpkRel
  obtain ⟨k_spk, hspkR, hspkV⟩ := signed_canonical_of_preKeysWf hdecOk.preKeysWf hspkGet
  obtain ⟨k_kyb, hkpkR, hkpubV, hksecV⟩ := kyber_canonical_of_preKeysWf hdecOk.preKeysWf hkpkGet
  have hspkPub_eq : spkPubBytes = (keyPairOf W.C k_spk.priv).publicKey.bytes.toList := by
    rw [hspkR] at hspkPubEq
    exact List.cons.inj hspkPubEq.symm |>.2
  have hspkPriv_eq : spkPrivBytes = k_spk.priv.toList := by
    rw [hspkR] at hspkPrivEq
    exact hspkPrivEq.symm
  have hkpub_eq : kyberPubBytes = k_kyb.pub.toList := by
    rw [hkpkR] at hkpkPubEq
    exact List.cons.inj hkpkPubEq.symm |>.2
  have hkpriv_eq : kyberPrivBytes = k_kyb.sec.toList := by
    rw [hkpkR] at hkpkPrivEq
    exact List.cons.inj hkpkPrivEq.symm |>.2
  have hidPriv : (keyPairOf W.C kp.privateKey.bytes).privateKey.bytes = kp.privateKey.bytes :=
    idKeyPair_keyPairOf_privateKey hkp
  have hidPub : kp.identityKey.publicKey = (keyPairOf W.C kp.privateKey.bytes).publicKey :=
    hdecOk.idPairDerived kp hkp
  have hikBSk_eq : ikBSk = E2E.vecU8 (keyPairOf W.C kp.privateKey.bytes).privateKey.bytes := by
    rw [hikBSk, hidPriv]
  have hikBPk_eq : ikBPk = E2E.vecU8 (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes := by
    rw [hikBPk, hidPub]
  have hspkBSk_eq :
      toU8 (clampBv8List spkPrivBytes) =
        E2E.vecU8 (keyPairOf W.C k_spk.priv).privateKey.bytes := by
    rw [hspkPriv_eq, clampBv8List_vec32_eq, ← toU8_vecToList_eq_vecU8]
    rfl
  have hspkBPk_eq :
      toU8 spkPubBytes = E2E.vecU8 (keyPairOf W.C k_spk.priv).publicKey.bytes := by
    rw [hspkPub_eq, toU8_vecToList_eq_vecU8]
  have hkpubU8_eq : toU8 kyberPubBytes = E2E.vecU8 k_kyb.pub := by
    rw [hkpub_eq, toU8_vecToList_eq_vecU8]
  have hkprivU8_eq : toU8 kyberPrivBytes = E2E.vecU8 k_kyb.sec := by
    rw [hkpriv_eq, toU8_vecToList_eq_vecU8]
  generalize hopkEq : hdrOpkIdBv? (mkPathAHdr m) = optOpk at wOpk hopkOk hopkBytes
  have hmOpk : m.opkId = optOpk := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkEq
  cases optOpk with
  | none =>
    refine ⟨{ spkId := m.spkId, spkPriv := k_spk.priv, kpkId := m.kpkId,
              kpkPub := k_kyb.pub, kpkSec := k_kyb.sec, opk := none },
      pkStoreKeys_eq_some_none_opk hspkGet hkpkGet hspkV hkpubV hksecV hmOpk,
      hspkPub_eq, hspkPriv_eq, fun reg => ?_⟩
    unfold mkP2AcceptKeysInput ofSignalPqxdhAcceptKeysInput ofSignalPqxdhHdr acceptInput opkOkSkBytes?
    rw [hopkEq]
    simp only [hmOpk, mkPathAHdr,
      hikBSk_eq, hikBPk_eq, hspkBSk_eq, hspkBPk_eq, hkpubU8_eq, hkprivU8_eq]
  | some j =>
    have hpkGet : getPreKey cliIo.rd F StoresGhost.opened.oneTime j = .ok wOpk :=
      (cliPk_getRel_ok_iff cliIo.rd F cliWrOk opkWord _ _ _ _
        StoresGhost.opened.oneTime j wOpk).mp hopkOk.1
    obtain ⟨sk, hpkR, hskV⟩ := oneTime_canonical_of_preKeysWf hdecOk.preKeysWf hpkGet
    obtain ⟨rawPriv, _, _, hrawEq, hskBytesEq⟩ := hopkBytes
    have hraw_sk : rawPriv = sk.toList := by
      rw [hpkR] at hrawEq
      exact hrawEq.symm
    have hopkSkU8 :
        toU8 opkSkBytes = E2E.vecU8 (keyPairOf W.C sk).privateKey.bytes := by
      rw [hskBytesEq, hraw_sk, clampBv8List_vec32_eq, ← toU8_vecToList_eq_vecU8]
      rfl
    refine ⟨{ spkId := m.spkId, spkPriv := k_spk.priv, kpkId := m.kpkId,
              kpkPub := k_kyb.pub, kpkSec := k_kyb.sec, opk := some (j, sk) },
      pkStoreKeys_eq_some_some_opk hspkGet hkpkGet hspkV hkpubV hksecV hmOpk hpkGet hskV,
      hspkPub_eq, hspkPriv_eq, fun reg => ?_⟩
    unfold mkP2AcceptKeysInput ofSignalPqxdhAcceptKeysInput ofSignalPqxdhHdr acceptInput opkOkSkBytes?
    rw [hopkEq]
    dsimp only []
    rw [hopkSkU8]
    simp only [hmOpk, mkPathAHdr, ite_true,
      hikBSk_eq, hikBPk_eq, hspkBSk_eq, hspkBPk_eq, hkpubU8_eq, hkprivU8_eq]

/-- Under successful SPK, KPK, OPK, and identity-keypair loads, `pkStoreKeys F m = some k` and
`mkP2AcceptKeysInput` equals `ofSignalPqxdhAcceptKeysInput (acceptInput...)`. -/
theorem pathA_acceptInput_agree {W : CliHooks} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {b : BitVec 64} {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} {opkWord : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)}
    {kp : IdentityKeyPair} {ikBSk ikBPk : SignalPqxdh.Bytes}
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hspkRel : (cliPollSpkKit E2E.HooksE.A0 b F m.spkId σ).getRel
      StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKit E2E.HooksE.A0 b F m.kpkId m.spkId pm.baseKey σ).getRel
      StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKit E2E.HooksE.A0 b F opkWord σ)
      StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hikBSk : ikBSk = E2E.vecU8 kp.privateKey.bytes)
    (hikBPk : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes) :
    ∃ k : ResponderPreKeySecrets,
      pkStoreKeys F m = some k ∧
      spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList ∧
      spkPrivBytes = k.spkPriv.toList ∧
      (∀ reg : BitVec 32,
        mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes =
        ofSignalPqxdhAcceptKeysInput
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)) :=
  pathA_acceptInput_agree_ext hdecOk hspkRel hspkPubEq hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq
    hopkOk hopkBytes hkp hikBSk hikBPk

/-- `acceptKeys = none` implies `decPkDef = some none` regardless of `regId` store state. -/
theorem decPkDef_pathA_accept_none_anyReg (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {m : PreKeyMessageFields} {i : SignalMessage} {k : ResponderPreKeySecrets} {kp : IdentityKeyPair}
    (hload : Slots.loadRec Scope F peer = .ok none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hpm : pkToE? pm = some m)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hacc : ∀ reg : BitVec 32,
      SignalPqxdh.Model.acceptKeys (modelPrims X W)
        (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = none) :
    decPkDef X W Scope F peer me pm coins = some none := by
  cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
  | error e =>
    cases e
    exact decPkDef_pathA_lookup_err X W Scope F peer me pm coins
      hload rfl htrust hpm (Or.inr (Or.inr hreg))
  | ok reg =>
    exact decPkDef_pathA_accept_none X W Scope F peer me pm coins
      hload rfl htrust hpm hi hk hkp hreg (hacc reg)

private theorem drKey_pqrKey_length_of_acceptKeys {P : Primitives}
    (hWF : StructuralPrims P) {inp : AcceptKeysInput} {dk : DRKey}
    (h : Model.acceptKeys P inp = some dk) :
    dk.pqrKey.length = 32 := by
  unfold Model.acceptKeys at h
  simp only [«guard», bind, Option.bind] at h
  repeat ((try dsimp only at h); first | contradiction | (split at h))
  all_goals repeat ((try dsimp only at h); first | contradiction | (split at h))
  all_goals
    injection h with hdk
    subst hdk
    rw [hWF.hkdfDerive96_eq_ref]
    simp [hkdfDerive96Ref, hkdfExpand96Ref, hmacSha256Ref_length]

private theorem bytesToBv8_eq_ofU8_list : ∀ bs : SignalPqxdh.Bytes, bytesToBv8 bs = E2E.ofU8 bs
  | [] => rfl
  | b :: bs => by
    simp only [bytesToBv8, E2E.ofU8, List.map_cons, List.cons.injEq]
    exact ⟨by simp, bytesToBv8_eq_ofU8_list bs⟩

private theorem shift8_or_extractLsb'_zero (x : BitVec 256) (b : BitVec 8) :
    ((x <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  bv_bits

private theorem shift8_or_extractLsb'_succ (x : BitVec 256) (b : BitVec 8) (j : Nat)
    (hj : j < 31) :
    ((x <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      x.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hb_ge : b.getLsbD (8 * (j + 1) + k) = false :=
    BitVec.getLsbD_of_ge b _ (by omega)
  have h1 : decide (8 * (j + 1) + k < 256) = true := decide_eq_true (by omega)
  have h2 : decide (8 * (j + 1) + k < 8) = false := decide_eq_false (by omega)
  have h3 : 8 * (j + 1) + k - 8 = 8 * j + k := by omega
  simp [hk, hb_ge, h1, h2, h3]

private theorem foldr_shift8_extractLsb' :
    ∀ (bs : List (BitVec 8)) (j : Nat) (hj : j < bs.length),
      8 * bs.length ≤ 256 →
      (bs.foldr (fun b (acc : BitVec 256) => (acc <<< 8) ||| b.zeroExtend 256) 0#256).extractLsb'
        (8 * j) 8 = bs[j]
  | [], j, hj, _ => by simp at hj
  | b :: bs, 0, _, _ => by
    simp only [List.foldr_cons, Nat.mul_zero, List.getElem_cons_zero]
    exact shift8_or_extractLsb'_zero _ b
  | b :: bs, j + 1, hj, hbound => by
    simp only [List.foldr_cons, List.getElem_cons_succ]
    simp only [List.length_cons] at hj hbound
    rw [shift8_or_extractLsb'_succ _ b j (by omega)]
    exact foldr_shift8_extractLsb' bs j (Nat.lt_of_succ_lt_succ hj) (by omega)

private theorem keyToBytes32_bytesToKey32_of_len32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    HMAC.keyToBytes32 (HKDF.bytesToKey32 bs) = bs := by
  apply List.ext_getElem
  · simp [HMAC.keyToBytes32, h]
  · intro j hj1 hj2
    simp only [HMAC.keyToBytes32, List.getElem_ofFn, HKDF.bytesToKey32]
    exact foldr_shift8_extractLsb' bs j hj2 (by omega)

private theorem pubKey_ext {a b : PublicKey} (h : a.bytes.toList = b.bytes.toList) : a = b := by
  cases a; cases b; congr; exact Subtype.ext h

private theorem privKey_ext {a b : PrivateKey} (h : a.bytes.toList = b.bytes.toList) : a = b := by
  cases a; cases b; congr; exact Subtype.ext h

private theorem idKey_ext {a b : IdentityKey}
    (h : a.publicKey.bytes.toList = b.publicKey.bytes.toList) : a = b := by
  cases a; cases b; congr; exact pubKey_ext h

private theorem keyPair_ext {a b : KeyPair}
    (hpub : a.publicKey.bytes.toList = b.publicKey.bytes.toList)
    (hpriv : a.privateKey.bytes.toList = b.privateKey.bytes.toList) : a = b := by
  cases a; cases b
  simp only [KeyPair.mk.injEq]
  exact ⟨pubKey_ext hpub, privKey_ext hpriv⟩

/-- `p2BobInitSessionV1` on `ofSignalPqxdhAcceptKeysInput (acceptInput...)` and
`initialStateValue W.C.F (p2BobSpqrParams drKey.pqrKey)` equals `pathAInitState` (`PEParams`
version). -/
theorem p2BobInitSessionV1_eq_pathAInitState_ext {P : Primitives} (hWF : StructuralPrims P)
    (W : PEParams)
    (kp : IdentityKeyPair) (reg : BitVec 32) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (drKey : DRKey) (dk0 : SignalPqxdh.DRKey)
    (ikBPk : SignalPqxdh.Bytes) (spkPubBytes : List (BitVec 8))
    (inp : AcceptKeysInput)
    (hik : ikBPk.length = 32) (hrem : inp.hdr.ikAPk.length = 32)
    (hspk_pub : (toU8 spkPubBytes).length = 32)
    (hspk_priv : (bytesToBv8 inp.spkBSk).length = 32)
    (hacc : Model.acceptKeys P inp = some drKey)
    (hdk : ofSignalPqxdhDRKey dk0 = drKey)
    (hinp : inp = ofSignalPqxdhAcceptKeysInput
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m))
    (hikBPk : bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList)
    (hspkPub : spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList) :
    p2BobInitSessionV1 ikBPk (toU8 spkPubBytes) inp drKey
      (initialStateValue W.C.F (p2BobSpqrParams drKey.pqrKey))
      hik hrem hspk_pub hspk_priv =
    pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk0 := by
  subst hdk
  have hpqrLen32 : (E2E.ofU8 dk0.pqrKey).length = 32 := by
    have hlen := drKey_pqrKey_length_of_acceptKeys hWF hacc
    simpa [ofSignalPqxdhDRKey, E2E.ofU8] using hlen
  have hpq :
      initialStateValue W.C.F (p2BobSpqrParams dk0.pqrKey) =
        (pqxdhSpqrSession W).init .b2a (HKDF.bytesToKey32 (E2E.ofU8 dk0.pqrKey)) := by
    have hk32 :
        bytesToBv8 dk0.pqrKey =
          HMAC.keyToBytes32 (HKDF.bytesToKey32 (E2E.ofU8 dk0.pqrKey)) := by
      rw [bytesToBv8_eq_ofU8_list, keyToBytes32_bytesToKey32_of_len32 hpqrLen32]
    unfold p2BobSpqrParams pqxdhSpqrSession CryptoVerification.LibsignalSpqrV1.spqrV1Session
    rw [hk32]
    exact initialStateValue_libsignal' W.C.F W.Q.K .b2a (HKDF.bytesToKey32 (E2E.ofU8 dk0.pqrKey))
  have hrem_eq : bytesToBv8 inp.hdr.ikAPk = m.idPub.toList := by
    rw [hinp]
    exact bytesToBv8_vecU8 m.idPub
  have hspk_pub_eq :
      bytesToBv8 (toU8 spkPubBytes) = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList := by
    rw [bytesToBv8_toU8, hspkPub]
  have hspk_priv_eq :
      bytesToBv8 inp.spkBSk = (keyPairOf W.C k.spkPriv).privateKey.bytes.toList := by
    rw [hinp]
    exact bytesToBv8_vecU8 (keyPairOf W.C k.spkPriv).privateKey.bytes
  have hik_id :
      ({ publicKey := { bytes := ⟨bytesToBv8 ikBPk, by simp [bytesToBv8, hik]⟩ } } : IdentityKey) =
        { publicKey := (keyPairOf W.C kp.privateKey.bytes).publicKey } :=
    idKey_ext (by simpa using hikBPk)
  have hrem_id :
      ({ publicKey := { bytes := ⟨bytesToBv8 inp.hdr.ikAPk, by simp [bytesToBv8, hrem]⟩ } } :
        IdentityKey) = { publicKey := { bytes := m.idPub } } :=
    idKey_ext (by simpa using hrem_eq)
  have hspk_kp :
      ({ publicKey := { bytes := ⟨bytesToBv8 (toU8 spkPubBytes), by simp [bytesToBv8, hspk_pub]⟩ },
         privateKey := { bytes := ⟨bytesToBv8 inp.spkBSk, hspk_priv⟩ } } : KeyPair) =
        keyPairOf W.C k.spkPriv :=
    keyPair_ext (by simpa using hspk_pub_eq) (by simpa using hspk_priv_eq)
  unfold p2BobInitSessionV1 pathAInitState initializeRecipientSession
  dsimp only [ofSignalPqxdhDRKey]
  rw [hpq, hik_id, hrem_id, hspk_kp]
  rfl

/-- `p2BobInitSessionV1` on `ofSignalPqxdhAcceptKeysInput (acceptInput...)` and
`initialStateValue W.C.F (p2BobSpqrParams drKey.pqrKey)` equals `pathAInitState`. -/
theorem p2BobInitSessionV1_eq_pathAInitState {P : Primitives} (hWF : StructuralPrims P)
    (W : CliHooks)
    (kp : IdentityKeyPair) (reg : BitVec 32) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (drKey : DRKey) (dk0 : SignalPqxdh.DRKey)
    (ikBPk : SignalPqxdh.Bytes) (spkPubBytes : List (BitVec 8))
    (inp : AcceptKeysInput)
    (hik : ikBPk.length = 32) (hrem : inp.hdr.ikAPk.length = 32)
    (hspk_pub : (toU8 spkPubBytes).length = 32)
    (hspk_priv : (bytesToBv8 inp.spkBSk).length = 32)
    (hacc : Model.acceptKeys P inp = some drKey)
    (hdk : ofSignalPqxdhDRKey dk0 = drKey)
    (hinp : inp = ofSignalPqxdhAcceptKeysInput
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m))
    (hikBPk : bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList)
    (hspkPub : spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList) :
    p2BobInitSessionV1 ikBPk (toU8 spkPubBytes) inp drKey
      (initialStateValue W.C.F (p2BobSpqrParams drKey.pqrKey))
      hik hrem hspk_pub hspk_priv =
    pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk0 :=
  p2BobInitSessionV1_eq_pathAInitState_ext hWF ⟨W.C, W.Q⟩ kp reg k m drKey dk0 ikBPk spkPubBytes
    inp hik hrem hspk_pub hspk_priv hacc hdk hinp hikBPk hspkPub

/-- `SessionExtraRel` holds between `G_bob` from `stageP2_v1_kits` and `pathAInitSession`
(`PEParams` version). -/
theorem sessionExtraRel_pathAInitSession_ext (W : PEParams)
    (kp : IdentityKeyPair) (localRegId : BitVec 32) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk0 : SignalPqxdh.DRKey) (G_bob : SessionGhost)
    (hpend : G_bob.pending = none)
    (hkyb : G_bob.kyber = none)
    (halice : G_bob.alice.bytes = bytesToBv8 (Model.encodeEC (mkPathAHdr m).ekAPk))
    (hregs : G_bob.regIds = unpack32 m.regId ++ unpack32 localRegId) :
    SessionExtraRel G_bob
      (pathAInitSession W ⟨kp.privateKey.bytes, localRegId⟩ k m dk0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PendingRel, hpend, pathAInitSession]
  · simp [KyberRel, hkyb, pathAInitSession]
  · rw [halice]
    dsimp only [mkPathAHdr, pathAInitSession, djbKey]
    exact bytesToBv8_encodeEC_vecU8 m.baseKey
  · rw [hregs]
    have htake : (unpack32 m.regId ++ unpack32 localRegId).take 4 = unpack32 m.regId := by
      simp [unpack32]
    rw [htake, pathAInitSession,
        ← CryptoVerification.E2E.Record.Serialization.SessionLenAux.leBytes_4_eq_unpack32]
  · rw [hregs]
    have hdrop : ((unpack32 m.regId ++ unpack32 localRegId).drop 4).take 4 =
        unpack32 localRegId := by
      simp [unpack32]
    rw [hdrop, pathAInitSession,
        ← CryptoVerification.E2E.Record.Serialization.SessionLenAux.leBytes_4_eq_unpack32]

/-- `SessionExtraRel` holds between `G_bob` from `stageP2_v1_kits` and `pathAInitSession`. -/
theorem sessionExtraRel_pathAInitSession (W : CliHooks)
    (kp : IdentityKeyPair) (localRegId : BitVec 32) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk0 : SignalPqxdh.DRKey) (G_bob : SessionGhost)
    (hpend : G_bob.pending = none)
    (hkyb : G_bob.kyber = none)
    (halice : G_bob.alice.bytes = bytesToBv8 (Model.encodeEC (mkPathAHdr m).ekAPk))
    (hregs : G_bob.regIds = unpack32 m.regId ++ unpack32 localRegId) :
    SessionExtraRel G_bob
      (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0) :=
  sessionExtraRel_pathAInitSession_ext ⟨W.C, W.Q⟩ kp localRegId k m dk0 G_bob
    hpend hkyb halice hregs

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
