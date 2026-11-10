/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P4 Spatial and Record-Length Bridges

Proves the `< 2 ^ 32` serialized 2-session record length bound `pathC_recPrev1Ok_of_tryDecrypt`,
repacks the `Prev1` session-store kit and remaining five CLI store kits into `storesAt`, and proves
the `StageP3Prev1` → `StageP4Prev1` → `dpPollSpecState.post` spatial bridges.
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

/-! ## 1. Canonicality & 32-Bit Record-Length Bound (`pathC_recPrev1Ok_of_tryDecrypt`) -/

theorem canonSession_of_sessionStateAt_extraRel {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {Rest : SepProp} {m : Memory}
    (hex : SessionExtraRel G s)
    (hm : m ⊨ sessionStateAt A ss G s.state ∗ Rest) :
    E2E.Record.Serialization.CanonSession G s := by
  have hm' : m ⊨ sessionStateReprAt A ss G s ∗ Rest := by
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hm
    unfold sessionStateReprAt
    exact Entails.pure_right hex (Entails.refl _)
  exact E2E.InMem.SessionStoreImpl.canonSession_of_satisfies_sessionAt A ss G s m
    (ProofLib.Satisfies.of_sep_left hm')

private theorem spqrV1Init_length_lt_4096 (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    (CryptoVerification.LibsignalSpqrV1.spqrV1Init F K dir k).length < 4096 := by
  unfold CryptoVerification.LibsignalSpqrV1.spqrV1Init
    CryptoVerification.LibsignalSpqrV1.spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [CryptoVerification.LibsignalSpqrV1.initialState,
      CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams] at hst
    rcases hi : CryptoVerification.LibsignalSpqrV1.initInner
        (CryptoVerification.LibsignalSpqrV1.spqrDeps F K)
        CryptoVerification.LibsignalSpqrV1.Version.v1
        (CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection dir)
        (CryptoGames.HMAC.keyToBytes32 k) with p | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst
      subst hst'
      have hin := CryptoVerification.SpqrV1.Top.StateSize.initInner_spqrDeps_raw_le hi
      have hk : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
        simp [CryptoGames.HMAC.keyToBytes32]
      refine Nat.lt_of_le_of_lt
        (CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState _) ?_
      simp only [CryptoVerification.SpqrV1.Top.StateSize.rawPqState,
        CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_none,
        CryptoVerification.SpqrV1.Top.StateSize.rawVN, hk]
      omega
  · decide

set_option maxHeartbeats 800000 in
theorem pathC_recPrev1Ok_of_tryDecrypt {A : RustAlloc} {b : BitVec 64} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {σ : DpKitStk}
    {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {s_old : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {G' : SessionGhost} {ss : BitVec 64} {Rest : SepProp} {mem : Memory}
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hex' : SessionExtraRel G'
      { pathAInitSession W ⟨kp.privateKey.bytes, reg⟩ k m dk with
        state := (genP3S5Model W.C W.Q.K peer me pm.message coins
          (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
        pendingPreKey := none
        pendingKyberPreKey := none })
    (hmem : mem ⊨ sessionStateAt A ss G'
      (genP3S5Model W.C W.Q.K peer me pm.message coins
        (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗ Rest) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    (cliPollStorePrev1Ops (A := A) (b := b) (F0 := F) (peer := peer) (σ := σ)).RecPrev1Ok
      G' ses' (E2E.Record.encSession (Over.clearPending s_old)) := by
  intro meE st' ses'
  change E2E.Record.Serialization.CanonSession G' ses' ∧
    (Over.encodeRecordPrev1 ses' (E2E.Record.encSession (Over.clearPending s_old))).length < 2 ^ 32
  have hd0 := hd.toDecPkOk₀_emptyScope
  let st0 := pathAInitState W meE k m dk
  refine ⟨canonSession_of_sessionStateAt_extraRel hex' hmem, ?_⟩
  have hok_pair : genP3S5Model W.C W.Q.K peer me pm.message coins st0 = (.ok pt, st') := by
    rcases hg : genP3S5Model W.C W.Q.K peer me pm.message coins st0 with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st', st0]; rw [hg]
    subst hr2
    rfl
  have htry : SessionState.tryDecryptFromRecord W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) st0 = (.ok pt, st') := by
    change SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) _ _ _ _ _ = _
    rw [tryDecryptFromRecord_preKey_ver_eq hd0 hver, hok_pair]
  have hIn0 := (pathAInitSession_scopeIn W meE k m dk).1
  obtain ⟨⟨hInP0, _hPq0, _hRep0⟩, ses₀, hCur₀, ⟨hRC0, _, _, _⟩⟩ := hIn0
  injection hCur₀ with hses₀; subst hses₀
  obtain ⟨hSeeds0, _, _⟩ := hInP0 (pathAInitSession W meE k m dk) rfl
  obtain ⟨_hSeeds', _hRC', _, _, key, hRecv⟩ :=
    CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) st0 st' pt hSeeds0 hRC0 htry
  have hVal0 : CryptoVerification.SpqrV1.Top.StateSize.ValidState st0.pqRatchetState :=
    (spqrV1Init_pqInV1 W.C.F W.Q.K .b2a (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))).1
  have hLen0 : st0.pqRatchetState.length < 4096 :=
    spqrV1Init_length_lt_4096 W.C.F W.Q.K .b2a (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  have hPqGrow :=
    (CryptoVerification.SpqrV1.Top.StateSize.spqrV1_recv_validState_length_le
      W.C.F W.Q.K st0.pqRatchetState pm.message.pqRatchet st'.pqRatchetState key
      hVal0 (by omega) hRecv).2
  obtain ⟨hKit', _⟩ := pathA_recOk_of_tryDecrypt hd0 hver hok
  have hb_strip : E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq ses')⟩ := by
    apply E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    rcases hKit' with ⟨⟨hin, _hpq, hrepr⟩, s1, hs1, hss⟩
    injection hs1 with hs1_eq; subst hs1_eq
    refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq ses', rfl, ?_⟩
    · intro s2 hs2; injection hs2 with hs2_eq; subst hs2_eq
      have hin0 := hin ses' rfl
      exact ⟨hin0.1, hin0.2.1, fun k1 hk1 => by simp [ses', Slots.PqValid.stripPq] at hk1⟩
    · intro s2 hs2; injection hs2 with hs2_eq; subst hs2_eq; rfl
    · intro s2 hs2; injection hs2 with hs2_eq; subst hs2_eq
      obtain ⟨hr1, hr2, hwf, hr4⟩ := hrepr ses' rfl
      exact ⟨hr1, hr2, hwf, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [ses', Slots.PqValid.stripPq] at hp,
        fun k1 hk1 => by simp [ses', Slots.PqValid.stripPq] at hk1, hss.2.2.2⟩
  have h21 :
      (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq ses')⟩).length < 2 ^ 21 :=
    E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge :
      (E2E.Record.encSession (Slots.PqValid.stripPq ses')).length ≤
        (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq ses')⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_ge' 1 (E2E.Record.encSession (Slots.PqValid.stripPq ses'))
  have heq :
      (E2E.Record.encSession ses').length =
        (E2E.Record.encSession (Slots.PqValid.stripPq ses')).length +
          (E2E.Record.bytesField 15 ses'.state.pqRatchetState).length := by
    simp only [E2E.Record.encSession, Slots.PqValid.stripPq,
      show (E2E.Record.bytesField 15 []).length = 0 from rfl,
      List.length_append]
    omega
  have hb15 :
      (E2E.Record.bytesField 15 ses'.state.pqRatchetState).length ≤
        ses'.state.pqRatchetState.length + 20 :=
    E2E.RecordX.bytesField_length_le' 15 ses'.state.pqRatchetState
  have hlf1 :
      (E2E.Record.lenField 1 (E2E.Record.encSession ses')).length ≤
        (E2E.Record.encSession ses').length + 20 :=
    E2E.RecordX.lenField_length_le' 1 (E2E.Record.encSession ses')
  have hlf2 := Over.lenField2_clearPending_length_lt hs_old
  have hst'_len : ses'.state.pqRatchetState.length = st'.pqRatchetState.length := rfl
  unfold Over.encodeRecordPrev1 E2E.Record.encodeRecord E2E.Record.msgField
  dsimp only [Option.map_some]
  rw [List.length_append]
  omega

/-! ## 2. Spatial Bridges (`StageP3Prev1` Ok → `stageP4Prev1Pre` → `dpPollSpecState.post`) -/

private theorem add_0x78_0x28 (a : BitVec 64) : (a + 0x78#64) + 0x28#64 = a + 0xa0#64 := by
  rw [BitVec.add_assoc]; rfl

theorem cliPollPrev1StoresKitsAt_entails_storesAt {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost) (pid spkId kpkId : BitVec 32) (kbk : PublicKey)
    (σ : DpKitStk) (ptr : BitVec 64) (g : StoresGhost) :
    (cliPollSessPrev1Kit A b F0 peer σ).storeAt (ptr + 0xf0#64) g.sessions ∗
    (cliPollIdKit A b F0 peer σ).identityAt ptr g.identity ∗
    (cliPollPkKit A b F0 pid σ).storeAt (ptr + 0xc8#64) g.oneTime ∗
    (cliPollSpkKit A b F0 spkId σ).storeAt (ptr + 0x50#64) g.signed ∗
    (cliPollKpkKit A b F0 kpkId spkId kbk σ).storeAt (ptr + 0x78#64) g.kyber ∗
    dirAt A (ptr + 0x118#64) g.pub ⊢
    storesAt A ptr g := by
  unfold storesAt
  dsimp only [cliPollSessPrev1Kit, cliSessPrev1StoreAt, cliPollIdKit, cliPollPkKit, cliPollSpkKit,
    cliPollKpkKit, cliIdStoreSpecFull, cliPreKeyStoreSpec, cliSignedPreKeyStoreSpec,
    cliKpkStoreSpecFull, cliIdStoreAtFull, cliIdStoreAt, cliPkStoreAt,
    cliSpkStoreAt, cliKpkStoreAtFull]
  rw [add_0x78_0x28 ptr]
  have drop1 (P : Prop) (Q : SepProp) : ⌜P⌝ ∗ Q ⊢ Q := Entails.pure_left fun _ => Entails.refl _
  have drop2 (P1 P2 : Prop) (Q : SepProp) : ⌜P1⌝ ∗ (⌜P2⌝ ∗ Q) ⊢ Q :=
    Entails.pure_left fun _ => drop1 P2 Q
  refine Entails.trans
    (sepConj_mono (drop1 _ _)
      (sepConj_mono (drop2 _ _ _)
        (sepConj_mono (drop1 _ _)
          (sepConj_mono (drop1 _ _)
            (sepConj_mono (drop1 _ _) (Entails.refl _)))))) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP3MidPathC_entails_p4_ext {A : RustAlloc} (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s2 s' : State)
    (rngPtr initErrsPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32)
    (enc pt : List (BitVec 8))
    (G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let prev1Kit := cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F spkId σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ
    (Over.stageP3DispatchOkMidPrev1 A img.base s0 s2 y.fut y.out initErrsPtr
        prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
      genP3S5PostFrame A img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      Over.overScratch s2.sp) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    Over.stageP4Prev1Pre img prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      prevCap prevPtr ptCap ptPtr initErrsPtr
      opkId? kpkId spkId 0#8 pt enc
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      G' st' ∗
    pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId preKeyMsgRem coinsPost := by
  dsimp only
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left
          (cliPollSessKit_storeAt_entails_prev1 (A := A) (b := img.base)
            (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer) (σ := cliKitStk B)
            (y.g.stores + 0xf0#64) StoresGhost.opened.sessions)))))))) ?_
  unfold Over.stageP3DispatchOkMidPrev1 genP3S5PostFrame stageP3CoroFrameAt stageP3OverStackFrameAt
    Over.stageP4Prev1Pre Over.stageP4Prev1RawPre Over.stageP4Prev1Shared pathAP4RemAt
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hlog :
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) =
      logOff img := rfl
  have hstk1 :
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack =
      stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hstk2 :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        stackAt sp rootStack =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hstk3 := stackAt_subStack_sub_eq sp B
    (cliPollStageP4Stack_le_subStack A img.base y.g.F Slots.scopeKit y.g.peer
      pid kpkId spkId y.g.msg.baseKey B)
    hsp_sub
  have hstk_swap :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) := by
    rw [hstk1, hstk2, hstk3]
  have hvt_eq :
      (cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ).ss_vt =
      (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).ss_vt := rfl
  have hcall_eq :
      stageP4CallStack
        (cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ)
        (cliPollIdKit A img.base y.g.F y.g.peer σ)
        (cliPollPkKit A img.base y.g.F pid σ)
        (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack
        (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKit A img.base y.g.F y.g.peer σ)
        (cliPollPkKit A img.base y.g.F pid σ)
        (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs2_sp, hs'_sp, hlog, hvt_eq, hcall_eq,
      overScratch_eq_sp538_spHighGaps sp,
      coro_2ac_20_eq_8_12 y.fut,
      coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr,
      sp_2b0_192_split sp, sp_3e0_344_eq_48_296 sp,
      sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit A img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit A img y.g.F pid σ,
      kyberVt_eq_cliPollKpkKit A img y.g.F kpkId spkId y.g.msg.baseKey σ]
  apply Entails.of_eq
  have hswap_all : ∀ (Rest : SepProp),
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack)) ∗ Rest =
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗ Rest := by
    intro Rest; rw [hstk_swap]
  trans ((memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack)) ∗
    (((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗
      ((y.fut + 0x90#64) ↦₆₄ (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).ss_vt) ∗
      ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗
      ((y.fut + 0xa0#64) ↦₆₄ (cliPollIdKit A img.base y.g.F y.g.peer σ).id_vt) ∗
      ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗
      ((y.fut + 0xb0#64) ↦₆₄ (cliPollPkKit A img.base y.g.F pid σ).pk_vt) ∗
      ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗
      ((y.fut + 0xd0#64) ↦₆₄ (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt) ∗
      prevVecAt A (y.fut + 0xe0#64) prevCap prevPtr [enc] ∗
      ((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId) ∗
      memRegion (y.fut + 0x2c8#64) 16 ∗ ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x250#64) 20 ∗
      ((sp + 0x278#64) ↦₆₄ ptCap) ∗ ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      logOff img ∗ A.pool ∗
      sessionStateAt A (y.fut + 0xf8#64) G' st' ∗
      memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
      (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion y.out 48 ∗
      (cliPollIdKit A img.base y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      (cliPollPkKit A img.base y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).ss_vt
        y.g.stores (cliPollIdKit A img.base y.g.F y.g.peer σ).id_vt
        (y.g.stores + 0xc8#64) (cliPollPkKit A img.base y.g.F pid σ).pk_vt
        (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt
        rngPtr ∗
      coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (signedVt img) rngPtr ∗
      memRegion (y.fut + 0x250#64) 48 ∗ memRegion (y.fut + 0x2d8#64) 184 ∗
      memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
      memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
      memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
      coroPostP2UnusedAt y.fut ∗ (sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗
      memRegion (sp + 0x930#64) 48 ∗ ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗ spLowGapsAt sp ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((sp + 0xb8#64) ↦₃₂ msgVer) ∗ memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x264#64) 12 ∗
      ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗ sp2b0GapsAt sp ∗
      memRegion (sp + 0x394#64) 12 ∗ ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0x3a8#64) 4 ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      memRegion (sp + 0x3ad#64) 27 ∗ memRegion (sp + 0x410#64) 296 ∗
      memRegion (sp + 0x538#64) 24 ∗ memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
      preKeyMsgRem ∗ TokenInit img ∗ coinsPost ∗
      (cliPollSpkKit A img.base y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub))
  · sep_frame
  · rw [hswap_all]; sep_frame

theorem stageP3MidPathC_entails_p4 (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s2 s' : State)
    (rngPtr initErrsPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32)
    (enc pt : List (BitVec 8))
    (G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
    let prev1Kit := cliPollSessPrev1Kit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
    let spkKit := cliPollSpkKit E2E.HooksE.A0 img.base y.g.F spkId σ
    let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kpkId spkId y.g.msg.baseKey σ
    (Over.stageP3DispatchOkMidPrev1 E2E.HooksE.A0 img.base s0 s2 y.fut y.out initErrsPtr
        prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
      genP3S5PostFrame E2E.HooksE.A0 img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      Over.overScratch s2.sp) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    Over.stageP4Prev1Pre img prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      prevCap prevPtr ptCap ptPtr initErrsPtr
      opkId? kpkId spkId 0#8 pt enc
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      G' st' ∗
    pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId preKeyMsgRem coinsPost :=
  stageP3MidPathC_entails_p4_ext (A := E2E.HooksE.A0) img B y s0 s2 s'
    rngPtr initErrsPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost opkId? msgVer pid kpkId spkId enc pt G' st'
    hs2_sp hs'_sp hsp_sub

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP4PathCExit_entails_exit_ext {A : RustAlloc} (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S)) (s0 s' : State)
    (rngPtr initErrsPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (outSlot preKeyMsgRem coinsPost : SepProp) (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32) (pt : List (BitVec 8))
    (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (sstf pstf : DirGhost) (istf : IdGhost) (kstf : KyberGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout : outSlot ⊢ decResAt A y.out res ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf) (hid : g'.identity = istf) (hot : g'.oneTime = pstf)
    (hspk : g'.signed = StoresGhost.opened.signed) (hkpk : g'.kyber = kstf)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let prev1Kit := cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ
    Over.stageP4Prev1ExitAt img prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64) ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot kpkId spkId pt y.g.peer y.g.msg.identityKey
      y.g.msg.baseKey sstf istf pstf kstf ∗
    pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId preKeyMsgRem coinsPost ⊢
    decResAt A y.out res ∗ storesAt A y.g.stores g' ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ (TokenInit img ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗ stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280 := by
  dsimp only
  unfold Over.stageP4Prev1ExitAt Over.stageP4Prev1Shared pathAP4RemAt
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hvt_eq :
      (cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ).ss_vt =
      (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).ss_vt := rfl
  have hcall_eq :
      stageP4CallStack (cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ)
        (cliPollIdKit A img.base y.g.F y.g.peer σ)
        (cliPollPkKit A img.base y.g.F pid σ)
        (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKit A img.base y.g.F y.g.peer σ)
        (cliPollPkKit A img.base y.g.F pid σ)
        (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs'_sp, hvt_eq, hcall_eq]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
      stackAt sp (stageP4CallStack
        (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKit A img.base y.g.F y.g.peer σ)
        (cliPollPkKit A img.base y.g.F pid σ)
        (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4Stack_le_subStack A img.base y.g.F Slots.scopeKit y.g.peer
        pid kpkId spkId y.g.msg.baseKey B) hsp_sub).symm
  have hstores :
      cliSessPrev1StoreAt A y.g.peer (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKit A img.base y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKit A img.base y.g.F pid σ).storeAt (y.g.stores + 0xc8#64) pstf ∗
      (cliPollSpkKit A img.base y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) kstf ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt A y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollPrev1StoresKitsAt_entails_storesAt img.base y.g.F y.g.peer pid spkId kpkId
      y.g.msg.baseKey σ y.g.stores g'
  have hcopy_join :=
    (coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr).symm
  rw [← sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer σ,
      ← idVt_eq_cliPollIdKit A img y.g.F y.g.peer σ,
      ← oneTimeVt_eq_cliPollPkKit A img y.g.F pid σ,
      ← kyberVt_eq_cliPollKpkKit A img y.g.F kpkId spkId y.g.msg.baseKey σ]
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hstack := stageP4Exit_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA
    0xfffffffffffffffe#64 ptCap ptPtr (BitVec.ofNat 64 pt.length) 0#64 initErrsPtr 0#64 msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      outSlot ∗
      (cliSessPrev1StoreAt A y.g.peer (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKit A img.base y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKit A img.base y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) pstf ∗
        (cliPollSpkKit A img.base y.g.F spkId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
          (y.g.stores + 0x78#64) kstf ∗
        dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      logOff img ∗
      A.pool ∗
      (TokenInit img ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        ((((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
          ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗ ((y.fut + 0x90#64) ↦₆₄ (sessVt img)) ∗
          ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗ ((y.fut + 0xa0#64) ↦₆₄ (idVt img)) ∗
          ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗ ((y.fut + 0xb0#64) ↦₆₄ (oneTimeVt img)) ∗
          ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗ ((y.fut + 0xd0#64) ↦₆₄ (kyberVt img))) ∗
          coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (signedVt img) rngPtr) ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
          (dpClosSubStack B - stageP4CallStack
            (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKit A img.base y.g.F y.g.peer σ)
            (cliPollPkKit A img.base y.g.F pid σ)
            (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗
      ((sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗ spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x264#64) 12 ∗
        ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp + 0x278#64) ↦₆₄ ptCap) ∗
        ((sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ sp2b0GapsAt sp ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (sp + 0x3ad#64) 27 ∗
        ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
        memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame)) ?_
  rw [hcopy_join, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  have hcoro_fold :
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        memRegion (y.fut + 0x2c8#64) 200 ∗ memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗ memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗ memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗ coroPostP2UnusedAt y.fut) ⊢
      dpFutDoneAt y.fut := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  have hstack_fold := Entails.trans (sepConj_mono_left hsp0) hstack
  exact Entails.trans
    (sepConj_mono hout (sepConj_mono hstores (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hcoro_fold (sepConj_mono_right hstack_fold))))))))))
    (Entails.of_eq (by sep_frame))

theorem stageP4PathCExit_entails_exit (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S)) (s0 s' : State)
    (rngPtr initErrsPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (outSlot preKeyMsgRem coinsPost : SepProp) (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32) (pt : List (BitVec 8))
    (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (sstf pstf : DirGhost) (istf : IdGhost) (kstf : KyberGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout : outSlot ⊢ decResAt E2E.HooksE.A0 y.out res ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf) (hid : g'.identity = istf) (hot : g'.oneTime = pstf)
    (hspk : g'.signed = StoresGhost.opened.signed) (hkpk : g'.kyber = kstf)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let prev1Kit := cliPollSessPrev1Kit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
    let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kpkId spkId y.g.msg.baseKey σ
    Over.stageP4Prev1ExitAt img prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64) ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot kpkId spkId pt y.g.peer y.g.msg.identityKey
      y.g.msg.baseKey sstf istf pstf kstf ∗
    pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId preKeyMsgRem coinsPost ⊢
    decResAt E2E.HooksE.A0 y.out res ∗ storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ E2E.HooksE.A0.pool ∗ (TokenInit img ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗ stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280 :=
  stageP4PathCExit_entails_exit_ext (A := E2E.HooksE.A0) img B y s0 s'
    rngPtr initErrsPtr whisperMsgPtr ptCap ptPtr whisperG outSlot preKeyMsgRem coinsPost
    opkId? msgVer pid kpkId spkId pt res sstf pstf istf kstf g' hs'_sp hsp_sub
    hout hmsg_fold hsess hid hot hspk hkpk hpub

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
