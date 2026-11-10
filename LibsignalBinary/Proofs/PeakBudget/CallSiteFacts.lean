/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Hops
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model

/-!
# Call-site predicates and wire / address length bounds (`CallSiteFacts`)

Defines call-site predicates (`EncCallSite`, `DecSigCallSite`, `InitCallSite`, `DecPkCallSite`) for
`signal_session::run` and derives value-level length bounds: parsed `ProtocolAddress` names have
length `≤ 40`, and `SignalMessage.tryFrom` / `Pksm.pksmParse` fields are bounded by the outer wire
slice length.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CallSiteFacts

open Arm64 ProofLib
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession
  (ProtoSignalMessage SignalMessage macLength)
open CryptoGames.LibsignalSessionApi (KyberPayload PreKeySignalMessage ProtoPreKeySignalMessage)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeKey decodeLoop decodeVarint decodeVarintAux emptyProtoSignalMessage mergeBytes
   mergeField mergeUint32 protoSignalCodec skipBytes skipField skipGroup skipScalar)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (hyphenatedLength pniPrefix pniPrefix_word serviceIdParse signalMessageAt tryParseHyphenated
   utf8 uuidTryParse)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall addrParse cliIo coinsOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost InitGhost RunSem addrValOf cliBundleAt readBundleV runFiles
   runRel slotFrame)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm
  (decodeProto decodeProtoLoop emptyProto mergeProtoField pksmParse)

/-! ## Call-site predicates -/

/-- Facts holding at `R2`'s `signal_session_ratchet::encrypt` call site. -/
def EncCallSite (img : Obj.Image) (S : RunSem) (g : RunCall) (x : EncGhost) : Prop :=
  runRel S g.i g.a ∧
  parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
  (∃ peerV ownB meV,
    g.c = .send peerV ∧
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    addrParse uuidTryParse ownB = some meV ∧
    x.peer.val = addrValOf peerV ∧
    x.me.val = addrValOf meV ∧
    x.F = runFiles g.i ∧
    x.coins = coinsOf g.i ∧
    x.ptext = g.i.stdin ∧
    x.ptext.length < 2 ^ 32 ∧
    x.coins.length < 2 ^ 63 ∧
    S.filesOk x.F x.peer.val x.me.val ∧
    S.encOk x.F x.peer.val x.coins) ∧
  (∃ m0 R0, m0 ⊨ slotFrame A0 img x.toSlotCtx ∗ R0)

/-- Facts holding at `R3a`'s `signal_session_ratchet::decrypt_signal` call site. -/
def DecSigCallSite (img : Obj.Image) (S : RunSem) (g : RunCall) (x : DecSigGhost) : Prop :=
  runRel S g.i g.a ∧
  parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
  (∃ peerV rest ownB meV,
    g.c = .recv peerV ∧
    g.i.stdin = 2#8 :: rest ∧
    rest.length < 2 ^ 32 ∧
    SignalMessage.tryFrom protoSignalCodec rest = .ok x.msg ∧
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    addrParse uuidTryParse ownB = some meV ∧
    x.peer.val = addrValOf peerV ∧
    x.me.val = addrValOf meV ∧
    x.F = runFiles g.i ∧
    x.coins = coinsOf g.i ∧
    x.coins.length < 2 ^ 63 ∧
    S.filesOk x.F x.peer.val x.me.val) ∧
  (∃ m0 R0, m0 ⊨ (slotFrame A0 img x.toSlotCtx ∗ signalMessageAt A0 x.msgG x.msgA x.msg) ∗ R0)

/-- Facts holding at `R1c`'s `signal_session_handshake::initiate` call site. -/
def InitCallSite (img : Obj.Image) (S : RunSem) (g : RunCall) (x : InitGhost) : Prop :=
  runRel S g.i g.a ∧
  parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
  (∃ peerV dir ownB meV,
    g.c = .init peerV dir ∧
    readBundleV (runFiles g.i) dir peerV.device = some x.bundle ∧
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    addrParse uuidTryParse ownB = some meV ∧
    x.peer.val = addrValOf peerV ∧
    x.me.val = addrValOf meV ∧
    x.F = runFiles g.i ∧
    x.coins = coinsOf g.i ∧
    x.coins.length < 2 ^ 63 ∧
    x.bundle.spkSig.length = 64 ∧
    x.bundle.kpkSig.length = 64 ∧
    x.bundle.kpk.length = 1568 ∧
    S.filesOk x.F x.peer.val x.me.val ∧
    S.initOk x.F x.peer.val x.me.val) ∧
  (∃ m0 R0, m0 ⊨
    (slotFrame A0 img x.toSlotCtx ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr) ∗ R0)

/-- Facts holding at `R3b`'s `signal_session_handshake::decrypt_prekey` call site. -/
def DecPkCallSite (img : Obj.Image) (S : RunSem) (g : RunCall) (x : DecPkGhost) : Prop :=
  runRel S g.i g.a ∧
  parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
  (∃ peerV rest ownB meV,
    g.c = .recv peerV ∧
    g.i.stdin = 3#8 :: rest ∧
    rest.length < 2 ^ 32 ∧
    S.pksmParse rest = some x.msg ∧
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    addrParse uuidTryParse ownB = some meV ∧
    x.peer.val = addrValOf peerV ∧
    x.me.val = addrValOf meV ∧
    x.F = runFiles g.i ∧
    x.coins = coinsOf g.i ∧
    x.coins.length < 2 ^ 63 ∧
    S.filesOk x.F x.peer.val x.me.val ∧
    S.decPkOk x.F x.peer.val x.me.val x.msg) ∧
  (∃ m0 R0, m0 ⊨ (slotFrame A0 img x.toSlotCtx ∗ preKeyMsgAt A0 x.msgG x.msgA x.msg) ∗ R0)

/-! ## Parsed address name length bound (`≤ 40`) -/

theorem tryParseHyphenated_length_eq {u} {bs : List (BitVec 8)}
    (h : tryParseHyphenated uuidTryParse bs = some u) :
    bs.length = 36 := by
  unfold tryParseHyphenated hyphenatedLength at h
  split_ifs at h with hlen
  exact hlen

theorem serviceIdParse_length_le {sid} {bs : List (BitVec 8)}
    (h : serviceIdParse uuidTryParse bs = some sid) :
    bs.length ≤ 40 := by
  unfold serviceIdParse at h
  have hpni : pniPrefix.length = 4 := by
    rw [pniPrefix_word]
    rfl
  split_ifs at h with hp
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨u, hu, _⟩ := h
    have hdrop := tryParseHyphenated_length_eq hu
    have hpre := (List.isPrefixOf_iff_prefix.mp hp).length_le
    rw [List.length_drop, hpni] at hdrop
    rw [hpni] at hpre
    omega
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨u, hu, _⟩ := h
    have h36 := tryParseHyphenated_length_eq hu
    omega

theorem addrParse_name_length_le {bs : List (BitVec 8)} {v : AddrV}
    (h : addrParse uuidTryParse bs = some v) :
    v.name.length ≤ 40 := by
  unfold addrParse at h
  rcases hr : CryptoVerification.SignalSession.Cli.MainHops.rsplitDot bs with _ | ⟨nm, dev⟩ <;>
    rw [hr] at h
  · cases h
  · dsimp only at h
    rcases hs : serviceIdParse uuidTryParse nm with _ | sid <;> rw [hs] at h
    · cases h
    · rcases hp : CryptoVerification.SignalSession.Cli.MainHops.parseUnsigned 255 dev with _ | d <;>
        rw [hp] at h
      · cases h
      · dsimp only at h
        split_ifs at h
        injection h with hv
        rw [← hv]
        exact serviceIdParse_length_le hs

def callAddrNameLen : CallV → Nat
  | .keygen me _ => me.name.length
  | .init peer _ => peer.name.length
  | .send peer => peer.name.length
  | .recv peer => peer.name.length

theorem parseArgs_peer_name_length_le {args : List (List (BitVec 8))} {c : CallV}
    (h : parseArgs uuidTryParse args = some c) :
    callAddrNameLen c ≤ 40 := by
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩⟩
  · cases h
  · cases h
  · unfold parseArgs at h
    dsimp only at h
    split_ifs at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact addrParse_name_length_le hp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact addrParse_name_length_le hp
  · unfold parseArgs at h
    dsimp only at h
    by_cases hkg : a0 = CryptoVerification.SignalSession.Cli.utf8 "keygen"
    · simp only [hkg, ↓reduceIte] at h
      rcases ha : addrParse uuidTryParse a1 with _ | me <;> rw [ha] at h
      · cases h
      · rcases hn : CryptoVerification.SignalSession.Cli.MainHops.parseUnsigned (2 ^ 32 - 1) a2 with
          _ | n <;> rw [hn] at h
        · cases h
        · dsimp only at h
          split_ifs at h
          injection h with hc
          rw [← hc]
          exact addrParse_name_length_le ha
    · simp only [hkg, ↓reduceIte] at h
      split_ifs at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact addrParse_name_length_le hp
  · cases h

/-! ## Wire field length bounds (`SignalMessage.tryFrom` and `Pksm.pksmParse`) -/

private theorem decodeVarintAux_length_le :
    ∀ (bs : List (BitVec 8)) (i : Nat) (acc v : BitVec 64) (rest : List (BitVec 8)),
      decodeVarintAux i acc bs = some (v, rest) → rest.length ≤ bs.length
  | [], _, _, _, _, h => by cases h
  | b :: tl, i, acc, v, rest, h => by
    unfold decodeVarintAux at h
    dsimp only at h
    split_ifs at h
    · injection h with h'
      obtain ⟨_, rfl⟩ := Prod.mk.inj h'
      exact Nat.le_succ _
    · exact Nat.le_trans (decodeVarintAux_length_le tl (i + 1) _ v rest h) (Nat.le_succ _)

private theorem decodeVarint_length_le {bs rest : List (BitVec 8)} {v : BitVec 64}
    (h : decodeVarint bs = some (v, rest)) :
    rest.length ≤ bs.length :=
  decodeVarintAux_length_le bs 0 0 v rest h

private theorem decodeKey_length_le {bs rest : List (BitVec 8)} {tw : Nat × WireType}
    (h : decodeKey bs = some (tw, rest)) :
    rest.length ≤ bs.length := by
  unfold decodeKey at h
  rcases hd : decodeVarint bs with _ | ⟨key, r⟩ <;> rw [hd] at h
  · cases h
  · dsimp only at h
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · simp only [hk, ↓reduceIte] at h; cases h
    · simp only [hk, ↓reduceIte] at h
      rcases hw : WireType.ofNat? (key.toNat % 8) with _ | wt <;> rw [hw] at h
      · cases h
      · dsimp only at h
        split_ifs at h
        injection h with h'
        obtain ⟨_, rfl⟩ := Prod.mk.inj h'
        exact decodeVarint_length_le hd

private theorem skipBytes_length_le {n : Nat} {bs r : List (BitVec 8)}
    (h : skipBytes n bs = some r) :
    r.length ≤ bs.length := by
  unfold skipBytes at h
  split_ifs at h
  injection h with hr
  rw [← hr, List.length_drop]
  omega

private theorem skipScalar_length_le {wt : WireType} {bs r : List (BitVec 8)}
    (h : skipScalar wt bs = some r) :
    r.length ≤ bs.length := by
  cases wt with
  | varint =>
    unfold skipScalar at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, rest⟩, hd, rfl⟩ := h
    exact decodeVarint_length_le hd
  | thirtyTwoBit => exact skipBytes_length_le h
  | sixtyFourBit => exact skipBytes_length_le h
  | lengthDelimited =>
    unfold skipScalar at h
    rcases hd : decodeVarint bs with _ | ⟨len, rest⟩ <;> rw [hd] at h
    · cases h
    · exact Nat.le_trans (skipBytes_length_le h) (decodeVarint_length_le hd)
  | startGroup => cases h
  | endGroup => cases h

private theorem skipField_skipGroup_length_le :
    ∀ fuel : Nat,
      (∀ depth tag wt bs r, skipField fuel depth tag wt bs = some r → r.length ≤ bs.length) ∧
      (∀ depth tag bs r, skipGroup fuel depth tag bs = some r → r.length ≤ bs.length)
  | 0 => ⟨(fun _ _ _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h)⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := skipField_skipGroup_length_le fuel
    refine ⟨?_, ?_⟩
    · intro depth tag wt bs r h
      unfold skipField at h
      split_ifs at h
      cases wt with
      | endGroup => cases h
      | startGroup => exact ihG depth tag bs r h
      | varint => exact skipScalar_length_le h
      | sixtyFourBit => exact skipScalar_length_le h
      | lengthDelimited => exact skipScalar_length_le h
      | thirtyTwoBit => exact skipScalar_length_le h
    · intro depth tag bs r h
      unfold skipGroup at h
      rcases hk : decodeKey bs with _ | ⟨⟨itag, iwt⟩, rest⟩ <;> rw [hk] at h
      · cases h
      · have hrest := decodeKey_length_le hk
        cases iwt <;> dsimp only at h
        case endGroup =>
          split_ifs at h
          injection h with hr
          rwa [← hr]
        all_goals
          rcases hs : skipField fuel (depth - 1) itag _ rest with _ | rest' <;> rw [hs] at h
          · cases h
          · exact Nat.le_trans (ihG depth tag rest' r h)
              (Nat.le_trans (ihF _ _ _ rest rest' hs) hrest)

private theorem mergeBytes_lengths_le {wt : WireType} {bs v r : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, r)) :
    v.length ≤ bs.length ∧ r.length ≤ bs.length := by
  unfold mergeBytes at h
  split_ifs at h
  rcases hd : decodeVarint bs with _ | ⟨len, rest⟩ <;> rw [hd] at h
  · cases h
  · dsimp only at h
    split_ifs at h
    injection h with h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    have hrest := decodeVarint_length_le hd
    rw [List.length_take, List.length_drop]
    omega

private theorem mergeUint32_length_le {wt : WireType} {bs r : List (BitVec 8)} {v : BitVec 32}
    (h : mergeUint32 wt bs = some (v, r)) :
    r.length ≤ bs.length := by
  unfold mergeUint32 at h
  split_ifs at h
  rcases hd : decodeVarint bs with _ | ⟨val, rest⟩ <;> rw [hd] at h
  · cases h
  · injection h with h'
    obtain ⟨_, rfl⟩ := Prod.mk.inj h'
    exact decodeVarint_length_le hd

private def protoSigFieldsBounded (N : Nat) (m : ProtoSignalMessage) : Prop :=
  (∀ v, m.ciphertext = some v → v.length ≤ N) ∧
    (∀ v, m.pqRatchet = some v → v.length ≤ N)

private theorem decodeLoop_fields_le (N : Nat) :
    ∀ (fuel : Nat) (m m' : ProtoSignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ N →
      protoSigFieldsBounded N m →
      decodeLoop fuel m bs = some m' →
      protoSigFieldsBounded N m'
  | _, m, m', [], _, hm, h => by
    unfold decodeLoop at h
    injection h with hm'
    rwa [← hm']
  | 0, _, _, _ :: _, _, _, h => by cases h
  | fuel + 1, m, m', b :: tl, hbs, hm, h => by
    unfold decodeLoop at h
    rcases hk : decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, rest⟩ <;> rw [hk] at h
    · cases h
    · have hrest : rest.length ≤ N := Nat.le_trans (decodeKey_length_le hk) hbs
      dsimp only at h
      rcases hmF : mergeField m tag wt rest with _ | ⟨m1, rest1⟩ <;> rw [hmF] at h
      · cases h
      · have hstep : rest1.length ≤ N ∧ protoSigFieldsBounded N m1 := by
          unfold mergeField at hmF
          split at hmF <;> simp only [Option.map_eq_some_iff] at hmF
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, ?_, hm.2⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, hm.1, ?_⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨r, hsk, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans ((skipField_skipGroup_length_le _).1 _ _ _ _ _ hsk) hrest, hm⟩
        exact decodeLoop_fields_le N fuel m1 m' rest1 hstep.1 hstep.2 h

theorem signalMessage_tryFrom_lengths_le {rest : List (BitVec 8)} {sm : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec rest = .ok sm) :
    sm.serialized = rest ∧ sm.ciphertext.length ≤ rest.length ∧
      sm.pqRatchet.length ≤ rest.length := by
  unfold SignalMessage.tryFrom at h
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split_ifs at h
  have hsub_len : ((rest.take (rest.length - macLength)).drop 1).length ≤ rest.length := by
    rw [List.length_drop, List.length_take]
    omega
  rcases hp : protoSignalCodec.decode ((rest.take (rest.length - macLength)).drop 1) with _ | p <;>
    rw [hp] at h
  · cases h
  · dsimp only at h
    rcases hrk : p.ratchetKey with _ | rk <;> rw [hrk] at h
    · cases h
    · dsimp only at h
      rcases hpk : CryptoGames.LibsignalSession.PublicKey.deserialize rk with _ | srk <;>
        rw [hpk] at h
      · cases h
      · dsimp only at h
        rcases hcnt : p.counter with _ | cnt <;> rw [hcnt] at h
        · cases h
        · dsimp only at h
          rcases hct : p.ciphertext with _ | ct <;> rw [hct] at h
          · cases h
          · dsimp only at h
            injection h with hsm
            rw [← hsm]
            have hfb := decodeLoop_fields_le rest.length _ emptyProtoSignalMessage p _ hsub_len
              ⟨(fun _ hv => by cases hv), (fun _ hv => by cases hv)⟩ hp
            refine ⟨rfl, hfb.1 ct hct, ?_⟩
            rcases hpq : p.pqRatchet with _ | pq
            · simp
            · exact hfb.2 pq hpq

private def protoPksmFieldsBounded (N : Nat) (m : ProtoPreKeySignalMessage) : Prop :=
  (∀ v, m.message = some v → v.length ≤ N) ∧
    (∀ v, m.kyberCiphertext = some v → v.length ≤ N)

private theorem decodeProtoLoop_fields_le (N : Nat) :
    ∀ (fuel : Nat) (m m' : ProtoPreKeySignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ N →
      protoPksmFieldsBounded N m →
      decodeProtoLoop fuel m bs = some m' →
      protoPksmFieldsBounded N m'
  | _, m, m', [], _, hm, h => by
    unfold decodeProtoLoop at h
    injection h with hm'
    rwa [← hm']
  | 0, _, _, _ :: _, _, _, h => by cases h
  | fuel + 1, m, m', b :: tl, hbs, hm, h => by
    unfold decodeProtoLoop at h
    rcases hk : decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, rest⟩ <;> rw [hk] at h
    · cases h
    · have hrest : rest.length ≤ N := Nat.le_trans (decodeKey_length_le hk) hbs
      dsimp only at h
      rcases hmF : mergeProtoField m tag wt rest with _ | ⟨m1, rest1⟩ <;> rw [hmF] at h
      · cases h
      · have hstep : rest1.length ≤ N ∧ protoPksmFieldsBounded N m1 := by
          unfold mergeProtoField at hmF
          split at hmF <;> simp only [Option.map_eq_some_iff] at hmF
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, ?_, hm.2⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, hm.1, ?_⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨r, hsk, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans ((skipField_skipGroup_length_le _).1 _ _ _ _ _ hsk) hrest, hm⟩
        exact decodeProtoLoop_fields_le N fuel m1 m' rest1 hstep.1 hstep.2 h

theorem pksmParse_lengths_le {rest : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : pksmParse rest = some pm) :
    pm.serialized = rest ∧
      pm.message.serialized.length ≤ rest.length ∧
      pm.message.ciphertext.length ≤ rest.length ∧
      pm.message.pqRatchet.length ≤ rest.length ∧
      ∀ ky : KyberPayload, pm.kyberPayload = some ky → ky.ciphertext.length ≤ rest.length := by
  rcases rest with _ | ⟨vb, body⟩
  · cases h
  · unfold pksmParse at h
    dsimp only at h
    split_ifs at h
    rcases hd : decodeProto body with _ | m <;> rw [hd] at h
    · cases h
    · dsimp only at h
      rcases hbk : m.baseKey with _ | bk <;> rw [hbk] at h
      · cases h
      · rcases hik : m.identityKey with _ | ik <;> rw [hik] at h
        · cases h
        · rcases hmsg : m.message with _ | msg <;> rw [hmsg] at h
          · cases h
          · rcases hsid : m.signedPreKeyId with _ | sid <;> rw [hsid] at h
            · cases h
            · dsimp only at h
              split_ifs at h
              rcases hpk1 : CryptoGames.LibsignalSession.PublicKey.deserialize bk with _ | bKey <;>
                rw [hpk1] at h
              · cases h
              · rcases hpk2 : CryptoGames.LibsignalSession.PublicKey.deserialize ik with
                  _ | iKey <;> rw [hpk2] at h
                · cases h
                · rcases hsm : SignalMessage.tryFrom protoSignalCodec msg with _ | inner <;>
                    rw [hsm] at h
                  · cases h
                  · dsimp only at h
                    injection h with hpm
                    rw [← hpm]
                    have hbody_le : body.length ≤ (vb :: body).length := Nat.le_succ _
                    have hfb := decodeProtoLoop_fields_le (vb :: body).length body.length
                      emptyProto m body hbody_le
                      ⟨(fun _ hv => by cases hv), (fun _ hv => by cases hv)⟩ hd
                    have hmsg_le : msg.length ≤ (vb :: body).length := hfb.1 msg hmsg
                    obtain ⟨hser, hct, hpq⟩ := signalMessage_tryFrom_lengths_le hsm
                    refine ⟨rfl, hser ▸ hmsg_le, Nat.le_trans hct hmsg_le,
                      Nat.le_trans hpq hmsg_le, ?_⟩
                    intro ky hky
                    dsimp only at hky
                    rcases hkpid : m.kyberPreKeyId with _ | kpid <;>
                      rcases hkpct : m.kyberCiphertext with _ | kpct <;>
                      rw [hkpid, hkpct] at hky
                    · cases hky
                    · cases hky
                    · cases hky
                    · injection hky with hky'
                      rw [← hky']
                      exact hfb.2 kpct hkpct

/-! ## Call-site unpackers -/

theorem encCallSite_bounds {img : Obj.Image} {S : RunSem} {g : RunCall} {x : EncGhost}
    (h : EncCallSite img S g x) :
    x.peer.val.name.length ≤ 40 ∧ x.me.val.name.length ≤ 40 ∧ x.ptext.length < 2 ^ 32 := by
  obtain ⟨_, hparse, ⟨peerV, ownB, meV, hc, _, hme, hpeer_eq, hme_eq, _, _, _, hpt, _, _, _⟩, _⟩ := h
  have hp := parseArgs_peer_name_length_le hparse
  rw [hc] at hp
  have hm := addrParse_name_length_le hme
  rw [hpeer_eq, hme_eq]
  exact ⟨hp, hm, hpt⟩

theorem decSigCallSite_bounds {img : Obj.Image} {S : RunSem} {g : RunCall} {x : DecSigGhost}
    (h : DecSigCallSite img S g x) :
    x.peer.val.name.length ≤ 40 ∧ x.me.val.name.length ≤ 40 ∧
      x.msg.serialized.length < 2 ^ 32 ∧
      x.msg.ciphertext.length < 2 ^ 32 ∧
      x.msg.pqRatchet.length < 2 ^ 32 := by
  obtain ⟨_, hparse, ⟨peerV, rest, ownB, meV, hc, _, hrest, htry, _, hme,
    hpeer_eq, hme_eq, _, _, _, _⟩, _⟩ := h
  have hp := parseArgs_peer_name_length_le hparse
  rw [hc] at hp
  have hm := addrParse_name_length_le hme
  obtain ⟨hser, hct, hpq⟩ := signalMessage_tryFrom_lengths_le htry
  rw [hpeer_eq, hme_eq, hser]
  exact ⟨hp, hm, hrest, Nat.lt_of_le_of_lt hct hrest, Nat.lt_of_le_of_lt hpq hrest⟩

theorem initCallSite_bounds {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (h : InitCallSite img S g x) :
    x.peer.val.name.length ≤ 40 ∧ x.me.val.name.length ≤ 40 := by
  obtain ⟨_, hparse, ⟨peerV, dir, ownB, meV, hc, _, _, hme, hpeer_eq, hme_eq, _, _, _, _, _, _, _, _⟩,
    _⟩ := h
  have hp := parseArgs_peer_name_length_le hparse
  rw [hc] at hp
  have hm := addrParse_name_length_le hme
  rw [hpeer_eq, hme_eq]
  exact ⟨hp, hm⟩

theorem decPkCallSite_bounds {img : Obj.Image} {S : RunSem} {g : RunCall} {x : DecPkGhost}
    (h : DecPkCallSite img S g x) (hpksm : S.pksmParse = pksmParse) :
    x.peer.val.name.length ≤ 40 ∧ x.me.val.name.length ≤ 40 ∧
      x.msg.serialized.length < 2 ^ 32 ∧
      x.msg.message.serialized.length < 2 ^ 32 ∧
      x.msg.message.ciphertext.length < 2 ^ 32 ∧
      x.msg.message.pqRatchet.length < 2 ^ 32 ∧
      ∀ ky, x.msg.kyberPayload = some ky → ky.ciphertext.length < 2 ^ 32 := by
  obtain ⟨_, hparse, ⟨peerV, rest, ownB, meV, hc, _, hrest, htry, _, hme,
    hpeer_eq, hme_eq, _, _, _, _, _⟩, _⟩ := h
  rw [hpksm] at htry
  have hp := parseArgs_peer_name_length_le hparse
  rw [hc] at hp
  have hm := addrParse_name_length_le hme
  obtain ⟨hser, hmser, hmct, hmpq, hky⟩ := pksmParse_lengths_le htry
  rw [hpeer_eq, hme_eq, hser]
  exact ⟨hp, hm, hrest,
    Nat.lt_of_le_of_lt hmser hrest,
    Nat.lt_of_le_of_lt hmct hrest,
    Nat.lt_of_le_of_lt hmpq hrest,
    fun ky h => Nat.lt_of_le_of_lt (hky ky h) hrest⟩

end LibsignalBinary.Proofs.PeakBudget.CallSiteFacts
