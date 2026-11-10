/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Frames
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Cells
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Stage 4 Segment 3: `SessionState` Construction, Move to `0x460`, and `logOff` Jump (`+4848 → +5252`)

Executes `+4848 → +5252` (`+0x12f0 → +0x1484`): runs `<SessionState>::new`,
`with_receiver_chain`, `with_sender_chain`, and `set_kyber_ciphertext`, moves the `344`-byte
`SessionState` into `[fsp + 0x460, fsp + 0x5b8)` (`[fsp + 0x5b9] := 1#8`), checks `logOff = 0#64`,
and jumps via `b.lo` to `+5252`, folding `sessionStateAt A (fsp + 0x460#64) sg ss`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem vecU8_eq_header_buf (A : RustAlloc) (base : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8 A base bs =
      ∃∗ cap : BitVec 64, ∃∗ bufPtr : BitVec 64,
        (base ↦₆₄ cap) ∗
        ((base + 8#64) ↦₆₄ bufPtr) ∗
        ((base + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap bufPtr bs := by
  unfold RustHeap.vecU8
  refine congrArg sepExists (funext fun cap => congrArg sepExists (funext fun bufPtr => ?_))
  have hhdr : RustHeap.vecU8At A base cap bufPtr bs =
      RustHeap.vecHeader base cap bufPtr (BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap bufPtr bs := by
    unfold RustHeap.vecU8At vecU8Buf; ac_rfl
  rw [hhdr]
  dsimp only [RustHeap.vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem encodeBytesField_len32_pos (tag : BitVec 32) {b : List (BitVec 8)}
    (hb : b.length = 32) :
    (LibsignalSpqrV1.Proto.encodeBytesField tag b).length =
      (LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited).length + 33 := by
  cases b with
  | nil => simp at hb
  | cons _ _ =>
    have hlen : (_ :: _).length = 32 := hb
    unfold LibsignalSpqrV1.Proto.encodeBytesField LibsignalSpqrV1.Proto.encodeBytesUncond
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_append, hlen]
    have hv : (LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 32)).length = 1 := by decide
    rw [hv]

theorem spqrInitialState_pqLen_pos (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (k : BitVec 256) :
    0 < (LibsignalSpqrV1.spqrV1Init F K .a2b k).length := by
  rw [← SpqrV1.Top.InitialState.initialStateValue_libsignal F K .a2b k]
  let au := LibsignalSpqrV1.Authenticator.new F (HMAC.keyToBytes32 k) 1#64
  have hpb : (SpqrV1.Top.InitInner.initV1State F .a2b (HMAC.keyToBytes32 k)).into_pb =
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := au.rootKey, macKey := au.macKey } } }) } := rfl
  have hrk := encodeBytesField_len32_pos 1#32 (b := au.rootKey)
    (by simp [au, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked])
  have hmk := encodeBytesField_len32_pos 2#32 (b := au.macKey)
    (by simp [au, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked])
  have hak := encodeBytesField_len32_pos 1#32 (b := HMAC.keyToBytes32 k)
    (by simp [HMAC.keyToBytes32])
  simp only [LibsignalSpqrV1.libsignalSpqrParams, LibsignalSpqrV1.Direction.ofSpqrDirection,
    SpqrV1.Top.InitialState.initialStateValue, SpqrV1.Top.InitialState.initialStatePB,
    SpqrV1.Top.InitialState.initialStateVN, hpb,
    LibsignalSpqrV1.PqRatchetState.encodeRaw, LibsignalSpqrV1.PqRatchetState.Inner.encode,
    LibsignalSpqrV1.V1State.encodeRaw, LibsignalSpqrV1.V1State.InnerState.encode,
    LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw,
    LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.encodeRaw,
    LibsignalSpqrV1.ProtoAuthenticator.encodeRaw, LibsignalSpqrV1.VersionNegotiationPB.encodeRaw,
    LibsignalSpqrV1.ChainParamsPB.encodeRaw, LibsignalSpqrV1.Proto.encodeOptMessage,
    LibsignalSpqrV1.Proto.encodeMessage, LibsignalSpqrV1.Proto.encodeUint32Field,
    LibsignalSpqrV1.Proto.encodeUint64Field, List.length_append, hrk, hmk, hak]
  decide

theorem aliceSession344_split_7words_288
    (base p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck : BitVec 64)
    (pad_f4 : BitVec 32) (pad40 : List (BitVec 8))
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) :
    let bs := aliceSession344Bv8 p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck
      pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144
    (base ↦ₛ bs) =
      (base ↦₆₄ 33#64) ∗
      ((base + 8#64) ↦₆₄ p1) ∗
      ((base + 16#64) ↦₆₄ 33#64) ∗
      ((base + 24#64) ↦₆₄ 33#64) ∗
      ((base + 32#64) ↦₆₄ p2) ∗
      ((base + 40#64) ↦₆₄ 33#64) ∗
      ((base + 48#64) ↦₆₄ 32#64) ∗
      ((base + 56#64) ↦ₛ bs.drop 56) := by
  intro bs
  let pre56 : List (BitVec 8) :=
    unpack64 33#64 ++ unpack64 p1 ++ unpack64 33#64 ++
      unpack64 33#64 ++ unpack64 p2 ++ unpack64 33#64 ++ unpack64 32#64
  let rest288 : List (BitVec 8) :=
    (unpack64 p3 ++ unpack64 32#64) ++
      receiverChainVecBytes24 cb ++
      aliceMid48Bv8 p4 c5 p5 l5 ++
      senderChainBytes100 spub spriv sck 0#32 ++
      aliceTail100Bv8 pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144
  have hpre56 : pre56.length = 56 := by simp [pre56, unpack64]
  have hbs_eq : bs = pre56 ++ rest288 := by
    dsimp only [bs, aliceSession344Bv8, aliceHead144Bv8, alicePre72Bv8, pre56, rest288]
    simp only [List.append_assoc]
  have hdrop : bs.drop 56 = rest288 := by
    rw [hbs_eq]
    exact List.drop_left' hpre56
  conv => lhs; rw [hbs_eq]
  rw [pointsToBytes_append, hpre56, ← hdrop]
  dsimp only [pre56]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes, sepConj_assoc]

theorem pointsToBytes32_entails_memRegion32 (base : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 32) :
    (base ↦ₛ bs) ⊢ memRegion base 32 :=
  h ▸ pointsToBytes_entails_memRegion base bs

theorem keyAndIdx_entails_memRegion36 (base : BitVec 64) (k : BitVec 256) (idx : BitVec 32) :
    (base ↦ₛ keyToBytes32 k) ∗ ((base + 32#64) ↦₃₂ idx) ⊢ memRegion base 36 := by
  have hlen : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
  rw [ProofLib.memRegion_split' (b := base) (n := 32) (k := 4)
        (b' := base + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (hlen ▸ pointsToBytes_entails_memRegion base (keyToBytes32 k))
    (pointsTo32_entails_memRegion (base + 32#64) idx)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 2400000 in
theorem stage4_step_session_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {kp : IdentityKeyPair} {ekAPk kemCtBytes : List (BitVec 8)}
    {kemCtPtr : BitVec 64} {baseKey : PublicKey}
    {rk1 : RootKey} {ck0 pqrKey : BitVec 256}
    {sendingKeyPair : KeyPair} {ck1 : ChainKey}
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A (cliExternsWith ext))
    (hLocal : Stage4CalleesExtX img P A ext)
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    {s : State} (hctrl : S4InInitiate img ext s0 s 4848) (htr : s.trace = s0.trace)
    (hx20_in : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_in : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hbase_eq : ekAPk = baseKey.bytes.toList)
    (hclamp : Ratchet.clampScalar sendingKeyPair.privateKey.bytes = sendingKeyPair.privateKey.bytes)
    (hck1_idx : ck1.index = 0#32)
    (hkem_len : kemCtBytes.length = 1569)
    (hkem_ne : kemCtPtr ≠ 0#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let pq : List (BitVec 8) := (pqxdhSpqrSession P).init .a2b pqrKey
    let ss := stage5SessionState kp.identityKey x.bundle.idKey x.bundle.spk rk1 ck0
      sendingKeyPair ck1 pq
    SepWPp (s4ProgExt img ext)
      (s4PcExt img ext 5252) s
      (((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗
        ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
        A.live kemCtPtr 1569 1 ∗
        (kemCtPtr ↦ₛ kemCtBytes) ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 0x460#64) 0x158 ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 1904#64) 288 ∗
        ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0) ∗
        ((fsp + 2288#64) ↦₃₂ 0#32) ∗
        ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗
        ((fsp + 2368#64) ↦₃₂ 0#32) ∗
        ((fsp + 2496#64) ↦ₛ sendingKeyPair.publicKey.bytes.toList) ∗
        ((fsp + 2528#64) ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
        ((fsp + 4064#64) ↦₆₄ 0#64) ∗
        RustHeap.vecU8 A (fsp + 4072#64) pq ∗
        memRegion (fsp + 4096#64) 312 ∗
        memRegion (fsp + 5632#64) 344 ∗
        ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
        memRegion (fsp + 7264#64) 24 ∗
        logOff img ∗
        A.pool ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        Frame)
      (fun sf Pf =>
        ∃ sg : SessionGhost,
          sf.trace = s0.trace ∧
          S4InInitiate img ext s0 sf 0x1484 ∧
          sf.readReg64 (.gpr 20#5) = fsp + 0x460#64 ∧
          (sg.localIk.bytes = ss.localIdentity.serialize ∧
            (match ss.remoteIdentity with
             | none => sg.remoteIk.bytes = []
             | some ik => sg.remoteIk.bytes = ik.serialize) ∧
            sg.alice.bytes = baseKey.serialize ∧
            sg.pending = none ∧
            (∃ kg, sg.kyber = some kg ∧ kg.vec.bytes = kemCtBytes) ∧
            (∃ scg sc, sg.sender = some scg ∧ ss.senderChain = some sc ∧
              scg.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
              scg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList) ∧
            ∀ gc ∈ sg.chains.zip ss.receiverChains,
              gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []) ∧
          (Pf ⊢
            ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗
            ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
            ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
            ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
            ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
            ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
            ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
            ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
            sessionStateAt A (fsp + 0x460#64) sg ss ∗
            ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
            memRegion (fsp + 1904#64) 288 ∗
            memRegion (fsp + 2256#64) 36 ∗
            memRegion (fsp + 2336#64) 36 ∗
            memRegion (fsp + 2496#64) 32 ∗
            memRegion (fsp + 2528#64) 32 ∗
            memRegion (fsp + 4064#64) 344 ∗
            memRegion (fsp + 5632#64) 344 ∗
            memRegion (fsp + 7232#64) 32 ∗
            memRegion (fsp + 7264#64) 24 ∗
            logOff img ∗
            A.pool ∗
            stackAt fsp (stk - cliInitiateFrame) ∗
            Frame))
      Qp (initOom s0) := by
  intro fsp pq ss
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hss_def : Hide
      (ss = stage5SessionState kp.identityKey x.bundle.idKey x.bundle.spk rk1 ck0
        sendingKeyPair ck1 pq) := ⟨rfl⟩
  have hfsp_align : ∀ (st : State), st.sp = fsp → st.spAligned = true :=
    fun st hst => fsp_aligned_of_s0 hstk hspk hst hctrl.spAligned
  have hsp0 : s.sp = fsp := hctrl.sp
  have hfp0 : s.readReg64 .fp = fsp + 7312#64 := hctrl.fp.trans hfp_fsp.val
  have hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20_in
  have hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21_in
  clear hx20_in hx21_in
  clear_value fsp pq ss
  stage4_spqr_fetches img.base (cliExternsWith ext)
  stage4_post_fetches img.base (cliExternsWith ext)
  stage4_bind_entry img.base (cliExternsWith ext)
  examples_hide_fetches
  have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
  have hsnew := sub_ok_at_s4PcExt hLocal.sessionStateNew
    (2 ^ 64 - ls_rel% "<libsignal_protocol::state::session::SessionState>::new"
      "libsignal_cli_handshake::initiate")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::new"))
    cliInitiate_fnOff cliSessionStateNew_fnOff (by decide)
  have hwrc := sub_ok_at_s4PcExt hLocal.withReceiverChain
    (2 ^ 64 - ls_rel% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain"
      "libsignal_cli_handshake::initiate")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain"))
    cliInitiate_fnOff cliWithReceiverChain_fnOff (by decide)
  have hwsc := sub_ok_at_s4PcExt hLocal.withSenderChain
    (2 ^ 64 - ls_rel% "<libsignal_protocol::state::session::SessionState>::with_sender_chain"
      "libsignal_cli_handshake::initiate")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_sender_chain"))
    cliInitiate_fnOff cliWithSenderChain_fnOff (by decide)
  have hskc := sub_ok_at_s4PcExt hLocal.setKyberCiphertext
    (2 ^ 64 - ls_rel% "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"
      "libsignal_cli_handshake::initiate")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"))
    cliInitiate_fnOff cliSetKyberCiphertext_fnOff (by decide)
  have hmcpy := memcpy_ok_at_init_ext hAlloc
  let ikABytes : List UInt8 :=
    CryptoVerification.E2E.vecU8 kp.identityKey.publicKey.bytes
  let ikBBytes : List UInt8 :=
    CryptoVerification.E2E.vecU8 x.bundle.idKey.publicKey.bytes
  let rk1Bytes : List UInt8 := CryptoVerification.E2E.toU8 (keyToBytes32 rk1)
  let baseBytes : List UInt8 := CryptoVerification.E2E.vecU8 baseKey.bytes
  let rpkBBytes : List UInt8 := CryptoVerification.E2E.vecU8 x.bundle.spk.bytes
  let ck0Bytes : List UInt8 := CryptoVerification.E2E.toU8 (keyToBytes32 ck0)
  let spubBytes : List UInt8 :=
    CryptoVerification.E2E.vecU8 sendingKeyPair.publicKey.bytes
  let sprivBytes : List UInt8 :=
    CryptoVerification.E2E.vecU8 sendingKeyPair.privateKey.bytes
  let ck1Bytes : List UInt8 :=
    CryptoVerification.E2E.toU8 (keyToBytes32 ck1.key)
  have hikA_bv : bytesToBv8 ikABytes = kp.identityKey.publicKey.bytes.toList :=
    ResponderCore.bytesToBv8_vecU8 _
  have hikB_bv : bytesToBv8 ikBBytes = x.bundle.idKey.publicKey.bytes.toList :=
    ResponderCore.bytesToBv8_vecU8 _
  have hrk1_bv : bytesToBv8 rk1Bytes = keyToBytes32 rk1 :=
    ResponderCore.bytesToBv8_toU8 _
  have hbase_bv : bytesToBv8 baseBytes = ekAPk :=
    (ResponderCore.bytesToBv8_vecU8 _).trans hbase_eq.symm
  have hrpkB_bv : bytesToBv8 rpkBBytes = x.bundle.spk.bytes.toList :=
    ResponderCore.bytesToBv8_vecU8 _
  have hck0_bv : bytesToBv8 ck0Bytes = keyToBytes32 ck0 :=
    ResponderCore.bytesToBv8_toU8 _
  have hspub_bv : bytesToBv8 spubBytes = sendingKeyPair.publicKey.bytes.toList :=
    ResponderCore.bytesToBv8_vecU8 _
  have hspriv_bv : bytesToBv8 sprivBytes = sendingKeyPair.privateKey.bytes.toList :=
    ResponderCore.bytesToBv8_vecU8 _
  have hck1_bv : bytesToBv8 ck1Bytes = keyToBytes32 ck1.key :=
    ResponderCore.bytesToBv8_toU8 _
  have hpc0 : s.pc = fnStart + bv% (4848) := by
    rw [hctrl.pc, s4PcExt, hfn_entry]
  have hrun0 : s.status = .Running := hctrl.run
  have halign0 : s.spAligned = true := hfsp_align s hsp0
  have hx19_0 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl.x19
  have hvr0 : calleeSavedVRegs s = calleeSavedVRegs s0 := hctrl.vregs
  apply sepWPp_steps_post (post := fun sf Pf =>
    ∃ sg : SessionGhost,
      sf.trace = s0.trace ∧
      sf.pc = s4PcExt img ext 0x1484 ∧
      sf.status = .Running ∧
      sf.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧
      sf.readReg64 .fp = s0.sp - 0x60#64 ∧
      sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
      ImgCallInv img sf ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      sf.readReg64 (.gpr 20#5) = fsp + 0x460#64 ∧
      (sg.localIk.bytes = ss.localIdentity.serialize ∧
        (match ss.remoteIdentity with
         | none => sg.remoteIk.bytes = []
         | some ik => sg.remoteIk.bytes = ik.serialize) ∧
        sg.alice.bytes = baseKey.serialize ∧
        sg.pending = none ∧
        (∃ kg, sg.kyber = some kg ∧ kg.vec.bytes = kemCtBytes) ∧
        (∃ scg sc, sg.sender = some scg ∧ ss.senderChain = some sc ∧
          scg.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
          scg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList) ∧
        ∀ gc ∈ sg.chains.zip ss.receiverChains,
          gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []) ∧
      (Pf ⊢
        ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗
        ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        sessionStateAt A (fsp + 0x460#64) sg ss ∗
        ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        memRegion (fsp + 1904#64) 288 ∗
        memRegion (fsp + 2256#64) 36 ∗
        memRegion (fsp + 2336#64) 36 ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗
        memRegion (fsp + 4064#64) 344 ∗
        memRegion (fsp + 5632#64) 344 ∗
        memRegion (fsp + 7232#64) 32 ∗
        memRegion (fsp + 7264#64) 24 ∗
        logOff img ∗
        A.pool ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        Frame))
  {
  have hvec_pq_eq := vecU8_eq_header_buf A (fsp + 4072#64) pq
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec_pq_eq
  conv => arg 4; rw [hvec_pq_eq, cells3_eq_memRegion24 (fsp + 7264#64),
      stackAt_fsp_split hstk hstk64 fsp sessionBuildStack (by decide),
      stackAt_sessionBuild_split_sessionNew fsp]
  s4_elim_exists spqrCap; s4_elim_exists spqrBufPtr
  s4_elim_exists u7264_0; s4_elim_exists u7264_1; s4_elim_exists u7264_2
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_step_to_frozen hctrl.inv
    (mid := fnStart + bv% (2 ^ 64 - ls_rel% "<libsignal_protocol::state::session::SessionState>::new"
      "libsignal_cli_handshake::initiate"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hs1_F hs1_sym
  have h4064_fold := spqrOut_4064_to_memRegion344 fsp 0#64
    spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
  s4_fold_pre h4064_fold
  let gNew : SessionStateNewGhost :=
    { outPtr := fsp + 5632#64
      version := 4#32
      localIkPtr := fsp + 0x348#64
      localIk32 := ikABytes
      remoteIkPtr := fsp + 0x3c8#64
      remoteIk32 := ikBBytes
      rootKeyPtr := fsp + 7232#64
      rootKey32 := rk1Bytes
      baseKeyPtr := fsp + 0x388#64
      baseKey32 := baseBytes
      spqrVecPtr := fsp + 7264#64
      spqrCap := spqrCap
      spqrBufPtr := spqrBufPtr
      spqrLen := BitVec.ofNat 64 pq.length }
  conv => arg 4; rw [← hikA_bv, ← hikB_bv, ← hrk1_bv, ← hbase_bv]
  refine sepWPp_call_wpp_split hsnew gNew
    (T := ((fsp + 0x348#64) ↦ₛ bytesToBv8 ikABytes) ∗
      ((fsp + 0x3c8#64) ↦ₛ bytesToBv8 ikBBytes) ∗
      ((fsp + 7232#64) ↦ₛ bytesToBv8 rk1Bytes) ∗
      ((fsp + 0x388#64) ↦ₛ bytesToBv8 baseBytes) ∗
      ((fsp + 7264#64) ↦₆₄ spqrCap) ∗
      ((fsp + 7272#64) ↦₆₄ spqrBufPtr) ∗
      ((fsp + 7280#64) ↦₆₄ BitVec.ofNat 64 pq.length) ∗
      memRegion (fsp + 5632#64) 344 ∗
      (memRegion (fsp - 4224#64) 128 ∗ stackAt fsp allocHookStack) ∗
      A.pool)
    (F := ?_)
    hs1_F hs1_sym
    (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
    (by s4_split_frame)
    ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sm _ _ =>
      hpanic sm _ (by
        dsimp only [sessionStateNewSpec, rustPanicOnOom]
        exact panic_oom_entails_initOnPanic A img S x stk s0 _ sm _ _ (by wp_norm_goal))) ?_
  · dsimp only [sessionStateNewSpec, gNew]
    have hsp_eq := frozen_sp_eq hs1_F fsp (by wp_norm_goal)
    rw [hsp_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.pure_right
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       ResponderCore.vecU8_length _, ResponderCore.vecU8_length _,
       by simp [rk1Bytes, CryptoVerification.E2E.toU8, keyToBytes32],
       ResponderCore.vecU8_length _⟩
      (Entails.of_eq (by s4_ac_rfl))
  intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_F hs2_sym
  dsimp only [sessionStateNewSpec, gNew]
  have hs1_sp_eq := frozen_sp_eq hs1_F fsp (by wp_norm_goal)
  have hver_mod : BitVec.ofNat 32 ((4#32 : BitVec 32).toNat % 256) = 4#32 := rfl
  conv => arg 4; rw [hs1_sp_eq, hver_mod]
  s4_elim_exists localIkBoxPtr; s4_elim_exists remoteIkBoxPtr
  s4_elim_exists rootKeyBoxPtr; s4_elim_exists baseKeyBoxPtr
  s4_pure_elim
  rintro ⟨hs2_tr_eq, hlocal_ne, hremote_ne, hroot_ne, hbase_ne⟩
  have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans (by wp_norm_goal)
  have hs2_sp' : s2.sp = fsp := hs2_sp.trans hs1_sp_eq
  have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
  have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hvr0
  have hs2_g19 := hs2_cs.gpr ⟨19, by decide⟩
  have hs2_g20 := hs2_cs.gpr ⟨20, by decide⟩
  have hs2_g21 := hs2_cs.gpr ⟨21, by decide⟩
  have hs2_g22 := hs2_cs.gpr ⟨22, by decide⟩
  have hs2_g23 := hs2_cs.gpr ⟨23, by decide⟩
  have hs2_g24 := hs2_cs.gpr ⟨24, by decide⟩
  have hs2_g25 := hs2_cs.gpr ⟨25, by decide⟩
  have hs2_g26 := hs2_cs.gpr ⟨26, by decide⟩
  have hs2_g27 := hs2_cs.gpr ⟨27, by decide⟩
  have hs2_g28 := hs2_cs.gpr ⟨28, by decide⟩
  have hs2_gfp := hs2_cs.gpr ⟨29, by decide⟩
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hsp0, hfp0, hx19_0, hx20, hx21] at hs2_g19 hs2_g20 hs2_g21 hs2_g22 hs2_g23 hs2_g24
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hsp0, hfp0, hx19_0, hx20, hx21] at hs2_g25 hs2_g26 hs2_g27 hs2_g28 hs2_gfp
  have hs2_pc' : s2.pc = fnStart + bv% (4912) := by rw [hs2_pc]; wp_norm_goal
  conv => arg 4; rw [memRegion96_split_92_4 (fsp + 5784#64)]
  s4_elim_exists pad92
  s4_pure_elim
  intro hpad92
  s4_elim_exists pad_f4
  conv => arg 4; rw [memRegion_eq_exists_bytes (fsp + 5888#64) 40 (by decide)]
  s4_elim_exists pad40
  s4_pure_elim
  intro hpad40
  conv => arg 4; rw [memRegion24_split_8_8_4_4 (fsp + 5936#64)]
  s4_elim_exists w130; s4_elim_exists w138; s4_elim_exists w140; s4_elim_exists pad_144
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  let pre72 := alicePre72Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
  let tail100Init := aliceTail100Bv8 pad_f4 pad40 0xffffffffffffffff#64 w130 w138 w140 pad_144
  let post248 := alicePost248Bv8 baseKeyBoxPtr spqrCap spqrBufPtr
    (BitVec.ofNat 64 pq.length) pad92 tail100Init
  have hpre72_eq := alicePre72_eq_pointsToBytes (fsp + 5632#64)
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
  have hmid48_eq := aliceMid48_eq_pointsToBytes (fsp + 5632#64)
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
  have htail100_eq := aliceTail100_eq_pointsToBytes (fsp + 5632#64)
    pad_f4 pad40 hpad40 0xffffffffffffffff#64 w130 w138 w140 pad_144
  have hpost248_eq := alicePost248_eq_pointsToBytes (fsp + 5632#64)
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
    pad92 tail100Init hpad92
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpre72_eq hmid48_eq htail100_eq hpost248_eq
  s4_rw_pre hpre72_eq
  s4_rw_pre hmid48_eq
  s4_rw_pre htail100_eq
  s4_rw_pre hpost248_eq
  s4_rw_pre (stackAt_sessionBuild_split_sessionNew fsp).symm
  conv => arg 4; rw [stackAt_sessionBuild_split_withReceiver fsp]
  have h7264_fold := cells3_entails_memRegion24 (fsp + 7264#64)
    spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h7264_fold
  s4_fold_pre h7264_fold
  apply sepWPp_step_to_frozen ⟨hs2_F, hs2_sym⟩
    (mid := fnStart + bv% (2 ^ 64 - ls_rel%
      "<libsignal_protocol::state::session::SessionState>::with_receiver_chain"
      "libsignal_cli_handshake::initiate"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hs3_F hs3_sym
  let gRecv : WithReceiverChainGhost :=
    { outPtr := fsp + 4064#64
      inPtr := fsp + 5632#64
      senderRatchetPubPtr := fsp + 0x408#64
      senderRatchetPub32 := rpkBBytes
      receiverChainKeyPtr := fsp + 2256#64
      receiverChainKey32 := ck0Bytes
      receiverChainIdx := 0#32
      oldVecPtr := 8#64
      pre72 := pre72
      post248 := post248 }
  conv => arg 4; rw [← hrpkB_bv, ← hck0_bv]
  refine sepWPp_call_wpp_split hwrc gRecv
    (T := ((fsp + 0x408#64) ↦ₛ bytesToBv8 rpkBBytes) ∗
      ((fsp + 2256#64) ↦ₛ bytesToBv8 ck0Bytes) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 5632#64) ↦ₛ pre72) ∗
      ((fsp + 5704#64) ↦₆₄ 0#64) ∗
      ((fsp + 5712#64) ↦₆₄ 8#64) ∗
      ((fsp + 5720#64) ↦₆₄ 0#64) ∗
      ((fsp + 5728#64) ↦ₛ post248) ∗
      memRegion (fsp + 4064#64) 344 ∗
      (memRegion (fsp - 4576#64) 480 ∗ stackAt fsp allocHookStack) ∗
      A.pool)
    (F := ?_)
    hs3_F hs3_sym
    (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
    (by s4_split_frame)
    ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sm _ _ =>
      hpanic sm _ (by
        dsimp only [withReceiverChainEmptySpec, rustPanicOnOom]
        exact panic_oom_entails_initOnPanic A img S x stk s0 _ sm _ _ (by wp_norm_goal))) ?_
  · dsimp only [withReceiverChainEmptySpec, gRecv]
    have hsp_eq := frozen_sp_eq hs3_F fsp (by wp_norm_goal)
    rw [hsp_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.pure_right
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       ResponderCore.vecU8_length _,
       by simp [ck0Bytes, CryptoVerification.E2E.toU8, keyToBytes32],
       alicePre72Bv8_length _ _ _,
       alicePost248Bv8_length _ _ _ _ _ _ hpad92
         (aliceTail100Bv8_length _ _ hpad40 _ _ _ _ _)⟩
      (Entails.of_eq (by s4_ac_rfl))
  intro s4 hs4_pc hs4_run hs4_sp hs4_cs hs4_F hs4_sym
  dsimp only [withReceiverChainEmptySpec, gRecv]
  have hs3_sp_eq := frozen_sp_eq hs3_F fsp (by wp_norm_goal)
  conv => arg 4; rw [hs3_sp_eq]
  s4_elim_exists receiverRatchetPubBoxPtr; s4_elim_exists receiverChainKeyBoxPtr
  s4_elim_exists chainBufPtr
  s4_pure_elim
  rintro ⟨hs4_tr_eq, hrpub_ne, hrck_ne, hcb_ne⟩
  have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans hs2_tr
  have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp_eq
  have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
  have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hs4_cs.vregs.trans hs2_vr
  have hs4_g19 := hs4_cs.gpr ⟨19, by decide⟩
  have hs4_g20 := hs2_cs.gpr ⟨20, by decide⟩
  have hs4_g20' := hs4_cs.gpr ⟨20, by decide⟩
  have hs4_g21 := hs4_cs.gpr ⟨21, by decide⟩
  have hs4_g22 := hs4_cs.gpr ⟨22, by decide⟩
  have hs4_g23 := hs4_cs.gpr ⟨23, by decide⟩
  have hs4_g24 := hs4_cs.gpr ⟨24, by decide⟩
  have hs4_g25 := hs4_cs.gpr ⟨25, by decide⟩
  have hs4_g26 := hs4_cs.gpr ⟨26, by decide⟩
  have hs4_g27 := hs4_cs.gpr ⟨27, by decide⟩
  have hs4_g28 := hs4_cs.gpr ⟨28, by decide⟩
  have hs4_gfp := hs4_cs.gpr ⟨29, by decide⟩
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs2_sp', hs2_g19, hs2_g20, hs2_g21, hs2_g22, hs2_g23, hs2_g24, hs2_g25, hs2_g26, hs2_g27, hs2_g28, hs2_gfp] at hs4_g19 hs4_g20' hs4_g21 hs4_g22 hs4_g23
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs2_sp', hs2_g19, hs2_g20, hs2_g21, hs2_g22, hs2_g23, hs2_g24, hs2_g25, hs2_g26, hs2_g27, hs2_g28, hs2_gfp] at hs4_g24 hs4_g25 hs4_g26 hs4_g27 hs4_g28 hs4_gfp
  have hs4_pc' : s4.pc = fnStart + bv% (4936) := by rw [hs4_pc]; wp_norm_goal
  have hin5632_fold := withReceiver_inPtr_to_memRegion344 (fsp + 5632#64) chainBufPtr
    pre72 post248 (alicePre72Bv8_length _ _ _)
    (alicePost248Bv8_length _ _ _ _ _ _ hpad92 (aliceTail100Bv8_length _ _ hpad40 _ _ _ _ _))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hin5632_fold
  s4_fold_pre hin5632_fold
  have hout4064_unfold := (alicePost248_eq_pointsToBytes (fsp + 4064#64)
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
    pad92 tail100Init hpad92).symm
  have hhead144_pack := aliceHead144_eq_pointsToBytes (fsp + 4064#64)
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hout4064_unfold hhead144_pack
  s4_rw_pre hout4064_unfold
  s4_rw_pre hhead144_pack
  have hpad92_mem : ((fsp + 4216#64) ↦ₛ pad92) ⊢ memRegion (fsp + 4216#64) 92 :=
    hpad92 ▸ pointsToBytes_entails_memRegion (fsp + 4216#64) pad92
  s4_fold_pre hpad92_mem
  s4_rw_pre (stackAt_sessionBuild_split_withReceiver fsp).symm
  conv => arg 4; rw [stackAt_sessionBuild_split_withSender fsp]
  apply sepWPp_step_to_frozen ⟨hs4_F, hs4_sym⟩
    (mid := fnStart + bv% (2 ^ 64 - ls_rel%
      "<libsignal_protocol::state::session::SessionState>::with_sender_chain"
      "libsignal_cli_handshake::initiate"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hs5_F hs5_sym
  let head144 := aliceHead144Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
  let gSend : WithSenderChainGhost :=
    { outPtr := fsp + 5632#64
      inPtr := fsp + 4064#64
      senderKeyPairPtr := fsp + 2496#64
      senderRatchetPub32 := spubBytes
      senderRatchetPriv32 := sprivBytes
      senderChainKeyPtr := fsp + 2336#64
      senderChainKey32 := ck1Bytes
      senderChainIdx := 0#32
      pre144 := head144
      post100 := tail100Init }
  conv => arg 4; rw [← hspub_bv, ← hspriv_bv, ← hck1_bv]
  refine sepWPp_call_wpp_split hwsc gSend
    (T := ((fsp + 2496#64) ↦ₛ bytesToBv8 spubBytes) ∗
      ((fsp + 2528#64) ↦ₛ bytesToBv8 sprivBytes) ∗
      ((fsp + 2336#64) ↦ₛ bytesToBv8 ck1Bytes) ∗
      ((fsp + 2368#64) ↦₃₂ 0#32) ∗
      ((fsp + 4064#64) ↦ₛ head144) ∗
      ((fsp + 4208#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (fsp + 4216#64) 92 ∗
      ((fsp + 4308#64) ↦ₛ tail100Init) ∗
      memRegion (fsp + 5632#64) 344 ∗
      (memRegion (fsp - 4256#64) 160 ∗ stackAt fsp allocHookStack) ∗
      A.pool)
    (F := ?_)
    hs5_F hs5_sym
    (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
    (by s4_split_frame)
    ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sm _ _ =>
      hpanic sm _ (by
        dsimp only [withSenderChainNoneSpec, rustPanicOnOom]
        exact panic_oom_entails_initOnPanic A img S x stk s0 _ sm _ _ (by wp_norm_goal))) ?_
  · dsimp only [withSenderChainNoneSpec, gSend]
    have hsp_eq := frozen_sp_eq hs5_F fsp (by wp_norm_goal)
    rw [hsp_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.pure_right
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       ResponderCore.vecU8_length _, ResponderCore.vecU8_length _,
       by simp [ck1Bytes, CryptoVerification.E2E.toU8, keyToBytes32],
       aliceHead144Bv8_length _ _ _ _ _ _ _ _,
       aliceTail100Bv8_length _ _ hpad40 _ _ _ _ _⟩
      (Entails.of_eq (by s4_ac_rfl))
  intro s6 hs6_pc hs6_run hs6_sp hs6_cs hs6_F hs6_sym
  dsimp only [withSenderChainNoneSpec, gSend]
  have hs5_sp_eq := frozen_sp_eq hs5_F fsp (by wp_norm_goal)
  conv => arg 4; rw [hs5_sp_eq]
  s4_elim_exists senderRatchetPubBoxPtr; s4_elim_exists senderRatchetPrivBoxPtr
  s4_elim_exists senderChainKeyBoxPtr
  s4_pure_elim
  rintro ⟨hs6_tr_eq, hspub_ne, hspriv_ne, hsck_ne⟩
  have hs6_tr : s6.trace = s0.trace := hs6_tr_eq.trans hs4_tr
  have hs6_sp' : s6.sp = fsp := hs6_sp.trans hs5_sp_eq
  have hs6_align : s6.spAligned = true := hfsp_align s6 hs6_sp'
  have hs6_vr : calleeSavedVRegs s6 = calleeSavedVRegs s0 := hs6_cs.vregs.trans hs4_vr
  have hs6_g19 := hs6_cs.gpr ⟨19, by decide⟩
  have hs6_g20 := hs6_cs.gpr ⟨20, by decide⟩
  have hs6_g21 := hs6_cs.gpr ⟨21, by decide⟩
  have hs6_g22 := hs6_cs.gpr ⟨22, by decide⟩
  have hs6_g23 := hs6_cs.gpr ⟨23, by decide⟩
  have hs6_g24 := hs6_cs.gpr ⟨24, by decide⟩
  have hs6_g25 := hs6_cs.gpr ⟨25, by decide⟩
  have hs6_g26 := hs6_cs.gpr ⟨26, by decide⟩
  have hs6_g27 := hs6_cs.gpr ⟨27, by decide⟩
  have hs6_g28 := hs6_cs.gpr ⟨28, by decide⟩
  have hs6_gfp := hs6_cs.gpr ⟨29, by decide⟩
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs4_sp', hs4_g19, hs4_g20', hs4_g21, hs4_g22, hs4_g23, hs4_g24, hs4_g25, hs4_g26, hs4_g27, hs4_g28, hs4_gfp] at hs6_g19 hs6_g20 hs6_g21 hs6_g22 hs6_g23
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs4_sp', hs4_g19, hs4_g20', hs4_g21, hs4_g22, hs4_g23, hs4_g24, hs4_g25, hs4_g26, hs4_g27, hs4_g28, hs4_gfp] at hs6_g24 hs6_g25 hs6_g26 hs6_g27 hs6_g28 hs6_gfp
  have hs6_pc' : s6.pc = fnStart + bv% (4960) := by rw [hs6_pc]; wp_norm_goal
  have hin4064_fold := withSender_inPtr_to_memRegion344 (fsp + 4064#64)
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr 0#32
    head144 tail100Init (aliceHead144Bv8_length _ _ _ _ _ _ _ _)
    (aliceTail100Bv8_length _ _ hpad40 _ _ _ _ _)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hin4064_fold
  s4_fold_pre hin4064_fold
  s4_rw_pre htail100_eq.symm
  have hkyb_pre := setKyberCt_pre_entails (fsp + 5632#64) w130 w138 w140
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkyb_pre
  s4_fold_pre hkyb_pre
  s4_rw_pre (stackAt_sessionBuild_split_withSender fsp).symm
  conv => arg 4; rw [stackAt_sessionBuild_split_setKyberCt fsp]
  apply sepWPp_step_to_frozen ⟨hs6_F, hs6_sym⟩
    (mid := fnStart + bv% (2 ^ 64 - ls_rel%
      "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"
      "libsignal_cli_handshake::initiate"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hs7_F hs7_sym
  refine sepWPp_call_wpp_split hskc (fsp + 5632#64, kemCtPtr, 1569#64)
    (T := ((fsp + 5928#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w1 : BitVec 64, (fsp + 5936#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (fsp + 5944#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 32, (fsp + 5952#64) ↦₃₂ w3) ∗
      cells (fsp - 48#64) 6)
    (F := ?_)
    hs7_F hs7_sym
    (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
    (by s4_split_frame)
    ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
  · dsimp only [Pqxdh.setKyberCiphertextNoneSpec]
    have hsp_eq := frozen_sp_eq hs7_F fsp (by wp_norm_goal)
    rw [hsp_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.pure_right
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      (Entails.of_eq (by s4_ac_rfl))
  intro s8 hs8_pc hs8_run hs8_sp hs8_cs hs8_F hs8_sym
  dsimp only [Pqxdh.setKyberCiphertextNoneSpec]
  have hs7_sp_eq := frozen_sp_eq hs7_F fsp (by wp_norm_goal)
  conv => arg 4; rw [hs7_sp_eq]
  s4_pure_elim
  intro hs8_tr_eq
  have hs8_tr : s8.trace = s0.trace := hs8_tr_eq.trans hs6_tr
  have hs8_sp' : s8.sp = fsp := hs8_sp.trans hs7_sp_eq
  have hs8_align : s8.spAligned = true := hfsp_align s8 hs8_sp'
  have hs8_vr : calleeSavedVRegs s8 = calleeSavedVRegs s0 := hs8_cs.vregs.trans hs6_vr
  have hs8_g19 := hs8_cs.gpr ⟨19, by decide⟩
  have hs8_g20 := hs8_cs.gpr ⟨20, by decide⟩
  have hs8_g21 := hs8_cs.gpr ⟨21, by decide⟩
  have hs8_g22 := hs8_cs.gpr ⟨22, by decide⟩
  have hs8_g23 := hs8_cs.gpr ⟨23, by decide⟩
  have hs8_g24 := hs8_cs.gpr ⟨24, by decide⟩
  have hs8_g25 := hs8_cs.gpr ⟨25, by decide⟩
  have hs8_g26 := hs8_cs.gpr ⟨26, by decide⟩
  have hs8_g27 := hs8_cs.gpr ⟨27, by decide⟩
  have hs8_g28 := hs8_cs.gpr ⟨28, by decide⟩
  have hs8_gfp := hs8_cs.gpr ⟨29, by decide⟩
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs6_sp', hs6_g19, hs6_g20, hs6_g21, hs6_g22, hs6_g23, hs6_g24, hs6_g25, hs6_g26, hs6_g27, hs6_g28, hs6_gfp] at hs8_g19 hs8_g20 hs8_g21 hs8_g22 hs8_g23
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs6_sp', hs6_g19, hs6_g20, hs6_g21, hs6_g22, hs6_g23, hs6_g24, hs6_g25, hs6_g26, hs6_g27, hs6_g28, hs6_gfp] at hs8_g24 hs8_g25 hs8_g26 hs8_g27 hs8_g28 hs8_gfp
  have hs8_pc' : s8.pc = fnStart + bv% (4976) := by rw [hs8_pc]; wp_norm_goal
  s4_rw_pre (stackAt_sessionBuild_split_setKyberCt fsp).symm
  s4_rw_pre (stackAt_fsp_split hstk hstk64 fsp sessionBuildStack (by decide)).symm
  conv => arg 4; rw [stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)]
  let ses344 := aliceSession344Bv8
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    pad_f4 pad40 1569#64 kemCtPtr 1569#64 0xffffffff#32 pad_144
  have hses344_len : ses344.length = 344 :=
    aliceSession344Bv8_length localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
      baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
      senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
      pad_f4 pad40 hpad40 1569#64 kemCtPtr 1569#64 0xffffffff#32 pad_144
  have hdrop288_len : (ses344.drop 56).length = 288 := by simp [hses344_len]
  have htail100_final := aliceTail100_eq_pointsToBytes (fsp + 5632#64)
    pad_f4 pad40 hpad40 1569#64 kemCtPtr 1569#64 0xffffffff#32 pad_144
  have hses344_pack := aliceSession344_pack (fsp + 5632#64)
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    pad_f4 pad40 1569#64 kemCtPtr 1569#64 0xffffffff#32 pad_144
  have hses5632_split := aliceSession344_split_7words_288 (fsp + 5632#64)
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    pad_f4 pad40 1569#64 kemCtPtr 1569#64 0xffffffff#32 pad_144
  have hses0x460_split := aliceSession344_split_7words_288 (fsp + 0x460#64)
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    pad_f4 pad40 1569#64 kemCtPtr 1569#64 0xffffffff#32 pad_144
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at htail100_final hses344_pack hses5632_split hses0x460_split
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  s4_rw_pre htail100_final
  s4_rw_pre hses344_pack
  s4_rw_pre hses5632_split
  have hlog5064 := logOff_eq_at_5064 himg (hfn_entry.symm.trans (s4EntryExt_eq_base_add img ext))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hlog5064
  conv => arg 4; rw [show (0x158 : Nat) = 344 from rfl,
      memRegion344_split_56_288 (fsp + 0x460#64),
      cells7_eq_memRegion56 (fsp + 0x460#64),
      hlog5064]
  s4_elim_exists d460_0; s4_elim_exists d460_1; s4_elim_exists d460_2; s4_elim_exists d460_3
  s4_elim_exists d460_4; s4_elim_exists d460_5; s4_elim_exists d460_6
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_step_to_frozen ⟨hs8_F, hs8_sym⟩
    (mid := fnStart + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hs9_F hs9_sym
  conv => arg 4; rw [← hdrop288_len]
  refine sepWPp_call_wpp_split hmcpy (fsp + 1904#64, fsp + 5688#64, ses344.drop 56)
    (T := memRegion (fsp + 1904#64) (ses344.drop 56).length ∗
      ((fsp + 5688#64) ↦ₛ ses344.drop 56) ∗
      stackAt fsp extHookStack)
    (F := ?_)
    hs9_F hs9_sym
    (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
    (by s4_split_frame)
    ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
  · dsimp only [session2MemcpySpecX, Spec.inImage]
    have hs9_sp_eq := frozen_sp_eq hs9_F fsp (by wp_norm_goal)
    rw [hs9_sp_eq]
    exact Entails.pure_right ⟨hs9_F, hs9_sym⟩
      (Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal, by rw [hdrop288_len]; wp_norm_goal⟩
        (Entails.of_eq (by s4_ac_rfl)))
  intro s10 hs10_pc hs10_run hs10_sp hs10_cs hs10_F hs10_sym
  dsimp only [session2MemcpySpecX, Spec.inImage]
  have hs9_sp_eq := frozen_sp_eq hs9_F fsp (by wp_norm_goal)
  conv => arg 4; rw [hdrop288_len, hs9_sp_eq]
  s4_pure_elim
  rintro ⟨_, hs10_tr_eq⟩
  have hs10_tr : s10.trace = s0.trace := hs10_tr_eq.trans hs8_tr
  have hs10_sp' : s10.sp = fsp := hs10_sp.trans hs9_sp_eq
  have hs10_align : s10.spAligned = true := hfsp_align s10 hs10_sp'
  have hs10_vr : calleeSavedVRegs s10 = calleeSavedVRegs s0 := hs10_cs.vregs.trans hs8_vr
  have hs10_g19 := hs10_cs.gpr ⟨19, by decide⟩
  have hs10_g20 := hs10_cs.gpr ⟨20, by decide⟩
  have hs10_g21 := hs10_cs.gpr ⟨21, by decide⟩
  have hs10_g22 := hs10_cs.gpr ⟨22, by decide⟩
  have hs10_g23 := hs10_cs.gpr ⟨23, by decide⟩
  have hs10_g24 := hs10_cs.gpr ⟨24, by decide⟩
  have hs10_g25 := hs10_cs.gpr ⟨25, by decide⟩
  have hs10_g26 := hs10_cs.gpr ⟨26, by decide⟩
  have hs10_g27 := hs10_cs.gpr ⟨27, by decide⟩
  have hs10_g28 := hs10_cs.gpr ⟨28, by decide⟩
  have hs10_gfp := hs10_cs.gpr ⟨29, by decide⟩
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs8_sp', hs8_g19, hs8_g20, hs8_g21, hs8_g22, hs8_g23, hs8_g24, hs8_g25, hs8_g26, hs8_g27, hs8_g28, hs8_gfp] at hs10_g19 hs10_g20 hs10_g21 hs10_g22 hs10_g23
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs8_sp', hs8_g19, hs8_g20, hs8_g21, hs8_g22, hs8_g23, hs8_g24, hs8_g25, hs8_g26, hs8_g27, hs8_g28, hs8_gfp] at hs10_g24 hs10_g25 hs10_g26 hs10_g27 hs10_g28 hs10_gfp
  have hs10_pc' : s10.pc = fnStart + bv% (5020) := by rw [hs10_pc]; wp_norm_goal
  apply sepWPp_step_to_frozen ⟨hs10_F, hs10_sym⟩
    (mid := fnStart + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hs11_F hs11_sym
  conv => arg 4; rw [← hdrop288_len]
  refine sepWPp_call_wpp_split hmcpy (fsp + 1176#64, fsp + 1904#64, ses344.drop 56)
    (T := memRegion (fsp + 1176#64) (ses344.drop 56).length ∗
      ((fsp + 1904#64) ↦ₛ ses344.drop 56) ∗
      stackAt fsp extHookStack)
    (F := ?_)
    hs11_F hs11_sym
    (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
    (by s4_split_frame)
    ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
  · dsimp only [session2MemcpySpecX, Spec.inImage]
    have hs11_sp_eq := frozen_sp_eq hs11_F fsp (by wp_norm_goal)
    rw [hs11_sp_eq]
    exact Entails.pure_right ⟨hs11_F, hs11_sym⟩
      (Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal, by rw [hdrop288_len]; wp_norm_goal⟩
        (Entails.of_eq (by s4_ac_rfl)))
  intro s12 hs12_pc hs12_run hs12_sp hs12_cs hs12_F hs12_sym
  dsimp only [session2MemcpySpecX, Spec.inImage]
  have hs11_sp_eq := frozen_sp_eq hs11_F fsp (by wp_norm_goal)
  conv => arg 4; rw [hs11_sp_eq]
  s4_pure_elim
  rintro ⟨_, hs12_tr_eq⟩
  have hs12_tr : s12.trace = s0.trace := hs12_tr_eq.trans hs10_tr
  have hs12_sp' : s12.sp = fsp := hs12_sp.trans hs11_sp_eq
  have hs12_align : s12.spAligned = true := hfsp_align s12 hs12_sp'
  have hs12_vr : calleeSavedVRegs s12 = calleeSavedVRegs s0 := hs12_cs.vregs.trans hs10_vr
  have hs12_g19 := hs12_cs.gpr ⟨19, by decide⟩
  have hs12_g20 := hs12_cs.gpr ⟨20, by decide⟩
  have hs12_g21 := hs12_cs.gpr ⟨21, by decide⟩
  have hs12_g22 := hs12_cs.gpr ⟨22, by decide⟩
  have hs12_g23 := hs12_cs.gpr ⟨23, by decide⟩
  have hs12_g24 := hs12_cs.gpr ⟨24, by decide⟩
  have hs12_g25 := hs12_cs.gpr ⟨25, by decide⟩
  have hs12_g26 := hs12_cs.gpr ⟨26, by decide⟩
  have hs12_g27 := hs12_cs.gpr ⟨27, by decide⟩
  have hs12_g28 := hs12_cs.gpr ⟨28, by decide⟩
  have hs12_gfp := hs12_cs.gpr ⟨29, by decide⟩
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs10_sp', hs10_g19, hs10_g20, hs10_g21, hs10_g22, hs10_g23, hs10_g24, hs10_g25, hs10_g26, hs10_g27, hs10_g28, hs10_gfp] at hs12_g19 hs12_g20 hs12_g21 hs12_g22 hs12_g23
  simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd, hs10_sp', hs10_g19, hs10_g20, hs10_g21, hs10_g22, hs10_g23, hs10_g24, hs10_g25, hs10_g26, hs10_g27, hs10_g28, hs10_gfp] at hs12_g24 hs12_g25 hs12_g26 hs12_g27 hs12_g28 hs12_gfp
  have hs12_pc' : s12.pc = fnStart + bv% (5048) := by rw [hs12_pc]; wp_norm_goal
  s4_rw_pre (stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)).symm
  let sg := stage5SessionGhost kp.identityKey x.bundle.idKey x.bundle.spk baseKey sendingKeyPair
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
    spqrCap spqrBufPtr
    receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    kemCtPtr pad_144 kemCtBytes
  apply sepWPp_step_to_frozen ⟨hs12_F, hs12_sym⟩ (mid := fnStart + bv% (5252))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF' hsym'
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs)
  have hcanf :
      sg.localIk.bytes = ss.localIdentity.serialize ∧
      (match ss.remoteIdentity with
       | none => sg.remoteIk.bytes = []
       | some ik => sg.remoteIk.bytes = ik.serialize) ∧
      sg.alice.bytes = baseKey.serialize ∧
      sg.pending = none ∧
      (∃ kg, sg.kyber = some kg ∧ kg.vec.bytes = kemCtBytes) ∧
      (∃ scg sc, sg.sender = some scg ∧ ss.senderChain = some sc ∧
        scg.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
        scg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList) ∧
      ∀ gc ∈ sg.chains.zip ss.receiverChains,
        gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = [] := by
    rw [hss_def.val]
    dsimp only [sg, stage5SessionGhost, stage5SessionState]
    refine ⟨rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, ⟨_, _, rfl, rfl, rfl, rfl⟩, ?_⟩
    intro gc hgc
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hgc
    subst hgc
    exact ⟨rfl, rfl⟩
  refine ⟨sg,
    by wp_norm_goal,
    by rw [s4PcExt, hfn_entry]; try wp_norm_goal,
    by wp_norm_goal,
    by simp only [wp_norm, arm64_norm, hs12_sp', hfsp_def.val, cliInitiateFrame],
    by rw [hfp_fsp.val]; wp_norm_goal,
    by wp_norm_goal,
    ⟨hF', hsym'⟩,
    by simp only [calleeSavedVRegs, arm64_norm]; exact hs12_vr,
    by wp_norm_goal,
    hcanf, ?_⟩
  rw [← hlog5064,
      hikA_bv, hikB_bv, hrk1_bv, hbase_bv, hrpkB_bv, hck0_bv, hspub_bv, hspriv_bv, hck1_bv,
      bytesToBv8_encodeEC_vecU8 kp.identityKey.publicKey.bytes,
      bytesToBv8_encodeEC_vecU8 x.bundle.idKey.publicKey.bytes,
      bytesToBv8_encodeEC_vecU8 baseKey.bytes,
      bytesToBv8_encodeEC_vecU8 x.bundle.spk.bytes,
      bytesToBv8_encodeEC_vecU8 sendingKeyPair.publicKey.bytes]
  have hser_ikA : (0x05#8 :: kp.identityKey.publicKey.bytes.toList) =
      kp.identityKey.publicKey.serialize := rfl
  have hser_ikB : (0x05#8 :: x.bundle.idKey.publicKey.bytes.toList) =
      x.bundle.idKey.publicKey.serialize := rfl
  have hser_base : (0x05#8 :: baseKey.bytes.toList) = baseKey.serialize := rfl
  have hser_rpkB : (0x05#8 :: x.bundle.spk.bytes.toList) = x.bundle.spk.serialize := rfl
  have hser_spub : (0x05#8 :: sendingKeyPair.publicKey.bytes.toList) =
      sendingKeyPair.publicKey.serialize := rfl
  rw [hser_ikA, hser_ikB, hser_base, hser_rpkB, hser_spub]
  have hinline := sessionInline_stage5
    kp.identityKey x.bundle.idKey x.bundle.spk baseKey rk1 ck0 sendingKeyPair ck1
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
    spqrCap spqrBufPtr
    receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    kemCtPtr pad_f4 pad_144 pad40 kemCtBytes pq hpad40 hck1_idx hkem_len
  have hheap := sessionHeap_stage5 A
    kp.identityKey x.bundle.idKey x.bundle.spk baseKey rk1 ck0 sendingKeyPair ck1
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
    spqrCap spqrBufPtr
    receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
    kemCtPtr pad_144 kemCtBytes pq
    hlocal_ne hremote_ne hroot_ne hcb_ne hbase_ne hrpub_ne hrck_ne hspub_ne hspriv_ne hsck_ne
    hkem_ne hclamp hkem_len
  have hsession_ent :
      ((fsp + 0x460#64) ↦ₛ ses344) ∗
      (((localIkBoxPtr ↦ₛ kp.identityKey.publicKey.serialize) ∗ A.live localIkBoxPtr 33 1) ∗
       ((remoteIkBoxPtr ↦ₛ x.bundle.idKey.publicKey.serialize) ∗ A.live remoteIkBoxPtr 33 1) ∗
       ((rootKeyBoxPtr ↦ₛ keyToBytes32 rk1) ∗ A.live rootKeyBoxPtr 32 1) ∗
       (A.live chainBufPtr 416 8 ∗
        receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
        memRegion (chainBufPtr + 0x64#64) 316 ∗
        (receiverRatchetPubBoxPtr ↦ₛ x.bundle.spk.serialize) ∗
          A.live receiverRatchetPubBoxPtr 33 1 ∗
        (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1) ∗
       ((baseKeyBoxPtr ↦ₛ baseKey.serialize) ∗ A.live baseKeyBoxPtr 33 1) ∗
       vecU8Buf A spqrCap spqrBufPtr pq ∗
       ((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
         A.live senderRatchetPubBoxPtr 33 1) ∗
       ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
         A.live senderRatchetPrivBoxPtr 32 1) ∗
       ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗ A.live senderChainKeyBoxPtr 32 1) ∗
       ((kemCtPtr ↦ₛ kemCtBytes) ∗ A.live kemCtPtr 1569 1)) ⊢
        sessionStateAt A (fsp + 0x460#64) sg ss :=
    hss_def.val ▸ Entails.trans (sepConj_mono (Entails.refl _) hheap)
      (RawByteMove.sessionStateAt_of_bytes A (fsp + 0x460#64) sg _ hinline)
  have h1904_mem : ((fsp + 1904#64) ↦ₛ ses344.drop 56) ⊢ memRegion (fsp + 1904#64) 288 :=
    hdrop288_len ▸ pointsToBytes_entails_memRegion (fsp + 1904#64) (ses344.drop 56)
  have h5632_mem : ((fsp + 5632#64) ↦ₛ ses344) ⊢ memRegion (fsp + 5632#64) 344 :=
    hses344_len ▸ pointsToBytes_entails_memRegion (fsp + 5632#64) ses344
  have h2256_mem := keyAndIdx_entails_memRegion36 (fsp + 2256#64) ck0 0#32
  have h2336_mem := keyAndIdx_entails_memRegion36 (fsp + 2336#64) ck1.key 0#32
  have h2496_mem := pointsToBytes32_entails_memRegion32 (fsp + 2496#64)
    (List.Vector.toList_length sendingKeyPair.publicKey.bytes)
  have h2528_mem := pointsToBytes32_entails_memRegion32 (fsp + 2528#64)
    (List.Vector.toList_length sendingKeyPair.privateKey.bytes)
  have h7232_mem := pointsToBytes32_entails_memRegion32 (fsp + 7232#64)
    (by simp [keyToBytes32] : (keyToBytes32 rk1).length = 32)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2256_mem h2336_mem
  s4_rw_ent hses0x460_split.symm
  s4_rw_ent hses5632_split.symm
  s4_fold_ent hsession_ent
  s4_fold_ent h1904_mem
  s4_fold_ent h2256_mem
  s4_fold_ent h2336_mem
  s4_fold_ent h2496_mem
  s4_fold_ent h2528_mem
  s4_fold_ent h5632_mem
  s4_fold_ent h7232_mem
  exact Entails.of_eq (by s4_ac_rfl)
  }
  { rintro sf Pf hsteps
      ⟨sg, htrf, hpcf, hrunf, hspf, hfpf, hx19f, hinvf, hvrf, hx20f, hcanf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq hTrace hsteps
        (htrf.trans htr.symm)).trans hctrl.files0
    exact ⟨sg, htrf,
      ⟨hpcf, hrunf, hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl.spAligned⟩,
      hx20f, hcanf, hentf⟩
  }

theorem stage4_step_session
    {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {kp : IdentityKeyPair} {ekAPk kemCtBytes : List (BitVec 8)}
    {kemCtPtr : BitVec 64} {baseKey : PublicKey}
    {rk1 : RootKey} {ck0 pqrKey : BitVec 256}
    {sendingKeyPair : KeyPair} {ck1 : ChainKey}
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    {s : State} (hctrl : InInitiate img W s0 s 4848) (htr : s.trace = s0.trace)
    (hx20_in : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_in : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hbase_eq : ekAPk = baseKey.bytes.toList)
    (hclamp : Ratchet.clampScalar sendingKeyPair.privateKey.bytes = sendingKeyPair.privateKey.bytes)
    (hck1_idx : ck1.index = 0#32)
    (hkem_len : kemCtBytes.length = 1569)
    (hkem_ne : kemCtPtr ≠ 0#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let pq : List (BitVec 8) := (pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b pqrKey
    let ss := stage5SessionState kp.identityKey x.bundle.idKey x.bundle.spk rk1 ck0
      sendingKeyPair ck1 pq
    SepWPp (initProg img W) (initPc img W 5252) s
      (((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
        A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ kemCtBytes) ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗ ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 0x460#64) 0x158 ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 1904#64) 288 ∗ ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0) ∗
        ((fsp + 2288#64) ↦₃₂ 0#32) ∗ ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗
        ((fsp + 2368#64) ↦₃₂ 0#32) ∗
        ((fsp + 2496#64) ↦ₛ sendingKeyPair.publicKey.bytes.toList) ∗
        ((fsp + 2528#64) ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
        ((fsp + 4064#64) ↦₆₄ 0#64) ∗ RustHeap.vecU8 A (fsp + 4072#64) pq ∗
        memRegion (fsp + 4096#64) 312 ∗ memRegion (fsp + 5632#64) 344 ∗
        ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗ memRegion (fsp + 7264#64) 24 ∗
        logOff img ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        ∃ sg : SessionGhost,
          sf.trace = s0.trace ∧ InInitiate img W s0 sf 0x1484 ∧
          sf.readReg64 (.gpr 20#5) = fsp + 0x460#64 ∧
          (sg.localIk.bytes = ss.localIdentity.serialize ∧
            (match ss.remoteIdentity with
             | none => sg.remoteIk.bytes = []
             | some ik => sg.remoteIk.bytes = ik.serialize) ∧
            sg.alice.bytes = baseKey.serialize ∧ sg.pending = none ∧
            (∃ kg, sg.kyber = some kg ∧ kg.vec.bytes = kemCtBytes) ∧
            (∃ scg sc, sg.sender = some scg ∧ ss.senderChain = some sc ∧
              scg.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
              scg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList) ∧
            ∀ gc ∈ sg.chains.zip ss.receiverChains,
              gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []) ∧
          (Pf ⊢
            ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
            ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
            ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
            ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
            ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
            ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
            sessionStateAt A (fsp + 0x460#64) sg ss ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
            memRegion (fsp + 1904#64) 288 ∗ memRegion (fsp + 2256#64) 36 ∗
            memRegion (fsp + 2336#64) 36 ∗ memRegion (fsp + 2496#64) 32 ∗
            memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 344 ∗
            memRegion (fsp + 5632#64) 344 ∗ memRegion (fsp + 7232#64) 32 ∗
            memRegion (fsp + 7264#64) 24 ∗ logOff img ∗ A.pool ∗
            stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp pq ss
  apply sepWPp_steps_post
    (stage4_step_session_ext (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W)
      hstk hstk64 hspk himg hh.alloc (Stage4CalleesExt.of_initLocalCallees hLocal).to_extX
      (initProg_traceFsSound img W) hpanic
      ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0, hctrl.inv,
        hctrl.vregs, hctrl.spAligned⟩
      htr hx20_in hx21_in hbase_eq hclamp hck1_idx hkem_len hkem_ne)
  rintro sf Pf _ ⟨sg, htrf, hc, hx20f, hcanf, hentf⟩
  exact ⟨sg, htrf, ⟨hc.pc, hc.run, hc.sp, hc.fp, hc.x19, hc.files0, hc.inv, hc.vregs,
    hc.spAligned⟩, hx20f, hcanf, hentf⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
