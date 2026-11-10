/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.WireEntries.RecvWireSameAccount
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTight
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.TightTargets
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitMain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepTightTargets
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.Chain
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargets
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Trap-at-RNG Front Segments for CLI Ratchet Decryption

Establishes `tryDecryptCallees_trap`, `s0_ok_P_trap` (`S0` under `remote ≠ local ∨ DistinctSid`),
`loadRatchet_okT_ext` (`S1`), `dhStep_okT_trap` (`S3`), and `errTail_ok_tight_alloc` (`ErrTail`)
on `trTrapProgAt img.base C abs` and `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
open CryptoVerification.LibsignalSession

/-! ## 1. Callee Contracts on `trTrapExterns` -/

theorem tryDecryptCallees_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCalleesExt
      img C A uuidTryParse (trTrapExterns C abs) := by
  let ext := trTrapExterns C abs
  have hS2 : Stage2Contracts_trap img.base C A uuidTryParse S ext :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hH
  have hA : AllocContracts img.base A ext := hS2.toAllocContracts
  have hle := sessionExterns_le_trTrap C abs
  have h_bb := blackBox_trTrapExterns C abs
  have : HkdfHooks C.F ext := hkdfHooks_trTrapExterns C abs
  have hnew := ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle
  refine
    { localIk := Getters.local_identity_key_ok_ext img A ext (pkTryFrom_ok_ext img ext himg)
      remoteIk := Glue.remoteIdentityKeyOk_ext img A ext himg
      sameAcc := Glue.is_same_account_ok_ext img.base h_bb
      clearUpk := Getters.clear_unacknowledged_pre_key_message_ok_ext img.base A ext hA
      dropChain := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_ext hA
      chainKeyToPb := chain_key_to_pb_ok_ext hA
      derivePk := derive_public_key_bytes_ok_of_contract
        (subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
          hS2.pub_from_secret.mono_outcome (x.secret, x.sec, x.out) R s0 hpc hrun hpre hsp
            fun _ hout => hout)
      trFrom := ReceiveRatchetFrom.trFrom_ok_ext himg hA (Glue.deserializeOk_ext img.base ext)
        (Glue.remoteIdentityKeyOk_ext img A ext himg) (Glue.dropSpeOk_ext himg hA)
        (Getters.drop_vec_chain_ok_ext hA)
      trApply := ReceiveRatchetApply.trApply_ok_ext hA (Glue.publicKeySerializeOk_ext hA)
        (Getters.drop_vec_message_key_ok_ext hA) (Getters.drop_vec_chain_ok_ext hA)
      findReceiverChainKey := Glue.findReceiverChainKeyOk_ext hle himg
      createChain := Keys.createChain_ok_of_contracts himg
        (Keys.calculateAgreement_ok_of_contracts himg hS2.dh hS2.shared_drop
          (ConsumeMessageKeyTransfer.ctEqRO_ok_ext img.base h_bb) hA.shim hA.alloc hS2.static_drop)
        (extract_ok_ext img C ext hnew)
        (expand_multi_info_ok_ext img.base C ext)
        (hA.dealloc_ok_at createChainName
          (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
          (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"),
                (ls_stub% "__rustc::__rust_dealloc")]))
      genKeys := Keys.generateKeys_ok_ext himg (extract_ok_ext img C ext hnew)
        (expand_multi_info_ok_ext img.base C ext) hA
      pkSer := Glue.publicKeySerializeOk_ext hA
      verifyMac := verifyMacWithAddresses_subroutine_ok_of_contracts img himg C A ext hA
        hS2.compress256 hS2.black_box hS2.uuid_try_parse hnew (Glue.publicKeySerializeOk_ext hA)
      cmk := ConsumeMessageKeyTransfer.cmk_ok_ext himg hH.alloc hle
      growOne := ConsumeMessageKeyTransfer.growOneChain_ok_ext himg hH.alloc hle }

/-! ## 2. Segment `S0` under `DistinctSid` -/

theorem isSameAccountEqDistinct_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt
      b A (trTrapExterns C abs) := by
  have hS2 := Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hH
  exact CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok_ext
    b A (trTrapExterns C abs)
    (ConsumeMessageKeyTransfer.publicKeyEq_ok_ext b (blackBox_trTrapExterns C abs))
    (ParseServiceId.parseSid_ok_of_code b (Rust.withPanics (trTrapExterns C abs)) hS2.uuid_try_parse)

theorem s0_ok_P_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : TripleRatchetHooks C A S abs)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCalleesExt
      img C A uuidTryParse (trTrapExterns C abs))
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    reaches_pc (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P_ext
    (ext := trTrapExterns C abs) himg
    hcallees.localIk hcallees.remoteIk hcallees.sameAcc
    (isSameAccountEqDistinct_ok_trap hH) x R s0 h_pc h_run h_sp_align hpre

theorem s0_ok_P_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hlocal : LocalIdentityKeyOkExt img A ext)
    (hremote : CryptoVerification.LibsignalTripleRatchet.Decrypt.RemoteIdentityKeyOkExt img A ext)
    (hsameDist : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32
      img.base A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P_x_ext
    himg hlocal hremote hsameDist x R s0 h_pc h_run h_sp_align hpre

/-! ## 3. Segment `S1` (`loadRatchet_okT_ext`) -/

theorem loadRatchet_okT_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (htrFrom : TrFromOkExt img A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s' := by
  have hcall := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_call_trFrom_reaches
    himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.P3kR1bc.reaches_outcome_steps hsteps_ret
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.P3kR1bc.loadRatchet_after_call_error_tight
          himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segFindChainPC img) s
        (fun s' => ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_after_call_ok
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

private theorem loadRatchet_okT_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (htrFrom : TrFromOkX img A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s)
    (hcode : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s' := by
  have hcall := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_call_trFrom_reaches_x
    himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.P3kR1bc.reaches_outcome_steps hsteps_ret
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.P3kR1bc.loadRatchet_after_call_error_tight
          himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segFindChainPC img) s
        (fun s' => ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_after_call_ok
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

/-! ## 4. Segment `S3` (`dhStep_okT_trap`) -/

private theorem staticDrop_ok_at2_td_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hS2 : Stage2Contracts_trap b C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2 ^ 64))
      zeroizeSecretSpec :=
  sub_ok_at_of_fnAddr hS2.static_drop
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    (num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
    (by simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName, arm64_norm])

theorem dhStep_okT_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS2 : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hcc : CreateChainOkExt img C A ext)
    (hdpk : DerivePublicKeyBytesOkExt img.base C ext)
    (hPkSer : PublicKeySerializeOkExt img.base A ext)
    (hToPb : ChainKeyToPbOkExt img.base A ext)
    (hGrowOne : GrowOneChainOkExt img A ext)
    (hDropChain : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hfrom : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hsp0 : rootStack ≤ s0.sp.toNat)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s) :
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∀ (_ : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem),
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
          | (.ok ck, r') =>
              ∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img
                x trG' { tr with ratchet := r' } st1 ck draws R s0 s'
          | (.error e, _) =>
              ∃ trG' r_err, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img
                x trG' { tr with ratchet := r_err } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R)) := by
  dsimp only
  intro hcode
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, ⟨_, _, herr⟩ | ⟨_, hoom⟩⟩ :=
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_missing_sender_chain
        (A := A) (ctl := ctl) (ext := ext)
        himg x trG tr st1 R s0 s hsc hs3 hcode
    · exact ⟨s', hsteps, Or.inl ⟨trG, tr.ratchet, herr⟩⟩
    · exact hoom.elim
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hstep1 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_recv_create_chain
      (S := P3kR1bd.spqrNoPanic)
      himg hcc x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, herr1 | ⟨hpan1, hq1⟩⟩ := hstep1
      · exact ⟨s1, hsteps1, Or.inl herr1⟩
      · exact ⟨s1, hsteps1, Or.inr ⟨hpan1,
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq1⟩⟩
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter | ⟨hpan1, hq1⟩⟩ := hstep1
      · have hrng := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.DhStepCallees.coinsFillAt_ok_td_ext
          (b := img.base) (cur := x.cur) (rest := x.rest)
          hS2.toAllocContracts (ProofLib.ObjectLoad.base_aligned_of_loads himg)
        have hsd := staticDrop_ok_at2_td_trap hS2
        have hstep2 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_keygen_and_send_create_chain
          (S := P3kR1bd.spqrNoPanic)
          himg hcc hdpk x trG tr st1 rk1 rck R s0 s1 hrng hsd hrk2_ne hafter (hsteps1.codeLoaded hcode)
        dsimp only at hstep2
        cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, herr2 | ⟨hpan2, hq2⟩⟩ := hstep2
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inl herr2⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr ⟨hpan2,
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq2⟩⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, hcommit | ⟨hpan2, hq2⟩⟩ := hstep2
          · have hsteps12 := Steps.trans hsteps1 hsteps2
            have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
            obtain ⟨s3, hsteps3, hout3 | ⟨hpan3, hq3⟩⟩ :=
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.s3_commit_spec_ext
                img C A ctl P3kR1bd.spqrNoPanic ext
                himg hS2.toAllocContracts
                hPkSer hToPb hGrowOne hDropChain
                x trG tr st1 sc rck (KeyPair.generate C (coinsOf x.rest))
                finalRootKey senderChainKey R s0 s2
                hsc hrc_len hclamp hcommit (hsteps12.codeLoaded hcode)
            · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl hout3⟩
            · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3,
                CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq3⟩⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr ⟨hpan2,
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq2⟩⟩
      · cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr ⟨hpan1,
            CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq1⟩⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr ⟨hpan1,
            CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq1⟩⟩

/-! ## 5. Tight `ErrTail` under `AllocContracts` -/

theorem errTail_ok_tight_alloc {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts img.base A ext)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext) :
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S uuidTryParse).1 = .error e →
      (x.model C S uuidTryParse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s := by
  intro x trG tr st1 e R s0 s he hmod1 hmod2 herr
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta.to_wpInv hmeta
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 =
      memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide,
        memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗
         (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [h140_split] at hmem3
    dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp :
      SepWP (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.retEpiloguePC img) s
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack)
        (fun sf P =>
          P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
               ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
               ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
               ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
               ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
               ((sp + 0x140#64) ↦₆₄ w0) ∗
               ((sp + 0x148#64) ↦₆₄ w1) ∗
               ((sp + 0x150#64) ↦₆₄ w2) ∗
               words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
               (x.ret ↦₆₄ speTag e) ∗
                words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
                A.pool ∗ stackAt sp dropChainStack) ∧
           tryDecryptWPInv s0 sf) := by
    have hcopy := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_copy_spe_wp
      (img := img) (ext := ext)
      (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      (t0 := t0) (t1 := t1) (t2 := t2)
      himg hpc hmeta_wp hx19 hx20 hx26
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
            A.pool ∗ stackAt sp dropChainStack)
      hcopy ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hcs_lt' : cs.length * 104 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
    have hdrop_cs := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_drop_chains_wp
      (img := img) (A := A) (ext := ext)
      himg hdrop hcs_lt' hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hdrop_cs ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2
    subst hP2
    have hre_cs :
        (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp dropChainStack) ∗
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
           ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
           ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
           ((sp + 0x140#64) ↦₆₄ w0) ∗
           ((sp + 0x148#64) ↦₆₄ w1) ∗
           ((sp + 0x150#64) ↦₆₄ w2) ∗
           words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
           (x.ret ↦₆₄ speTag e) ∗
           words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
           (if trG.pq.cap = 0#64 then emp
            else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
              memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
        ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
          A.pool ∗ stackAt sp allocHookStack) ∗
         (memRegion (sp - 4144#64) 48 ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          (x.ret ↦₆₄ speTag e) ∗
          words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
             memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
      rw [stackAt_dropChainStack_sub sp]
      have hcomm1 :
          (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗
              (stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48)) ∗
            (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
             ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
             ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗
             ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
             (x.ret ↦₆₄ speTag e) ∗
             words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
             (if trG.ratchet.chainsCap = 0#64 then emp
              else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
                memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                  ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
             (if trG.pq.cap = 0#64 then emp
              else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
                memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
           (A.pool ∗ stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      have hcomm2 :
          ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
            A.pool ∗ stackAt sp allocHookStack) ∗
           (memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
           (A.pool ∗ stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      rw [hcomm1, hcomm2]
      exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))
    refine SepWP.mono_pre (by dsimp only [sp] at hre_cs ⊢; exact hre_cs) ?_
    have hdealloc_cs := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_dealloc_chains_wp
      (img := img) (A := A) (ext := ext)
      himg hAlloc hcs_lt hpc2 hmeta2 hx20_2
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hdealloc_cs ?_ ?_
    · dsimp only [sp]
    intro s3 P3 ⟨hP3, hmeta3⟩ hpc3
    subst hP3
    have hdealloc_pq := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_dealloc_pq_wp
      (img := img) (A := A) (ext := ext)
      (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr)
      himg hAlloc hpc3 hmeta3
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4)
      hdealloc_pq ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
    rw [stackAt_dropChainStack_sub sp]
    dsimp only [sp]; sep_ac_rfl
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗
         H_spe ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]
    exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]
    exact decRel_afterTrFrom x.G
  apply CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.P3kR1bc.reaches_epilogue_to_outcome_tight
    himg x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩
  subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]
    exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗
          ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          (stackAt sp dropChainStack ∗
           memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right
      (sepConj_mono hdec_ent
      (sepConj_mono_left
        (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4))))
    hmem_f_re

end CryptoVerification.Cli.LibsignalSpqrV1.M4
