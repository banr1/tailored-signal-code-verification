/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightP
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Root
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.Callees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS7
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS8
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS9
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegDhMain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ErrTailProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0A
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S1Proof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S2B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SpqrRecv
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepTightTargets
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Root
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge

/-!
# Trap-at-RNG & CLI Tight Handshake `try_decrypt_with_state::<Coins>`

Proves `tryDecryptPqV1_ok_PTight_trap` on `trTrapProgAt img.base C abs` against
`tryDecryptSpecTPTight`, together with `TryDecryptPqV1RunStmt*_trap` and CLI corollaries on
`tripleRatchetProgAtExt img.base (cliExterns W)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model

/-! ## 1. Trap-at-RNG Tight Seam Contracts (`S0SpecP_trap`, `ErrTailSpecTight_trap`, `S1SpecTight_trap`, `S3SpecTight_trap`) -/

/-- `DecryptPq.S0Spec_trap` with weak precondition `tryDecryptSpecP`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0SpecP_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.LocalIdentityKeyOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.RemoteIdentityKeyOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap img.base C abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img →
      s0.status = .Running →
      s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0)

/-- `DecryptPq.ErrTailSpec_trap` with the outcome stated against `Decrypt.tryDecryptSpecTight`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpecTight_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s

/-- `DecryptPq.S1Spec_trap` with the `.error` outcome stated against `Decrypt.tryDecryptSpecTight`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1SpecTight_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrFromOk_trap img C A abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (trTrapProgAt img.base C abs)
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s'

/-- `DecryptPq.S3Spec_trap` with both `.Panicked` disjuncts stated against `tryDecryptOnPanicTight`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3SpecTight_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DerivePublicKeyBytesOk_trap img.base C abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.PublicKeySerializeOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ChainKeyToPbOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG' r1,
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

/-! ## 2. Trap-at-RNG Tight Seam Proofs (`errTail_okT_trap`, `s1_okT_trap`, `s3_okT_trap`, `s0_ok_P_trap`) -/

/-- Tight `ErrTail` proof on `trTrapProgAt` from `SegA.errTail_ok_trap` via `spqrDropPanic`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_okT_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpecTight_trap img C A ctl uuidTryParse S abs := by
  intro himg hH hdrop x trG tr st1 e R s0 s hne hm1 hm2 herr
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hm1]; intro h; injection h with h'; exact hne h'
  have hmod := model_spqrDropPanic_eq_of_ne_panic hnpan
  have hm1' : (x.model C (spqrDropPanic S) uuidTryParse).1 = .error e := by rw [hmod, hm1]
  have hm2' : (x.model C (spqrDropPanic S) uuidTryParse).2 = st1 := by rw [hmod, hm2]
  exact reaches_outcome_tight_of_spqrDropPanic hnpan
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok_trap
      himg (tripleRatchetHooks_withSpqr hH) hdrop x trG tr st1 e R s0 s hne hm1' hm2' herr)

/-- Tight `S1` proof on `trTrapProgAt` from `SegA.s1_ok_trap` via `spqrDropPanic`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_okT_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1SpecTight_trap img C A ctl uuidTryParse S abs := by
  intro himg htrFrom x R s0 s hS1 hcode
  have hs1 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_trap
    (S := spqrDropPanic S) himg htrFrom x R s0 s hS1 hcode
  cases hres : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk r st1 =>
    rw [hres] at hs1
    cases r with
    | error e =>
      have ⟨hm, hne⟩ := model_of_fromSessionState_error (C := C) (S := S) hres
      have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
        rw [hm]; intro h; injection h with h'; exact hne h'
      exact reaches_outcome_tight_of_spqrDropPanic hnpan hs1
    | ok tr =>
      exact hs1

/-- Tight `S3` proof on `trTrapProgAt` from `SegB.s3_ok_trap` instantiated at `DhStep.P3kR1bd.spqrNoPanic`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_okT_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3SpecTight_trap img C A ctl uuidTryParse S abs := by
  intro himg hHooks hcc hdpk hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hs3 hcode
  have hs3_np := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok_trap
    img C A ctl DhStep.P3kR1bd.spqrNoPanic abs
    himg (tripleRatchetHooks_withSpqr hHooks) hcc hdpk hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hs3 hcode
  dsimp only at hs3_np ⊢
  cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet with
  | mk res r1 =>
    rw [hdh] at hs3_np
    cases res with
    | ok ck =>
      rcases hs3_np with ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
      · exact ⟨s', hsteps, Or.inl hok⟩
      · exact ⟨s', hsteps, Or.inr ⟨hpan,
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq⟩⟩
    | error e =>
      rcases hs3_np with ⟨s', hsteps, herr | ⟨hpan, hq⟩⟩
      · exact ⟨s', hsteps, Or.inl herr⟩
      · exact ⟨s', hsteps, Or.inr ⟨hpan,
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq⟩⟩

private theorem coinsAfter_zero_sa_trap (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢
      CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt
    CryptoVerification.SignalSession.Coins.tapeAt2
    CryptoVerification.SignalSession.Coins.coinsAfter
    CryptoVerification.SignalSession.Coins.tapeAfter2
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

/-- Weak-`pre` `S0SpecP_trap` proof on `trTrapProgAt` for handshake `try_decrypt_with_state::<Coins>`,
chaining `SegA.s0_step{1,2,3}_reaches_trap` with `ResponderClosure.P3P4.s0_step45_reaches_pq_distinct_trap`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok_P_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0SpecP_trap img C A ctl uuidTryParse S abs := by
  intro himg hlocal hremote _hsame x R s0 h_pc h_run h_sp_align hpre
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨
      stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗ (vecGhostAt A
      x.G.remoteIk (x.ss + 0x18#64) ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
      vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
      optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
      optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
      optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
      ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗
      ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
      ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
      memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hcall_inv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab := ⟨hfrozen0, hsym0⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap
    (C := C) (abs := abs) himg
  have h_pc' : s0.pc = (trTrapProgAt img.base C abs).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
    h_pc.trans hentry
  have h_segS1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img =
      (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 472#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC
    rw [hentry]
  rw [h_segS1]
  refine SegA.reaches_pc_seq_callInv hcall_inv
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step1_reaches_trap
      hlocal x _ s0 h_pc' h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1)
    ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
    hx29_1, hm1⟩ hinv1
  have hm_s2 : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
      (vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
        memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
        stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
        (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
            (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
          vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
          optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
          optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
          ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗
          ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
          ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
          logOff img ∗ memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine SegA.reaches_pc_seq_callInv hinv1
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step2_reaches_trap
      x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
      hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
    hx24_2, hx25_2, hx29_2, hm2⟩ hinv2
  have hm_s3 : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
        ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ vecGhostAt A x.G.localIk x.ss ∗
        memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
            (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
          vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
          optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
          optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
          ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗
          ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
          ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
          memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  refine SegA.reaches_pc_seq_callInv hinv2
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step3_reaches_trap
      hremote x _ s0 s2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2
      hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
    hx29_3, hm3⟩ hinv3
  have hm_s45 : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
        memRegion (s0.sp - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗
        vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗
        ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        memRegion x.ret 48 ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (SegA.reaches_pc_callInv hinv3
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step45_reaches_pq_distinct_trap
        himg x _ s0 s3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3
        hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx29_5, hm5⟩, hfrozen5, hsym5⟩
  rw [← h_segS1] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hfrozen5, hsym5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
      (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗
        logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
        memRegion (s0.sp - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗
        vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗
        ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Arm64.Satisfies.mono
    (sepConj_mono_left (coinsAfter_zero_sa_trap img.base x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

/-! ## 3. Trap-at-RNG Seam Composition (`reaches_outcome_of_s4QF_PTight_trap`, `try_decrypt_ok_of_seamsQF_PTight_trap`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF_PTight_trap
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q Pstk F C A S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap img C A uuidTryParse abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_trap img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_trap img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_trap img C A ctl uuidTryParse S abs)
    (herrT : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpecTight_trap img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : Q x.st.pqRatchetState)
    (hPstk : Pstk (s0.sp - 1504#64).toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG
      { tr0 with ratchet := r1 } st1 ck draws (F ∗ R) s0 s4)
    (hL4 : (trTrapProgAt img.base C abs).CodeLoaded s4.mem) :
    reaches_outcome (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF_PTight Q F C A ctl uuidTryParse S img)
      x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  have hs4_step :=
    hs4 hloads hhooks hcallees.cmk x trG { tr0 with ratchet := r1 } st1 ck draws (F ∗ R) s0 s4
      hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      have hmodel := model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact Arm64.reaches_outcome_steps hsteps4
          (reaches_outcome_tryDecryptSpecQF_PTight_of_tight
            (herrT hloads hhooks hcallees.dropChain x trG' { tr0 with ratchet := r2 } st1 e
              (F ∗ R) s0 s4' hne hm1 hm2 herr_st))
      · exact reaches_outcome_of_panicQF_PTight hsteps4 hpan
          (onPanicTight_drop_frame (onPanicTight_of_cmk_panic hm1 hp hmem))
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Arm64.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hs5_step :=
          hs5 hloads hhooks hrecv x trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
            hQ hpqr0 hPstk hs5_state hL5
        dsimp only at hs5_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs5_step
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          have hne : e ≠ .panic := by subst e; cases sd <;> nofun
          rcases hs5_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := model_of_spqr_error htr herc hcmk hspqr hnp5
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            subst hdraws
            exact Arm64.reaches_outcome_steps hsteps5'
              (reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk htr herc hcmk
                (herr hloads hhooks hcallees.dropChain x trG5
                  { tr0 with ratchet := r2 } st1 e (F ∗ R) s0 s5'
                  hne hm1 hm2 herr_st))
          · exact reaches_outcome_of_panicQF_PTight hsteps5' hpan
              (tryDecrypt_onPanicTight_of_afterCmk_cli htr herc hcmk hq)
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine Arm64.reaches_outcome_steps hsteps6
              (reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk htr herc hcmk ?_)
            have hL6 := hsteps6.codeLoaded hL5
            have hseed32 : mkg.seed.length = 32 :=
              decrypt_mkg_seed hseeds htr herc hcmk
            obtain ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hoom⟩⟩ :=
              hs6 hloads hcallees.genKeys x trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws (F ∗ R) s0 s6 hseed32 hs6_state hL6
            rotate_left; · exact False.elim hoom
            refine Arm64.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := hs7 hloads hhooks hcallees.verifyMac x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (F ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 =
                  .error (.invalidMessage x.msgType .macFailed) := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact Arm64.reaches_outcome_steps hsteps7'
                  (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) (F ∗ R) s0 s7' hne hm1 hm2 herr_st)
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic
                  hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine Arm64.reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := hs8 hloads hhooks x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (F ∗ R) s0 s8 hs8_state hL8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Arm64.reaches_outcome_steps hsteps8'
                      (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) (F ∗ R) s0 s8' hne hm1 hm2 herr_st)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic
                      hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 }
                          with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Arm64.reaches_outcome_steps hsteps9
                      (hs9 hloads hhooks hcallees.trApply hcallees.clearUpk x trG5
                        { tr0 with ratchet := r2 } st1 newPqrState pt (F ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic
                      hsteps9 hpan hq
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic
                  hsteps8 hpan hq
          · exact reaches_outcome_of_panicQF_PTight hsteps6 hpan
              (tryDecrypt_onPanicTight_of_afterCmk_cli htr herc hcmk hq)
      · exact reaches_outcome_of_panicQF_PTight hsteps5 hpan
          (onPanicTight_drop_frame (tryDecrypt_onPanicTight_of_afterCmk_cli htr herc hcmk hq))

/-- Full tight + weak-`pre` seam composition on `trTrapProgAt img.base C abs`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seamsQF_PTight_trap
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hPstk : ∀ sp0 : BitVec 64, rootStack ≤ sp0.toNat → Pstk (sp0 - 1504#64).toNat)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q Pstk F C A S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap img C A uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0SpecP_trap img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1SpecTight_trap img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec_trap img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3SpecTight_trap img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_trap img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_trap img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_trap img C A ctl uuidTryParse S abs)
    (herrT : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpecTight_trap img C A ctl uuidTryParse S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF_PTight Q F C A ctl uuidTryParse S img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF_PTight] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm] at hpre
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre_P hpre
  have hPstk0 : Pstk (s0.sp - 1504#64).toNat := hPstk s0.sp hstk
  obtain ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hoom⟩⟩ :=
    hs0 hloads hcallees.localIk hcallees.remoteIk hcallees.sameAcc x (F ∗ R) s0 hpc hrun hsp hpre hL
  rotate_left; · exact False.elim hoom
  refine Arm64.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 hloads hcallees.trFrom x (F ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact reaches_outcome_tryDecryptSpecQF_PTight_of_tight hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine Arm64.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step :=
        hs2 hloads hcallees.findReceiverChainKey x trG2 tr0 st1 (F ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        obtain ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
        rotate_left; · exact False.elim hoom
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          ensureReceiverChain_of_find_error hf
        have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact Arm64.reaches_outcome_steps hsteps2'
          (reaches_outcome_tryDecryptSpecQF_PTight_of_tight
            (herrT hloads hhooks hcallees.dropChain x trG2 tr0 st1 e (F ∗ R) s0 s2'
              hne hm1 hm2 herr_st))
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          obtain ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine Arm64.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF_PTight_trap
            hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr herrT
            hseeds hQ hPstk0 htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          obtain ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine Arm64.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 hloads hhooks hcallees.createChain hcallees.derivePk
            hcallees.pkSer hcallees.chainKeyToPb hcallees.growOne hcallees.dropChain
            x trG2 tr0 st1 (F ∗ R) s0 s3 htr hf htr_chains hstk hs3_state hL3
          dsimp only at hs3_step
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · exact Arm64.reaches_outcome_steps hsteps3'
                  (reaches_outcome_tryDecryptSpecQF_PTight_of_tight
                    (herrT hloads hhooks hcallees.dropChain x trG3 { tr0 with ratchet := r1' } st1 e
                      (F ∗ R) s0 s3' hne hm1 hm2 herr_st))
              · exact reaches_outcome_of_panicQF_PTight hsteps3' hpan (onPanicTight_drop_frame hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine Arm64.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF_PTight_trap
                  hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr herrT
                  hseeds hQ hPstk0 htr herc rfl hs4_state hL4
              · exact reaches_outcome_of_panicQF_PTight hsteps4 hpan (onPanicTight_drop_frame hq)

/-! ## 4. `tryDecryptPqV1_ok_PTight_trap` & Run Statement Corollaries -/

/-- Handshake `try_decrypt_with_state::<Coins>` meets
`tryDecryptSpecTPTight` at the trap-at-RNG program
`trTrapProgAt img.base C abs`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) := by
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap himg]
  have hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap
      (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (LibsignalSpqrV1.TokenInit img)
      C A (LibsignalSpqrV1.spqrV1 C.F K) abs img :=
    LibsignalSpqrV1.spqrRecvSpecXT_imp_spqrRecvSpec _ _ A C.F K img
      (CryptoVerification.Cli.SpqrV1.Top.Recv.spqr_recv_ok_trap C A K abs img hH hQ himg)
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seamsQF_PTight_trap
    (fun _ h => spqrRecvStack_le_sub_of_rootStack h)
    himg hH hrecv
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees_trap
      C A (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok_P_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_okT_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_trap
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_okT_trap
      img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s4_ok_trap
      img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s5_okQF_trap
      img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s6_ok_trap img C A ctl abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_trap
      img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok_trap
      img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok_trap
      img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok_trap
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_okT_trap

/-- `_trap` twin of `TryDecryptPqV1RunStmt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmt_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)

/-- `_trap` twin of `TryDecryptPqV1RunStmtP`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtP_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)

/-- Tight `_trap` counterpart of `TryDecryptPqV1RunStmtP` concluding `tryDecryptSpecTPTight`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPTight_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_P
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtP C A ctl K abs img := by
  intro hH hQ himg
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg]
  change subroutine_ok _ (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img) _
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr himg]
  exact subroutine_ok_mono
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight C A ctl K abs img hH hQ himg)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight_weaken h)
    (fun _ _ _ _ _ h => h)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_run_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPTight_trap C A ctl K abs img := by
  intro hH hQ himg
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap himg]
  change subroutine_ok _ (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img) _
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap himg]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_trap C A ctl K abs img hH hQ himg

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_P_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtP_trap C A ctl K abs img := by
  intro hH hQ himg
  exact subroutine_ok_mono
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_run_trap C A ctl K abs img hH hQ himg)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight_weaken h)
    (fun _ _ _ _ _ h => h)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmt_trap C A ctl K abs img := by
  intro hH hQ himg
  exact subroutine_ok_mono
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_P_trap C A ctl K abs img hH hQ himg)
    (fun _ _ _ h => CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP_pre_of_tryDecryptSpecT h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

/-! ## 5. CLI Corollaries (`tripleRatchetProgAtExt img.base (cliExterns W)`) -/

/-- CLI corollary (arbitrary `A`, `K` with hooks): transfers `tryDecryptPqV1_ok_PTight_trap`
from `trTrapProgAt` to the CLI program `tripleRatchetProgAtExt img.base (cliExterns W)` via
`Cli.Slots.subroutine_ok_cli_of_trTrap`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_cli_of_hooks
    (W : CryptoVerification.SignalSession.CliHooks) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (img : Obj.Image)
    (hH : TripleRatchetHooks W.C A (LibsignalSpqrV1.spqrV1 W.C.F K)
      (CryptoVerification.SignalSession.cliExterns W))
    (hQ : LibsignalSpqrV1.SpqrHooks W.C A K
      (CryptoVerification.SignalSession.cliExterns W))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      ((tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight W.C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F K) img) :=
  CryptoVerification.SignalSession.Cli.Slots.subroutine_ok_cli_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_trap
      W.C A ctl K (CryptoVerification.SignalSession.cliExterns W) img hH hQ himg)

/-- CLI corollary (`A := E2E.HooksE.A0`, `K := W.Q.K`): unconditional in `W : CliHooks` and
`Obj.Loads libsignalSessionImage img`, discharging `TripleRatchetHooks` and `SpqrHooks` via
`Cli.Slots.cliExterns_tripleRatchetHooks` and `Cli.Slots.cliExterns_spqrHooks`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_cli
    (W : CryptoVerification.SignalSession.CliHooks) (ctl : BitVec 64) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      ((tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight W.C
        CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_cli_of_hooks
    W CryptoVerification.E2E.HooksE.A0 ctl W.Q.K img
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_tripleRatchetHooks W
      (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_spqrHooks W)
    himg

/-- CLI corollary (`tryDecryptSpecTP`, `A := E2E.HooksE.A0`, `K := W.Q.K`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_P_cli
    (W : CryptoVerification.SignalSession.CliHooks) (ctl : BitVec 64) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      ((tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP W.C
        CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img) :=
  subroutine_ok_mono
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_cli W ctl img himg)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight_weaken h)
    (fun _ _ _ _ _ h => h)

/-- CLI corollary (`tryDecryptSpecT`, `A := E2E.HooksE.A0`, `K := W.Q.K`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_cli
    (W : CryptoVerification.SignalSession.CliHooks) (ctl : BitVec 64) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      ((tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT W.C
        CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img) :=
  subroutine_ok_mono
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_P_cli W ctl img himg)
    (fun _ _ _ h => CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP_pre_of_tryDecryptSpecT h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
