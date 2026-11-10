/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5

/-!
# Top-Level Stage Assembly for `signal_session_handshake::initiate`

Composes `signal_session_coins_fill`, the store and local callee bundles, and Stages 1–5 across
`AtInitEntry` and `AtStage2`..`AtStage5` to establish `initSlotSpec` on both `initProg img W`
(`cliInitiate_ok_proof`) and `initProgExt img ext` (`cliInitiate_ext_ok_of_stages`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Top-level `initiate` slot theorem on `tripleRatchetProgAtExt img.base (cliExterns W)`. -/
theorem cliInitiate_ok_proof {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliInitiateName)
      (initSlotSpec A img S stk) := by
  have hStore : InitStoreCallees img A W B stk :=
    initStoreCallees_ok W B himg hh hRead stk hstk hstk64
  have hLocal : InitLocalCallees img A W stk :=
    initLocalCallees_ok W B himg hh stk hstk hstk64
  have hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk) :=
    fun hc1 hc2 => signal_session_coins_fill_ok W himg hh hc1 hc2
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc hrun0 hpre hal
  simp only [initSlotSpec, Spec.inImage, slotFrame, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hF, hsym⟩,
    ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfs0, hfilesOk, hsInitOk, hspk⟩,
    hcoinsLt, hm⟩ := hpre
  have hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val :=
    hok x.F x.peer.val x.me.val hfilesOk hsInitOk
  have hs0 : AtInitEntry img W x s0 :=
    { pc := hpc
      run := hrun0
      inv := ⟨hF, hsym⟩
      spAligned := hal
      x0 := hx0
      x1 := hx1
      x2 := hx2
      x3 := hx3
      x4 := hx4
      x5 := hx5
      x6 := hx6
      x7 := hx7
      x8 := hx8
      files := hfs0 }
  refine ⟨initEntryMem A img x stk s0, ?_, ?_⟩
  · simpa only [initEntryMem, sepConj_assoc] using hm
  · have hpostK : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf →
        (((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpec A img S stk).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
      intro sf Pf ⟨hsp, hcs, hent⟩
      exact ⟨fun hmPf => Satisfies.mono (sepConj_mono_left hent) hmPf, hsp, hcs⟩
    have hpanicK : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf →
        ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpec A img S stk).onPanic x s0 sf ∗ R)) := by
      intro sf Pf hent hmPf
      exact Satisfies.mono (sepConj_mono_left hent) hmPf
    exact initiate_stage1_ok himg hh hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs0
      hpostK hpanicK fun s2 be hs2 =>
        initiate_stage2_ok himg hh hCoins hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs2
          hpostK hpanicK fun s3 kp ekASk ekAPk pqspkPtr opkId hs3 =>
            initiate_stage3_ok himg hh hCoins hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs3
              hpostK hpanicK fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr hs4 =>
                initiate_stage4_ok himg hh hCoins hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs4
                  hpostK hpanicK fun s5 sg ss hs5 =>
                    initiate_stage5_ok himg hh hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs5
                      hpostK hpanicK

/-! ## Extern-parameterized stage assembly -/

/-- Assembles Stages 1–5 with `signal_session_coins_fill_ext_ok` and `initStoreCallees_ext_ok`
into `initSlotSpec A img S stk` on `initProgExt img ext`. -/
theorem cliInitiate_ext_ok_of_stages {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hd : StoreExtDeps img A P (cliExternsWith ext) B stk)
    (hS : S.initiate = initDef X P)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ P F peer me)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hStage1 : ∀ {x : InitGhost} {s0 : State} {Q Qp : State → SepProp → Prop},
      InitStoreCalleesExt img A (cliExternsWith ext) B stk →
      InitOk₀ P x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      AtInitEntryExt img ext x s0 →
      (∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) →
      (∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) →
      (∀ (s2 : State) (be : PreKeyBundleFields),
        AtStage2Ext img P ext X x be s0 s2 →
        SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
          (stage2Mem A img x stk s0) Q Qp (initOom s0)) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s0
        (initEntryMem A img x stk s0) Q Qp (initOom s0))
    (hStage2 : ∀ {x : InitGhost} {be : PreKeyBundleFields} {s0 s2 : State} {Q Qp : State → SepProp → Prop},
      (∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
        subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
          (coinsFillSpec img cStk)) →
      InitStoreCalleesExt img A (cliExternsWith ext) B stk →
      InitOk₀ P x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      AtStage2Ext img P ext X x be s0 s2 →
      (∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) →
      (∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) →
      (∀ (s3 : State) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
          (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32),
        AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
        SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
          (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0))
    (hStage3 : ∀ {x : InitGhost} {be : PreKeyBundleFields}
        {kp : CryptoVerification.RecordCodecs.IdentityKeyPair}
        {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
        {s0 s3 : State} {Q Qp : State → SepProp → Prop},
      (∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
        subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
          (coinsFillSpec img cStk)) →
      InitOk₀ P x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      (∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) →
      (∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) →
      (∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
          (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
        AtStage4Ext img P ext X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr
          kemCtPtr opkId s0 s4 →
        SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
          (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
          Q Qp (initOom s0)) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
        (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0))
    (hStage4 : ∀ {x : InitGhost} {be : PreKeyBundleFields}
        {kp : CryptoVerification.RecordCodecs.IdentityKeyPair}
        {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
        {kemCtBytes hkSlotBytes : List (BitVec 8)} {pqspkPtr kemCtPtr : BitVec 64}
        {opkId : BitVec 32} {s0 s4 : State} {Q Qp : State → SepProp → Prop},
      (∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
        subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
          (coinsFillSpec img cStk)) →
      InitOk₀ P x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      AtStage4Ext img P ext X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
        opkId s0 s4 →
      (∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) →
      (∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) →
      (∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8))),
        AtStage5Ext img P ext X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
        SepWPp (initProgExt img ext) (s0.readReg64 .lr) s5
          (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0) Q Qp (initOom s0)) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0))
    (hStage5 : ∀ {x : InitGhost} {be : PreKeyBundleFields}
        {kp : CryptoVerification.RecordCodecs.IdentityKeyPair}
        {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
        {pqspkPtr : BitVec 64} {opkId : BitVec 32}
        {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
        {s0 s5 : State} {Q Qp : State → SepProp → Prop},
      InitStoreCalleesExt img A (cliExternsWith ext) B stk →
      InitOk₀ P x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      AtStage5Ext img P ext X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      (∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) →
      (∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s5
        (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0) Q Qp (initOom s0)) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliInitiateName)
      (initSlotSpec A img S stk) := by
  let _ := hS
  have hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk :=
    initStoreCallees_ext_ok B himg hd hstk hstk64
  have hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk) :=
    fun hc1 hc2 => signal_session_coins_fill_ext_ok himg hOk hc1 hc2
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc hrun0 hpre hal
  simp only [initSlotSpec, Spec.inImage, slotFrame, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hF, hsym⟩,
    ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfs0, hfilesOk, hsInitOk, hspk⟩,
    hcoinsLt, hm⟩ := hpre
  have hinitOk : InitOk₀ P x.F x.peer.val x.me.val :=
    hok x.F x.peer.val x.me.val hfilesOk hsInitOk
  have hs0 : AtInitEntryExt img ext x s0 :=
    { pc := hpc
      run := hrun0
      inv := ⟨hF, hsym⟩
      spAligned := hal
      x0 := hx0
      x1 := hx1
      x2 := hx2
      x3 := hx3
      x4 := hx4
      x5 := hx5
      x6 := hx6
      x7 := hx7
      x8 := hx8
      files := hfs0 }
  refine ⟨initEntryMem A img x stk s0, ?_, ?_⟩
  · simpa only [initEntryMem, sepConj_assoc] using hm
  · have hpostK : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf →
        (((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpec A img S stk).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
      intro sf Pf ⟨hsp, hcs, hent⟩
      exact ⟨fun hmPf => Satisfies.mono (sepConj_mono_left hent) hmPf, hsp, hcs⟩
    have hpanicK : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf →
        ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpec A img S stk).onPanic x s0 sf ∗ R)) := by
      intro sf Pf hent hmPf
      exact Satisfies.mono (sepConj_mono_left hent) hmPf
    exact hStage1 hStore hinitOk hcoinsLt hspk hs0 hpostK hpanicK fun s2 be hs2 =>
      hStage2 @hCoins hStore hinitOk hcoinsLt hspk hs2 hpostK hpanicK
        fun s3 kp ekASk ekAPk pqspkPtr opkId hs3 =>
          hStage3 @hCoins hinitOk hcoinsLt hspk hs3 hpostK hpanicK
            fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr hs4 =>
              hStage4 @hCoins hinitOk hcoinsLt hspk hs4 hpostK hpanicK fun s5 sg ss hs5 =>
                hStage5 hStore hinitOk hcoinsLt hspk hs5 hpostK hpanicK

/-- Specializes an extern-parameterized `cliInitiate_ext_ok` witness to `cliExterns W` at `HooksE.A0`. -/
theorem cliInitiate_ok_of_ext
    (hExt : ∀ {img : Obj.Image} {P : PEParams} {A : RustAlloc}
      {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem),
      Obj.Loads libsignalSessionImage img →
      CliExternsOk P A ext →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr Cli.readFileName)
        (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
      S.initiate = initDef X P →
      (∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ P F peer me) →
      ∀ stk : Nat, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
        subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliInitiateName)
          (initSlotSpec A img S stk))
    {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk HooksE.A0 img B.readFile))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliInitiateName)
      (initSlotSpec HooksE.A0 img S stk) :=
  hExt (ext := cliHookExterns W) X B S himg (cliExterns_ok W) hRead hS hok stk hstk hstk64

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
