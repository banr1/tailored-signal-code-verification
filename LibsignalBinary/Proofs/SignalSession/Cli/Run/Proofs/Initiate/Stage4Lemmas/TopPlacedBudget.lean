/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSessionPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExitPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqr
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 4 Top-Level Composition (`[LibsignalPlacement]`)

Composes the budget-threaded Stage 4 segments (`+4260 → +5252` and early `create_chain` error exit
`+4508 → RET`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlacedBudget

open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  InitExitPostPlaced InitPanicPostPlaced InitLocalCalleesPlaced RunHooksPlaced
  coinsFillSpecPlacedW3 stage2MemPlaced stage3MemPlaced stage4MemPlaced stage5MemPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas hiding
  errExitMemPlaced initiate_stage4_placed_ok_impl
  panic_oom_entails_initOnPanic_placed panic_oom_only_entails_initOnPanic_placed
  stage4_branch_4496_err_placed stage4_branch_4496_ok_placed
  stage4_err_exit_placed stage4_step_prechain_to_4496_placed
  stage4_step_session_placed stage4_step_spqr_placed
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage4MemPlaced stage5MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExitPlacedBudget
  (errExitMemPlaced stage4ErrExitEvents stage4_err_exit_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudget
  (stage4PreChainEvents stage4_branch_4496_err_placed stage4_branch_4496_ok_placed
   stage4_step_prechain_to_4496_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSessionPlacedBudget
  (stage4StepSessionEvents stage4_step_session_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
  (stage4_step_spqr_placed)

s4_clean_sp_attrs

private theorem padCoins_take32_len (coins : List (BitVec 8)) :
    ((padCoins coins).toList.take 32).length = 32 := by simp; decide

private theorem ofU8_toU8_id : ∀ (bs : List (BitVec 8)), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (ofU8_toU8_id rest)

private theorem u8Vec_toU8_vec {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (toU8 v.toList) = v := by
  apply Subtype.ext
  show ((ofU8 (toU8 v.toList) ++ List.replicate n 0#8).take n) = v.toList
  rw [ofU8_toU8_id, List.take_append_of_le_length (by rw [v.toList_length]),
      List.take_of_length_le (by rw [v.toList_length])]

private theorem baseKey_bytes_eq_ekAPk_ext {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {kp : IdentityKeyPair} {be : PreKeyBundleFields} {coins : List (BitVec 8)}
    {ekAPk : List (BitVec 8)} {hdrEkAPk : List UInt8}
    (hekPair : ekAPk = (keyPairOf P.C ⟨(padCoins coins).toList.take 32, padCoins_take32_len coins⟩).publicKey.bytes.toList)
    (hhdr : hdrEkAPk = (modelPrims X P).x25519Base
      (initiateInput P ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk) :
    ekAPk = (PublicKey.mk (u8Vec 32 hdrEkAPk)).bytes.toList := by
  subst hekPair hhdr
  let v : List.Vector (BitVec 8) 32 := ⟨(padCoins coins).toList.take 32, padCoins_take32_len coins⟩
  change (P.C.pubKey (Ratchet.clampScalar v)).toList =
    (u8Vec 32 (toU8 (P.C.pubKey (Ratchet.clampScalar (u8Vec 32 (toU8 v.toList)))).toList)).toList
  rw [u8Vec_toU8_vec v, u8Vec_toU8_vec (P.C.pubKey (Ratchet.clampScalar v))]

private theorem baseKey_bytes_eq_ekAPk {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {kp : IdentityKeyPair} {be : PreKeyBundleFields} {coins : List (BitVec 8)}
    {ekAPk : List (BitVec 8)} {hdrEkAPk : List UInt8}
    (hekPair : ekAPk = (keyPairOf W.C ⟨(padCoins coins).toList.take 32, padCoins_take32_len coins⟩).publicKey.bytes.toList)
    (hhdr : hdrEkAPk = (modelPrims X ⟨W.C, W.Q⟩).x25519Base
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk) :
    ekAPk = (PublicKey.mk (u8Vec 32 hdrEkAPk)).bytes.toList :=
  baseKey_bytes_eq_ekAPk_ext (P := ⟨W.C, W.Q⟩) hekPair hhdr

/-- Total allocator events along Stage 4's early `Err(.invalidKeyAgreement)` exit (`+4260 → RET`). -/
def stage4ErrTotalEvents (W : CliHooks) (x : InitGhost) : List AllocEvent :=
  stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins)) ++
    stage4ErrExitEvents

/-- Total allocator events along Stage 4's `Ok` path (`+4260 → +5252`) for SPQR trace `evsSpqr`. -/
def stage4OkTotalEvents (W : CliHooks) (x : InitGhost) (evsSpqr : List AllocEvent) :
    List AllocEvent :=
  stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins)) ++
    evsSpqr ++ stage4StepSessionEvents

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem initiate_stage4_placed_ok_impl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsPreChain : FitsEvents M lim st
      (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))))
    (hFitsSpqr : ∀ (rk1 : RootKey) (ck1 : ChainKey),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      FitsEnv M lim
        (M.stepEvents
          (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st)
        (InitStateEnv
          (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
            (bytesToKey32 (ofU8 dk.pqrKey)))))
    (hFitsSess : ∀ (rk1 : RootKey) (ck1 : ChainKey) (evsSpqr : List AllocEvent),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      FitsEvents M lim
        (M.stepEvents evsSpqr
          (M.stepEvents
            (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st))
        stage4StepSessionEvents)
    (hEnvErr :
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .error .invalidKeyAgreement →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (stage4ErrTotalEvents W x) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
      opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
        (evsSpqr : List AllocEvent),
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
        (stage5MemPlaced A lim (M.stepEvents (stage4OkTotalEvents W x evsSpqr) st)
          x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
      (stage4MemPlaced A lim st x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
      Q Qp oom := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hfsp_eq : Hide (s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp) := ⟨rfl⟩
  have hfiles_s0 : s0.fs.files = x.F := hs4.ctrl.files0.symm.trans hs4.files
  obtain ⟨hkpkLen, hspk_eq, hidB_eq⟩ := bundleEOf_props hs4.bundleEq
  have hidA_eq : (⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ : IdentityKey) = kp.identityKey :=
    idKey_eq_of_publicKey_eq (hinitOk.idPairDerived kp hs4.kpOk)
  obtain ⟨hrk_bv, hpq_bv, hck_bv, hek_hdr⟩ := dk_lengths_of_keysOk hs4.keysOk
  have hekASk_len : ekASk.length = 32 := by
    rw [hs4.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPk_len : ekAPk.length = 32 := by
    rw [hs4.ekPairEq.2]; exact List.Vector.toList_length _
  let baseKey : PublicKey := PublicKey.mk (u8Vec 32 hdr.ekAPk)
  have hbaseKey_def : Hide (baseKey = PublicKey.mk (u8Vec 32 hdr.ekAPk)) := ⟨rfl⟩
  have hbase_eq : ekAPk = baseKey.bytes.toList :=
    baseKey_bytes_eq_ekAPk hs4.ekPairEq.2 hek_hdr
  have hhk_append : hkSlotBytes =
      ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32 :=
    hs4.hkSlotEq.trans (hkSlotBytes_eq_append dk)
  conv => arg 4; unfold stage4MemPlaced; dsimp (config := { proj := false }) only; rw [hfsp_eq.val]
  clear_value fsp
  s4_pure_elim
  rintro ⟨hkem_len, _hhk_len⟩
  have h4064_split :
      memRegion (fsp + 4064#64) 344 =
        memRegion (fsp + 4064#64) 32 ∗ memRegion (fsp + 4096#64) 312 :=
    ProofLib.memRegion_split' (b := fsp + 4064#64) (n := 32) (k := 312)
      (b' := fsp + 4096#64) rfl (by bv_omega) (by decide)
  have h5632_split :
      memRegion (fsp + 5632#64) 344 =
        memRegion (fsp + 5632#64) 72 ∗ memRegion (fsp + 5704#64) 272 :=
    ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 72) (k := 272)
      (b' := fsp + 5704#64) rfl (by bv_omega) (by decide)
  conv => arg 4; rw [stage4Locals_carve_5ba fsp, stage4Locals_carve_994 fsp, h4064_split, h5632_split]
  conv => arg 4; unfold stage3KeySlotsAt; dsimp (config := { proj := false }) only
  let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
  let keySlotsRest : SepProp :=
    ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
      memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      (A.repAlloc).live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ x.bundle.kpk) ∗
      ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ∗
      memRegion (fsp + 0x45a#64) 6
  let outerFixed : SepProp :=
    storesAt A.repAlloc x.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc x.peer x.peerA ∗
      protocolAddressAt A.repAlloc x.me x.meA ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗
      memRegion x.ret 48 ∗
      initSaved s0 ∗
      memRegion fsp 0x60 ∗
      memRegion (fsp + 0x80#64) 0x50 ∗
      initArgsAtPlaced fsp x s0 ∗
      initFreshRecAt fsp ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8)
  let PrechainFrame : SepProp :=
    outerFixed ∗
      keySlotsRest ∗
      ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
      A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ kemCtBytes) ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
      ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      FromRecordCallees.lsLogOff ∗
      stage4IdleSlots fsp ∗
      memRegion (fsp + 1904#64) 288 ∗
      memRegion (fsp + 2336#64) 16 ∗
      memRegion (fsp + 4096#64) 312 ∗
      memRegion (fsp + 5704#64) 272 ∗
      memRegion (fsp + 7232#64) 32 ∗
      memRegion (fsp + 7264#64) 24
  refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
    (sepWPp_mono_pre
      (by
        dsimp (config := { proj := false }) only [PrechainFrame, outerFixed, keySlotsRest,
          stage4IdleSlots, opkFlag]
        rw [hfsp_eq.val]
        exact Entails.of_eq (by rcases x.bundle.opk with _ | ⟨_, _⟩ <;> dsimp only <;> s4_ac_rfl))
      (stage4_step_prechain_to_4496_placed (A := A) (lim := lim) (st := st) (Frame := PrechainFrame)
        hstk hstk64 hspk hh hCoins hLocal hcoinsLt hFitsPreChain
        hs4.ctrl hs4.trace hs4.x20 hs4.x21 hs4.x22 hrk_bv hpq_bv hck_bv hhk_append)) ?_
  rintro s4a P4a _ _ _ ⟨htr4a, hctrl4a, hx20_4a, hx21_4a, hx22_4a, hx25_4a, hent4a⟩
  rw [hfsp_eq.val] at hx20_4a hx21_4a hx22_4a hx25_4a hent4a
  set ephClamped : List.Vector (BitVec 8) 32 := Ratchet.clampScalar (stage4EphVec x.coins)
  set rk0 : RootKey := bytesToKey32 (ofU8 dk.rootKey)
  set ck0 : BitVec 256 := bytesToKey32 (ofU8 dk.chainKey)
  set pqrKey : BitVec 256 := bytesToKey32 (ofU8 dk.pqrKey)
  have hephClamped_def : Hide (ephClamped = Ratchet.clampScalar (stage4EphVec x.coins)) := ⟨rfl⟩
  have hrk0_def : Hide (rk0 = bytesToKey32 (ofU8 dk.rootKey)) := ⟨rfl⟩
  have hck0_def : Hide (ck0 = bytesToKey32 (ofU8 dk.chainKey)) := ⟨rfl⟩
  have hpqrKey_def : Hide (pqrKey = bytesToKey32 (ofU8 dk.pqrKey)) := ⟨rfl⟩
  have hclamp_idem_eph : Ratchet.clampScalar ephClamped = ephClamped := by
    rw [hephClamped_def.val]
    exact clampScalar_idem (stage4EphVec x.coins)
  let st1 := M.stepEvents (stage4PreChainEvents W.C x.bundle.spk ephClamped) st
  have hst1_def : Hide (st1 = M.stepEvents (stage4PreChainEvents W.C x.bundle.spk ephClamped) st) :=
    ⟨rfl⟩
  clear_value baseKey ephClamped rk0 ck0 pqrKey st1
  let Post4496Frame : SepProp :=
    coinsCursorAtPlaced x.coinsP x.coins 192 ∗
      ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0) ∗
      ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
      memRegion (fsp + 2352#64) 100 ∗
      ((fsp + 2496#64) ↦ₛ (W.C.pubKey ephClamped).toList) ∗
      ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗
      memRegion (fsp + 4064#64) 32 ∗
      stackAt fsp (stk - cliInitiateFrame) ∗
      PrechainFrame
  rcases rootCreateChain_ok_or_err W.C rk0 x.bundle.spk ⟨ephClamped⟩ with
    ⟨rk1, ck1, hcc_ok⟩ | hcc_err
  · have hFitsSpqr' :
        FitsEnv M lim st1
          (InitStateEnv (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b pqrKey)) := by
      rw [hst1_def.val]
      exact hFitsSpqr rk1 ck1 hcc_ok
    have hck1_idx : ck1.index = 0#32 := chainKey_index_of_rootCreateChain_ok hcc_ok
    rw [hcc_ok] at hent4a
    dsimp only [createChainResultAt] at hent4a
    simp (config := { zeta := false }) only [BitVec.add_assoc, BitVec.reduceAdd] at hent4a
    refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
      (sepWPp_mono_pre
        (by
          refine Entails.trans hent4a ?_
          dsimp (config := { proj := false }) only [Post4496Frame]
          rw [hfsp_eq.val, ← hst1_def.val]
          exact Entails.of_eq (by s4_ac_rfl))
        (stage4_branch_4496_ok_placed (A := A) (lim := lim) (st := st1)
          (rk1 := rk1) (ck1 := ck1) (Frame := Post4496Frame)
          hstk hspk hctrl4a htr4a
          (by rw [hfsp_eq.val]; exact hx20_4a)
          (by rw [hfsp_eq.val]; exact hx21_4a)
          (by rw [hfsp_eq.val]; exact hx22_4a)
          (by rw [hfsp_eq.val]; exact hx25_4a))) ?_
    rintro s4b P4b _ _ _ ⟨htr4b, hctrl4b, hx20_4b, hx21_4b, hx22_4b, hx25_4b, hent4b⟩
    rw [hfsp_eq.val] at hx20_4b hx21_4b hx22_4b hx25_4b hent4b
    let sendingKeyPair : KeyPair :=
      { publicKey := ⟨W.C.pubKey ephClamped⟩
        privateKey := ⟨ephClamped⟩ }
    have hclamp_sk :
        Ratchet.clampScalar sendingKeyPair.privateKey.bytes = sendingKeyPair.privateKey.bytes :=
      hclamp_idem_eph
    have h2352_20_80 :
        memRegion (fsp + 2352#64) 100 =
          memRegion (fsp + 2352#64) 20 ∗ memRegion (fsp + 2372#64) 80 :=
      ProofLib.memRegion_split' (b := fsp + 2352#64) (n := 20) (k := 80)
        (b' := fsp + 2372#64) rfl (by bv_omega) (by decide)
    have h2336_36 :
        memRegion (fsp + 2336#64) 36 =
          memRegion (fsp + 2336#64) 16 ∗ memRegion (fsp + 2352#64) 20 :=
      ProofLib.memRegion_split' (b := fsp + 2336#64) (n := 16) (k := 20)
        (b' := fsp + 2352#64) rfl (by bv_omega) (by decide)
    have hstk_spqr := stackAt_fsp_split hstk hstk64 fsp
      CryptoVerification.SpqrV1.Top.InitialState.initialStateStack (by decide)
    let RestSess : SepProp :=
      outerFixed ∗
        keySlotsRest ∗
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        memRegion (fsp + 2192#64) 24 ∗
        ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
        memRegion (fsp + 2372#64) 80 ∗
        stage4IdleSlots fsp
    let SpqrFrame : SepProp :=
      stackAt (fsp - BitVec.ofNat 64 CryptoVerification.SpqrV1.Top.InitialState.initialStateStack)
          (stk - cliInitiateFrame - CryptoVerification.SpqrV1.Top.InitialState.initialStateStack) ∗
        ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗
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
        ((fsp + 2496#64) ↦ₛ sendingKeyPair.publicKey.bytes.toList) ∗
        ((fsp + 2528#64) ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
        memRegion (fsp + 4096#64) 312 ∗
        memRegion (fsp + 5704#64) 272 ∗
        memRegion (fsp + 7264#64) 24 ∗
        outerFixed ∗
        keySlotsRest ∗
        coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        memRegion (fsp + 2192#64) 24 ∗
        ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0) ∗
        memRegion (fsp + 2372#64) 80 ∗
        stage4IdleSlots fsp
    refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
      (sepWPp_mono_pre
        (by
          refine Entails.trans hent4b ?_
          dsimp (config := { proj := false }) only [Post4496Frame, PrechainFrame, SpqrFrame,
            sendingKeyPair]
          rw [hfsp_eq.val, h2352_20_80, hstk_spqr, h2336_36]
          exact Entails.of_eq (by s4_ac_rfl))
        (stage4_step_spqr_placed (A := A) (lim := lim) (st := st1)
          (rk1 := rk1) (ck1 := ck1) (pqrKey := pqrKey) (Frame := SpqrFrame)
          hstk hstk64 hspk hLocal.spqrChainParams hLocal.spqrInitialState hFitsSpqr'
          hctrl4b htr4b
          (by rw [hfsp_eq.val]; exact hx20_4b)
          (by rw [hfsp_eq.val]; exact hx21_4b)
          (by rw [hfsp_eq.val]; exact hx22_4b)
          (by rw [hfsp_eq.val]; exact hx25_4b) hck1_idx))
      ?_
    rintro s4c P4c _ _ _ ⟨evsSpqr, hevsSpqr, htr4c, hctrl4c, hx20_4c, hx21_4c, hent4c⟩
    rw [hfsp_eq.val] at hx20_4c hx21_4c hent4c
    have hFitsSess' :
        FitsEvents M lim (M.stepEvents evsSpqr st1) stage4StepSessionEvents := by
      rw [hst1_def.val]
      exact hFitsSess rk1 ck1 evsSpqr hcc_ok hevsSpqr
    refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
      (sepWPp_mono_pre
        (by
          refine Entails.trans hent4c ?_
          dsimp (config := { proj := false }) only [SpqrFrame, RestSess]
          rw [hfsp_eq.val, hstk_spqr, h5632_split]
          exact Entails.of_eq (by s4_ac_rfl))
        (stage4_step_session_placed (A := A) (lim := lim) (x := x) (st := M.stepEvents evsSpqr st1)
          (kp := kp) (rk1 := rk1) (ck0 := ck0) (pqrKey := pqrKey)
          (sendingKeyPair := sendingKeyPair) (ck1 := ck1) (Frame := RestSess)
          hstk hstk64 hspk hh.alloc hLocal.sessionStateNew hLocal.withReceiverChain
          hLocal.withSenderChain hLocal.setKyberCiphertext hFitsSess' hctrl4c htr4c
          (by rw [hfsp_eq.val]; exact hx20_4c)
          (by rw [hfsp_eq.val]; exact hx21_4c)
          hbase_eq hclamp_sk hck1_idx hkem_len hs4.kemCtNonNull))
      ?_
    rintro s5 P5 _ _ _
      ⟨sg, htr5, hctrl5, hx20_5,
        ⟨hcan_lik, hcan_rik, hcan_alice, hcan_pend, ⟨kg, hkg_eq, hkg_bytes⟩, hcan_send, hcan_recv⟩,
        hent5⟩
    rw [hfsp_eq.val] at hx20_5 hent5
    set pq : List (BitVec 8) := (pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b pqrKey
    let ss := stage5SessionState kp.identityKey x.bundle.idKey x.bundle.spk rk1 ck0
      sendingKeyPair ck1 pq
    have hinit_sess :
        initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
          ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
          (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
          (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss := by
      rw [hidA_eq, hidB_eq, hspk_eq, ← hrk0_def.val, ← hck0_def.val, ← hpqrKey_def.val]
      dsimp only [ss, pq, sendingKeyPair]
      rw [hephClamped_def.val] at hcc_ok ⊢
      exact initializeInitiatorSession_eq_ok_stage5 W kp.identityKey x.bundle.idKey x.bundle.spk
        rk0 ck0 pqrKey x.coins rk1 ck1 hcc_ok
    have hpq_le : ss.pqRatchetState.length ≤ 1208 :=
      spqrInitialState_pqLen_le_1208 W.C.F W.Q.K pqrKey
    have hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 :=
      { ctrl := hctrl5
        trace := htr5
        files := hctrl5.files0.trans hfiles_s0
        x8 := hs4.x8
        bundleEq := hs4.bundleEq
        trustedOk := hs4.trustedOk
        kpOk := hs4.kpOk
        ekPairEq := hs4.ekPairEq
        opkIdEq := hs4.opkIdEq
        keysOk := hs4.keysOk
        initSessOk := hinit_sess
        pqLen := hpq_le
        canonPre := ⟨hcan_lik, hcan_rik, hbaseKey_def.val ▸ hcan_alice, hcan_pend,
          ⟨kg, hkg_eq, hkg_bytes.trans hs4.kemCtEq⟩, hcan_send, hcan_recv⟩
        pqspkNonNull := hs4.pqspkNonNull
        x20 := by rw [hfsp_eq.val]; exact hx20_5 }
    have hst5_eq :
        M.stepEvents stage4StepSessionEvents (M.stepEvents evsSpqr st1) =
          M.stepEvents (stage4OkTotalEvents W x evsSpqr) st := by
      rw [hst1_def.val, hephClamped_def.val]
      simp only [stage4OkTotalEvents, AllocCostModel.stepEvents, List.foldl_append]
    refine sepWPp_mono_pre
      (by
        refine Entails.trans hent5 ?_
        dsimp (config := { proj := false }) only [RestSess, outerFixed, keySlotsRest, opkFlag]
        unfold stage5MemPlaced stage3KeySlotsAt
        dsimp (config := { proj := false }) only
        rw [hfsp_eq.val, hst5_eq, ← stage4Locals_merge_5ba fsp]
        have hpref0xd0 := stage4Prefix_0xd0_merge fsp kemCtPtr (fsp + 0x408#64) (fsp + 0x3c8#64)
        have h2224_m := pointsToBytes32_entails_memRegion32 (fsp + 2224#64)
          (by simp [keyToBytes32] : (keyToBytes32 rk0).length = 32)
        have h2304_m := pointsToBytes32_entails_memRegion32 (fsp + 2304#64)
          (by simp [keyToBytes32] : (keyToBytes32 pqrKey).length = 32)
        s4_fold_ent hpref0xd0
        s4_fold_ent h2224_m
        s4_fold_ent h2304_m
        exact Entails.of_eq (by rcases x.bundle.opk with _ | ⟨_, _⟩ <;> dsimp only <;> s4_ac_rfl))
      (hnext s5 sg ss evsSpqr hevsSpqr hs5)
  · have hcc_err_raw :
        rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .error .invalidKeyAgreement := by
      simpa only [← hrk0_def.val, ← hephClamped_def.val] using hcc_err
    obtain ⟨evsErr, hEnv, hst_err0⟩ := hEnvErr hcc_err
    have hst_err : M.stepEvents stage4ErrExitEvents st1 = M.stepEvents evsErr st0 := by
      rw [hst1_def.val, hephClamped_def.val]
      simpa only [stage4ErrTotalEvents, AllocCostModel.stepEvents, List.foldl_append] using hst_err0
    rw [hcc_err] at hent4a
    dsimp only [createChainResultAt] at hent4a
    simp (config := { zeta := false }) only [BitVec.add_assoc, BitVec.reduceAdd] at hent4a
    refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
      (sepWPp_mono_pre
        (by
          refine Entails.trans hent4a ?_
          dsimp (config := { proj := false }) only [Post4496Frame]
          rw [hfsp_eq.val, ← hst1_def.val]
          exact Entails.of_eq (by s4_ac_rfl))
        (stage4_branch_4496_err_placed (A := A) (lim := lim) (st := st1)
          (Frame := Post4496Frame) hstk hspk hctrl4a htr4a)) ?_
    rintro s4e P4e _ _ _ ⟨htr4e, hctrl4e, hent4e⟩
    rw [hfsp_eq.val] at hent4e
    have herr_sem : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_createChain_err hs4.bundleEq hs4.trustedOk hs4.kpOk hs4.keysOk
        (by rw [hspk_eq]; exact hcc_err_raw)
    let Rest5ba : SepProp :=
      stage4IdleSlots fsp ∗
        memRegion (fsp + 1904#64) 288 ∗
        memRegion (fsp + 2192#64) 24 ∗
        memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗
        memRegion (fsp + 2304#64) 32 ∗
        memRegion (fsp + 2336#64) 16 ∗
        memRegion (fsp + 2352#64) 100 ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗
        memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 4096#64) 312 ∗
        ((fsp + 5632#64) ↦₃₂ 1#32) ∗
        memRegion (fsp + 5636#64) 4 ∗
        memRegion (fsp + 5688#64) 16 ∗
        memRegion (fsp + 5704#64) 272 ∗
        memRegion (fsp + 7232#64) 32 ∗
        memRegion (fsp + 7264#64) 24
    let Leak : SepProp :=
      coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt
    refine sepWPp_mono_pre
      (by
        refine Entails.trans hent4e ?_
        unfold errExitMemPlaced stage3KeySlotsAt
        dsimp (config := { proj := false }) only [Post4496Frame, PrechainFrame, Rest5ba, Leak,
          outerFixed, keySlotsRest, opkFlag]
        rw [hfsp_eq.val]
        have hkem_mem : (kemCtPtr ↦ₛ kemCtBytes) ⊢ memRegion kemCtPtr 1569 :=
          hkem_len ▸ pointsToBytes_entails_memRegion kemCtPtr kemCtBytes
        have h2224_m := pointsToBytes32_entails_memRegion32 (fsp + 2224#64)
          (by simp [keyToBytes32] : (keyToBytes32 rk0).length = 32)
        have h2256_m := keyAndIdx_entails_memRegion36 (fsp + 2256#64) ck0 0#32
        have h2304_m := pointsToBytes32_entails_memRegion32 (fsp + 2304#64)
          (by simp [keyToBytes32] : (keyToBytes32 pqrKey).length = 32)
        have h2496_m := pointsToBytes32_entails_memRegion32 (fsp + 2496#64)
          (List.Vector.toList_length (W.C.pubKey ephClamped))
        have h2528_m := pointsToBytes32_entails_memRegion32 (fsp + 2528#64)
          (List.Vector.toList_length ephClamped)
        simp (config := { zeta := false }) only [BitVec.add_assoc, BitVec.reduceAdd] at h2256_m
        s4_fold_ent hkem_mem
        s4_fold_ent h2224_m
        s4_fold_ent h2256_m
        s4_fold_ent h2304_m
        s4_fold_ent h2496_m
        s4_fold_ent h2528_m
        exact Entails.of_eq (by rcases x.bundle.opk with _ | ⟨_, _⟩ <;> dsimp only <;> s4_ac_rfl))
      (stage4_err_exit_placed (A := A) (lim := lim) (st0 := st0) (st := st1) (evs := evsErr)
        (kp := kp) (w70 := fsp + 0x408#64) (w78 := fsp + 0x3c8#64) (opkId := opkId)
        (Rest5ba := Rest5ba) (Leak := Leak)
        hstk hstk64 hspk hh hEnv hst_err hpost hctrl4e htr4e hs4.x8
        hekAPk_len hekASk_len hkpkLen hs4.pqspkNonNull hs4.kemCtNonNull herr_sem
        (by rw [hfsp_eq.val]; exact err_rest5ba_merge fsp))

theorem initiate_stage4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsPreChain : FitsEvents M lim st
      (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))))
    (hFitsSpqr : ∀ (rk1 : RootKey) (ck1 : ChainKey),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      FitsEnv M lim
        (M.stepEvents
          (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st)
        (InitStateEnv
          (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
            (bytesToKey32 (ofU8 dk.pqrKey)))))
    (hFitsSess : ∀ (rk1 : RootKey) (ck1 : ChainKey) (evsSpqr : List AllocEvent),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      FitsEvents M lim
        (M.stepEvents evsSpqr
          (M.stepEvents
            (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st))
        stage4StepSessionEvents)
    (hEnvErr :
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .error .invalidKeyAgreement →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (stage4ErrTotalEvents W x) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
      opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (_hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
        (evsSpqr : List AllocEvent),
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
        (stage5MemPlaced A lim (M.stepEvents (stage4OkTotalEvents W x evsSpqr) st)
          x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
      (stage4MemPlaced A lim st x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
      Q Qp oom :=
  initiate_stage4_placed_ok_impl hh hCoins hLocal hFitsPreChain hFitsSpqr hFitsSess hEnvErr
    hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpost hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlacedBudget

end
