/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Seed Unroll Part A (`+0x0b6c → +0x0c48`: `pqspk` Copy + Draws `0..6`)

Copies `pqspk` (`1568` bytes) to `[fsp + 0x9c0, fsp + 0xfe0)`, splits the scratch 32-bit word slots
at `[fsp + 0x08, fsp + 0x6c)`, and proves unrolled coin draws `0..6`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefix coinsCursorAt coinWord
  padCoins dhPrefix dhRemAt
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem scratch120_split (fsp : BitVec 64) :
    memRegion fsp 0x78 =
      memRegion fsp 8 ∗ memRegion (fsp + 0x68#64) 4 ∗ memRegion (fsp + 0x60#64) 4 ∗
      memRegion (fsp + 0x5c#64) 4 ∗ memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x08#64) 4 ∗ memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
      memRegion (fsp + 0x70#64) 8 := by
  rw [← memRegion_merge_at fsp 8 112 (fsp + 0x08#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x08#64) 4 108 (fsp + 0x0c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x0c#64) 4 104 (fsp + 0x10#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x10#64) 4 100 (fsp + 0x14#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x14#64) 4 96 (fsp + 0x18#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x18#64) 4 92 (fsp + 0x1c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c#64) 4 88 (fsp + 0x20#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x20#64) 4 84 (fsp + 0x24#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x24#64) 4 80 (fsp + 0x28#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x28#64) 4 76 (fsp + 0x2c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x2c#64) 4 72 (fsp + 0x30#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x30#64) 4 68 (fsp + 0x34#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x34#64) 4 64 (fsp + 0x38#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x38#64) 4 60 (fsp + 0x3c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x3c#64) 4 56 (fsp + 0x40#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x40#64) 4 52 (fsp + 0x44#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x44#64) 4 48 (fsp + 0x48#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x48#64) 4 44 (fsp + 0x4c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x4c#64) 4 40 (fsp + 0x50#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x50#64) 4 36 (fsp + 0x54#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x54#64) 4 32 (fsp + 0x58#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x58#64) 4 28 (fsp + 0x5c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x5c#64) 4 24 (fsp + 0x60#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x60#64) 4 20 (fsp + 0x64#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x64#64) 4 16 (fsp + 0x68#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x68#64) 4 12 (fsp + 0x6c#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x6c#64) 4 8 (fsp + 0x70#64) (by bv_omega) (by decide)]
  ac_rfl

private theorem kem_locals_9c0 (fsp : BitVec 64) :
    memRegion (fsp + 0x9c0#64) 0xc40 =
      memRegion (fsp + 0x9c0#64) 1568 ∗ memRegion (fsp + 0xfe0#64) 32 ∗
      memRegion (fsp + 0x1000#64) 0x600 := by
  rw [← memRegion_merge_at (fsp + 0x9c0#64) 1568 1568 (fsp + 0xfe0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64) (by bv_omega) (by decide)]

private theorem kem_locals_1600 (fsp : BitVec 64) :
    memRegion (fsp + 0x1600#64) 24 =
      memRegion (fsp + 0x1600#64) 4 ∗ memRegion (fsp + 0x1604#64) 20 := by
  rw [← memRegion_merge_at (fsp + 0x1600#64) 4 20 (fsp + 0x1604#64) (by bv_omega) (by decide)]

private theorem mem4_elim_word {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z : BitVec 32, SepWPp prog ret s (B ∗ ((a ↦₃₂ z) ∗ R)) Q Qp oom) :
    SepWPp prog ret s ((memRegion a 4 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, ProofLib.memRegion_four a, sepExists_sepConj_left]
  exact sepWPp_exists_elim_oom fun z =>
    sepWPp_conseq_oom
      (Entails.of_eq (by rw [← sepConj_assoc, sepConj_comm (a ↦₃₂ z) B, sepConj_assoc])) (h z)

private theorem mem8_elim_word {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z : BitVec 64, SepWPp prog ret s (B ∗ ((a ↦₆₄ z) ∗ R)) Q Qp oom) :
    SepWPp prog ret s ((memRegion a 8 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, ProofLib.memRegion_eight a, sepExists_sepConj_left]
  exact sepWPp_exists_elim_oom fun z =>
    sepWPp_conseq_oom
      (Entails.of_eq (by rw [← sepConj_assoc, sepConj_comm (a ↦₆₄ z) B, sepConj_assoc])) (h z)

private theorem s3_repack_kpk {A : RustAlloc} (fsp : BitVec 64) (x : InitGhost)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId : BitVec 32) :
    ((let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
      ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      A.live pqspkPtr 1568 1 ∗
      ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) ∗
     (pqspkPtr ↦ₛ x.bundle.kpk)) =
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId := by
  (try dsimp only [stage3KeySlotsAt]); ac_rfl

set_option maxHeartbeats 1200000 in set_option maxRecDepth 200000 in
theorem kem_coins_a_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sb : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiate img W s0 sb 0xb6c) (htr : sb.trace = s0.trace)
    (hx20 : sb.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sb.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : sb.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hnext : ∀ (sc : State)
        (z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : BitVec 32),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiate img W s0 sc 0xc48 → sc.trace = s0.trace →
      sc.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sc.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sc
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 60 ∗
          A.pool ∗ stackAt fsp cliCoinsFillStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ z6) ∗ ((fsp + 0x48#64) ↦₃₂ z7) ∗
          ((fsp + 0x44#64) ↦₃₂ z8) ∗ ((fsp + 0x40#64) ↦₃₂ z9) ∗
          ((fsp + 0x3c#64) ↦₃₂ z10) ∗ ((fsp + 0x38#64) ↦₃₂ z11) ∗
          ((fsp + 0x34#64) ↦₃₂ z12) ∗ ((fsp + 0x30#64) ↦₃₂ z13) ∗
          ((fsp + 0x2c#64) ↦₃₂ z14) ∗ ((fsp + 0x28#64) ↦₃₂ z15) ∗
          ((fsp + 0x24#64) ↦₃₂ z16) ∗ ((fsp + 0x20#64) ↦₃₂ z17) ∗
          ((fsp + 0x1c#64) ↦₃₂ z18) ∗ ((fsp + 0x18#64) ↦₃₂ z19) ∗
          ((fsp + 0x14#64) ↦₃₂ z20) ∗ ((fsp + 0x10#64) ↦₃₂ z21) ∗
          ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (s0.readReg64 .lr) sb
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, _, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub_cf : cliCoinsFillStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub64 : stk - cliInitiateFrame ≤ 2 ^ 64 := stk_sub_le_2pow64 hstk64
  have hstk_cf :
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) =
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 cliCoinsFillStack) (cliCoinsFillStack - extHookStack) ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) := by
    rw [sepConj_comm (stackAt fsp extHookStack), ← stackAt_sub_split_init fsp hsub_ext hsub64,
        stackAt_sub_split_init fsp hsub_cf hsub64,
        stackAt_sub_split_init fsp (by decide : extHookStack ≤ cliCoinsFillStack) (by decide)]
    ac_rfl
  refine sepWPp_conseq_oom (P' :=
    ((memRegion (fsp + 0x68#64) 4 ∗ memRegion (fsp + 0x60#64) 4 ∗
      memRegion (fsp + 0x5c#64) 4 ∗ memRegion (fsp + 0x58#64) 4 ∗
      memRegion (fsp + 0x54#64) 4 ∗ memRegion (fsp + 0x50#64) 4 ∗
      memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x40#64) 4 ∗
      memRegion (fsp + 0x3c#64) 4 ∗ memRegion (fsp + 0x38#64) 4 ∗
      memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x28#64) 4 ∗
      memRegion (fsp + 0x24#64) 4 ∗ memRegion (fsp + 0x20#64) 4 ∗
      memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x10#64) 4 ∗
      memRegion (fsp + 0x0c#64) 4 ∗ memRegion (fsp + 0x08#64) 4 ∗
      memRegion (fsp + 0x70#64) 8 ∗ memRegion (fsp + 0x1600#64) 4 ∗ emp) ∗
     (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
      A.pool ∗ stackAt fsp extHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 cliCoinsFillStack) (cliCoinsFillStack - extHookStack) ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - cliCoinsFillStack) ∗
      A.live secretsPtr 192 1 ∗
      (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
      dhRemAt secretsPtr dh4? ∗
      memRegion fsp 8 ∗
      memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
      stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
      memRegion (fsp + 0x9c0#64) 1568 ∗ memRegion (fsp + 0xfe0#64) 32 ∗
      memRegion (fsp + 0x1000#64) 0x600 ∗ memRegion (fsp + 0x1604#64) 20 ∗
      memRegion (fsp + 0x1618#64) 0x648 ∗
      ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)))
    (by
      dsimp only [fsp] at hstk_cf ⊢
      refine sep_replace (Entails.of_eq hstk_cf) (by sep_frame) ?_
      rw [kem_locals_9c0, kem_locals_1600, scratch120_split]
      sep_frame) ?_
  refine mem4_elim_word fun z0 => mem4_elim_word fun z1 =>
    mem4_elim_word fun z2 => mem4_elim_word fun z3 =>
    mem4_elim_word fun z4 => mem4_elim_word fun z5 =>
    mem4_elim_word fun z6 => mem4_elim_word fun z7 =>
    mem4_elim_word fun z8 => mem4_elim_word fun z9 =>
    mem4_elim_word fun z10 => mem4_elim_word fun z11 =>
    mem4_elim_word fun z12 => mem4_elim_word fun z13 =>
    mem4_elim_word fun z14 => mem4_elim_word fun z15 =>
    mem4_elim_word fun z16 => mem4_elim_word fun z17 =>
    mem4_elim_word fun z18 => mem4_elim_word fun z19 =>
    mem4_elim_word fun z20 => mem4_elim_word fun z21 =>
    mem4_elim_word fun z22 => mem4_elim_word fun z23 =>
    mem8_elim_word fun z70 => mem4_elim_word fun z1600 => ?_
  rw [emp_sepConj]
  obtain ⟨halign_b, _, hfsp_b⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom
    (show _ ⊢ ((fsp + 0x70#64) ↦₆₄ z70) ∗ ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗
        ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗ _ by
      dsimp only [fsp, stage3KeySlotsAt]; sep_frame) ?_
  refine' s3_block_to_call hh
    (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    0xb8c (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = pqspkPtr ∧
      sm.readReg64 .x2 = 1568#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt] at hpc ⊢
    rw [hfsp_b]
    exact s3_step_b6c_b8c pqspkPtr z70 _ halign_b hpc hctrl.run
      (by rwa [← hfsp_b]) (by rwa [← hfsp_b]) (by rwa [← hfsp_b])
  · intro sm_mc hctrl_mc hpcm_mc hlrm_mc htrm_mc ⟨hx0_mc, hx1_mc, hx2_mc, hx20_mc, hx21_mc⟩
    rw [← hfsp_b] at *
    refine s3_memcpy hh (fsp + 0x9c0#64) pqspkPtr x.bundle.kpk _
      hctrl_mc (htrm_mc.trans htr) hpcm_mc hlrm_mc
      hx0_mc hx1_mc (by rw [hx2_mc, hkpkLen]; decide) hpanic
      (by rw [hctrl_mc.sp, hkpkLen]; (try dsimp only [fsp]); sep_frame) ?_
    intro s_0 hctrl_0 hcs_0 _ htr_0
    rw [hctrl_mc.sp]
    have hx20_0 := hcs_0.2.1.trans hx20_mc; have hx21_0 := hcs_0.2.2.1.trans hx21_mc
    have hcf_re :
        stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 cliCoinsFillStack)
            (cliCoinsFillStack - extHookStack) =
        stackAt fsp cliCoinsFillStack := by
      rw [sepConj_comm,
          ← stackAt_sub_split_init fsp (by decide : extHookStack ≤ cliCoinsFillStack) (by decide)]
    refine sepWPp_conseq_oom
      (sep_replace (sepConj_mono
        (Entails.of_eq (s3_repack_kpk (A := A) fsp x kp ekASk ekAPk pqspkPtr opkId))
        (Entails.of_eq hcf_re))
        (by cases x.bundle.opk <;> ((try dsimp only [fsp]); sep_frame)) (Entails.refl _)) ?_
    obtain ⟨halign_0, _, hfsp_0⟩ := hctrl_0.step_ctx fsp
    refine sepWPp_conseq_oom
      (show _ ⊢ ((fsp + 0x1600#64) ↦₃₂ z1600) ∗ _ by dsimp only [fsp]; sep_frame) ?_
    refine' s3_block_to_call hh
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
      0xba0 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hctrl_0 ?_ ?_; rotate_left 1
    · have hpc := hctrl_0.pc
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt] at hpc ⊢
      rw [hfsp_0]
      exact s3_step_b8c_ba0 z1600 _ halign_0 hpc hctrl_0.run
        (by rwa [← hfsp_0]) (by rwa [← hfsp_0])
    · intro sm_d0 hctrl_d0 hpcm_d0 hlrm_d0 htrm_d0 ⟨hx0_d0, hx1_d0, hx20_d0, hx21_d0⟩
      rw [← hfsp_0] at *
      refine s3_coins_fill4 hh hCoins hcoinsLt 0 (by decide) _
        hctrl_d0 (htrm_d0.trans (htr_0.trans (htrm_mc.trans htr))) hpcm_d0 hlrm_d0
        hx0_d0 hx1_d0 hpanic
        (by rw [hctrl_d0.sp]; (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame) ?_
      intro s_1 hctrl_1 hcs_1 htr_1
      rw [hctrl_d0.sp]
      have htr1 : s_1.trace = s0.trace :=
        htr_1.trans (htrm_d0.trans (htr_0.trans (htrm_mc.trans htr)))
      have hx20_1 := hcs_1.2.1.trans hx20_d0; have hx21_1 := hcs_1.2.2.1.trans hx21_d0
      refine s3_draw_to_slot hh hCoins hcoinsLt 1 (by decide) (by decide)
        0xba0 0xbbc 0x68#64 z0 _ hctrl_1 htr1 hx20_1 hx21_1 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            clear * - G halign hpc hrun hx20' hx21'
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xba0 28
            try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            examples_hide_fetches; wp_steps
            exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (by simp only [arm64_norm, wp_norm]; sep_frame)
              ⟨by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_2 hctrl_2 htr2 hx20_2 hx21_2 => ?_
      refine s3_draw_to_slot hh hCoins hcoinsLt 2 (by decide) (by decide)
        0xbbc 0xbd8 0x60#64 z1 _ hctrl_2 htr2 hx20_2 hx21_2 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            clear * - G halign hpc hrun hx20' hx21'
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xbbc 28
            try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            examples_hide_fetches; wp_steps
            exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (by simp only [arm64_norm, wp_norm]; sep_frame)
              ⟨by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_3 hctrl_3 htr3 hx20_3 hx21_3 => ?_
      refine s3_draw_to_slot hh hCoins hcoinsLt 3 (by decide) (by decide)
        0xbd8 0xbf4 0x5c#64 z2 _ hctrl_3 htr3 hx20_3 hx21_3 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            clear * - G halign hpc hrun hx20' hx21'
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xbd8 28
            try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            examples_hide_fetches; wp_steps
            exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (by simp only [arm64_norm, wp_norm]; sep_frame)
              ⟨by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_4 hctrl_4 htr4 hx20_4 hx21_4 => ?_
      refine s3_draw_to_slot hh hCoins hcoinsLt 4 (by decide) (by decide)
        0xbf4 0xc10 0x58#64 z3 _ hctrl_4 htr4 hx20_4 hx21_4 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            clear * - G halign hpc hrun hx20' hx21'
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xbf4 28
            try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            examples_hide_fetches; wp_steps
            exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (by simp only [arm64_norm, wp_norm]; sep_frame)
              ⟨by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_5 hctrl_5 htr5 hx20_5 hx21_5 => ?_
      refine s3_draw_to_slot hh hCoins hcoinsLt 5 (by decide) (by decide)
        0xc10 0xc2c 0x54#64 z4 _ hctrl_5 htr5 hx20_5 hx21_5 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            clear * - G halign hpc hrun hx20' hx21'
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xc10 28
            try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            examples_hide_fetches; wp_steps
            exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (by simp only [arm64_norm, wp_norm]; sep_frame)
              ⟨by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_6 hctrl_6 htr6 hx20_6 hx21_6 => ?_
      refine s3_draw_to_slot hh hCoins hcoinsLt 6 (by decide) (by decide)
        0xc2c 0xc48 0x50#64 z5 _ hctrl_6 htr6 hx20_6 hx21_6 hpanic
        (by intro G halign hpc hrun hx20' hx21'
            clear * - G halign hpc hrun hx20' hx21'
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xc2c 28
            try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            try simp only [arm64_norm, wp_norm] at hx20' hx21'
            examples_hide_fetches; wp_steps
            exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (by simp only [arm64_norm, wp_norm]; sep_frame)
              ⟨by wp_norm_goal, by wp_norm_goal,
               by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        fun s_7 hctrl_7 htr7 hx20_7 hx21_7 => ?_
      exact sepWPp_conseq_oom
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        (hnext s_7 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
          hctrl_7 htr7 hx20_7 hx21_7)

/-! ## `CliExternsOk` Generalization (`kem_coins_a_ok_ext`) -/

set_option Elab.async false

set_option maxHeartbeats 800000 in set_option maxRecDepth 200000 in
private theorem kem_coins_a1_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s_1 : State} {Q Qp : State → SepProp → Prop}
    (z0 z1 z2 : BitVec 32) (F : SepProp)
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 s_1 0xba0) (htr : s_1.trace = s0.trace)
    (hx20 : s_1.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s_1.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ s_4 : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 s_4 0xbf4 → s_4.trace = s0.trace →
      s_4.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s_4.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s_4
        (coinsCursorAt img x.coinsP x.coins 48 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ F)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s_1
      (coinsCursorAt img x.coinsP x.coins 36 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 0 (by decide)) ∗
        stackAt fsp cliCoinsFillStack ∗
        ((fsp + 0x68#64) ↦₃₂ z0) ∗ ((fsp + 0x60#64) ↦₃₂ z1) ∗ ((fsp + 0x5c#64) ↦₃₂ z2) ∗ F)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 1 (by decide) (by decide)
    0xba0 0xbbc 0x68#64 z0 _ hctrl htr hx20 hx21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xba0 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; sep_frame)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_2 hctrl_2 htr2 hx20_2 hx21_2 => ?_
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 2 (by decide) (by decide)
    0xbbc 0xbd8 0x60#64 z1 _ hctrl_2 htr2 hx20_2 hx21_2 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xbbc 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; sep_frame)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_3 hctrl_3 htr3 hx20_3 hx21_3 => ?_
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 3 (by decide) (by decide)
    0xbd8 0xbf4 0x5c#64 z2 _ hctrl_3 htr3 hx20_3 hx21_3 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xbd8 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; sep_frame)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_4 hctrl_4 htr4 hx20_4 hx21_4 => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext s_4 hctrl_4 htr4 hx20_4 hx21_4)

set_option maxHeartbeats 800000 in set_option maxRecDepth 200000 in
private theorem kem_coins_a2_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s_4 : State} {Q Qp : State → SepProp → Prop}
    (z3 z4 z5 : BitVec 32) (F : SepProp)
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 s_4 0xbf4) (htr : s_4.trace = s0.trace)
    (hx20 : s_4.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s_4.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ s_7 : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 s_7 0xc48 → s_7.trace = s0.trace →
      s_7.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s_7.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s_7
        (coinsCursorAt img x.coinsP x.coins 60 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗ F)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s_4
      (coinsCursorAt img x.coinsP x.coins 48 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        stackAt fsp cliCoinsFillStack ∗
        ((fsp + 0x58#64) ↦₃₂ z3) ∗ ((fsp + 0x54#64) ↦₃₂ z4) ∗ ((fsp + 0x50#64) ↦₃₂ z5) ∗ F)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 4 (by decide) (by decide)
    0xbf4 0xc10 0x58#64 z3 _ hctrl htr hx20 hx21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xbf4 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; sep_frame)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_5 hctrl_5 htr5 hx20_5 hx21_5 => ?_
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 5 (by decide) (by decide)
    0xc10 0xc2c 0x54#64 z4 _ hctrl_5 htr5 hx20_5 hx21_5 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xc10 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; sep_frame)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_6 hctrl_6 htr6 hx20_6 hx21_6 => ?_
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 6 (by decide) (by decide)
    0xc2c 0xc48 0x50#64 z5 _ hctrl_6 htr6 hx20_6 hx21_6 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xc2c 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; sep_frame)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_7 hctrl_7 htr7 hx20_7 hx21_7 => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext s_7 hctrl_7 htr7 hx20_7 hx21_7)

set_option maxHeartbeats 800000 in set_option maxRecDepth 200000 in
theorem kem_coins_a_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sb : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Ext img P0 ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 sb 0xb6c) (htr : sb.trace = s0.trace)
    (hx20 : sb.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sb.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : sb.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hnext : ∀ (sc : State)
        (z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : BitVec 32),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 sc 0xc48 → sc.trace = s0.trace →
      sc.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sc.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sc
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 60 ∗
          A.pool ∗ stackAt fsp cliCoinsFillStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ z6) ∗ ((fsp + 0x48#64) ↦₃₂ z7) ∗
          ((fsp + 0x44#64) ↦₃₂ z8) ∗ ((fsp + 0x40#64) ↦₃₂ z9) ∗
          ((fsp + 0x3c#64) ↦₃₂ z10) ∗ ((fsp + 0x38#64) ↦₃₂ z11) ∗
          ((fsp + 0x34#64) ↦₃₂ z12) ∗ ((fsp + 0x30#64) ↦₃₂ z13) ∗
          ((fsp + 0x2c#64) ↦₃₂ z14) ∗ ((fsp + 0x28#64) ↦₃₂ z15) ∗
          ((fsp + 0x24#64) ↦₃₂ z16) ∗ ((fsp + 0x20#64) ↦₃₂ z17) ∗
          ((fsp + 0x1c#64) ↦₃₂ z18) ∗ ((fsp + 0x18#64) ↦₃₂ z19) ∗
          ((fsp + 0x14#64) ↦₃₂ z20) ∗ ((fsp + 0x10#64) ↦₃₂ z21) ∗
          ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sb
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, _, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub_cf : cliCoinsFillStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub64 : stk - cliInitiateFrame ≤ 2 ^ 64 := stk_sub_le_2pow64 hstk64
  have hstk_cf :
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) =
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 cliCoinsFillStack) (cliCoinsFillStack - extHookStack) ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) := by
    rw [sepConj_comm (stackAt fsp extHookStack), ← stackAt_sub_split_init fsp hsub_ext hsub64,
        stackAt_sub_split_init fsp hsub_cf hsub64,
        stackAt_sub_split_init fsp (by decide : extHookStack ≤ cliCoinsFillStack) (by decide)]
    ac_rfl
  refine sepWPp_conseq_oom (P' :=
    ((memRegion (fsp + 0x68#64) 4 ∗ memRegion (fsp + 0x60#64) 4 ∗
      memRegion (fsp + 0x5c#64) 4 ∗ memRegion (fsp + 0x58#64) 4 ∗
      memRegion (fsp + 0x54#64) 4 ∗ memRegion (fsp + 0x50#64) 4 ∗
      memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x40#64) 4 ∗
      memRegion (fsp + 0x3c#64) 4 ∗ memRegion (fsp + 0x38#64) 4 ∗
      memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x28#64) 4 ∗
      memRegion (fsp + 0x24#64) 4 ∗ memRegion (fsp + 0x20#64) 4 ∗
      memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x10#64) 4 ∗
      memRegion (fsp + 0x0c#64) 4 ∗ memRegion (fsp + 0x08#64) 4 ∗
      memRegion (fsp + 0x70#64) 8 ∗ memRegion (fsp + 0x1600#64) 4 ∗ emp) ∗
     (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
      A.pool ∗ stackAt fsp extHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 cliCoinsFillStack) (cliCoinsFillStack - extHookStack) ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - cliCoinsFillStack) ∗
      A.live secretsPtr 192 1 ∗
      (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
      dhRemAt secretsPtr dh4? ∗
      memRegion fsp 8 ∗
      memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
      stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
      memRegion (fsp + 0x9c0#64) 1568 ∗ memRegion (fsp + 0xfe0#64) 32 ∗
      memRegion (fsp + 0x1000#64) 0x600 ∗ memRegion (fsp + 0x1604#64) 20 ∗
      memRegion (fsp + 0x1618#64) 0x648 ∗
      ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)))
    (by
      dsimp only [fsp] at hstk_cf ⊢
      refine sep_replace (Entails.of_eq hstk_cf) (by sep_frame) ?_
      rw [kem_locals_9c0, kem_locals_1600, scratch120_split]
      sep_frame) ?_
  refine mem4_elim_word fun z0 => mem4_elim_word fun z1 =>
    mem4_elim_word fun z2 => mem4_elim_word fun z3 =>
    mem4_elim_word fun z4 => mem4_elim_word fun z5 =>
    mem4_elim_word fun z6 => mem4_elim_word fun z7 =>
    mem4_elim_word fun z8 => mem4_elim_word fun z9 =>
    mem4_elim_word fun z10 => mem4_elim_word fun z11 =>
    mem4_elim_word fun z12 => mem4_elim_word fun z13 =>
    mem4_elim_word fun z14 => mem4_elim_word fun z15 =>
    mem4_elim_word fun z16 => mem4_elim_word fun z17 =>
    mem4_elim_word fun z18 => mem4_elim_word fun z19 =>
    mem4_elim_word fun z20 => mem4_elim_word fun z21 =>
    mem4_elim_word fun z22 => mem4_elim_word fun z23 =>
    mem8_elim_word fun z70 => mem4_elim_word fun z1600 => ?_
  rw [emp_sepConj]
  obtain ⟨halign_b, _, hfsp_b⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom
    (show _ ⊢ ((fsp + 0x70#64) ↦₆₄ z70) ∗ ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗
        ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗ _ by
      dsimp only [fsp, stage3KeySlotsAt]; sep_frame) ?_
  refine' Ext.s3_block_to_call hOk
    (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    0xb8c (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = pqspkPtr ∧
      sm.readReg64 .x2 = 1568#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc ⊢
    rw [hfsp_b]
    exact Ext.s3_step_b6c_b8c pqspkPtr z70 _ halign_b hpc hctrl.run
      (by rwa [← hfsp_b]) (by rwa [← hfsp_b]) (by rwa [← hfsp_b])
  · intro sm_mc hctrl_mc hpcm_mc hlrm_mc htrm_mc ⟨hx0_mc, hx1_mc, hx2_mc, hx20_mc, hx21_mc⟩
    rw [← hfsp_b] at *
    refine Ext.s3_memcpy hOk (fsp + 0x9c0#64) pqspkPtr x.bundle.kpk _
      hctrl_mc (htrm_mc.trans htr) hpcm_mc hlrm_mc
      hx0_mc hx1_mc (by rw [hx2_mc, hkpkLen]; decide) hpanic
      (by rw [hctrl_mc.sp, hkpkLen]; (try dsimp only [fsp]); sep_frame) ?_
    intro s_0 hctrl_0 hcs_0 _ htr_0
    rw [hctrl_mc.sp]
    have hx20_0 := hcs_0.2.1.trans hx20_mc; have hx21_0 := hcs_0.2.2.1.trans hx21_mc
    have hcf_re :
        stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 cliCoinsFillStack)
            (cliCoinsFillStack - extHookStack) =
        stackAt fsp cliCoinsFillStack := by
      rw [sepConj_comm,
          ← stackAt_sub_split_init fsp (by decide : extHookStack ≤ cliCoinsFillStack) (by decide)]
    refine sepWPp_conseq_oom
      (sep_replace (sepConj_mono
        (Entails.of_eq (s3_repack_kpk (A := A) fsp x kp ekASk ekAPk pqspkPtr opkId))
        (Entails.of_eq hcf_re))
        (by cases x.bundle.opk <;> ((try dsimp only [fsp]); sep_frame)) (Entails.refl _)) ?_
    obtain ⟨halign_0, _, hfsp_0⟩ := hctrl_0.step_ctx fsp
    refine sepWPp_conseq_oom
      (show _ ⊢ ((fsp + 0x1600#64) ↦₃₂ z1600) ∗ _ by dsimp only [fsp]; sep_frame) ?_
    refine' Ext.s3_block_to_call hOk
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
      0xba0 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hctrl_0 ?_ ?_; rotate_left 1
    · have hpc := hctrl_0.pc
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc ⊢
      rw [hfsp_0]
      exact Ext.s3_step_b8c_ba0 z1600 _ halign_0 hpc hctrl_0.run
        (by rwa [← hfsp_0]) (by rwa [← hfsp_0])
    · intro sm_d0 hctrl_d0 hpcm_d0 hlrm_d0 htrm_d0 ⟨hx0_d0, hx1_d0, hx20_d0, hx21_d0⟩
      rw [← hfsp_0] at *
      refine Ext.s3_coins_fill4 hOk hCoins hcoinsLt 0 (by decide) _
        hctrl_d0 (htrm_d0.trans (htr_0.trans (htrm_mc.trans htr))) hpcm_d0 hlrm_d0
        hx0_d0 hx1_d0 hpanic
        (by rw [hctrl_d0.sp]; (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame) ?_
      intro s_1 hctrl_1 hcs_1 htr_1
      rw [hctrl_d0.sp]
      have htr1 : s_1.trace = s0.trace :=
        htr_1.trans (htrm_d0.trans (htr_0.trans (htrm_mc.trans htr)))
      have hx20_1 := hcs_1.2.1.trans hx20_d0; have hx21_1 := hcs_1.2.2.1.trans hx21_d0
      refine sepWPp_conseq_oom
        (by (try dsimp only [fsp]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
        (kem_coins_a1_ext z0 z1 z2 _ hOk hCoins hcoinsLt hpanic hctrl_1 htr1 hx20_1 hx21_1
          fun s_4 hctrl_4 htr4 hx20_4 hx21_4 => ?_)
      refine sepWPp_conseq_oom
        (by (try dsimp only [fsp]); (try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]); sep_frame)
        (kem_coins_a2_ext z3 z4 z5 _ hOk hCoins hcoinsLt hpanic hctrl_4 htr4 hx20_4 hx21_4
          fun s_7 hctrl_7 htr7 hx20_7 hx21_7 => ?_)
      exact sepWPp_conseq_oom
        (by (try dsimp only [fsp]); (try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]); sep_frame)
        (hnext s_7 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
          hctrl_7 htr7 hx20_7 hx21_7)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
