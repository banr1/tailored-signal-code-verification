/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model

/-!
# Stage 3 PQXDH Helpers

Byte/cell lemmas, `S3InvPrefix`, reusable `s3_calc_agree` call combinators for
`calculate_agreement`, and shared zero-DH unwind collapses (`s3_dh_collapse_common`,
`s3_dh_unwind_1544`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## Byte and Cell Helpers -/

private theorem pack8_extract0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_bits
private theorem pack8_extract8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_bits
private theorem pack8_extract16 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_bits
private theorem pack8_extract24 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_bits
private theorem pack8_extract32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 32 8 = b4 := by bv_bits
private theorem pack8_extract40 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 40 8 = b5 := by bv_bits
private theorem pack8_extract48 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 48 8 = b6 := by bv_bits
private theorem pack8_extract56 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 56 8 = b7 := by bv_bits

private theorem bytes8_exists_cell64 {l : List (BitVec 8)} (hl : l.length = 8) :
    ∃ w : BitVec 64, ∀ p : BitVec 64, (p ↦ₛ l) = (p ↦₆₄ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl
  refine ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, fun p => ?_⟩
  unfold Arm64.pointsTo64
  rw [pack8_extract0, pack8_extract8, pack8_extract16, pack8_extract24,
      pack8_extract32, pack8_extract40, pack8_extract48, pack8_extract56,
      pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_nil]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

theorem bytes32_exists_cells4 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ∀ p : BitVec 64,
      (p ↦ₛ bs) =
        (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) := by
  obtain ⟨w0, hw0⟩ := bytes8_exists_cell64 (l := bs.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := bytes8_exists_cell64 (l := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨w2, hw2⟩ := bytes8_exists_cell64 (l := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨w3, hw3⟩ := bytes8_exists_cell64 (l := bs.drop 24) (by simp [h])
  refine ⟨w0, w1, w2, w3, fun p => ?_⟩
  have hbs : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h1 := (List.take_append_drop 8 bs).symm
    have h2 := (List.take_append_drop 8 (bs.drop 8)).symm
    have h3 := (List.take_append_drop 8 (bs.drop 16)).symm
    simp only [Nat.reduceAdd, List.drop_drop] at h2 h3
    conv_lhs => rw [h1]; arg 2; rw [h2]; arg 2; rw [h3]
  conv_lhs => rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      show (bs.take 8).length = 8 from by simp [h],
      show ((bs.drop 8).take 8).length = 8 from by simp [h],
      show ((bs.drop 16).take 8).length = 8 from by simp [h],
      hw0, hw1, hw2, hw3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem allOnes64_4_eq_F_X25519 (p : BitVec 64) :
    (p ↦₆₄ (-1#64)) ∗ ((p + 8#64) ↦₆₄ (-1#64)) ∗
      ((p + 16#64) ↦₆₄ (-1#64)) ∗ ((p + 24#64) ↦₆₄ (-1#64)) =
      (p ↦ₛ bytesToBv8 F_X25519) := by
  have h1 : ∀ q : BitVec 64, (q ↦₆₄ (-1#64)) = (q ↦ₛ List.replicate 8 0xff#8) := fun q => by
    unfold Arm64.pointsTo64
    dsimp only [List.replicate]
    rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
        pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
        pointsToBytes_nil]
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    rfl
  have hf : bytesToBv8 F_X25519 =
      List.replicate 8 0xff#8 ++ (List.replicate 8 0xff#8 ++
        (List.replicate 8 0xff#8 ++ List.replicate 8 0xff#8)) := rfl
  rw [hf, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, List.length_replicate]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← h1]

theorem memRegion32_cells4 (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ w0, p ↦₆₄ w0) ∗ (∃∗ w1, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3, (p + 24#64) ↦₆₄ w3) := by
  rw [← memRegion_merge_at p 8 24 (p + 8#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 8#64) 8 16 (p + 16#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 16#64) 8 8 (p + 24#64) (by bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64),
      ProofLib.memRegion_eight (p + 16#64), ProofLib.memRegion_eight (p + 24#64)]

theorem cells3_to_memRegion24 (p w0 w1 w2 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ⊢ memRegion p 24 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))) ?_
  rw [memRegion_merge_at (p + 8#64) 8 8 (p + 16#64) (by bv_omega) (by decide),
      memRegion_merge_at p 8 16 (p + 8#64) (by bv_omega) (by decide)]
  exact Entails.refl _

theorem append_bv8_at (p : BitVec 64) (xs ys : SignalPqxdh.Bytes) (k : BitVec 64)
    (hk : BitVec.ofNat 64 xs.length = k) :
    (p ↦ₛ bytesToBv8 xs) ∗ ((p + k) ↦ₛ bytesToBv8 ys) = (p ↦ₛ bytesToBv8 (xs ++ ys)) := by
  unfold bytesToBv8
  rw [List.map_append, pointsToBytes_append, List.length_map, hk]

theorem fp_eq_fsp_add {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (hctrl : InInitiate img W s0 s k) :
    s.readReg64 (.gpr 29#5) = s.sp + 0x1c90#64 := by
  change s.readReg64 .fp = _
  have hsp := hctrl.sp
  rw [hctrl.fp, hsp, cliInitiateFrame_eq]; bv_omega

theorem fp_slot_30 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7264#64 = s.readReg64 (.gpr 29#5) - 48#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_28 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7272#64 = s.readReg64 (.gpr 29#5) - 40#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_20 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7280#64 = s.readReg64 (.gpr 29#5) - 32#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_50 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7232#64 = s.readReg64 (.gpr 29#5) - 80#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_48 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7240#64 = s.readReg64 (.gpr 29#5) - 72#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_40 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7248#64 = s.readReg64 (.gpr 29#5) - 64#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_38 {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s.sp + 7256#64 = s.readReg64 (.gpr 29#5) - 56#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega

theorem stage3KeySlotsAt_repack_dh1 (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗ ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      (let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
       ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗ ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
       (match b.opk with
        | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
        | none => memRegion (fsp + 0x439#64) 32) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]; ac_rfl

/-! ## Invariant Bundle, `calculate_agreement`, and Unwind Helpers -/

def S3InvPrefix (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ initSaved s0 ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAt img fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba)

/-- Call `InitLocalCallees.calculateAgreement` under the uniform `stackAt s.sp extHookStack`. -/
theorem s3_calc_agree {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (ourA : BitVec 64) (ourSk : SignalPqxdh.Bytes) (theirA : BitVec 64) (theirPk : SignalPqxdh.Bytes)
    (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntry img W -
      bv% (ls_rel% "<libsignal_core::curve::PrivateKey>::calculate_agreement"
        "libsignal_cli_handshake::initiate"))
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hx0 : s.readReg64 .x0 = ourA) (hx1 : s.readReg64 .x1 = theirA)
    (hx8 : s.readReg64 .x8 = s.sp + 0x1600#64)
    (hourLen : ourSk.length = 32) (htheirLen : theirPk.length = 32)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ (ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
      memRegion (s.sp + 0x1600#64) 24 ∗ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (herr : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk = List.replicate 32 0 →
      ∀ (sm : State) (hi : BitVec 56) (u2 : BitVec 64),
        InInitiate img W s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
        SepWPp (initProg img W) (s0.readReg64 .lr) sm
          ((ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
            ((s.sp + 0x1600#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x1608#64) ↦₆₄ (hi ++ 3#8)) ∗
            ((s.sp + 0x1610#64) ↦₆₄ u2) ∗ A.pool ∗ stackAt s.sp extHookStack ∗ F)
          Q Qp (initOom s0))
    (hok : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk ≠ List.replicate 32 0 →
      ∀ (sm : State) (dhPtr : BitVec 64),
        InInitiate img W s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
        SepWPp (initProg img W) (s0.readReg64 .lr) sm
          ((ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
            ((s.sp + 0x1600#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x1608#64) ↦₆₄ dhPtr) ∗
            ((s.sp + 0x1610#64) ↦₆₄ 32#64) ∗
            (dhPtr ↦ₛ bytesToBv8 ((modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk)) ∗
            A.live dhPtr 32 1 ∗ A.pool ∗ stackAt s.sp extHookStack ∗ F)
          Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  rw [calculateAgreement_fnAddr_eq img W] at hpc
  have hstk_split := stackAt_sub_split_init s.sp
    (by decide : ResponderCore.calculateAgreementStack ≤ extHookStack) (by decide)
  have hpre' : P ⊢
      (pqxdhCalculateAgreementFrozenSpec (modelPrims X ⟨W.C, W.Q⟩) A img).pre
        (ourA, ourSk, theirA, theirPk, s.sp + 0x1600#64, s.sp) s ∗
        (memRegion (s.sp - BitVec.ofNat 64 extHookStack)
          (extHookStack - ResponderCore.calculateAgreementStack) ∗ F) := by
    refine Entails.trans hpre ?_
    rw [hstk_split]
    simp only [pqxdhCalculateAgreementFrozenSpec, sepConj_assoc]
    refine Entails.pure_right ⟨hctrl.inv.1, hx0, hx1, hx8, trivial, hourLen, htheirLen⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  refine s3_call hh (hLocal.calculateAgreement X)
    (ourA, ourSk, theirA, theirPk, s.sp + 0x1600#64, s.sp)
    (memRegion (s.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - ResponderCore.calculateAgreementStack) ∗ F)
    hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro sm _ hpan
    dsimp only [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec,
      rustPanicOnOom] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1.1
  · intro _ _ _ hex
    simp [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec] at hex
  · intro _ _ hoom
    simp [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec] at hoom
  · intro sm _ _ _ hcsm _ hof
    dsimp only [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec,
      pqxdhCalculateAgreementResultAt, ofSignalPqxdhPrimitives]
    rw [sepConj_assoc]
    refine sepWPp_pure_elim_oom fun htrm => ?_
    have hctrl' := hof htrm
    by_cases hdh : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk = List.replicate 32 0
    · simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun hi => ?_
      refine sepWPp_conseq_oom ?_ (herr hdh sm hi u2 hctrl' hcsm htrm)
      rw [hstk_split]; exact Entails.of_eq (by ac_rfl)
    · simp only [hdh, ↓reduceIte]
      have hlen : (bytesToBv8 ((modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk)).length = 32 := by
        rw [bytesToBv8_length]; exact modelPrims_x25519_len X ⟨W.C, W.Q⟩ ourSk theirPk
      have hbox := boxSliceU8_32_entails A (s.sp + 0x1600#64 + 8#64)
        (bytesToBv8 ((modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk)) hlen
      refine sepWPp_conseq_oom
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (sepConj_mono_right hbox))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun dhPtr => ?_
      refine sepWPp_conseq_oom ?_ (hok hdh sm dhPtr hctrl' hcsm htrm)
      rw [hstk_split]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by ac_rfl)

/-- Shared collapse from active DH Stage-3 state into `unwind_1544_ok` / `unwind_1548_ok`. -/
theorem s3_dh_collapse_common {A : RustAlloc} {img : Obj.Image} {B : RunBudgets}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekAPkLen : ekAPk.length = 32) (hekASkLen : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗ A.pool ∗
      A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗ memRegion fsp 0x80 ∗
      stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x1310 ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      memRegion (fsp + 0x1c70#64) 0x20 ∗ stackAt fsp extHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ⊢
      ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗ storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ logOff img ∗ A.pool ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗ initFreshRecAt fsp ∗ memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img := by
  dsimp only [S3InvPrefix]
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hstk_re := (stackAt_sub_split_init fsp hsub_ext (stk_sub_le_2pow64 hstk64)).symm
  have hslot : s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 := by
    dsimp only [fsp]; rw [cliInitiateFrame_eq]; bv_omega
  have hkeys := stage3KeySlotsAt_collapse A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
    hekAPkLen hekASkLen hkpkLen
  have hargs := initArgsAt_collapse img fsp x s0
  have hb58 := pointsTo8_entails_memRegion1 (fsp + 0x5b8#64) 0#8
  refine Entails.trans (Entails.of_eq (P := _) (Q :=
      initArgsAt img fsp x s0 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗
        (memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗ stackAt fsp extHookStack) ∗
        (memRegion fsp 0x80 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
          memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
          memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 ∗
          ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          logOff img ∗ A.pool ∗ initSaved s0 ∗
          A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
          initFreshRecAt fsp ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
          memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x1310 ∗
          memRegion (fsp + 0x1c70#64) 0x20 ∗
          coinsCursorAt img x.coinsP x.coins 32 ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img))
    (by dsimp only [fsp]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hargs (sepConj_mono hkeys
    (sepConj_mono hb58 (sepConj_mono (Entails.of_eq hstk_re) (Entails.refl _))))) ?_
  have hm128 : memRegion fsp 0x80 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
      memRegion (fsp + 0xd0#64) 0x58 = memRegion fsp 0x128 := by
    rw [memRegion_merge_at (fsp + 0x80#64) 0x50 0x58 (fsp + 0xd0#64) (by bv_omega) (by decide),
        memRegion_merge_at fsp 0x80 0xa8 (fsp + 0x80#64) (by bv_omega) (by decide)]
  have hm2e0 : memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 0x298#64) 0x190 =
      memRegion (fsp + 0x148#64) 0x2e0 :=
    memRegion_merge_at (fsp + 0x148#64) 0x150 0x190 (fsp + 0x298#64) (by bv_omega) (by decide)
  have hm181 : memRegion (fsp + 0x438#64) 0x28 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 = memRegion (fsp + 0x438#64) 0x181 := by
    rw [memRegion_merge_at (fsp + 0x460#64) 0x158 1 (fsp + 0x5b8#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x438#64) 0x28 0x159 (fsp + 0x460#64) (by bv_omega) (by decide)]
  have hm37e : memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 =
      memRegion (fsp + 0x5ba#64) 0x37e :=
    memRegion_merge_at (fsp + 0x5ba#64) (0x930 - 0x5ba) 8 (fsp + 0x930#64) (by bv_omega) (by decide)
  refine Entails.of_eq ?_
  dsimp only [fsp] at hm128 hm2e0 hm181 hm37e hslot ⊢
  rw [hslot, ← hm128, ← hm2e0, ← hm181, ← hm37e]
  ac_rfl

/-- One-shot zero-DH unwind discharge at `+0x1544` for `DH2`, `DH3`, and `DH4`. -/
theorem s3_dh_unwind_1544 {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s : State} {P_in P_extra : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekAPkLen : ekAPk.length = 32) (hekASkLen : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64) (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiate img W s0 s 0x1544) (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10) (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (w1 w2 lenWord : BitVec 64)
    (hextra : P_extra ⊢
      memRegion secretsPtr 192 ∗ stage3KeySlotsAt A (s0.sp - BitVec.ofNat 64 cliInitiateFrame)
        x.bundle kp ekASk ekAPk pqspkPtr opkId)
    (hsplit : P_in ⊢
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P_extra ∗ S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗
        ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗
        ((fsp + 0x1600#64) ↦₆₄ 1#64) ∗ ((fsp + 0x1608#64) ↦₆₄ w1) ∗ ((fsp + 0x1610#64) ↦₆₄ w2) ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P_in Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine sepWPp_conseq_oom (Entails.trans hsplit ?_)
    (unwind_1544_ok hh hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl htr
      hx26 hx1 hpost hpanic)
  have hbase := s3_dh_collapse_common (A := A) (img := img) (x := x) (kp := kp)
    (ekASk := ekASk) (ekAPk := ekAPk) (pqspkPtr := pqspkPtr) (secretsPtr := secretsPtr)
    (opkId := opkId) hstk hstk64 hekAPkLen hekASkLen hkpkLen s0
  have hek_m : ((fsp + 0x9a0#64) ↦ₛ ekASk) ⊢ memRegion (fsp + 0x9a0#64) 0x20 :=
    pointsToBytes_entails_memRegion_len hekASkLen
  have hsret := cells3_to_memRegion24 (fsp + 0x1600#64) 1#64 w1 w2
  have hm78 : memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ⊢ memRegion fsp 0x80 := by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
    rw [memRegion_merge_at fsp 0x78 8 (fsp + 0x78#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  have hc20 : ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
      memRegion (fsp + 0x1c70#64) 0x20 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  have hloc_re :
      memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗ ((fsp + 0x1c60#64) ↦₆₄ 192#64) ⊢
      memRegion (fsp + 0x958#64) 0x1310 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))))) ?_
    rw [memRegion_merge_at (fsp + 0x1618#64) 0x648 8 (fsp + 0x1c60#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x1600#64) 24 0x650 (fsp + 0x1618#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x668 (fsp + 0x1600#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12a8 (fsp + 0x9c0#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x958#64) 0x48 0x12c8 (fsp + 0x9a0#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  refine sep_replace (sepConj_mono hextra (sepConj_mono hek_m
      (sepConj_mono hsret (sepConj_mono hm78 hc20))))
    (by dsimp only [fsp]; sep_frame) ?_
  refine sep_replace hloc_re (by dsimp only [fsp]; sep_frame) ?_
  refine Entails.trans ?_ hbase
  dsimp only [fsp]; sep_frame

/-! ## Contract-Parameterized Helpers (`Stage3Lemmas.Ext`) -/

namespace Ext

theorem fp_eq_fsp_add {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (hctrl : InInitiateExt img ext s0 s k) :
    s.readReg64 (.gpr 29#5) = s.sp + 0x1c90#64 := by
  change s.readReg64 .fp = _
  have hsp := hctrl.sp
  rw [hctrl.fp, hsp, cliInitiateFrame_eq]; bv_omega

theorem fp_slot_30 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7264#64 = s.readReg64 (.gpr 29#5) - 48#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_28 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7272#64 = s.readReg64 (.gpr 29#5) - 40#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_20 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7280#64 = s.readReg64 (.gpr 29#5) - 32#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_50 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7232#64 = s.readReg64 (.gpr 29#5) - 80#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_48 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7240#64 = s.readReg64 (.gpr 29#5) - 72#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_40 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7248#64 = s.readReg64 (.gpr 29#5) - 64#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_38 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InInitiateExt img ext s0 s k) :
    s.sp + 7256#64 = s.readReg64 (.gpr 29#5) - 56#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega

theorem calcAgreeSubStk_le_frame {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) :
    ResponderCore.calculateAgreementStackExt ≤ stk - cliInitiateFrame :=
  Nat.le_trans
    (by dsimp only [ResponderCore.calculateAgreementStackExt,
          ResponderCore.calculateAgreementSubStackExt, Initiator.pqxdhHookStackExt]; decide)
    (stk_sub_ge_base hstk)

theorem pqxdhEntryStk_le_frame {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) :
    Initiator.pqxdhEntryStackExt ≤ stk - cliInitiateFrame :=
  Nat.le_trans (by dsimp only [Initiator.pqxdhEntryStackExt]; decide) (stk_sub_ge_base hstk)

def pqxdhCalculateAgreementFrozenSpecAt (calcStk : Nat) (P : Primitives) (A : RustAlloc)
    (img : Obj.Image) :
    Spec (BitVec 64 × SignalPqxdh.Bytes × BitVec 64 × SignalPqxdh.Bytes × BitVec 64 × BitVec 64) :=
  { ResponderCore.pqxdhCalculateAgreementBaseSpecExt P A img with
    pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
      ⌜img.FrozenLoaded s ∧ s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
        s.readReg64 .x8 = ret ∧ s.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
        (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗
        A.pool ∗ stackAt sp calcStk
    post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
        pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
        stackAt sp calcStk }

abbrev pqxdhCalculateAgreementFrozenSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :=
  pqxdhCalculateAgreementFrozenSpecAt ResponderCore.calculateAgreementStackExt P A img

theorem calculateAgreement_frozen_ok_of_specExt {P : Primitives} {A : RustAlloc}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img (cliExternsWith ext)) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (pqxdhCalculateAgreementFrozenSpecExt P A img) := by
  refine subroutine_ok_outcome_intro
    fun ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhCalculateAgreementFrozenSpecExt, pqxdhCalculateAgreementFrozenSpecAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx⟩, hpre⟩
  have hpre' : s0.mem ⊨
      (ResponderCore.pqxdhCalculateAgreementSpecExt P A img).pre
        (ourA, our, theirA, their, ret, sp) s0 ∗ R := by
    dsimp only [ResponderCore.pqxdhCalculateAgreementSpecExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx, ?_⟩
    have hro := rodata_0x7ff6a himg hF.roData hpre
    refine Satisfies.mono (Entails.of_eq ?_) hro
    ac_rfl
  refine subroutine_ok.mono_outcome hag (ourA, our, theirA, their, ret, sp) R s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ResponderCore.pqxdhCalculateAgreementSpecExt] at hq
    have hq' : sf.mem ⊨
        ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          ((pqxdhCalculateAgreementFrozenSpecExt P A img).post
            (ourA, our, theirA, their, ret, sp) s0 sf ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hq
      dsimp only [pqxdhCalculateAgreementFrozenSpecExt, pqxdhCalculateAgreementFrozenSpecAt,
        ResponderCore.pqxdhCalculateAgreementBaseSpecExt]
      ac_rfl
    exact Satisfies.of_sep_right hq'
  · exact Or.inr hpan

/-- Call `calculate_agreement` on `initProgExt img ext` under any callee stack `calcStk` and
caller stack sub-budget `subStk ≥ calcStk`. -/
theorem s3_calc_agree {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {S : RunSem} {x : InitGhost} {stk calcStk subStk : Nat}
    (hOk : CliExternsOk P0 A ext)
    (hCalcAgree : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (pqxdhCalculateAgreementFrozenSpecAt calcStk (modelPrims X P0) A img))
    (ourA : BitVec 64) (ourSk : SignalPqxdh.Bytes)
    (theirA : BitVec 64) (theirPk : SignalPqxdh.Bytes)
    (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntryExt img ext -
      bv% (ls_rel% "<libsignal_core::curve::PrivateKey>::calculate_agreement"
        "libsignal_cli_handshake::initiate"))
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = ourA) (hx1 : s.readReg64 .x1 = theirA)
    (hx8 : s.readReg64 .x8 = s.sp + 0x1600#64)
    (hourLen : ourSk.length = 32) (htheirLen : theirPk.length = 32)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ (ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
      memRegion (s.sp + 0x1600#64) 24 ∗ A.pool ∗ stackAt s.sp subStk ∗ F)
    (herr : (modelPrims X P0).x25519 ourSk theirPk = List.replicate 32 0 →
      ∀ (sm : State) (hi : BitVec 56) (u2 : BitVec 64),
        InInitiateExt img ext s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
        SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
          ((ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
            ((s.sp + 0x1600#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x1608#64) ↦₆₄ (hi ++ 3#8)) ∗
            ((s.sp + 0x1610#64) ↦₆₄ u2) ∗ A.pool ∗ stackAt s.sp subStk ∗ F)
          Q Qp (initOom s0))
    (hok : (modelPrims X P0).x25519 ourSk theirPk ≠ List.replicate 32 0 →
      ∀ (sm : State) (dhPtr : BitVec 64),
        InInitiateExt img ext s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
        SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
          ((ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
            ((s.sp + 0x1600#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x1608#64) ↦₆₄ dhPtr) ∗
            ((s.sp + 0x1610#64) ↦₆₄ 32#64) ∗
            (dhPtr ↦ₛ bytesToBv8 ((modelPrims X P0).x25519 ourSk theirPk)) ∗
            A.live dhPtr 32 1 ∗ A.pool ∗ stackAt s.sp subStk ∗ F)
          Q Qp (initOom s0))
    (hsub : calcStk ≤ subStk := by
      try dsimp only [ResponderCore.calculateAgreementStackExt,
        ResponderCore.calculateAgreementSubStackExt, ResponderCore.calculateAgreementStack,
        Initiator.pqxdhHookStackExt, Initiator.pqxdhEntryStackExt, extHookStack]
      decide)
    (hsub64 : subStk ≤ 2 ^ 64 := by
      try dsimp only [ResponderCore.calculateAgreementStackExt,
        ResponderCore.calculateAgreementSubStackExt, ResponderCore.calculateAgreementStack,
        Initiator.pqxdhHookStackExt, Initiator.pqxdhEntryStackExt, extHookStack]
      decide) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  rw [calculateAgreement_fnAddr_eq img ext] at hpc
  have hstk_split := stackAt_sub_split_init s.sp hsub hsub64
  have hpre' : P ⊢
      (pqxdhCalculateAgreementFrozenSpecAt calcStk (modelPrims X P0) A img).pre
        (ourA, ourSk, theirA, theirPk, s.sp + 0x1600#64, s.sp) s ∗
        (memRegion (s.sp - BitVec.ofNat 64 subStk)
          (subStk - calcStk) ∗ F) := by
    refine Entails.trans hpre ?_
    rw [hstk_split]
    simp only [pqxdhCalculateAgreementFrozenSpecAt, sepConj_assoc]
    refine Entails.pure_right ⟨hctrl.inv.1, hx0, hx1, hx8, trivial, hourLen, htheirLen⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  refine s3_call hOk hCalcAgree
    (ourA, ourSk, theirA, theirPk, s.sp + 0x1600#64, s.sp)
    (memRegion (s.sp - BitVec.ofNat 64 subStk)
      (subStk - calcStk) ∗ F)
    hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro sm _ hpan
    dsimp only [pqxdhCalculateAgreementFrozenSpecAt,
      ResponderCore.pqxdhCalculateAgreementBaseSpecExt, rustPanicOnOom] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1.1
  · intro _ _ _ hex
    simp [pqxdhCalculateAgreementFrozenSpecAt,
      ResponderCore.pqxdhCalculateAgreementBaseSpecExt] at hex
  · intro _ _ hoom
    simp [pqxdhCalculateAgreementFrozenSpecAt,
      ResponderCore.pqxdhCalculateAgreementBaseSpecExt] at hoom
  · intro sm _ _ _ hcsm _ hof
    dsimp only [pqxdhCalculateAgreementFrozenSpecAt,
      ResponderCore.pqxdhCalculateAgreementBaseSpecExt,
      pqxdhCalculateAgreementResultAt, ofSignalPqxdhPrimitives]
    rw [sepConj_assoc]
    refine sepWPp_pure_elim_oom fun htrm => ?_
    have hctrl' := hof htrm
    by_cases hdh : (modelPrims X P0).x25519 ourSk theirPk = List.replicate 32 0
    · simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun hi => ?_
      refine sepWPp_conseq_oom ?_ (herr hdh sm hi u2 hctrl' hcsm htrm)
      rw [hstk_split]; exact Entails.of_eq (by ac_rfl)
    · simp only [hdh, ↓reduceIte]
      have hlen : (bytesToBv8 ((modelPrims X P0).x25519 ourSk theirPk)).length = 32 := by
        rw [bytesToBv8_length]; exact modelPrims_x25519_len X P0 ourSk theirPk
      have hbox := boxSliceU8_32_entails A (s.sp + 0x1600#64 + 8#64)
        (bytesToBv8 ((modelPrims X P0).x25519 ourSk theirPk)) hlen
      refine sepWPp_conseq_oom
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (sepConj_mono_right hbox))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun dhPtr => ?_
      refine sepWPp_conseq_oom ?_ (hok hdh sm dhPtr hctrl' hcsm htrm)
      rw [hstk_split]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by ac_rfl)

/-- Shared collapse from active DH Stage-3 state into `Ext.unwind_1544_ok` / `Ext.unwind_1548_ok`,
parameterized over any stack sub-budget `subStk ≤ stk - cliInitiateFrame`. -/
theorem s3_dh_collapse_common {A : RustAlloc} {img : Obj.Image}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32} {stk subStk : Nat}
    (hsub : subStk ≤ stk - cliInitiateFrame) (hstk64 : stk ≤ 2 ^ 63)
    (hekAPkLen : ekAPk.length = 32) (hekASkLen : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗ A.pool ∗
      A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗ memRegion fsp 0x80 ∗
      stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x1310 ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      memRegion (fsp + 0x1c70#64) 0x20 ∗ stackAt fsp subStk ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - subStk) ⊢
      ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗ storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ logOff img ∗ A.pool ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗ initFreshRecAt fsp ∗ memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img := by
  dsimp only [S3InvPrefix]
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hstk_re := (stackAt_sub_split_init fsp hsub (stk_sub_le_2pow64 hstk64)).symm
  have hslot : s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 := by
    dsimp only [fsp]; rw [cliInitiateFrame_eq]; bv_omega
  have hkeys := stage3KeySlotsAt_collapse A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
    hekAPkLen hekASkLen hkpkLen
  have hargs := initArgsAt_collapse img fsp x s0
  have hb58 := pointsTo8_entails_memRegion1 (fsp + 0x5b8#64) 0#8
  refine Entails.trans (Entails.of_eq (P := _) (Q :=
      initArgsAt img fsp x s0 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗
        (memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - subStk) ∗ stackAt fsp subStk) ∗
        (memRegion fsp 0x80 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
          memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
          memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 ∗
          ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          logOff img ∗ A.pool ∗ initSaved s0 ∗
          A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
          initFreshRecAt fsp ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
          memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x1310 ∗
          memRegion (fsp + 0x1c70#64) 0x20 ∗
          coinsCursorAt img x.coinsP x.coins 32 ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img))
    (by dsimp only [fsp]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hargs (sepConj_mono hkeys
    (sepConj_mono hb58 (sepConj_mono (Entails.of_eq hstk_re) (Entails.refl _))))) ?_
  have hm128 : memRegion fsp 0x80 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
      memRegion (fsp + 0xd0#64) 0x58 = memRegion fsp 0x128 := by
    rw [memRegion_merge_at (fsp + 0x80#64) 0x50 0x58 (fsp + 0xd0#64) (by bv_omega) (by decide),
        memRegion_merge_at fsp 0x80 0xa8 (fsp + 0x80#64) (by bv_omega) (by decide)]
  have hm2e0 : memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 0x298#64) 0x190 =
      memRegion (fsp + 0x148#64) 0x2e0 :=
    memRegion_merge_at (fsp + 0x148#64) 0x150 0x190 (fsp + 0x298#64) (by bv_omega) (by decide)
  have hm181 : memRegion (fsp + 0x438#64) 0x28 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 = memRegion (fsp + 0x438#64) 0x181 := by
    rw [memRegion_merge_at (fsp + 0x460#64) 0x158 1 (fsp + 0x5b8#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x438#64) 0x28 0x159 (fsp + 0x460#64) (by bv_omega) (by decide)]
  have hm37e : memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 =
      memRegion (fsp + 0x5ba#64) 0x37e :=
    memRegion_merge_at (fsp + 0x5ba#64) (0x930 - 0x5ba) 8 (fsp + 0x930#64) (by bv_omega) (by decide)
  refine Entails.of_eq ?_
  dsimp only [fsp] at hm128 hm2e0 hm181 hm37e hslot ⊢
  rw [hslot, ← hm128, ← hm2e0, ← hm181, ← hm37e]
  ac_rfl

/-- One-shot zero-DH unwind discharge at `+0x1544` for `DH2`, `DH3`, and `DH4`,
parameterized over any stack sub-budget `subStk ≤ stk - cliInitiateFrame`. -/
theorem s3_dh_unwind_1544 {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32} {stk subStk : Nat}
    {s0 s : State} {P_in P_extra : SepProp} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hS : S.initiate = initDef X P0)
    (hnone : initDef X P0 x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekAPkLen : ekAPk.length = 32) (hekASkLen : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64) (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiateExt img ext s0 s 0x1544) (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10) (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (w1 w2 lenWord : BitVec 64)
    (hextra : P_extra ⊢
      memRegion secretsPtr 192 ∗ stage3KeySlotsAt A (s0.sp - BitVec.ofNat 64 cliInitiateFrame)
        x.bundle kp ekASk ekAPk pqspkPtr opkId)
    (hsplit : P_in ⊢
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P_extra ∗ S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp subStk ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - subStk) ∗
        A.live secretsPtr 192 1 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗
        ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗
        ((fsp + 0x1600#64) ↦₆₄ 1#64) ∗ ((fsp + 0x1608#64) ↦₆₄ w1) ∗ ((fsp + 0x1610#64) ↦₆₄ w2) ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18)
    (hsub : subStk ≤ stk - cliInitiateFrame := by
      first
      | exact calcAgreeSubStk_le_frame hstk
      | exact pqxdhEntryStk_le_frame hstk
      | exact Nat.le_trans (by decide) (stk_sub_ge_base hstk)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P_in Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine sepWPp_conseq_oom (Entails.trans hsplit ?_)
    (unwind_1544_ok hOk hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl htr
      hx26 hx1 hpost hpanic)
  have hbase := s3_dh_collapse_common (A := A) (img := img) (x := x) (kp := kp)
    (ekASk := ekASk) (ekAPk := ekAPk) (pqspkPtr := pqspkPtr) (secretsPtr := secretsPtr)
    (opkId := opkId) hsub hstk64 hekAPkLen hekASkLen hkpkLen s0
  have hek_m : ((fsp + 0x9a0#64) ↦ₛ ekASk) ⊢ memRegion (fsp + 0x9a0#64) 0x20 :=
    pointsToBytes_entails_memRegion_len hekASkLen
  have hsret := cells3_to_memRegion24 (fsp + 0x1600#64) 1#64 w1 w2
  have hm78 : memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ⊢ memRegion fsp 0x80 := by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
    rw [memRegion_merge_at fsp 0x78 8 (fsp + 0x78#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  have hc20 : ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
      memRegion (fsp + 0x1c70#64) 0x20 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  have hloc_re :
      memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗ ((fsp + 0x1c60#64) ↦₆₄ 192#64) ⊢
      memRegion (fsp + 0x958#64) 0x1310 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))))) ?_
    rw [memRegion_merge_at (fsp + 0x1618#64) 0x648 8 (fsp + 0x1c60#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x1600#64) 24 0x650 (fsp + 0x1618#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x668 (fsp + 0x1600#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12a8 (fsp + 0x9c0#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x958#64) 0x48 0x12c8 (fsp + 0x9a0#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  refine sep_replace (sepConj_mono hextra (sepConj_mono hek_m
      (sepConj_mono hsret (sepConj_mono hm78 hc20))))
    (by dsimp only [fsp]; sep_frame) ?_
  refine sep_replace hloc_re (by dsimp only [fsp]; sep_frame) ?_
  refine Entails.trans ?_ hbase
  dsimp only [fsp]; sep_frame

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

