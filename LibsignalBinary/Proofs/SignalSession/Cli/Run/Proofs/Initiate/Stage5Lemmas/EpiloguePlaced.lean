/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Epilogue
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage 5 Frame Reassembly, Shared Epilogue, and Error Cleanup (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` proofs of `collapse_initLocals_placed`,
`stage5_epilogue_placed_ok` (`+0x0350..+0x037c → lr`), and `stage5_err_cleanup_placed_ok`
(`+0x1858 → +0x0350 → lr`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

/-- Collapse all stack locals `[fsp, fsp + initLocalsSize)` into `memRegion fsp initLocalsSize`
with `initArgsAtPlaced fsp x s0`. -/
theorem collapse_initLocals_placed [LibsignalPlacement] (fsp : BitVec 64) {x : InitGhost}
    {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 : State}
    (w128 w130 w138 : BitVec 64) (b5b8 b5b9 : BitVec 8)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) :
    memRegion fsp 0xd0 ∗
      initArgsAtPlaced fsp x s0 ∗
      ((fsp + 0x128#64) ↦₆₄ w128) ∗ ((fsp + 0x130#64) ↦₆₄ w130) ∗ ((fsp + 0x138#64) ↦₆₄ w138) ∗
      memRegion (fsp + 0x140#64) 344 ∗
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
        memRegion (fsp + 0x2b8#64) 0x48 ∗
        ((fsp + 0x300#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((fsp + 0x304#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 0x308#64) 0x40 ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x438#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        stage3OpkSlotAt fsp x.bundle ∗
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x45a#64) 6) ∗
      memRegion (fsp + 0x460#64) 344 ∗
      ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ b5b9) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ⊢
      memRegion fsp initLocalsSize := by
  have hargs : initArgsAtPlaced fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
    dsimp only [initArgsAtPlaced]
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))))))))))) ?_
    rw [← ProofLib.memRegion_split' (b := fsp + 0x118#64) (n := 8) (k := 8) (b' := fsp + 0x120#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x114#64) (n := 4) (k := 16) (b' := fsp + 0x118#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x110#64) (n := 4) (k := 20) (b' := fsp + 0x114#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x108#64) (n := 8) (k := 24) (b' := fsp + 0x110#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x100#64) (n := 8) (k := 32) (b' := fsp + 0x108#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0xf8#64) (n := 8) (k := 40) (b' := fsp + 0x100#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0xf0#64) (n := 8) (k := 48) (b' := fsp + 0xf8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0xe8#64) (n := 8) (k := 56) (b' := fsp + 0xf0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0xe0#64) (n := 8) (k := 64) (b' := fsp + 0xe8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0xd8#64) (n := 8) (k := 72) (b' := fsp + 0xe0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0xd0#64) (n := 8) (k := 80) (b' := fsp + 0xd8#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hopk : stage3OpkSlotAt fsp x.bundle ⊢ memRegion (fsp + 0x439#64) 32 := by
    dsimp only [stage3OpkSlotAt]
    cases x.bundle.opk with
    | none => exact Entails.refl _
    | some p =>
      have h := pointsToBytes_entails_memRegion (fsp + 0x439#64) p.2.bytes.toList
      simpa using h
  have hkeys :
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
        memRegion (fsp + 0x2b8#64) 0x48 ∗
        ((fsp + 0x300#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((fsp + 0x304#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 0x308#64) 0x40 ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x438#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        stage3OpkSlotAt fsp x.bundle ∗
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x45a#64) 6) ⊢
      memRegion (fsp + 0x298#64) 0x1c8 := by
    refine Entails.trans
      (sepConj_mono (by simpa [hekLen.2] using pointsToBytes_entails_memRegion (fsp + 0x298#64) ekAPk)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (by simpa using pointsToBytes_entails_memRegion (fsp + 0x348#64) kp.identityKey.publicKey.bytes.toList)
      (sepConj_mono (by simpa using pointsToBytes_entails_memRegion (fsp + 0x368#64) kp.privateKey.bytes.toList)
      (sepConj_mono (by simpa [hekLen.2] using pointsToBytes_entails_memRegion (fsp + 0x388#64) ekAPk)
      (sepConj_mono (by simpa [hekLen.1] using pointsToBytes_entails_memRegion (fsp + 0x3a8#64) ekASk)
      (sepConj_mono (by simpa using pointsToBytes_entails_memRegion (fsp + 0x3c8#64) x.bundle.idKey.publicKey.bytes.toList)
      (sepConj_mono (by simpa using pointsToBytes_entails_memRegion (fsp + 0x3e8#64) x.bundle.spk.bytes.toList)
      (sepConj_mono (by simpa using pointsToBytes_entails_memRegion (fsp + 0x408#64) x.bundle.spk.bytes.toList)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono hopk
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
        (Entails.refl _)))))))))))))))))) ?_
    rw [← ProofLib.memRegion_split' (b := fsp + 0x459#64) (n := 1) (k := 6) (b' := fsp + 0x45a#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x439#64) (n := 32) (k := 7) (b' := fsp + 0x459#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x438#64) (n := 1) (k := 39) (b' := fsp + 0x439#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x430#64) (n := 8) (k := 40) (b' := fsp + 0x438#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x428#64) (n := 8) (k := 48) (b' := fsp + 0x430#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x408#64) (n := 32) (k := 56) (b' := fsp + 0x428#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x3e8#64) (n := 32) (k := 88) (b' := fsp + 0x408#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x3c8#64) (n := 32) (k := 120) (b' := fsp + 0x3e8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x3a8#64) (n := 32) (k := 152) (b' := fsp + 0x3c8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x388#64) (n := 32) (k := 184) (b' := fsp + 0x3a8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x368#64) (n := 32) (k := 216) (b' := fsp + 0x388#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x348#64) (n := 32) (k := 248) (b' := fsp + 0x368#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x308#64) (n := 64) (k := 280) (b' := fsp + 0x348#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x304#64) (n := 4) (k := 344) (b' := fsp + 0x308#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x300#64) (n := 4) (k := 348) (b' := fsp + 0x304#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x2b8#64) (n := 72) (k := 352) (b' := fsp + 0x300#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := fsp + 0x298#64) (n := 32) (k := 424) (b' := fsp + 0x2b8#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
    (sepConj_mono hargs
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono hkeys
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (Entails.refl _))))))))))) ?_
  dsimp only [initLocalsSize]
  rw [← ProofLib.memRegion_split' (b := fsp + 0x5b9#64) (n := 1) (k := 7312 - 0x5ba) (b' := fsp + 0x5ba#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x5b8#64) (n := 1) (k := 7312 - 0x5b9) (b' := fsp + 0x5b9#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x460#64) (n := 344) (k := 7312 - 0x5b8) (b' := fsp + 0x5b8#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x298#64) (n := 0x1c8) (k := 7312 - 0x460) (b' := fsp + 0x460#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x140#64) (n := 344) (k := 7312 - 0x298) (b' := fsp + 0x298#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x138#64) (n := 8) (k := 7312 - 0x140) (b' := fsp + 0x140#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x130#64) (n := 8) (k := 7312 - 0x138) (b' := fsp + 0x138#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x128#64) (n := 8) (k := 7312 - 0x130) (b' := fsp + 0x130#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0xd0#64) (n := 0x58) (k := 7312 - 0x128) (b' := fsp + 0x128#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp) (n := 0xd0) (k := 7312 - 0xd0) (b' := fsp + 0xd0#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

section EpilogueBlockPlaced

private theorem sp_epilogue_add1_placed (a : BitVec 64) : (a - 7408#64) + 4096#64 = a - 3312#64 := by
  bv_omega
private theorem sp_epilogue_add2_placed (a : BitVec 64) : (a - 3312#64) + 3216#64 = a - 96#64 := by
  bv_omega
private theorem sp_epilogue_add3_placed (a : BitVec 64) : (a - 96#64) + 96#64 = a := by
  bv_omega
attribute [local arm64_norm, local wp_norm]
  sp_epilogue_add1_placed sp_epilogue_add2_placed sp_epilogue_add3_placed

/-- Shared epilogue (`+0x0350..+0x037c → lr` on `initProgPlaced W`): writes
`(x26, x27, x25, x28, x24, x21)` to `x.ret`, restores `s0.sp` and all callee-saved registers,
and discharges `Q` via `InitExitPostPlaced`. -/
theorem stage5_epilogue_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) Unit)
    (OutHeap Junk : SepProp)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = initEntryPlaced + offEpilogue)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F)
    (hfss : s.fs.files = x.F)
    (hout : ∀ sf, slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' res s0 sf)
    (hres :
      ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((x.ret + 0x08#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 0x10#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 0x18#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 0x20#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 0x28#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ OutHeap) ⊢
        initResAt A x.ret res)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (memRegion x.ret 48 ∗ initSaved s0 ∗
        memRegion fsp initLocalsSize ∗ stackAt fsp (stk - cliInitiateFrame) ∗
        OutHeap ∗ storesAt A x.stores g' ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ Junk)
      Q Qp := by
  intro fsp
  dsimp only [initProgPlaced, lsProg_521, offEpilogue] at hpc ⊢
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply SepWPp.of_sepWP_ret
  conv =>
    arg 4
    rw [sret48_words6_split x.ret]
    unfold initSaved
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine hpost _ _ ⟨by wp_norm_goal, ?_, ?_⟩
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs]
  · dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    refine Entails.sepExists_right g' (Entails.sepExists_right res ?_)
    refine Entails.pure_right
      ⟨slotTrace_of_trace_eq (x := x)
         (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]; exact htr)
         hfs0
         (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]; exact hfss),
       hout _⟩ ?_
    have hstkFull := reassemble_stackAt_full (B := B) s0 hstk hstk64
    dsimp only at hstkFull
    refine Entails.trans (Q :=
        (((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((x.ret + 0x08#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
          ((x.ret + 0x10#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((x.ret + 0x18#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
          ((x.ret + 0x20#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
          ((x.ret + 0x28#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ OutHeap) ∗
          (memRegion fsp initLocalsSize ∗ initSaved s0 ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
          storesAt A x.stores g' ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ Junk))
      (Entails.of_eq ?_) ?_
    · unfold initSaved
      simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      s5_ac_rfl
    refine Entails.trans
      (sepConj_mono hres (sepConj_mono hstkFull
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (Entails.top_right (Q := anyHeap) fun _ => trivial)))))))))) ?_
    exact Entails.of_eq (by s5_ac_rfl)

end EpilogueBlockPlaced

theorem sepWPp_step_to_lscro_mem {prog : Program} {pl : MultiPlacement} {ret mid : BitVec 64}
    {s sm : State} {P Pm : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hstep : SepWP prog mid s P (fun s' P' => (∃ m, s' = sm.setMem m) ∧ P' = Pm))
    (hcont : ∀ m, LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl (sm.setMem m).mem →
      SepWPp prog ret (sm.setMem m) Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_of_sepWP_lscro (mid := mid) hcrl ?_
  refine SepWP.seq (mid := mid) hstep ?_
  rintro _ _ hpc hrun ⟨⟨m, rfl⟩, rfl⟩
  exact SepWP.done hpc hrun (hcont m)

attribute [local arm64_norm, local wp_norm] fsp_err_eqs

set_option maxHeartbeats 800000 in
/-- Error cleanup starting at `+0x1858` on `initProgPlaced W`: drops `SessionStructure`
(`[fsp + 0x5b9] = 1#8`), deallocates `pqspkPtr` (`1568` bytes, align `1`), skips empty
`initFreshRecAt`, and enters `stage5_epilogue_placed_ok` to establish `InitExitPostPlaced`
with `SpeOwned` at `x.ret`. -/
theorem stage5_err_cleanup_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost}
    {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg' : SessionGhost} {ss' : SessionState (List (BitVec 8))}
    {k : RunDrop.SpeOwned} {SpeHeap Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpc : s.pc = initEntryPlaced + offErrEntry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F)
    (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hw0_ne3 : s.readReg64 (.gpr 26#5) ≠ 0xFFFFFFFFFFFFFFFD#64)
    (hspe :
      ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((x.ret + 0x08#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 0x10#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 0x18#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 0x20#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 0x28#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ SpeHeap) ⊢
        RunDrop.speOwnedAt A x.ret k)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗
        initArgsAtPlaced fsp x s0 ∗
        initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A (fsp + 0x460#64) sg' ss' ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        SpeHeap ∗ Extra)
      Q Qp := by
  intro fsp
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_mem hinv (mid := lsmpl.base 512)
  · dsimp only [initProgPlaced, lsProg_521, offErrEntry] at hpc ⊢
    wp_steps
    s5_step_done
  intro _ hcrl1
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (dropSS_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dropSS_placed (ret_pc := initEntryPlaced + offErrEntryDropDone)
    hh hLocal.dropSessionStructure fsp (fsp + 0x460#64) sg' ss' ?errF1
    (by wp_norm_goal; try rfl) (by wp_norm_lhs) (by simp only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offErrEntryDropDone]; wp_norm_goal; try rfl)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hcrl1
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    hpan ?errPre1 ?_
  case errPre1 => s5_close_frame
  intro sm1 hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1
  have hfs1' : sm1.fs.files = x.F := hfs1.trans hfss
  simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19, hvregs] at hcs1
  rcases hcs1 with ⟨hx19_1, _, hx21_1, _, _, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (dropSS_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; rw [stage3KeySlotsAt_unfold]; simp only [sepConj_assoc]
  rw [initEntryPlaced_eq_blkPl] at hpc1
  apply sepWPp_step_to_lscro_mem hinv1 (mid := lsρ lsRustDeallocSymCli)
  · dsimp only [initProgPlaced, lsProg_521, offErrEntryDropDone] at hpc1 ⊢
    wp_steps
    s5_step_done
  intro _ hcrl2
  have hkpkMem : (pqspkPtr ↦ₛ x.bundle.kpk) ⊢ memRegion pqspkPtr 1568 := by
    simpa [hkpkLen] using pointsToBytes_entails_memRegion pqspkPtr x.bundle.kpk
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_placed (ret_pc := initEntryPlaced + offErrAfterDealloc)
    hh (s5_dealloc_ok_at_placed hh) fsp pqspkPtr 1568 1 ?errF2
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [initEntryPlaced, offErrAfterDealloc]; wp_norm_goal; try rfl)
    (by simp only [wp_norm, arm64_norm, htr1]) hcrl2
    (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) layoutOk_1568_1
    hpan ?errPre2 ?_
  case errPre2 =>
    inImageKitClearInvHyps
    s5_have_eq hpull : (pqspkPtr ↦ₛ x.bundle.kpk) ∗ ?restKpk := by
      conv => lhs; simp only [wp_norm, arm64_norm, hsp1]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hkpkMem) ?_)
    s5_close_frame
  intro sm2 hpc2 hrun2 hsp2 hal2 hcs2 hinv2 htr2 hfs2
  have hfs2' : sm2.fs.files = x.F := hfs2.trans hfs1'
  simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx21_1, hx24_1, hx25_1,
    hx26_1, hx27_1, hx28_1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, _, hx21_2, _, _, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; unfold initFreshRecAt; simp only [sepConj_assoc]
  have hw0_ne3' : sm2.readReg64 (.gpr 26#5) + 3#64 ≠ 0#64 := by
    rw [hx26_2]
    intro h
    exact hw0_ne3 (by bv_omega)
  rw [initEntryPlaced_eq_blkPl] at hpc2
  apply sepWPp_step_to_lscro_mem hinv2 (mid := initEntryPlaced + offEpilogue)
  · dsimp only [initProgPlaced, lsProg_521, offErrAfterDealloc, offEpilogue] at hpc2 ⊢
    rw [initEntryPlaced_eq_blkPl]
    wp_steps
    s5_step_done
  intro _ _
  have hrec344 :
      ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (fsp + 0x148#64) 0x150 ⊢
        memRegion (fsp + 0x140#64) 344 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [← ProofLib.memRegion_split' (b := fsp + 0x140#64) (n := 8) (k := 336)
          (b' := fsp + 0x148#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hloc := collapse_initLocals_placed fsp (x := x) (kp := kp)
    (ekASk := ekASk) (ekAPk := ekAPk) (pqspkPtr := pqspkPtr) (opkId := opkId) (s0 := s0)
    0#64 8#64 0#64 0#8 0#8 hekLen
  refine sepWPp_conseq ?_
    (stage5_epilogue_placed_ok (B := B) StoresGhost.opened
      (.error (.protocol .invalidProtobufEncoding)) SpeHeap Extra
      hstk hstk64
      (by dsimp only [initEntryPlaced, offEpilogue]; wp_norm_goal; try rfl)
      (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm]; exact hsp2)
      hsp_align
      (by simp only [wp_norm, arm64_norm, hvregs_2])
      (by simp only [wp_norm, arm64_norm, hx19_2])
      (by simp only [wp_norm, arm64_norm, htr2])
      hfs0 hfs2'
      (fun _ => slotOut_err_of_some_none hans)
      (by
        simp only [wp_norm, arm64_norm, hx26_2, hx27_2, hx25_2, hx28_2, hx24_2, hx21_2]
        exact Entails.trans hspe
          (Entails.sepExists_right k (Entails.refl _)))
      hpost)
  inImageKitClearInvHyps
  s5_have_eq hperm1 :
      (((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (fsp + 0x148#64) 0x150) ∗
      ?remAfterRec := by
    conv => lhs; simp only [wp_norm, arm64_norm]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hperm1)
    (Entails.trans (sepConj_mono_left hrec344) ?_)
  s5_have_eq hperm2 :
      (memRegion fsp 0xd0 ∗
        initArgsAtPlaced fsp x s0 ∗
        ((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗ ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
        memRegion (fsp + 0x140#64) 344 ∗
        (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
          memRegion (fsp + 0x2b8#64) 0x48 ∗
          ((fsp + 0x300#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((fsp + 0x304#64) ↦₃₂ opkId) ∗
          memRegion (fsp + 0x308#64) 0x40 ∗
          ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
          ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
          ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x438#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
          stage3OpkSlotAt fsp x.bundle ∗
          ((fsp + 0x459#64) ↦₈ 0#8) ∗
          memRegion (fsp + 0x45a#64) 6) ∗
        memRegion (fsp + 0x460#64) 344 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ∗ ?remFinal := by
    conv => lhs; simp only [opk8_truncate_eq]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hperm2)
    (Entails.trans (sepConj_mono_left hloc) ?_)
  exact Entails.of_eq (by s5_ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
