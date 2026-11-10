/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProof
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P4 Kyber Pre-Key Refusal Arm

Budget-threaded `[LibsignalPlacement]` Kyber `mark_used` refusal theorems and unified 4-kit Stage P4
spatial bundles (`stageP4SharedPlaced`, `stageP4RawPrePlaced`, `stageP4PrePlaced`,
`stageP4ExitAtPlaced`) on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  stageP4SaveIdSharedPlaced stageP4SaveIdPrePlaced
  stageP4SaveIdOkPostPlaced stageP4SaveIdErrPostPlaced
  stageP4_saveIdentity_dispatch_vregs_kits_placed
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4_markKyber_to_38c_vregs_mark_placed stageP4_markKyber_to_38c_vregs_kits_placed
  kyberRefusedSharedPlaced kyberRefusedPrePlaced
  kyberRefusedMarkErrPostPlaced kyberRefusedSaveErrPostPlaced
  stageP4_kyber_refused_core_vregs_kits_placed_ok
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  stageP4_kyber_refused_vregs_kits_placed_ok
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget (
  stageP4SaveIdSharedPlaced stageP4SaveIdPrePlaced
  stageP4SaveIdOkPostPlaced stageP4SaveIdErrPostPlaced
  stageP4_saveIdentity_dispatch_vregs_kits_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  MarkStepEnv StageP4MarkErrEnv
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4_markKyber_to_38c_vregs_mark_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedSaveErrEnv
)

private theorem sepWPp_frame_false {prog : Program} {ret : BitVec 64} {s : State}
    {P Pcore F : SepProp} {Qcore Q Qp : State → SepProp → Prop}
    (hcore : SepWPp prog ret s Pcore Qcore (fun _ _ => False))
    (hpre : P = Pcore ∗ F)
    (hpost : ∀ sf P1, Qcore sf P1 → Q sf (P1 ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hpre, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P1, hmf, hq⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hmo⟩⟩ :=
    hcore (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P1 ∗ F, hmf, hpost sf P1 hq⟩⟩
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hmo).elim

/-! ## Allocation envelopes for the Kyber refusal path -/

/-- Entry budget envelope for `P4.1` (`SaveStepEnv`) followed by `P4.2` (`MarkStepEnv`). -/
abbrev StageP4SaveMarkBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)

/-- Allocation envelope on the `save_identity = Ok(c)` + `mark_kyber_pre_key_used = Err(e)`
exit of Stage P4: `SaveStepEnv` followed by `StageP4MarkErrEnv`. -/
def StageP4KyberRefusedMarkErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)

/-- Combined exit allocation envelope of the Kyber refusal path covering both `mark_used = Err(e)`
and `save_identity = Err(())`. -/
def StageP4KyberRefusedEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (evs : List AllocEvent) : Prop :=
  StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
    rem remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∨
  StageP4MatchedSaveErrEnv ikit ikitEnv ist0 rem remoteIk evs

theorem fitsEnv_saveMark_of_markErr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {ist0 : ikit.IdState} {kst0 : kpkKit.KpkState}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {kyberPreKeyId signedPreKeyId : BitVec 32} {baseKey : PublicKey}
    (h : FitsEnv M lim st
      (StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        rem remoteIk kyberPreKeyId signedPreKeyId baseKey)) :
    FitsEnv M lim st
      (StageP4SaveMarkBudgetEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        rem remoteIk kyberPreKeyId signedPreKeyId baseKey) :=
  h.mono fun
    | _, Or.inl h1 => Or.inl h1
    | _, Or.inr ⟨_, _, rfl, h1, h2⟩ => SeqEnv.append h1 (SeqEnv.inl h2)

theorem fitsEnv_saveMark_of_kyberRefused {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {ist0 : ikit.IdState} {kst0 : kpkKit.KpkState}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {kyberPreKeyId signedPreKeyId : BitVec 32} {baseKey : PublicKey}
    (h : FitsEnv M lim st
      (StageP4KyberRefusedEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        rem remoteIk kyberPreKeyId signedPreKeyId baseKey)) :
    FitsEnv M lim st
      (StageP4SaveMarkBudgetEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        rem remoteIk kyberPreKeyId signedPreKeyId baseKey) :=
  fitsEnv_saveMark_of_markErr (h.mono fun _ he => Or.inl he)

/-! ## Placed 2-kit Kyber refusal spatial predicates and theorems -/

def kyberRefusedSharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x2e0#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (kyberRefusedCallStack ikit kpkKit)

def kyberRefusedPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  kyberRefusedSharedPlaced A lim st0 ikit kpkKit s0 s s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kpkKit.storeAt kyberStorePtr kst0

def kyberRefusedMarkErrPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s sf : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (c : IdentityChange) (e : kpkKit.MarkErr) : SepProp :=
  kyberRefusedSharedPlaced A lim stf ikit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
    idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  speErrAt kpkKit.markErr outPtr e ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) ∗
  kpkKit.storeAt kyberStorePtr
    (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))

def kyberRefusedSaveErrPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s sf : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState) : SepProp :=
  kyberRefusedSharedPlaced A lim stf ikit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
    idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  savePollPlacedOutAt outPtr (.error ()) ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) ∗
  kpkKit.storeAt kyberStorePtr kst0

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` 2-kit Kyber `mark_used` refusal theorem (`mark`-only
kit) preserving `calleeSavedVRegs`. -/
theorem stageP4_kyber_refused_core_vregs_mark_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hfits : FitsEnv M lim st0
      (StageP4SaveMarkBudgetEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey))
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (kyberRefusedPrePlaced A lim st0 ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        ist0 kst0 G ssSt)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent),
            StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
              peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ kyberRefusedMarkErrPostPlaced A lim (M.stepEvents evs st0) ikit kpkKit
              s0 s sf coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
              kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0 c e)) ∨
         (∃ (evs : List AllocEvent),
            StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ kyberRefusedSaveErrPostPlaced A lim (M.stepEvents evs st0) ikit kpkKit
              s0 s sf coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
              kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0))))
      Qp := by
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  let F1 : SepProp :=
    ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
    memRegion (s.sp + 0x2e0#64) 36 ∗
    kpkKit.storeAt kyberStorePtr kst0 ∗
    memRegion (s.sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
      (kyberRefusedCallStack ikit kpkKit - saveIdCallStack ikit)
  have hpre1 :
      kyberRefusedPrePlaced A lim st0 ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        ist0 kst0 G ssSt ⊢
      stageP4SaveIdPrePlaced A lim st0 ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr kpkKit.kpk_vt prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ssSt ∗ F1 := by
    unfold kyberRefusedPrePlaced kyberRefusedSharedPlaced
      stageP4SaveIdPrePlaced stageP4SaveIdSharedPlaced F1
    rw [stack_kyberRefused_to_saveId ikit kpkKit s.sp hsp_ub]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre1 ?_
  refine stageP4_saveIdentity_dispatch_vregs_kits_placed ext ikit ikitEnv
    hdealloc hDropSS3 hikit hiVt st0 s0 s
    coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (0#64 + kpkKit.markShimOff) prevStatesPtr ptCap ptPtr v_3d0
    opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ssSt F1 _
    haddr_id hfits.seq_left hopk_ne2 hpt_le hsp_save
    (fun hro' hP' => hkVt.markSlot hro' hP')
    (hfs.mono (fun _ h => h.1) (fun h => h.1))
    hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c evs_save s1 P1 hevs_save hst1 hrel1 hpc1 hrun1 hsp1 htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1
      hlr1 hcro1 hvregs1 hP1 => ?_)
    (fun evs_save sf Pf hevs_save hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  · -- P4.1 Ok(c) → P4.2 mark_kyber_pre_key_used (refused)
    let F2 : SepProp :=
      ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
      ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
      ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
      ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
      ((coroPtr + 0xd0#64) ↦₆₄ kpkKit.kpk_vt) ∗
      ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗
      ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
      ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
      ((coroPtr + 0x2ac#64) ↦₃₂ opkIdIsSome) ∗
      ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
      ((coroPtr + 0x2b4#64) ↦₃₂ 1#32) ∗
      ((coroPtr + 0x2b8#64) ↦₃₂ kyberPreKeyId) ∗
      ((coroPtr + 0x2bc#64) ↦₃₂ signedPreKeyId) ∗
      ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
      ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
      memRegion (s.sp + 0x250#64) 20 ∗
      ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
      ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      memRegion (s.sp + 0x2b0#64) 36 ∗
      ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
      (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) ∗
      memRegion (s.sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
        (kyberRefusedCallStack ikit kpkKit - markKyberCallStack kpkKit)
    have hdrop1 :
        P1 ⊢ (saveIdVtablesAt ikit ∗ ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff))) ∗
          (stageP4MarkKyberPrePlaced A lim (M.stepEvents evs_save st0) kpkKit s0 s1
            coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
            ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗ F2) := by
      refine Entails.trans hP1 ?_
      exact Entails.replace_factor
        (Entails.of_eq ((stack_kyberRefused_to_saveId ikit kpkKit s.sp hsp_ub).symm.trans
          (stack_kyberRefused_to_markKyber ikit kpkKit s.sp hsp_ub)))
        (by unfold stageP4SaveIdOkPostPlaced stageP4SaveIdSharedPlaced F1; sep_focus)
        (by unfold stageP4MarkKyberPrePlaced stageP4MarkKyberSharedPlaced F2; rw [hsp1]; sep_ac_rfl)
    refine SepWPp.drop_pre_of_entails hdrop1 ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hfs1 := (hfs.of_steps hst1 htr1 (fun hQ => hQ.1.2 peer.val remoteIk (.ok c))).mono
      (fun _ h => h.2) (fun h => h.2)
    refine stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit kpkKitEnv
      hdealloc hDropSS3 hkpkKit hkVt (M.stepEvents evs_save st0)
      s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
      kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ssSt F2 _
      hmarkOk (hfits.seq_right hevs_save) hpt_le hsp_mark hfs1 hcro1 hpc1 hrun1 hsp1_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun _ _ _ _ _ _ _ _ hrel_ok => by intros; exact (hrefused hrel_ok).elim)
      (fun e evs_mark sf Pf hevs_mark hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    have hevs_tot :
        StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
          peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey (evs_save ++ evs_mark) :=
      SeqEnv.append hevs_save hevs_mark
    have hst_tot :
        M.stepEvents evs_mark (M.stepEvents evs_save st0) =
          M.stepEvents (evs_save ++ evs_mark) st0 :=
      (M.stepEvents_append evs_save evs_mark st0).symm
    refine ⟨markKyberVtablesAt kpkKit,
      kyberRefusedMarkErrPostPlaced A lim (M.stepEvents (evs_save ++ evs_mark) st0) ikit kpkKit
        s0 s sf coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId kyberPreKeyId signedPreKeyId
        pt peer remoteIk baseKey ist0 kst0 c e,
      ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
      Or.inl ⟨c, e, evs_save ++ evs_mark, hevs_tot, hrel1, hrel2,
        by rw [htr2, htr1, List.append_assoc], Entails.refl _⟩⟩
    refine Entails.trans hPf
      (Entails.replace_factor
        (coro2ac_words_entails_memRegion20 coroPtr opkIdIsSome opkId 1#32 kyberPreKeyId signedPreKeyId)
        (by
          unfold stageP4MarkKyberErrPostPlaced stageP4MarkKyberSharedPlaced F2
          rw [hsp1, hst_tot, coro298_split_eq coroPtr opkIdIsSome opkId]
          sep_focus)
        (by
          unfold kyberRefusedMarkErrPostPlaced kyberRefusedSharedPlaced
          rw [stack_kyberRefused_to_markKyber ikit kpkKit s.sp hsp_ub]
          sep_ac_rfl))
  · -- P4.1 Err() arm
    refine ⟨saveIdVtablesAt ikit ∗ ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)),
      kyberRefusedSaveErrPostPlaced A lim (M.stepEvents evs_save st0) ikit kpkKit s0 s sf
        coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkIdIsSome opkId kyberPreKeyId signedPreKeyId
        pt peer remoteIk baseKey ist0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      Or.inr ⟨evs_save, hevs_save, hrelf, htrf, Entails.refl _⟩⟩
    refine Entails.trans hPf ?_
    unfold stageP4SaveIdErrPostPlaced stageP4SaveIdSharedPlaced
      kyberRefusedSaveErrPostPlaced kyberRefusedSharedPlaced F1
    rw [stack_kyberRefused_to_saveId ikit kpkKit s.sp hsp_ub]
    exact Entails.of_eq (by sep_ac_rfl)

theorem stageP4_kyber_refused_core_vregs_kits_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hfits : FitsEnv M lim st0
      (StageP4SaveMarkBudgetEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey))
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (kyberRefusedPrePlaced A lim st0 ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        ist0 kst0 G ssSt)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent),
            StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
              peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ kyberRefusedMarkErrPostPlaced A lim (M.stepEvents evs st0) ikit kpkKit
              s0 s sf coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
              kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0 c e)) ∨
         (∃ (evs : List AllocEvent),
            StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ kyberRefusedSaveErrPostPlaced A lim (M.stepEvents evs st0) ikit kpkKit
              s0 s sf coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
              kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0))))
      Qp :=
  stageP4_kyber_refused_core_vregs_mark_placed_ok ext ikit ikitEnv kpkKit kpkKitEnv
    hdealloc hDropSS3 hikit hiVt (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt
    st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId kyberPreKeyId signedPreKeyId
    b_2c0 pt peer remoteIk baseKey ist0 kst0 G ssSt
    haddr_id hmarkOk hrefused hfits hopk_ne2 hpt_le hsp_ub hfs hcro hpc hrun hsp_align
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-! ## Placed 4-kit Stage P4 spatial predicates and refusal theorems -/

def stageP4SharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x2e0#64) 36 ∗
  memRegion (s.sp + 0x310#64) 36 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (stageP4CallStack kit ikit pkKit kpkKit)

def stageP4RawPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4SharedPlaced A lim st0 kit ikit pkKit kpkKit s0 s s coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
    ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kpkKit.storeAt kyberStorePtr kst0 ∗
  pkKit.storeAt preKeyStorePtr pst0 ∗
  kit.storeAt sessionStorePtr sst0

abbrev stageP4PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr
    v_3d0 (coroOpkIdAtP4 coroPtr opkId?) kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
    baseKey sst0 ist0 pst0 kst0 G ssSt

def stageP4ExitAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) : SepProp :=
  stageP4SharedPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
    ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  outSlot ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kpkKit.storeAt kyberStorePtr kstf ∗
  pkKit.storeAt preKeyStorePtr pstf ∗
  kit.storeAt sessionStorePtr sstf

set_option maxHeartbeats 800000 in
/-- Budget-threaded `[LibsignalPlacement]` 4-kit Stage P4 Kyber `mark_used` refusal theorem
(`mark`-only kit) preserving `calleeSavedVRegs`. -/
theorem stageP4_kyber_refused_vregs_mark_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext) (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hfits : FitsEnv M lim st0
      (StageP4SaveMarkBudgetEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4PrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ssSt)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent),
            StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
              peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit s0 s sf
              coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
              (speErrAt kpkKit.markErr outPtr e) kyberPreKeyId signedPreKeyId pt peer remoteIk
              baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))) ∨
         (∃ (evs : List AllocEvent),
            StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit s0 s sf
              coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
              (savePollPlacedOutAt outPtr (.error ())) kyberPreKeyId signedPreKeyId pt peer
              remoteIk baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0
              kst0))))
      Qp := by
  have hsp_kr : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (kyberRefusedStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  let F_ext : SepProp :=
    ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
    ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
    ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
    ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
    memRegion (s.sp + 0x310#64) 36 ∗
    memRegion (s.sp + 0x340#64) 36 ∗
    pkKit.storeAt preKeyStorePtr pst0 ∗
    kit.storeAt sessionStorePtr sst0 ∗
    memRegion (s.sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
      (stageP4CallStack kit ikit pkKit kpkKit - kyberRefusedCallStack ikit kpkKit)
  let Qpost : State → SepProp → Prop := fun sf Pf =>
    Steps (lsProg_518 ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
    ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
    ((∃ c e evs,
        StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
          peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∧
        ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
        kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
        sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
          kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
        (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit s0 s sf
          coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
          kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
          (speErrAt kpkKit.markErr outPtr e) kyberPreKeyId signedPreKeyId pt peer remoteIk
          baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))) ∨
     (∃ evs,
        StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs ∧
        ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
        sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
        (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit s0 s sf
          coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
          kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
          (savePollPlacedOutAt outPtr (.error ())) kyberPreKeyId signedPreKeyId pt peer remoteIk
          baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)))
  have hbody : ∀ (opkIdIsSome opkId : BitVec 32), opkIdIsSome - 2#32 ≠ 0#32 →
      (((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId) ⊢
        coroOpkIdAtP4 coroPtr opkId?) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ssSt)
        Qpost Qp := by
    intro opkIdIsSome opkId hopk_ne2 hopk_fold
    have hcore := stageP4_kyber_refused_core_vregs_mark_placed_ok ext ikit ikitEnv kpkKit kpkKitEnv
      hdealloc hDropSS3 hikit hiVt hkpkKit hkVt (Qp := fun _ _ => False) st0 s0 s
      coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr
      prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId kyberPreKeyId signedPreKeyId
      b_2c0 pt peer remoteIk baseKey ist0 kst0 G ssSt
      haddr_id hmarkOk hrefused hfits hopk_ne2 hpt_le hsp_kr hfs hcro hpc hrun hsp_align
      hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    have hpre_eq :
        stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ssSt =
        kyberRefusedPrePlaced A lim st0 ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey ist0 kst0 G ssSt ∗ F_ext := by
      unfold stageP4RawPrePlaced stageP4SharedPlaced kyberRefusedPrePlaced kyberRefusedSharedPlaced
        F_ext
      rw [stack_stageP4_to_kyberRefused kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_ac_rfl
    refine sepWPp_frame_false hcore hpre_eq
      fun sf P1 ⟨hst, hspf, hcsf, hvregsf, hcrof, hbr⟩ =>
        ⟨hst, hspf, hcsf, hvregsf, hcrof, ?_⟩
    rcases hbr with ⟨c, e, evs, hevs, hr1, hr2, htr, hP1⟩ | ⟨evs, hevs, hr1, htr, hP1⟩
    · refine Or.inl ⟨c, e, evs, hevs, hr1, hr2, htr, Entails.trans (sepConj_mono_left hP1)
        (Entails.replace_factor hopk_fold
          (by unfold kyberRefusedMarkErrPostPlaced kyberRefusedSharedPlaced F_ext; sep_focus)
          (by
            unfold stageP4ExitAtPlaced stageP4SharedPlaced
            rw [stack_stageP4_to_kyberRefused kit ikit pkKit kpkKit s.sp hsp_ub]
            sep_ac_rfl))⟩
    · refine Or.inr ⟨evs, hevs, hr1, htr, Entails.trans (sepConj_mono_left hP1)
        (Entails.replace_factor hopk_fold
          (by unfold kyberRefusedSaveErrPostPlaced kyberRefusedSharedPlaced F_ext; sep_focus)
          (by
            unfold stageP4ExitAtPlaced stageP4SharedPlaced
            rw [stack_stageP4_to_kyberRefused kit ikit pkKit kpkKit s.sp hsp_ub]
            sep_ac_rfl))⟩
  cases opkId? with
  | none =>
    unfold stageP4PrePlaced stageP4RawPrePlaced coroOpkIdAtP4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun opkIdDummy => ?_
    exact hbody 0#32 opkIdDummy (by decide)
      (by unfold coroOpkIdAtP4; exact Entails.sepExists_right opkIdDummy (Entails.refl _))
  | some opkId =>
    exact hbody 1#32 opkId (by decide) (Entails.refl _)

theorem stageP4_kyber_refused_vregs_kits_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext) (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hfits : FitsEnv M lim st0
      (StageP4SaveMarkBudgetEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4PrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ssSt)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent),
            StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
              peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit s0 s sf
              coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
              (speErrAt kpkKit.markErr outPtr e) kyberPreKeyId signedPreKeyId pt peer remoteIk
              baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))) ∨
         (∃ (evs : List AllocEvent),
            StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs ∧
            ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit s0 s sf
              coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
              kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
              (savePollPlacedOutAt outPtr (.error ())) kyberPreKeyId signedPreKeyId pt peer
              remoteIk baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0
              kst0))))
      Qp :=
  stageP4_kyber_refused_vregs_mark_placed_ok ext kit ikit ikitEnv pkKit kpkKit kpkKitEnv
    hdealloc hDropSS3 hikit hiVt (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt
    st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId
    signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ssSt
    haddr_id hmarkOk hrefused hfits hpt_le hsp_ub hfs hcro hpc hrun hsp_align
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget
