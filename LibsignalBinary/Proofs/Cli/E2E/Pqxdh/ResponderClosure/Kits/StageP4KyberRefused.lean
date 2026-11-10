/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P4 Kyber Pre-Key Refusal Arm and 4-Kit Spatial Predicates

Verifies the Stage P4 Kyber pre-key refusal path (`stageP4_kyber_refused_core_kits_ok` and
`stageP4_kyber_refused_kits_ok`, `+0x34dc → s0.readReg64 .x30`) when `mark_kyber_pre_key_used`
refuses (`∀ u, ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok u)`), and defines
the shared 4-kit Stage P4 spatial predicates (`stageP4Shared`, `stageP4Pre`, `stageP4ExitAt`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Stack, coroutine slot, and `StageP3GenStmt` bridge helpers -/

/-- Stack budget for the Kyber pre-key refusal path (`P4.1` `save_identity` and `P4.2`
`mark_kyber_pre_key_used` plus their error-unwind tails). -/
def kyberRefusedCallStack {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit) (markKyberCallStack kpkKit)

theorem stack_kyberRefused_to_saveId {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64) :
    stackAt sp (kyberRefusedCallStack ikit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
        (kyberRefusedCallStack ikit kpkKit - saveIdCallStack ikit) ∗
        stackAt sp (saveIdCallStack ikit) :=
  P3P4.stackAt_sub_eq sp _ _ (Nat.le_max_left _ _) hn

theorem stack_kyberRefused_to_markKyber {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64) :
    stackAt sp (kyberRefusedCallStack ikit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
        (kyberRefusedCallStack ikit kpkKit - markKyberCallStack kpkKit) ∗
        stackAt sp (markKyberCallStack kpkKit) :=
  P3P4.stackAt_sub_eq sp _ _ (Nat.le_max_right _ _) hn

theorem kyberRefusedStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    kyberRefusedCallStack ikit kpkKit ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.max_le.mpr ⟨saveIdStack_le_stageP4 kit ikit pkKit kpkKit,
    markKyberStack_le_stageP4 kit ikit pkKit kpkKit⟩

theorem stack_stageP4_to_kyberRefused {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64) :
    stackAt sp (stageP4CallStack kit ikit pkKit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
        (stageP4CallStack kit ikit pkKit kpkKit - kyberRefusedCallStack ikit kpkKit) ∗
        stackAt sp (kyberRefusedCallStack ikit kpkKit) :=
  P3P4.stackAt_sub_eq sp _ _ (kyberRefusedStack_le_stageP4 kit ikit pkKit kpkKit) hn

/-- Lift a Stage P4 `SepWPp` under `P3P4.PanicOomProp s0` into `StageP3GenStmt`'s `genP3S5PanicProp`
    continuation at `+0x34dc`. -/
theorem SepWPp.to_genP3S5PanicProp {prog : Program} {ret : BitVec 64}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) :=
  SepWPp.mono_panic (fun _ _ hp => Or.inl hp) h

/-- Coroutine `opk_id : Option<u32>` representation at `coroPtr + 0x298..0x2a0` entering Stage P4
    (definitionally equal to `TopLevel.coroOpkIdAt`). -/
def coroOpkIdAtP4 (coroPtr : BitVec 64) (opkId? : Option (BitVec 32)) : SepProp :=
  match opkId? with
  | none => ∃∗ opkIdDummy : BitVec 32,
      ((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy)
  | some opkId =>
      ((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId)

theorem coro298_split_eq (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x298#64) ↦₆₄ (hi ++ lo)) =
      ((coroPtr + 0x298#64) ↦₃₂ lo) ∗ ((coroPtr + 0x29c#64) ↦₃₂ hi) := by
  have h : coroPtr + 0x29c#64 = (coroPtr + 0x298#64) + 4#64 := by bv_omega
  rw [h, ← pointsTo32_pair_eq]

theorem coro2ac_words_entails_memRegion20 (coroPtr : BitVec 64)
    (w0 w1 w2 w3 w4 : BitVec 32) :
    ((coroPtr + 0x2ac#64) ↦₃₂ w0) ∗
    ((coroPtr + 0x2b0#64) ↦₃₂ w1) ∗
    ((coroPtr + 0x2b4#64) ↦₃₂ w2) ∗
    ((coroPtr + 0x2b8#64) ↦₃₂ w3) ∗
    ((coroPtr + 0x2bc#64) ↦₃₂ w4) ⊢
      memRegion (coroPtr + 0x2ac#64) 20 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2ac#64) (n := 4) (k := 16)
        (b' := coroPtr + 0x2b0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2b0#64) (n := 4) (k := 12)
        (b' := coroPtr + 0x2b4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2b4#64) (n := 4) (k := 8)
        (b' := coroPtr + 0x2b8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2b8#64) (n := 4) (k := 4)
        (b' := coroPtr + 0x2bc#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo32_entails_memRegion _ _))))

theorem sp3e0_344_eq_48_296 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 296 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 296)
    (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)
/-! ## Read-only vtable drop and postcondition weakening combinators -/

/-- Replace a sub-assertion `A ⊢ B` inside a large `SepProp` entailment `P ⊢ Q` via `sep_focus`
    on `P = A ∗ R` and `ac_rfl` on `B ∗ R = Q`. -/
theorem Entails.replace_factor {A B R P Q : SepProp}
    (hab : A ⊢ B) (hp : P = A ∗ R) (hq : B ∗ R = Q) : P ⊢ Q := by
  rw [hp, ← hq]
  exact sepConj_mono_left hab

/-- Drop a left factor `Drop` (such as `.rodata` vtable assertions introduced from `FrozenLoaded`)
    from a `SepWPp` spatial precondition while keeping any caller frame `R` intact. -/
theorem SepWPp.drop_pre_left {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem SepWPp.drop_pre_of_entails {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hdrop : P ⊢ Drop ∗ P')
    (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.weaken_pre hdrop (SepWPp.drop_pre_left h)

/-- Absorb an existentially witnessed left factor `Drop` at a `SepWPp` return postcondition while
    preserving the caller's arbitrary frame `R`. -/
theorem SepWPp.congr_post_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q2 Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P_f => ∃ Drop P_clean, (P_f ⊢ Drop ∗ P_clean) ∧ Q2 sf P_clean) Qp) :
    SepWPp prog ret s P Q2 Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, Drop, P_clean, hent, hQ2⟩ | hpan | hoom
  · have hmf' : sf.mem ⊨ (Drop ∗ P_clean) ∗ R :=
      Arm64.Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hmf'
    exact Or.inl ⟨hpc, hrun, P_clean, Satisfies.of_sep_right hmf', hQ2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

/-! ## Core 2-kit Kyber `mark_used` refusal theorem -/

/-- Shared spatial resources across `P4.1` and `P4.2` on the 2-kit Kyber refusal path. -/
def kyberRefusedShared {A : RustAlloc} (img : Obj.Image)
    (ikit : IdentityStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
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
  protocolAddressAt A peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  logOff img ∗
  A.pool ∗
  stackAt s.sp (kyberRefusedCallStack ikit kpkKit)

/-- Spatial precondition at `+0x34dc` for `stageP4_kyber_refused_core_kits_ok`. -/
def kyberRefusedPre {A : RustAlloc} (img : Obj.Image)
    (ikit : IdentityStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  kyberRefusedShared img ikit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
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

/-- Spatial postcondition on the Kyber refusal arm: `speErrAt kpkKit.markErr outPtr e`, `ikit`
updated by `saveUpdate ... (.ok c)`, and `kpkKit` updated by `markUpdate ... (.error e)`. -/
def kyberRefusedMarkErrPost {A : RustAlloc} (img : Obj.Image)
    (ikit : IdentityStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (c : IdentityChange) (e : kpkKit.MarkErr) : SepProp :=
  kyberRefusedShared img ikit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  speErrAt kpkKit.markErr outPtr e ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) ∗
  kpkKit.storeAt kyberStorePtr (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))

/-- Spatial postcondition of `stageP4_kyber_refused_core_kits_ok` when `P4.1` `save_identity` errors
    before reaching `P4.2` (`kpkKit.storeAt` untouched). -/
def kyberRefusedSaveErrPost {A : RustAlloc} (img : Obj.Image)
    (ikit : IdentityStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState) : SepProp :=
  kyberRefusedShared img ikit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  savePollOutAt img.base outPtr (.error ()) ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) ∗
  kpkKit.storeAt kyberStorePtr kst0

set_option maxHeartbeats 1200000 in
/-- Verifies the 2-kit Kyber `mark_used` refusal path (`+0x34dc → s0.readReg64 .x30`), requiring
only `ikit` and `kpkKit`: runs `save_identity` and, on `Ok c`, takes the `mark_kyber_pre_key_used`
`Err(e)` refusal arm and unwinds via `+0x54c → +0x550`. -/
theorem stageP4_kyber_refused_core_kits_ok_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kyberRefusedPre img ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        ist0 kst0 G st)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr),
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ kyberRefusedMarkErrPost img ikit kpkKit s0 s coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
              opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0 c e)) ∨
         (ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ kyberRefusedSaveErrPost img ikit kpkKit s0 s coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
              opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0))))
      (PanicOomProp s0) := by
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
      kyberRefusedPre img ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        ist0 kst0 G st ⊢
      stageP4SaveIdPre img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
        kyberStorePtr kpkKit.kpk_vt prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G st ∗ F1 := by
    unfold kyberRefusedPre kyberRefusedShared stageP4SaveIdPre stageP4SaveIdShared F1
    rw [stack_kyberRefused_to_saveId ikit kpkKit s.sp hsp_ub]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre1 ?_
  refine stageP4_saveIdentity_dispatch_kits_p4 img ext ikit hA hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (img.base + kpkKit.markShimOff) prevStatesPtr ptCap ptPtr v_3d0
    opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G st F1 _
    hb haddr_id hopk_ne2 hpt_le hsp_save
    (fun hF' hP' => hkVt.markSlot hF' hP')
    (hfs.mono (fun _ h => h.1) (fun h => h.1))
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hF1 hsym1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hFf hsymf hPf => ?_)
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
      protocolAddressAt A peer remoteAddrPtr ∗
      (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
      logOff img ∗
      ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) ∗
      memRegion (s.sp - BitVec.ofNat 64 (kyberRefusedCallStack ikit kpkKit))
        (kyberRefusedCallStack ikit kpkKit - markKyberCallStack kpkKit)
    have hdrop1 :
        P1 ⊢ (saveIdVtablesAt ikit ∗ ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff))) ∗
          (stageP4MarkKyberPre img kpkKit s0 s1 coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
            ptCap ptPtr b_2c0 pt baseKey kst0 G st ∗ F2) := by
      refine Entails.trans hP1 ?_
      exact Entails.replace_factor
        (Entails.of_eq ((stack_kyberRefused_to_saveId ikit kpkKit s.sp hsp_ub).symm.trans
          (stack_kyberRefused_to_markKyber ikit kpkKit s.sp hsp_ub)))
        (by unfold stageP4SaveIdOkPost stageP4SaveIdShared F1; sep_focus)
        (by unfold stageP4MarkKyberPre stageP4MarkKyberShared F2; rw [hsp1]; ac_rfl)
    refine SepWPp.drop_pre_of_entails hdrop1 ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := (hfs.of_steps hst1 htr1 (fun hQ => hQ.1.2 peer.val remoteIk (.ok c))).mono
      (fun _ h => h.2) (fun h => h.2)
    refine stageP4_markKyber_to_38c_kits_p4 img ext kpkKit hA hDropSS3 hkpkKit hkVt
      s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
      kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G st F2 _
      hb hmarkOk hpt_le hsp_mark hfs1 hF1 hsym1 hpc1 hrun1 hsp1_align htr1_pfx
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1
      (fun _ _ _ _ hrel_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ => (hrefused hrel_ok).elim)
      (fun e sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hFf hsymf hPf => ?_)
    refine ⟨markKyberVtablesAt kpkKit,
      kyberRefusedMarkErrPost img ikit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0 c e,
      ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hFf, hsymf,
      Or.inl ⟨c, e, hrel1, hrel2, by rw [htr2, htr1, List.append_assoc], Entails.refl _⟩⟩
    refine Entails.trans hPf
      (Entails.replace_factor
        (coro2ac_words_entails_memRegion20 coroPtr opkIdIsSome opkId 1#32 kyberPreKeyId signedPreKeyId)
        (by
          unfold stageP4MarkKyberErrPost stageP4MarkKyberShared F2
          rw [hsp1, coro298_split_eq coroPtr opkIdIsSome opkId]
          sep_focus)
        (by
          unfold kyberRefusedMarkErrPost kyberRefusedShared
          rw [stack_kyberRefused_to_markKyber ikit kpkKit s.sp hsp_ub]
          ac_rfl))
  · -- P4.1 Err() arm
    refine ⟨saveIdVtablesAt ikit ∗ ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)),
      kyberRefusedSaveErrPost img ikit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0,
      ?_, hstf, hspf, hcsf, hFf, hsymf,
      Or.inr ⟨hrelf, htrf, Entails.refl _⟩⟩
    refine Entails.trans hPf ?_
    unfold stageP4SaveIdErrPost stageP4SaveIdShared kyberRefusedSaveErrPost kyberRefusedShared F1
    rw [stack_kyberRefused_to_saveId ikit kpkKit s.sp hsp_ub]
    exact Entails.of_eq (by ac_rfl)

theorem stageP4_kyber_refused_core_kits_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : kyberRefusedCallStack ikit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kyberRefusedPre img ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        ist0 kst0 G st)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr),
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ kyberRefusedMarkErrPost img ikit kpkKit s0 s coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
              opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0 c e)) ∨
         (ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ kyberRefusedSaveErrPost img ikit kpkKit s0 s coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
              opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ist0 kst0))))
      (PanicOomProp s0) :=
  stageP4_kyber_refused_core_kits_ok_p4 img ext ikit kpkKit (.of_allocContracts hA) hDropSS3
    hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId kyberPreKeyId
    signedPreKeyId b_2c0 pt peer remoteIk baseKey ist0 kst0 G st hb haddr_id hmarkOk hrefused
    hopk_ne2 hpt_le hsp_ub hfs hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28

/-! ## Unified 4-kit Stage P4 spatial predicates and refusal corollary -/

/-- Combined `envOk` predicate across all four stores touched in Stage P4. -/
def stageP4EnvOk {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) (f : FsFiles) : Prop :=
  kit.envOk f ∧ ikit.envOk f ∧ pkKit.envOk f ∧ kpkKit.envOk f

/-- Combined `Quiet` predicate across all four stores touched in Stage P4. -/
def stageP4Quiet {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) : Prop :=
  kit.Quiet ∧ ikit.Quiet ∧ pkKit.Quiet ∧ kpkKit.Quiet

/-- Shared spatial resources preserved across all of Stage P4 (`+0x34dc → s0.readReg64 .x30`). -/
def stageP4Shared {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
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
  protocolAddressAt A peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  logOff img ∗
  A.pool ∗
  stackAt s.sp (stageP4CallStack kit ikit pkKit kpkKit)

/-- Full 4-kit Stage P4 entry assertion at `+0x34dc` parameterized by an `opkSlot` assertion
    at `coroPtr + 0x298..0x2a0`. -/
def stageP4RawPre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4Shared img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
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

/-- Full 4-kit Stage P4 entry assertion at `+0x34dc` over `opkId? : Option (BitVec 32)`. -/
abbrev stageP4Pre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    (coroOpkIdAtP4 coroPtr opkId?) kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
    sst0 ist0 pst0 kst0 G st

/-- Exit spatial assertion common to all five Stage P4 outcomes (`Ok` and the four store `Err`s),
    parameterized by `(opkSlot outSlot : SepProp)` and the final four store states. -/
def stageP4ExitAt {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) : SepProp :=
  stageP4Shared img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
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

/-- Frames untouched `pkKit.storeAt` and `kit.storeAt` onto `stageP4_kyber_refused_core_kits_ok`
over the full 4-kit `stageP4Pre` frame. -/
theorem stageP4_kyber_refused_kits_ok_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G st)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr),
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
              sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
              (coroOpkIdAtP4 coroPtr opkId?) (speErrAt kpkKit.markErr outPtr e) kyberPreKeyId signedPreKeyId
              pt peer remoteIk baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))) ∨
         (ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
              remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
              ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
              (savePollOutAt img.base outPtr (.error ()))
              kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0
              (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0))))
      (PanicOomProp s0) := by
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
    Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
    ClosureCalleeSavedP4 s0 sf ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
    ((∃ c e, ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
        kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
        sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
          kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
        (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (coroOpkIdAtP4 coroPtr opkId?) (speErrAt kpkKit.markErr outPtr e) kyberPreKeyId signedPreKeyId
          pt peer remoteIk baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))) ∨
     (ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
        sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
        (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (coroOpkIdAtP4 coroPtr opkId?) (savePollOutAt img.base outPtr (.error ()))
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0
          (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)))
  have hbody : ∀ (opkIdIsSome opkId : BitVec 32), opkIdIsSome - 2#32 ≠ 0#32 →
      (((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId) ⊢
        coroOpkIdAtP4 coroPtr opkId?) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (stageP4RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
          ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G st)
        Qpost (PanicOomProp s0) := by
    intro opkIdIsSome opkId hopk_ne2 hopk_fold
    have hcore := stageP4_kyber_refused_core_kits_ok_p4 img ext ikit kpkKit hA hDropSS3
      hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
      kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey ist0 kst0 G st
      hb haddr_id hmarkOk hrefused hopk_ne2 hpt_le hsp_kr hfs hF hsym hpc hrun hsp_align
      htr_pfx hx19 hx24 hx25 hx26 hx27 hx28
    have hpre_eq :
        stageP4RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
          ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G st =
        kyberRefusedPre img ikit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
          idStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdIsSome opkId
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey ist0 kst0 G st ∗ F_ext := by
      unfold stageP4RawPre stageP4Shared kyberRefusedPre kyberRefusedShared F_ext
      rw [stack_stageP4_to_kyberRefused kit ikit pkKit kpkKit s.sp hsp_ub]
      ac_rfl
    refine SepWPp.frame_ret_oom hcore hpre_eq fun sf P1 _ _ ⟨hst, hspf, hcsf, hFf, hsymf, hbr⟩ =>
      ⟨hst, hspf, hcsf, hFf, hsymf, ?_⟩
    rcases hbr with ⟨c, e, hr1, hr2, htr, hP1⟩ | ⟨hr1, htr, hP1⟩
    · refine Or.inl ⟨c, e, hr1, hr2, htr, Entails.trans (sepConj_mono_left hP1)
        (Entails.replace_factor hopk_fold
          (by unfold kyberRefusedMarkErrPost kyberRefusedShared F_ext; sep_focus)
          (by
            unfold stageP4ExitAt stageP4Shared
            rw [stack_stageP4_to_kyberRefused kit ikit pkKit kpkKit s.sp hsp_ub]
            ac_rfl))⟩
    · refine Or.inr ⟨hr1, htr, Entails.trans (sepConj_mono_left hP1)
        (Entails.replace_factor hopk_fold
          (by unfold kyberRefusedSaveErrPost kyberRefusedShared F_ext; sep_focus)
          (by
            unfold stageP4ExitAt stageP4Shared
            rw [stack_stageP4_to_kyberRefused kit ikit pkKit kpkKit s.sp hsp_ub]
            ac_rfl))⟩
  cases opkId? with
  | none =>
    unfold stageP4Pre stageP4RawPre coroOpkIdAtP4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun opkIdDummy => ?_
    exact hbody 0#32 opkIdDummy (by decide)
      (by unfold coroOpkIdAtP4; exact Entails.sepExists_right opkIdDummy (Entails.refl _))
  | some opkId =>
    exact hbody 1#32 opkId (by decide) (Entails.refl _)

theorem stageP4_kyber_refused_kits_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (haddr_id : ikit.addrOk peer.val)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrefused : ¬ kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (fun f => ikit.envOk f ∧ kpkKit.envOk f) (ikit.Quiet ∧ kpkKit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G st)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        ((∃ (c : IdentityChange) (e : kpkKit.MarkErr),
            ikit.saveRel ist0 peer.val remoteIk (.ok c) ∧
            kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) ++
              kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) ∧
            (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
              sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
              (coroOpkIdAtP4 coroPtr opkId?) (speErrAt kpkKit.markErr outPtr e) kyberPreKeyId signedPreKeyId
              pt peer remoteIk baseKey sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))) ∨
         (ikit.saveRel ist0 peer.val remoteIk (.error ()) ∧
            sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) ∧
            (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
              remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
              ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
              (savePollOutAt img.base outPtr (.error ()))
              kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0
              (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0))))
      (PanicOomProp s0) :=
  stageP4_kyber_refused_kits_ok_p4 img ext kit ikit pkKit kpkKit (.of_allocContracts hA) hDropSS3
    hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G st
    hb haddr_id hmarkOk hrefused hpt_le hsp_ub hfs hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
