/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges

/-!
# SPE Error-Ownership and Store Impossibility Bridges

Converts error layouts emitted by Stages P1–P4 (`stageP3ErrPost`, `recordResultAt`, `speErrAt`,
and `apiDecResultAt`) into `decResAt E2E.HooksE.A0 out (.error err) ∗ anyHeap` for packaging via
`dpPollPost_of_decResAt`, and discharges impossible `.error` branches on `cliPollSessKit.storeRel`
and `cliPollIdKit.saveRel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Low-Level `memRegion` & `vecU8` Packing Helpers -/

theorem entails_sepConj_anyHeap (P : SepProp) : P ⊢ P ∗ anyHeap := by
  have hemp : P = P ∗ emp := (sepConj_emp P).symm
  conv => lhs; rw [hemp]
  exact sepConj_mono_right (entails_anyHeap emp)

theorem words2_at20_entails_memRegion16 (p w4 w5 : BitVec 64) :
    ((p + 0x20#64) ↦₆₄ w4) ∗ ((p + 0x28#64) ↦₆₄ w5) ⊢ memRegion (p + 0x20#64) 16 := by
  rw [ProofLib.memRegion_split' (b := p + 0x20#64) (n := 8) (k := 8)
        (b' := p + 0x28#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)

theorem words5_at08_entails_memRegion40 (p w1 w2 w3 w4 w5 : BitVec 64) :
    ((p + 0x08#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗
    ((p + 0x20#64) ↦₆₄ w4) ∗ ((p + 0x28#64) ↦₆₄ w5) ⊢ memRegion (p + 0x08#64) 40 := by
  rw [ProofLib.memRegion_split' (b := p + 0x08#64) (n := 8) (k := 32)
        (b' := p + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x10#64) (n := 8) (k := 24)
        (b' := p + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x18#64) (n := 8) (k := 16)
        (b' := p + 0x20#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (words2_at20_entails_memRegion16 p w4 w5)))

theorem words3_heap_entails_exists_vecU8 (A : RustAlloc) (p cap ptr len : BitVec 64) :
    (((p + 0x08#64) ↦₆₄ cap) ∗ ((p + 0x10#64) ↦₆₄ ptr) ∗ ((p + 0x18#64) ↦₆₄ len)) ∗
    (∃∗ bs : List (BitVec 8),
      ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ⊢
    ∃∗ bs : List (BitVec 8), RustHeap.vecU8 A (p + 0x08#64) bs := by
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  have hpull :
      (((p + 0x08#64) ↦₆₄ cap) ∗ ((p + 0x10#64) ↦₆₄ ptr) ∗ ((p + 0x18#64) ↦₆₄ len)) ∗
      (⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
      ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((p + 0x08#64) ↦₆₄ cap) ∗ ((p + 0x10#64) ↦₆₄ ptr) ∗ ((p + 0x18#64) ↦₆₄ len) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
    ac_rfl
  rw [hpull]
  refine Entails.pure_left fun ⟨hlen, hle, hlt, hnz⟩ => ?_
  subst hlen
  refine Entails.sepExists_right bs ?_
  unfold RustHeap.vecU8 vecU8At vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have h10 : (p + 0x08#64) + 8#64 = p + 0x10#64 := by bv_omega
  have h18 : (p + 0x08#64) + 16#64 = p + 0x18#64 := by bv_omega
  rw [h10, h18]
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hle, hlt, hnz⟩⟩
  rw [hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Structured `speAt` / `recordResultAt` / `SpeErrSpec` → `decResAt` Bridges -/

theorem speAt_entails_decResAt_err (A : RustAlloc) (fnName : List (BitVec 8))
    (out : BitVec 64) (e : SignalProtocolError) (err : ApiError AddrVal Unit) :
    speAt A fnName out e ⊢ decResAt A out (.error err) :=
  speOwnedAt_entails_decResAt_err A out (.proto fnName e) err

theorem recordResultAt_err_entails_decResAt (A : RustAlloc) (out : BitVec 64)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit) :
    recordResultAt A out (.error e) ⊢ decResAt A out (.error err) :=
  recordResultAt_err_owned A out e

theorem plainSpeWords_entails_decResAt_err (A : RustAlloc) (out : BitVec 64)
    (i : Nat) (hi : RunDrop.PlainSpeTag i) (w1 w2 w3 w4 w5 : BitVec 64)
    (err : ApiError AddrVal Unit) :
    speWordsAt out (speWord i) w1 w2 w3 w4 w5 ⊢ decResAt A out (.error err) := by
  unfold speWordsAt
  refine Entails.trans (sepConj_mono_right (words5_at08_entails_memRegion40 out w1 w2 w3 w4 w5)) ?_
  exact speOwnedAt_entails_decResAt_err A out (.plain i hi) err

theorem strSpeWords_entails_decResAt_anyHeap (A : RustAlloc) (out : BitVec 64)
    (i : Nat) (hi : RunDrop.StrSpeTag i) (cap ptr len w4 w5 : BitVec 64)
    (Extra : SepProp) (err : ApiError AddrVal Unit) :
    speWordsAt out (speWord i) cap ptr len w4 w5 ∗
    ((∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗ Extra) ⊢
    decResAt A out (.error err) ∗ anyHeap := by
  have hreord :
      speWordsAt out (speWord i) cap ptr len w4 w5 ∗
      ((∃∗ bs : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗ Extra) =
      ((out ↦₆₄ speWord i) ∗
        ((((out + 0x08#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗ ((out + 0x18#64) ↦₆₄ len)) ∗
          (∃∗ bs : List (BitVec 8),
            ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (if cap = 0 then emp
             else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
               memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))) ∗
        (((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5))) ∗ Extra := by
    unfold speWordsAt
    ac_rfl
  rw [hreord]
  refine sepConj_mono ?_ (entails_anyHeap Extra)
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (words3_heap_entails_exists_vecU8 A out cap ptr len)
        (words2_at20_entails_memRegion16 out w4 w5))) ?_
  exact speOwnedAt_entails_decResAt_err A out (.withString i hi) err

theorem cliReadErrSpec_entails_decResAt_anyHeap (A : RustAlloc) (out : BitVec 64)
    (e : CliReadErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliReadErrSpec A) out e ⊢ decResAt A out (.error err) ∗ anyHeap := by
  dsimp only [speErrAt, cliReadErrSpec, cliReadErrHeap]
  exact strSpeWords_entails_decResAt_anyHeap A out 1 (by decide)
    e.cap e.ptr e.len e.w4 e.w5 _ err

theorem cliGetErrSpec_entails_decResAt_anyHeap (A : RustAlloc) (out : BitVec 64)
    (w : Nat) (hw : w < 32) (hw_plain : RunDrop.PlainSpeTag w)
    (e : CliGetErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliGetErrSpec A w hw) out e ⊢ decResAt A out (.error err) ∗ anyHeap := by
  rcases e with ⟨tag, cap, ptr, len, w4, w5⟩
  cases tag with
  | missing =>
    dsimp only [speErrAt, cliGetErrSpec]
    rw [sepConj_emp]
    exact Entails.trans
      (plainSpeWords_entails_decResAt_err A out w hw_plain cap ptr len w4 w5 err)
      (entails_sepConj_anyHeap _)
  | decodeErr =>
    dsimp only [speErrAt, cliGetErrSpec]
    rw [sepConj_emp]
    exact Entails.trans
      (plainSpeWords_entails_decResAt_err A out 2 (by decide) cap ptr len w4 w5 err)
      (entails_sepConj_anyHeap _)
  | readErr =>
    dsimp only [speErrAt, cliGetErrSpec, cliReadErrHeap]
    exact strSpeWords_entails_decResAt_anyHeap A out 1 (by decide) cap ptr len w4 w5 _ err

theorem cliKpkMarkErrSpec_entails_decResAt_anyHeap (A : RustAlloc) (out : BitVec 64)
    (e : CliKpkMarkErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliKpkMarkErrSpec A) out e ⊢ decResAt A out (.error err) ∗ anyHeap := by
  rcases e with ⟨ans, hne, cap, ptr, len, w4, w5⟩
  cases ans with
  | ok => exact absurd rfl hne
  | reused =>
    dsimp only [speErrAt, cliKpkMarkErrSpec]
    exact strSpeWords_entails_decResAt_anyHeap A out 24 (by decide) cap ptr len w4 w5 emp err
  | readErr =>
    dsimp only [speErrAt, cliKpkMarkErrSpec]
    exact strSpeWords_entails_decResAt_anyHeap A out 1 (by decide) cap ptr len w4 w5 _ err
  | malformed =>
    dsimp only [speErrAt, cliKpkMarkErrSpec]
    exact strSpeWords_entails_decResAt_anyHeap A out 1 (by decide) cap ptr len w4 w5 emp err

/-! ## 3. Concrete `cliPoll*Kit` Error Bridges & `storeRel` / `saveRel` Impossibility -/

theorem apiDecResultAt_proto_entails_decResAt (A : RustAlloc) (out : BitVec 64)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit) :
    apiDecResultAt A out (.error (.protocol e)) ⊢ decResAt A out (.error err) :=
  recordResultAt_err_entails_decResAt A out e err

theorem cliSelfSpeErrSpec_entails_decResAt_err (A : RustAlloc) (out : BitVec 64)
    (e : CliSelfSpeErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliSelfSpeErrSpec A) out e ⊢ decResAt A out (.error err) :=
  Entails.trans (Entails.sepExists_right e (Entails.refl _))
    (cliSelfSpeErrAt_biEntails A out).1

theorem cliPollPk_getErr_entails_decResAt_anyHeap (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollPkKit A b F0 pid σ).GetErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollPkKit A b F0 pid σ).getErr out e ⊢ decResAt A out (.error err) ∗ anyHeap :=
  cliGetErrSpec_entails_decResAt_anyHeap A out 13 (by decide) (by decide) e err

theorem cliPollSpk_getErr_entails_decResAt_anyHeap (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (sid : BitVec 32) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollSpkKit A b F0 sid σ).GetErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSpkKit A b F0 sid σ).getErr out e ⊢ decResAt A out (.error err) ∗ anyHeap :=
  cliGetErrSpec_entails_decResAt_anyHeap A out 14 (by decide) (by decide) e err

theorem cliPollKpk_getErr_entails_decResAt_anyHeap (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (kid ksid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollKpkKit A b F0 kid ksid kbk σ).GetErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollKpkKit A b F0 kid ksid kbk σ).getErr out e ⊢
      decResAt A out (.error err) ∗ anyHeap :=
  cliGetErrSpec_entails_decResAt_anyHeap A out 15 (by decide) (by decide) e err

theorem cliPollPk_removeErr_entails_decResAt_anyHeap (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollPkKit A b F0 pid σ).RemoveErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollPkKit A b F0 pid σ).removeErr out e ⊢
      decResAt A out (.error err) ∗ anyHeap :=
  cliReadErrSpec_entails_decResAt_anyHeap A out e err

theorem cliPollKpk_markErr_entails_decResAt_anyHeap (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (kid ksid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollKpkKit A b F0 kid ksid kbk σ).MarkErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollKpkKit A b F0 kid ksid kbk σ).markErr out e ⊢
      decResAt A out (.error err) ∗ anyHeap :=
  cliKpkMarkErrSpec_entails_decResAt_anyHeap A out e err

theorem cliPollSelf_kpErr_entails_decResAt_err (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollSelfKit A b F0 peer σ).KpErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKit A b F0 peer σ).kpErr out e ⊢ decResAt A out (.error err) :=
  cliSelfSpeErrSpec_entails_decResAt_err A out e err

theorem cliPollSelf_regIdErr_entails_decResAt_err (A : RustAlloc) (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) (out : BitVec 64)
    (e : (cliPollSelfKit A b F0 peer σ).RegIdErr) (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKit A b F0 peer σ).regIdErr out e ⊢ decResAt A out (.error err) :=
  cliSelfSpeErrSpec_entails_decResAt_err A out e err

theorem cliSess_storeRel_not_err {A : RustAlloc} {b : BitVec 64} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {σ : DpKitStk}
    {d : DirGhost} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))} :
    ¬ (cliPollSessKit A b F0 Scope peer σ).storeRel d rem r (.error ()) :=
  nofun

theorem cliId_saveRel_not_err {A : RustAlloc} {b : BitVec 64} {F0 : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} :
    ¬ (cliPollIdKit A b F0 peer σ).saveRel g rem k (.error ()) := by
  rintro ⟨_, _, ⟨⟩⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

