/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.FromRecordChainCloneCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Verification of `Chain::clone [local#2]` (`0x3846c`, Block `161`)

Proves fixed-image (`chain_clone_ok`, `senderChain_clone_ok`) and relocatable `[LibsignalPlacement]`
(`chain_clone_placed_ok`, `senderChain_clone_placed_ok`) contracts for
`<session_structure::Chain as Clone>::clone [local#2]` via the unified `protoChainAt` layout.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_setPC (s : State) (v : BitVec 64) :
    calleeSavedVRegs (s.setPC v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_setPState (s : State) (p : PState) :
    calleeSavedVRegs (s.setPState p) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl

/-! ## 1. `protoChainAt` Bridge and `chainClone` / `senderChainClone` Corollaries -/

/-- Common layout predicate for `session_structure::Chain` at `a` without the receiver-vs-sender
`priv.bytes = []` or `srk.bytes.length = 33` side conditions, used as the internal specification of
`Chain::clone [local#2]` so both `chainCloneSpec` and `senderChainCloneSpec` follow by pure framing. -/
private def protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧
    gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

private def protoChainCloneSpec (A : RustAlloc) : Spec ChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s.sp chainCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) ∗
      protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def ProtoChainCloneOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName)
    (protoChainCloneSpec A)

private def ProtoChainCloneOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneName)
    (protoChainCloneSpec A)

section
set_option quotPrecheck false
local notation (priority := high) "protoChainAt" =>
  (fun (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) =>
    (⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
      vecGhostAt A gc.1.srk a ∗
      vecGhostAt A gc.1.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
        (gc.1.keys.zip gc.2.messageKeys) ∗
      optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) : SepProp))

local notation (priority := high) "protoChainCloneSpec" =>
  (fun (A : RustAlloc) =>
    ({ pre := fun x s =>
         ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
           memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s.sp chainCloneStack
       post := fun x s0 sf =>
         ⌜sf.trace = s0.trace⌝ ∗
           (∃∗ g' : ChainGhost,
             ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
               g'.keys.length = x.gc.1.keys.length⌝ ∗
             protoChainAt A (g', x.gc.2) x.dst) ∗
           protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack
       onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap } :
      Spec ChainCloneGhost))

local notation (priority := high) "ProtoChainCloneOkExt" =>
  (fun (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) =>
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName) (protoChainCloneSpec A))

local notation (priority := high) "ProtoChainCloneOk" =>
  (fun (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
      (abs : String → Option (State → State)) =>
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneName) (protoChainCloneSpec A))

theorem chainAt_eq_protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ protoChainAt A gc a) := by
  simp only [chainAt, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length ∧
        gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) =
      ((gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) ∧
        PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h4, h5⟩, h1, h2, h3⟩,
      fun ⟨⟨h4, h5⟩, h1, h2, h3⟩ => ⟨h1, h2, h3, h4, h5⟩⟩
  rw [hp]

theorem optSenderChainAt_some_eq_chainAt (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) =
      (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
        protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
          ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a) := by
  simp only [optSenderChainAt, optChainKeyAt, List.length_nil, Nat.zero_le,
    true_and, and_true, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey ∧
        g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) =
      ((g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) ∧
        PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h3, h4⟩, h1⟩,
      fun ⟨⟨h2, h3, h4⟩, h1⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hp]; rfl

theorem chainClone_of_protoChainClone_gen
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec A)) :
    subroutine_ok prog entry (chainCloneSpec A) := by
  change subroutine_ok prog entry (FromRecordChainClone.protoChainCloneSpec A) at hclone
  have hchain_eq : ∀ A gc a, chainAt A gc a =
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
        FromRecordChainClone.protoChainAt A gc a) := chainAt_eq_protoChainAt
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  simp only [chainCloneSpec, hchain_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ FromRecordChainClone.protoChainAt A x.gc x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ FromRecordChainClone.protoChainAt A x.gc x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ FromRecordChainClone.protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ FromRecordChainClone.protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (FromRecordChainClone.protoChainCloneSpec A).pre x s0 ∗ (⌜P_rc⌝ ∗ R) := by
    simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine (hclone.to_outcome x (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp).mono_outcome
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (FromRecordChainClone.protoChainAt A (g', x.gc.2) x.dst ∗
            FromRecordChainClone.protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (FromRecordChainClone.protoChainAt A (g', x.gc.2) x.dst ∗
            FromRecordChainClone.protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (FromRecordChainClone.protoChainAt A (g', x.gc.2) x.dst ∗
              FromRecordChainClone.protoChainAt A x.gc x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    simp only [chainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv', hkeys'⟩, ?_⟩
    rw [hchain_eq A (g', x.gc.2) x.dst, hchain_eq A x.gc x.src]
    have hsrk33' : g'.srk.bytes.length = 33 := by rw [hsrk', hsrk33]
    have hpriv_nil' : g'.priv.bytes = [] := hpriv'.trans hpriv_nil
    set P_rc' : Prop := g'.srk.bytes.length = 33 ∧ g'.priv.bytes = []
    change sf.mem ⊨
      (⌜P_rc'⌝ ∗ FromRecordChainClone.protoChainAt A (g', x.gc.2) x.dst) ∗
      (⌜P_rc⌝ ∗ FromRecordChainClone.protoChainAt A x.gc x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ FromRecordChainClone.protoChainAt A (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ FromRecordChainClone.protoChainAt A x.gc x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (FromRecordChainClone.protoChainAt A (g', x.gc.2) x.dst ∗
            FromRecordChainClone.protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [FromRecordChainClone.protoChainCloneSpec, chainCloneSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem chainClone_of_protoChainClone_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hclone : ProtoChainCloneOkExt b A ext) :
    ChainCloneOkExt b A ext :=
  chainClone_of_protoChainClone_gen hclone

theorem chainClone_of_protoChainClone
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hclone : ProtoChainCloneOk b C A ctl abs) :
    ChainCloneOk b C A ctl abs :=
  chainClone_of_protoChainClone_ext hclone

theorem senderChainClone_of_chainClone_gen
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hbridge : ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : subroutine_ok prog entry (protoChainCloneSpec A)) :
    subroutine_ok prog entry (senderChainCloneSpec A) := by
  change ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
    ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
      g.srk.bytes.length = 33⌝ ∗
    FromRecordChainClone.protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
      ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a at hbridge
  change subroutine_ok prog entry (FromRecordChainClone.protoChainCloneSpec A) at hclone
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  simp only [senderChainCloneSpec, hbridge, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc0 : ChainGhost × ReceiverChain :=
    (⟨x.g.srk, x.g.priv, x.g.mkCap, x.g.mkPtr, [], x.g.ck⟩,
      ⟨x.sc.ratchetKey.publicKey, some x.sc.chainKey, []⟩)
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ FromRecordChainClone.protoChainAt A gc0 x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ FromRecordChainClone.protoChainAt A gc0 x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ FromRecordChainClone.protoChainAt A gc0 x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ FromRecordChainClone.protoChainAt A gc0 x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (FromRecordChainClone.protoChainCloneSpec A).pre ⟨x.dst, x.src, gc0⟩ s0 ∗ (⌜P_sc⌝ ∗ R) := by
    simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine (hclone.to_outcome ⟨x.dst, x.src, gc0⟩ (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp).mono_outcome
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (FromRecordChainClone.protoChainAt A (g', gc0.2) x.dst ∗
            FromRecordChainClone.protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (FromRecordChainClone.protoChainAt A (g', gc0.2) x.dst ∗
            FromRecordChainClone.protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (FromRecordChainClone.protoChainAt A (g', gc0.2) x.dst ∗
              FromRecordChainClone.protoChainAt A gc0 x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    simp only [senderChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sg', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv'⟩, ?_⟩
    rw [hbridge A x.dst sg' x.sc, hbridge A x.src x.g x.sc]
    have hpriv'_eq : sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList :=
      hpriv'.trans hpriv_eq
    have hsrk33' : sg'.srk.bytes.length = 33 := by
      change g'.srk.bytes.length = 33
      rw [hsrk', hsrk33]
    let P_sc' : Prop :=
      sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
        sg'.srk.bytes.length = 33
    let gc' : ChainGhost × ReceiverChain :=
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc0.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ FromRecordChainClone.protoChainAt A gc' x.dst) ∗
      (⌜P_sc⌝ ∗ FromRecordChainClone.protoChainAt A gc0 x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ FromRecordChainClone.protoChainAt A gc' x.dst) ∗
          (⌜P_sc⌝ ∗ FromRecordChainClone.protoChainAt A gc0 x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (FromRecordChainClone.protoChainAt A gc' x.dst ∗
            FromRecordChainClone.protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [FromRecordChainClone.protoChainCloneSpec, senderChainCloneSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [FromRecordChainClone.protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem senderChainClone_of_chainClone_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hbridge : ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : ProtoChainCloneOkExt b A ext) :
    SenderChainCloneOkExt b A ext :=
  senderChainClone_of_chainClone_gen hbridge hclone

theorem senderChainClone_of_chainClone
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hbridge : ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : ProtoChainCloneOk b C A ctl abs) :
    SenderChainCloneOk b C A ctl abs :=
  senderChainClone_of_chainClone_ext hbridge hclone

end

/-! ## 2. Stack Frame Decomposition and Address Normalization for `Chain::clone [local#2]` -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm, local wp_norm]
private theorem fp_neg_48 (sp : BitVec 64) :
    sp - 96#64 + bv% (2 ^ 64 - 48) = sp - 144#64 := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem fp_neg_40 (sp : BitVec 64) :
    sp - 96#64 + bv% (2 ^ 64 - 40) = sp - 136#64 := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem fp_neg_32 (sp : BitVec 64) :
    sp - 96#64 + bv% (2 ^ 64 - 32) = sp - 128#64 := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem fp_neg_24 (sp : BitVec 64) :
    sp - 96#64 + bv% (2 ^ 64 - 24) = sp - 120#64 := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem fp_neg_12 (sp : BitVec 64) :
    sp - 96#64 + bv% (2 ^ 64 - 12) = sp - 108#64 := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem fp_neg_8 (sp : BitVec 64) :
    sp - 96#64 + bv% (2 ^ 64 - 8) = sp - 104#64 := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem fp_neg_48_int (sp : BitVec 64) :
    sp - 96#64 + (-48 : Int64).toBitVec = sp - 144#64 := fp_neg_48 sp

@[local arm64_norm, local wp_norm]
private theorem fp_neg_40_int (sp : BitVec 64) :
    sp - 96#64 + (-40 : Int64).toBitVec = sp - 136#64 := fp_neg_40 sp

@[local arm64_norm, local wp_norm]
private theorem fp_neg_32_int (sp : BitVec 64) :
    sp - 96#64 + (-32 : Int64).toBitVec = sp - 128#64 := fp_neg_32 sp

@[local arm64_norm, local wp_norm]
private theorem fp_neg_24_int (sp : BitVec 64) :
    sp - 96#64 + (-24 : Int64).toBitVec = sp - 120#64 := fp_neg_24 sp

@[local arm64_norm, local wp_norm]
private theorem fp_neg_12_int (sp : BitVec 64) :
    sp - 96#64 + (-12 : Int64).toBitVec = sp - 108#64 := fp_neg_12 sp

@[local arm64_norm, local wp_norm]
private theorem fp_neg_8_int (sp : BitVec 64) :
    sp - 96#64 + (-8 : Int64).toBitVec = sp - 104#64 := fp_neg_8 sp

namespace ChainCloneRegReadSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

end ChainCloneRegReadSimp

private theorem memRegion_eight_eq_two_four (a : BitVec 64) :
    (∃∗ v : BitVec 64, a ↦₆₄ v) =
      (∃∗ w0 : BitVec 32, a ↦₃₂ w0) ∗ (∃∗ w1 : BitVec 32, (a + 4#64) ↦₃₂ w1) := by
  rw [← memRegion_eight, ProofLib.memRegion_split a 4 4 (by decide),
    memRegion_four a, memRegion_four (a + 4#64)]

private theorem cells_sub_succ' (sp : BitVec 64) (a k : Nat) (hk : k ≠ 0) (h : 8 ≤ a) :
    cells (sp - BitVec.ofNat 64 a) k =
      (∃∗ v : BitVec 64, (sp - BitVec.ofNat 64 a) ↦₆₄ v) ∗
        cells (sp - BitVec.ofNat 64 (a - 8)) (k - 1) := by
  rw [cells_sub_succ sp a k hk h, sepExists_sepConj_left]

private theorem cells_add_succ' (ptr : BitVec 64) (a k : Nat) (hk : k ≠ 0) :
    cells (ptr + BitVec.ofNat 64 a) k =
      (∃∗ v : BitVec 64, (ptr + BitVec.ofNat 64 a) ↦₆₄ v) ∗
        cells (ptr + BitVec.ofNat 64 (a + 8)) (k - 1) := by
  have heq :
      cells (ptr + BitVec.ofNat 64 a) k =
        ∃∗ v : BitVec 64, ((ptr + BitVec.ofNat 64 a) ↦₆₄ v) ∗
          cells (ptr + BitVec.ofNat 64 (a + 8)) (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [cells_succ, Nat.add_sub_cancel]
    congr 1; funext v; congr 2
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [heq, sepExists_sepConj_left]

private theorem stackAt_chainClone_eq (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      stackAt (sp - 208#64) allocHookStack ∗
      (∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
      (∃∗ w1a : BitVec 32, (sp - 200#64) ↦₃₂ w1a) ∗
      (∃∗ w1b : BitVec 32, (sp - 196#64) ↦₃₂ w1b) ∗
      (∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
      (∃∗ w12a : BitVec 32, (sp - 112#64) ↦₃₂ w12a) ∗
      (∃∗ w12b : BitVec 32, (sp - 108#64) ↦₃₂ w12b) ∗
      (∃∗ v13 : BitVec 64, (sp - 104#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (sp - 96#64) ↦₆₄ v14) ∗
      (∃∗ v15 : BitVec 64, (sp - 88#64) ↦₆₄ v15) ∗
      (∃∗ v16 : BitVec 64, (sp - 80#64) ↦₆₄ v16) ∗
      (∃∗ v17 : BitVec 64, (sp - 72#64) ↦₆₄ v17) ∗
      (∃∗ v18 : BitVec 64, (sp - 64#64) ↦₆₄ v18) ∗
      (∃∗ v19 : BitVec 64, (sp - 56#64) ↦₆₄ v19) ∗
      (∃∗ v20 : BitVec 64, (sp - 48#64) ↦₆₄ v20) ∗
      (∃∗ v21 : BitVec 64, (sp - 40#64) ↦₆₄ v21) ∗
      (∃∗ v22 : BitVec 64, (sp - 32#64) ↦₆₄ v22) ∗
      (∃∗ v23 : BitVec 64, (sp - 24#64) ↦₆₄ v23) ∗
      (∃∗ v24 : BitVec 64, (sp - 16#64) ↦₆₄ v24) ∗
      (∃∗ v25 : BitVec 64, (sp - 8#64) ↦₆₄ v25) := by
  have hsplit := stackAt_split_cells sp allocHookStack 26 (by decide)
  change stackAt sp chainCloneStack =
    stackAt (sp - 208#64) allocHookStack ∗ cells (sp - BitVec.ofNat 64 208) 26 at hsplit
  rw [hsplit]
  simp (disch := decide) only [cells_sub_succ', Nat.reduceSub, cells_zero, sepConj_emp]
  change stackAt (sp - 208#64) allocHookStack ∗
      ((∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
      ((∃∗ v1 : BitVec 64, (sp - 200#64) ↦₆₄ v1) ∗
      ((∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
      ((∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
      ((∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
      ((∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
      ((∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
      ((∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7) ∗
      ((∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      ((∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      ((∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
      ((∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
      ((∃∗ v12 : BitVec 64, (sp - 112#64) ↦₆₄ v12) ∗
      ((∃∗ v13 : BitVec 64, (sp - 104#64) ↦₆₄ v13) ∗
      ((∃∗ v14 : BitVec 64, (sp - 96#64) ↦₆₄ v14) ∗
      ((∃∗ v15 : BitVec 64, (sp - 88#64) ↦₆₄ v15) ∗
      ((∃∗ v16 : BitVec 64, (sp - 80#64) ↦₆₄ v16) ∗
      ((∃∗ v17 : BitVec 64, (sp - 72#64) ↦₆₄ v17) ∗
      ((∃∗ v18 : BitVec 64, (sp - 64#64) ↦₆₄ v18) ∗
      ((∃∗ v19 : BitVec 64, (sp - 56#64) ↦₆₄ v19) ∗
      ((∃∗ v20 : BitVec 64, (sp - 48#64) ↦₆₄ v20) ∗
      ((∃∗ v21 : BitVec 64, (sp - 40#64) ↦₆₄ v21) ∗
      ((∃∗ v22 : BitVec 64, (sp - 32#64) ↦₆₄ v22) ∗
      ((∃∗ v23 : BitVec 64, (sp - 24#64) ↦₆₄ v23) ∗
      ((∃∗ v24 : BitVec 64, (sp - 16#64) ↦₆₄ v24) ∗
      (∃∗ v25 : BitVec 64, (sp - 8#64) ↦₆₄ v25)))))))))))))))))))))))))) = _
  rw [memRegion_eight_eq_two_four (sp - 200#64), memRegion_eight_eq_two_four (sp - 112#64)]
  have h196 : sp - 200#64 + 4#64 = sp - 196#64 := by bv_omega
  have h108 : sp - 112#64 + 4#64 = sp - 108#64 := by bv_omega
  rw [h196, h108]
  ac_rfl

private theorem memRegion_104_eq_slots (ptr : BitVec 64) :
    memRegion ptr 104 =
      (∃∗ v0 : BitVec 64, ptr ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (ptr + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (ptr + 16#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (ptr + 24#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (ptr + 32#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (ptr + 40#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (ptr + 48#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (ptr + 56#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (ptr + 64#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (ptr + 72#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (ptr + 80#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (ptr + 88#64) ↦₆₄ v11) ∗
      (∃∗ w12 : BitVec 32, (ptr + 96#64) ↦₃₂ w12) ∗
      memRegion (ptr + 100#64) 4 := by
  rw [show (104 : Nat) = 96 + 8 from rfl, ProofLib.memRegion_split ptr 96 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl, ProofLib.memRegion_split (ptr + 96#64) 4 4 (by decide),
      (memRegion_cells ptr 12 (by decide) : memRegion ptr 96 = cells ptr 12),
      memRegion_four (ptr + 96#64),
      show cells ptr 12 = cells (ptr + BitVec.ofNat 64 0) 12 by rw [BitVec.add_zero]]
  simp (disch := decide) only [cells_add_succ', Nat.reduceAdd, Nat.reduceSub, cells_zero, sepConj_emp]
  have h0 : ptr + BitVec.ofNat 64 0 = ptr := BitVec.add_zero ptr
  have h100 : ptr + 96#64 + 4#64 = ptr + 100#64 := by bv_omega
  rw [h0, h100]
  change ((∃∗ v0 : BitVec 64, ptr ↦₆₄ v0) ∗
      ((∃∗ v1 : BitVec 64, (ptr + 8#64) ↦₆₄ v1) ∗
      ((∃∗ v2 : BitVec 64, (ptr + 16#64) ↦₆₄ v2) ∗
      ((∃∗ v3 : BitVec 64, (ptr + 24#64) ↦₆₄ v3) ∗
      ((∃∗ v4 : BitVec 64, (ptr + 32#64) ↦₆₄ v4) ∗
      ((∃∗ v5 : BitVec 64, (ptr + 40#64) ↦₆₄ v5) ∗
      ((∃∗ v6 : BitVec 64, (ptr + 48#64) ↦₆₄ v6) ∗
      ((∃∗ v7 : BitVec 64, (ptr + 56#64) ↦₆₄ v7) ∗
      ((∃∗ v8 : BitVec 64, (ptr + 64#64) ↦₆₄ v8) ∗
      ((∃∗ v9 : BitVec 64, (ptr + 72#64) ↦₆₄ v9) ∗
      ((∃∗ v10 : BitVec 64, (ptr + 80#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (ptr + 88#64) ↦₆₄ v11)))))))))))) ∗
      ((∃∗ w12 : BitVec 32, (ptr + 96#64) ↦₃₂ w12) ∗ memRegion (ptr + 100#64) 4) = _
  ac_rfl

/-! ## 3. Separation-Logic and Arithmetic Helpers for Cloning `Vec<u8>`, `ChainKey`, and `MessageKey` -/

private theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  Entails.antisymm h1 h2

private theorem srk_length_pos {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : 0 < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons _ _ => exact Nat.succ_pos _

private theorem vecU8At_eq_of_nil (A : RustAlloc) (a cap ptr : BitVec 64) :
    vecU8At A a cap ptr [] =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A cap ptr [] := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]

private theorem vecGhostAt_eq_of_nil (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hnil : g.bytes = []) :
    vecGhostAt A g a =
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr [] := by
  unfold vecGhostAt
  rw [hnil, vecU8At_eq_of_nil]

private theorem vecU8At_eq_of_pos (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8At A a cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  unfold vecU8At vecHeader
  apply sepProp_eq_of_entails
  · rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : cap ≠ 0 := by
      intro h0; rw [h0] at hlen; change bs.length ≤ 0 at hlen; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    have hcomm :
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : cap ≠ 0 := by
      intro h0; rw [h0] at hlen; change bs.length ≤ 0 at hlen; omega
    rw [sepConj_pure_left_comm]
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    simp only [hne, ↓reduceIte]
    have hcomm :
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _

private theorem vecGhostAt_eq_of_pos (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hpos : 0 < g.bytes.length) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) :=
  vecU8At_eq_of_pos A a g.cap g.ptr g.bytes hpos

private theorem vecU8Buf_nil_eq (A : RustAlloc) :
    vecU8Buf A 0#64 1#64 [] = emp := by
  unfold vecU8Buf
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

private theorem vecU8Buf_pos_eq (A : RustAlloc) (ptr' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr' : ptr' ≠ 0#64) :
    vecU8Buf A (BitVec.ofNat 64 bs.length) ptr' bs =
      A.live ptr' bs.length 1 ∗ (ptr' ↦ₛ bs) := by
  unfold vecU8Buf
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [htoNat] at ht; change bs.length = 0 at ht; omega
  have hptr_ne : ptr' ≠ 0 := hptr'
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hlt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.refl _

/-- Invariant for the cloned `Option<chain::ChainKey>` buffer in registers `(x25, x28, w27)`
before it is written to the destination `Chain` at offset `+72`. -/
private def clonedOptChainKeyBuf (A : RustAlloc) (ckPin' : VecPin)
    (x25 x28 : BitVec 64) (w27 : BitVec 32) : Option ChainKey → SepProp
  | none => ⌜x25 = optChainKeyNone⌝
  | some ck =>
      ⌜ckPin' = ⟨32#64, x28⟩ ∧ x25 = 32#64 ∧ w27 = ck.index⌝ ∗
        vecU8Buf A 32#64 x28 (keyToBytes32 ck.key)

private theorem fold_optChainKeyAt (A : RustAlloc) (ckPin' : VecPin)
    (x25 x28 : BitVec 64) (w27 : BitVec 32) (optCk : Option ChainKey) (a : BitVec 64) :
    (((a ↦₆₄ x25) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ x25) ∗
      ((a + 24#64) ↦₃₂ w27) ∗ memRegion (a + 28#64) 4) ∗
     clonedOptChainKeyBuf A ckPin' x25 x28 w27 optCk) ⊢
      optChainKeyAt A ckPin' optCk a := by
  cases optCk with
  | none =>
    unfold clonedOptChainKeyBuf optChainKeyAt
    rw [sepConj_comm ((a ↦₆₄ x25) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ x25) ∗
      ((a + 24#64) ↦₃₂ w27) ∗ memRegion (a + 28#64) 4)]
    apply Entails.pure_left; rintro rfl
    have h8_1 : ((a + 8#64) ↦₆₄ x28) ⊢ memRegion (a + 8#64) 8 :=
      pointsTo64_entails_memRegion (a + 8#64) x28
    have h8_2 : ((a + 16#64) ↦₆₄ optChainKeyNone) ⊢ memRegion (a + 16#64) 8 :=
      pointsTo64_entails_memRegion (a + 16#64) optChainKeyNone
    have h4_1 : ((a + 24#64) ↦₃₂ w27) ⊢ memRegion (a + 24#64) 4 :=
      pointsTo32_entails_memRegion (a + 24#64) w27
    have hstep :
        ((a ↦₆₄ optChainKeyNone) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ optChainKeyNone) ∗
          ((a + 24#64) ↦₃₂ w27) ∗ memRegion (a + 28#64) 4) ⊢
        ((a ↦₆₄ optChainKeyNone) ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗
          memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4) :=
      sepConj_mono_right (sepConj_mono h8_1 (sepConj_mono h8_2 (sepConj_mono_left h4_1)))
    refine Entails.trans hstep ?_
    have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
    have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
    rw [show (24 : Nat) = 16 + 8 from rfl,
        ProofLib.memRegion_split (a + 8#64) 16 8 (by decide),
        show (16 : Nat) = 8 + 8 from rfl,
        ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
        ha16, ha24,
        show (8 : Nat) = 4 + 4 from rfl,
        ProofLib.memRegion_split (a + 24#64) 4 4 (by decide),
        ha28]
    have hcomm :
        ((a ↦₆₄ optChainKeyNone) ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗
          memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4) =
        ((a ↦₆₄ optChainKeyNone) ∗
          ((memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8) ∗
           (memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4))) := by
      ac_rfl
    rw [hcomm]
    exact Entails.refl _
  | some ck =>
    unfold clonedOptChainKeyBuf optChainKeyAt
    dsimp only
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨rfl, rfl, rfl⟩
    dsimp only
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have hlen : BitVec.ofNat 64 (keyToBytes32 ck.key).length = 32#64 := by
      simp [keyToBytes32]
    rw [hlen]
    have hcomm :
        (((a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
          ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4) ∗
         vecU8Buf A 32#64 x28 (keyToBytes32 ck.key)) =
        ((((a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ 32#64)) ∗
          vecU8Buf A 32#64 x28 (keyToBytes32 ck.key)) ∗
         ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4) := by
      ac_rfl
    rw [hcomm]
    exact Entails.refl _

/-- Untouched parts of a source `chain::MessageKey` at `a` during the `MessageKey` clone loop. -/
private def messageKeySourceFrame (A : RustAlloc) (gk : MessageKeyGhost)
    (mkg : MessageKeyGenerator) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
  ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
  ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
  memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length) (gk.seed.cap.toNat - mkg.seed.length) ∗
  memRegion (a + 100#64) 4

private theorem messageKeyAt_eq_source (A : RustAlloc) (gk : MessageKeyGhost)
    (mkg : MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A (gk, mkg) a =
      ⌜0 < mkg.seed.length ∧ mkg.seed.length ≤ gk.seed.cap.toNat ∧
        gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
      ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      ((a + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg a := by
  unfold messageKeyAt messageKeySourceFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hseed_ne
    have hpos : 0 < mkg.seed.length := List.length_pos_of_ne_nil hseed_ne
    rw [vecU8At_eq_of_nil A a, vecU8At_eq_of_nil A (a + 24#64),
        vecU8At_eq_of_nil A (a + 48#64),
        vecU8At_eq_of_pos A (a + 72#64) gk.seed.cap gk.seed.ptr mkg.seed hpos]
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88]
    have hpure_comm :
        (((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.cipher.cap gk.cipher.ptr []) ∗
         (((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.mac.cap gk.mac.ptr []) ∗
         (((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.iv.cap gk.iv.ptr []) ∗
         (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
          memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
            (gk.seed.cap.toNat - mkg.seed.length)) ∗
         ((a + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (a + 100#64) 4) =
        (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          ((a + 40#64) ↦₆₄ 0#64) ∗
          ((a + 64#64) ↦₆₄ 0#64) ∗
          ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((a + 96#64) ↦₃₂ mkg.counter) ∗
          ((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
           vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
           ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
           vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
           ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗
           vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
           ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
           memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
             (gk.seed.cap.toNat - mkg.seed.length) ∗
           memRegion (a + 100#64) 4)) := by
      ac_rfl
    rw [hpure_comm]
    apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
    exact Entails.pure_right ⟨hpos, hlen, hlt, hptr⟩ (Entails.refl _)
  · apply Entails.pure_left; rintro ⟨hpos, hlen, hlt, hptr⟩
    have hseed_ne : mkg.seed ≠ [] := List.ne_nil_of_length_pos hpos
    apply Entails.pure_right hseed_ne
    rw [vecU8At_eq_of_nil A a, vecU8At_eq_of_nil A (a + 24#64),
        vecU8At_eq_of_nil A (a + 48#64),
        vecU8At_eq_of_pos A (a + 72#64) gk.seed.cap gk.seed.ptr mkg.seed hpos]
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88]
    have hpure_comm :
        (((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.cipher.cap gk.cipher.ptr []) ∗
         (((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.mac.cap gk.mac.ptr []) ∗
         (((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.iv.cap gk.iv.ptr []) ∗
         (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
          memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
            (gk.seed.cap.toNat - mkg.seed.length)) ∗
         ((a + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (a + 100#64) 4) =
        (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          ((a + 40#64) ↦₆₄ 0#64) ∗
          ((a + 64#64) ↦₆₄ 0#64) ∗
          ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((a + 96#64) ↦₃₂ mkg.counter) ∗
          ((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
           vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
           ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
           vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
           ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗
           vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
           ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
           memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
             (gk.seed.cap.toNat - mkg.seed.length) ∗
           memRegion (a + 100#64) 4)) := by
      ac_rfl
    rw [hpure_comm]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

private def clonedMessageKeyGhost (seedLen seedPtr' : BitVec 64) : MessageKeyGhost :=
  { cipher := ⟨0#64, 1#64⟩
    mac    := ⟨0#64, 1#64⟩
    iv     := ⟨0#64, 1#64⟩
    seed   := ⟨seedLen, seedPtr'⟩ }

private theorem fold_cloned_messageKeyAt (A : RustAlloc) (mkg : MessageKeyGenerator)
    (seedPtr' dst : BitVec 64)
    (hpos : 0 < mkg.seed.length) (hlt : mkg.seed.length < 2 ^ 63) (hptr' : seedPtr' ≠ 0#64) :
    ((dst ↦₆₄ 0#64) ∗
      ((dst + 8#64) ↦₆₄ 1#64) ∗
      ((dst + 16#64) ↦₆₄ 0#64) ∗
      ((dst + 24#64) ↦₆₄ 0#64) ∗
      ((dst + 32#64) ↦₆₄ 1#64) ∗
      ((dst + 40#64) ↦₆₄ 0#64) ∗
      ((dst + 48#64) ↦₆₄ 0#64) ∗
      ((dst + 56#64) ↦₆₄ 1#64) ∗
      ((dst + 64#64) ↦₆₄ 0#64) ∗
      ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dst + 80#64) ↦₆₄ seedPtr') ∗
      ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dst + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dst + 100#64) 4 ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      (seedPtr' ↦ₛ mkg.seed)) =
      messageKeyAt A (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dst := by
  unfold messageKeyAt clonedMessageKeyGhost
  have hseed_ne : mkg.seed ≠ [] := List.ne_nil_of_length_pos hpos
  rw [vecU8At_eq_of_nil A dst, vecU8At_eq_of_nil A (dst + 24#64),
      vecU8At_eq_of_nil A (dst + 48#64),
      vecU8At_eq_header_sep_buf A (dst + 72#64),
      vecU8Buf_nil_eq A,
      vecU8Buf_pos_eq A seedPtr' mkg.seed hpos hlt hptr']
  unfold vecHeader
  have hd32 : dst + 24#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 24#64 + 16#64 = dst + 40#64 := by bv_omega
  have hd56 : dst + 48#64 + 8#64 = dst + 56#64 := by bv_omega
  have hd64 : dst + 48#64 + 16#64 = dst + 64#64 := by bv_omega
  have hd80 : dst + 72#64 + 8#64 = dst + 80#64 := by bv_omega
  have hd88 : dst + 72#64 + 16#64 = dst + 88#64 := by bv_omega
  rw [hd32, hd40, hd56, hd64, hd80, hd88]
  simp only [sepConj_emp]
  apply sepProp_eq_of_entails
  · apply Entails.pure_right hseed_ne
    have hcomm :
        ((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64) ∗
          ((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64) ∗
          ((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64) ∗
          ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
          ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) =
        (((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64)) ∗
         (((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64)) ∗
         (((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64)) ∗
         ((((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
           ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length)) ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) ∗
         ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _
  · apply Entails.pure_left; intro _
    have hcomm :
        (((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64)) ∗
         (((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64)) ∗
         (((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64)) ∗
         ((((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
           ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length)) ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) ∗
         ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4) =
        ((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64) ∗
          ((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64) ∗
          ((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64) ∗
          ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
          ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _

private def clonedChainGhost (gc : ChainGhost × ReceiverChain)
    (srkPtr' privPtr' mkCap' mkPtr' : BitVec 64)
    (keys' : List MessageKeyGhost) (ckPin' : VecPin) : ChainGhost :=
  { srk   := ⟨BitVec.ofNat 64 gc.1.srk.bytes.length, srkPtr', gc.1.srk.bytes⟩
    priv  := ⟨BitVec.ofNat 64 gc.1.priv.bytes.length, privPtr', gc.1.priv.bytes⟩
    mkCap := mkCap'
    mkPtr := mkPtr'
    keys  := keys'
    ck    := ckPin' }

private theorem fold_chainAt_dst (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (dst srkPtr' privPtr' mkPtr' x25 x28 : BitVec 64) (w27 : BitVec 32)
    (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = gc.2.messageKeys.length) :
    ((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((dst + 8#64) ↦₆₄ srkPtr') ∗
      ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((dst + 32#64) ↦₆₄ privPtr') ∗
      ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((dst + 56#64) ↦₆₄ mkPtr') ∗
      ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((dst + 72#64) ↦₆₄ x25) ∗
      ((dst + 80#64) ↦₆₄ x28) ∗
      ((dst + 88#64) ↦₆₄ x25) ∗
      ((dst + 96#64) ↦₃₂ w27) ∗
      memRegion (dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
        (keys'.zip gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey) ⊢
      protoChainAt A
        (clonedChainGhost gc srkPtr' privPtr' (BitVec.ofNat 64 gc.2.messageKeys.length)
          mkPtr' keys' ckPin', gc.2) dst := by
  unfold protoChainAt clonedChainGhost vecGhostAt vecAt
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  rw [vecU8At_eq_header_sep_buf A dst, vecU8At_eq_header_sep_buf A (dst + 24#64)]
  unfold vecHeader
  have hzip_len : (keys'.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  rw [hzip_len]
  have hd32 : dst + 24#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 24#64 + 16#64 = dst + 40#64 := by bv_omega
  have hd56 : dst + 48#64 + 8#64 = dst + 56#64 := by bv_omega
  have hd64 : dst + 48#64 + 16#64 = dst + 64#64 := by bv_omega
  have hd80 : dst + 72#64 + 8#64 = dst + 80#64 := by bv_omega
  have hd88 : dst + 72#64 + 16#64 = dst + 88#64 := by bv_omega
  have hd96 : dst + 72#64 + 24#64 = dst + 96#64 := by bv_omega
  have hd100 : dst + 72#64 + 28#64 = dst + 100#64 := by bv_omega
  rw [hd32, hd40, hd56, hd64]
  have hcomm :
      ((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        ((dst + 8#64) ↦₆₄ srkPtr') ∗
        ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        ((dst + 32#64) ↦₆₄ privPtr') ∗
        ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
        ((dst + 56#64) ↦₆₄ mkPtr') ∗
        ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
        ((dst + 72#64) ↦₆₄ x25) ∗
        ((dst + 80#64) ↦₆₄ x28) ∗
        ((dst + 88#64) ↦₆₄ x25) ∗
        ((dst + 96#64) ↦₃₂ w27) ∗
        memRegion (dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
          (keys'.zip gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey) =
      ((((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
         ((dst + 8#64) ↦₆₄ srkPtr') ∗
         ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length)) ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes) ∗
       ((((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
         ((dst + 32#64) ↦₆₄ privPtr') ∗
         ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length)) ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes) ∗
       ((((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
         ((dst + 56#64) ↦₆₄ mkPtr') ∗
         ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length)) ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
          (keys'.zip gc.2.messageKeys)) ∗
       ((((dst + 72#64) ↦₆₄ x25) ∗
         ((dst + 80#64) ↦₆₄ x28) ∗
         ((dst + 88#64) ↦₆₄ x25) ∗
         ((dst + 96#64) ↦₃₂ w27) ∗
         memRegion (dst + 100#64) 4) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey)) := by
    ac_rfl
  rw [hcomm]
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  have hck := fold_optChainKeyAt A ckPin' x25 x28 w27 gc.2.chainKey (dst + 72#64)
  rwa [hd80, hd88, hd96, hd100] at hck

/-! ## 4. Stack Bundles and Epilogue (`+0x2e0..+0x31c`) -/

/-- Callee-saved register save area `[s0.sp - 96#64 .. s0.sp - 8#64]` plus the two stack slots
`[s0.sp - 120#64 .. s0.sp - 108#64]` that are only referenced in dead code paths. -/
private def savedRegsOnStack (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
  (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
  (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
  (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)

/-- The 8 spill slots `[sp - 208#64 .. sp - 152#64]` when existentially quantified. -/
private def spillSlotsExist (sp : BitVec 64) : SepProp :=
  (∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
  (∃∗ w1a : BitVec 32, (sp - 200#64) ↦₃₂ w1a) ∗
  (∃∗ w1b : BitVec 32, (sp - 196#64) ↦₃₂ w1b) ∗
  (∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
  (∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
  (∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
  (∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
  (∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
  (∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7)

private theorem fold_stackAt_chainClone (s0 : State) (v8 v9 v10 v13 : BitVec 64) :
    (stackAt (s0.sp - 208#64) allocHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ v8) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      stackAt s0.sp chainCloneStack := by
  rw [stackAt_chainClone_eq s0.sp]
  unfold spillSlotsExist savedRegsOnStack
  have h8 : ((s0.sp - 144#64) ↦₆₄ v8) ⊢ ∃∗ x : BitVec 64, (s0.sp - 144#64) ↦₆₄ x :=
    Entails.sepExists_right v8 (Entails.refl _)
  have h9 : ((s0.sp - 136#64) ↦₆₄ v9) ⊢ ∃∗ x : BitVec 64, (s0.sp - 136#64) ↦₆₄ x :=
    Entails.sepExists_right v9 (Entails.refl _)
  have h10 : ((s0.sp - 128#64) ↦₆₄ v10) ⊢ ∃∗ x : BitVec 64, (s0.sp - 128#64) ↦₆₄ x :=
    Entails.sepExists_right v10 (Entails.refl _)
  have h13 : ((s0.sp - 104#64) ↦₆₄ v13) ⊢ ∃∗ x : BitVec 64, (s0.sp - 104#64) ↦₆₄ x :=
    Entails.sepExists_right v13 (Entails.refl _)
  have h14 : ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 96#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5)) (Entails.refl _)
  have h15 : ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 88#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5)) (Entails.refl _)
  have h16 : ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 80#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5)) (Entails.refl _)
  have h17 : ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 72#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5)) (Entails.refl _)
  have h18 : ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 64#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5)) (Entails.refl _)
  have h19 : ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 56#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5)) (Entails.refl _)
  have h20 : ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 48#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5)) (Entails.refl _)
  have h21 : ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 40#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5)) (Entails.refl _)
  have h22 : ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 32#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5)) (Entails.refl _)
  have h23 : ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 24#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5)) (Entails.refl _)
  have h24 : ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 16#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5)) (Entails.refl _)
  have h25 : ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 8#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)
  have hstep :
      (stackAt (s0.sp - 208#64) allocHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
         ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
         ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) ⊢
      (stackAt (s0.sp - 208#64) allocHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        ((∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
         (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
         (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
         (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
         (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
         (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
         (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
         (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
         (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
         (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
         (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
         (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) :=
    sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h8 (sepConj_mono h9 (sepConj_mono h10 (sepConj_mono h13
        (sepConj_mono h14 (sepConj_mono h15 (sepConj_mono h16 (sepConj_mono h17
          (sepConj_mono h18 (sepConj_mono h19 (sepConj_mono h20 (sepConj_mono h21
            (sepConj_mono h22 (sepConj_mono h23 (sepConj_mono h24
              (sepConj_mono_left h25)))))))))))))))))
  refine Entails.trans hstep ?_
  have hcomm :
      (stackAt (s0.sp - 208#64) allocHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        ((∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
         (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
         (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
         (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
         (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
         (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
         (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
         (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
         (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
         (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
         (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
         (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) =
      (stackAt (s0.sp - 208#64) allocHookStack ∗
        (∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
        (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
        (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
        (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
        (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
        (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
        (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
        (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
        (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        (∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
        (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
        (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
        (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
        (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
        (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
        (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
        (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
        (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
        (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
        (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
        (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25)) := by
    ac_rfl
  rw [hcomm]
  exact Entails.refl _

private meta def hex5Str (n : Nat) : String :=
  let d (k : Nat) : Char :=
    let v := (n >>> (4 * k)) &&& 0xf
    if v < 10 then Char.ofNat ('0'.toNat + v) else Char.ofNat ('a'.toNat + v - 10)
  String.ofList [d 4, d 3, d 2, d 1, d 0]

/-- Introduce anonymous `fetch` hypotheses on `tripleRatchetProgAtExt` for `k ∈ [kStart, kEnd)`
    (instruction index `k`, byte offset `4 * k`) of `Chain::clone [local#2]` (`0x3846c`). -/
elab "clone_fetches_range " b:term:max ext:term:max
    hfn:term:max kStart:num kEnd:num : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let k0 := kStart.getNat
    let k1 := kEnd.getNat
    for k in [k0:k1] do
      let byteOff := 4 * k
      let absOff := num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") + byteOff
      let decName := Lean.Name.mkStr4 "CryptoVerification" "LibsignalTripleRatchet" "FromRecordChainClone"
        s!"chainCloneBin_decode_0x{hex5Str absOff}"
      let decId := Lean.mkIdent decName
      let byteOffLit := Lean.Syntax.mkNumLit (toString byteOff)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := libsignalSessionCode_fetch_fnAddr (b := $b)
          (H := Rust.withPanics $ext)
          $hfn (k := $byteOffLit) (by decide) $decId))

private structure Slots104 where
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64
  v8 : BitVec 64
  v9 : BitVec 64
  v10 : BitVec 64
  v11 : BitVec 64
  w12 : BitVec 32

private theorem entails_sepExists_left {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q :=
  Entails.sepExists_elim h

private theorem entails_sepExists_sepConj_left {α : Type} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]
  exact entails_sepExists_left h

private theorem entails_pull_exists {α : Type} {A : SepProp} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, (A ∗ P x) ∗ Q ⊢ R) : A ∗ (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]
  exact entails_sepExists_left h

private theorem memRegion_104_eq_slots104 (ptr : BitVec 64) :
    memRegion ptr 104 =
      ∃∗ d : Slots104,
        (ptr ↦₆₄ d.v0) ∗
        ((ptr + 8#64) ↦₆₄ d.v1) ∗
        ((ptr + 16#64) ↦₆₄ d.v2) ∗
        ((ptr + 24#64) ↦₆₄ d.v3) ∗
        ((ptr + 32#64) ↦₆₄ d.v4) ∗
        ((ptr + 40#64) ↦₆₄ d.v5) ∗
        ((ptr + 48#64) ↦₆₄ d.v6) ∗
        ((ptr + 56#64) ↦₆₄ d.v7) ∗
        ((ptr + 64#64) ↦₆₄ d.v8) ∗
        ((ptr + 72#64) ↦₆₄ d.v9) ∗
        ((ptr + 80#64) ↦₆₄ d.v10) ∗
        ((ptr + 88#64) ↦₆₄ d.v11) ∗
        ((ptr + 96#64) ↦₃₂ d.w12) ∗
        memRegion (ptr + 100#64) 4 := by
  rw [memRegion_104_eq_slots ptr]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun v1 => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    refine entails_pull_exists fun v7 => ?_
    refine entails_pull_exists fun v8 => ?_
    refine entails_pull_exists fun v9 => ?_
    refine entails_pull_exists fun v10 => ?_
    refine entails_pull_exists fun v11 => ?_
    refine entails_pull_exists fun w12 => ?_
    apply Entails.sepExists_right ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, w12⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun d => ?_
    exact sepConj_mono (Entails.sepExists_right d.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v6 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v7 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v8 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v9 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v10 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v11 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right d.w12 (Entails.refl _))))))))))))))

private theorem epilogue_post_entails (A : RustAlloc) (x : ChainCloneGhost) (s0 sf : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (htrace : sf.trace = s0.trace) :
    ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
      ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 32#64) ↦₆₄ privPtr') ∗
      ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
      ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 72#64) ↦₆₄ x25) ∗
      ((x.dst + 80#64) ↦₆₄ x28) ∗
      ((x.dst + 88#64) ↦₆₄ x25) ∗
      ((x.dst + 96#64) ↦₃₂ w27) ∗
      memRegion (x.dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
        (keys'.zip x.gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
      protoChainAt A x.gc x.src ∗
      A.pool ∗
      stackAt (s0.sp - 208#64) allocHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      (protoChainCloneSpec A).post x s0 sf := by
  unfold protoChainCloneSpec
  dsimp only
  apply Entails.pure_right htrace
  let g' := clonedChainGhost x.gc srkPtr' privPtr'
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' keys' ckPin'
  have hg' :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ⊢
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) := by
    refine Entails.trans
      (fold_chainAt_dst A x.gc x.dst srkPtr' privPtr' mkPtr' x25 x28 w27 keys' ckPin'
        hsrk hmax hklen) ?_
    apply Entails.sepExists_right g'
    exact Entails.pure_right ⟨rfl, rfl, hklen.trans hsrc_klen.symm⟩ (Entails.refl _)
  have hst := fold_stackAt_chainClone s0
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) v9 v10 v13
  have hgroup :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ∗
       protoChainAt A x.gc x.src ∗
       A.pool ∗
       (stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hg' (sepConj_mono_right (sepConj_mono_right hst))

private theorem chain_clone_epilogue {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx9 : s.readReg64 (Reg.gpr 9#5) = mkPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  clone_fetches_range b ext hfn 184 200
  clear hfn
  unfold tripleRatchetProgAtExt at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨by simp_all, ?_, ?_⟩
  · constructor <;> simp_all
  · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
    refine Entails.trans ?_
      (epilogue_post_entails A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

/-! ## 5. Extern Hook and Panic Tail Lemmas for `tripleRatchetProgAtExt` at `chainCloneName` -/

/-- No-op shim spec that records trace preservation. -/
private def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

private theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

/-- Region `memcpy` spec that records trace preservation. -/
private def sessionMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs)

private theorem sessionMemcpy_hookOk : HookOk hookMemcpy sessionMemcpySpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, sessionMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

private theorem panic_at_handle_error {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext chainCloneName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")) (by fnoff_eq)

private theorem shim_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
      sessionShimSpec :=
  hA.shim_ok_at chainCloneName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")) (by fnoff_eq)

private theorem alloc_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at chainCloneName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")) (by fnoff_eq)

private theorem memcpy_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
      sessionMemcpySpec :=
  hA.session_memcpy_region_ok_at chainCloneName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")) (by fnoff_eq)

private theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem sepWP_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog ret s (A ∗ B ∗ C) post) :
    SepWP prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWP.pure_elim h

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem chain_clone_panic_800 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hpanic := panic_at_handle_error (b := b) (ext := ext)
  clone_fetches_range b ext hfn 200 203
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_panic_812 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hpanic := panic_at_handle_error (b := b) (ext := ext)
  clone_fetches_range b ext hfn 203 206
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_panic_824 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hpanic := panic_at_handle_error (b := b) (ext := ext)
  clone_fetches_range b ext hfn 206 209
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_panic_836 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hpanic := panic_at_handle_error (b := b) (ext := ext)
  clone_fetches_range b ext hfn 209 212
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_panic_848 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hpanic := panic_at_handle_error (b := b) (ext := ext)
  clone_fetches_range b ext hfn 212 215
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_panic_860 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hpanic := panic_at_handle_error (b := b) (ext := ext)
  clone_fetches_range b ext hfn 215 218
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## 6. `MessageKey` Clone Loop (`0x38604 .. 0x38718` and `0x385c8 .. 0x38600`) -/

private theorem mul104_ne_of_lt {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    BitVec.ofNat 64 (104 * total) ≠ BitVec.ofNat 64 (104 * doneLen) := by
  intro heq
  have h1 : 104 * total < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have h2 : 104 * doneLen < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
  omega

private theorem mul104_beq_eq_false {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul104_ne_of_lt hlt htot

private theorem off_add_104 (doneLen : Nat) :
    BitVec.ofNat 64 (104 * doneLen) + 104#64 = BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

private theorem ptr_off_add_104 (mkPtr' : BitVec 64) (doneLen : Nat) :
    mkPtr' + BitVec.ofNat 64 (104 * doneLen) + 104#64 =
      mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  rw [BitVec.add_assoc, off_add_104]

private theorem memRegion_mk_cons (mkPtr' : BitVec 64) (doneLen n : Nat)
    (hn : n + 1 ≤ maxMessageKeys) :
    memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * (n + 1)) =
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 ∗
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1))) (104 * n) := by
  have hmul : 104 * (n + 1) = 104 + 104 * n := by omega
  have hle : 104 + 104 * n ≤ 2 ^ 64 := by unfold maxMessageKeys at hn; omega
  rw [hmul,
      ProofLib.memRegion_split (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 (104 * n) hle,
      ptr_off_add_104]

private theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  bv_omega

private theorem fold_iter_messageKeys (A : RustAlloc)
    (gk : MessageKeyGhost) (mkg : MessageKeyGenerator)
    (srcCur dstCur seedPtr' : BitVec 64)
    (R0 R0b R1 R2 : SepProp)
    (hpos : 0 < mkg.seed.length)
    (hle : mkg.seed.length ≤ gk.seed.cap.toNat)
    (hlt : gk.seed.cap.toNat < 2 ^ 63)
    (hptr : gk.seed.ptr ≠ 0)
    (hptr' : seedPtr' ≠ 0#64) :
    ((seedPtr' ↦ₛ mkg.seed) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      R0 ∗
      R0b ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      ((srcCur + 16#64) ↦₆₄ 0#64) ∗
      ((srcCur + 40#64) ↦₆₄ 0#64) ∗
      ((srcCur + 64#64) ↦₆₄ 0#64) ∗
      ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg srcCur ∗
      R1 ∗
      (dstCur ↦₆₄ 0#64) ∗
      ((dstCur + 8#64) ↦₆₄ 1#64) ∗
      ((dstCur + 16#64) ↦₆₄ 0#64) ∗
      ((dstCur + 24#64) ↦₆₄ 0#64) ∗
      ((dstCur + 32#64) ↦₆₄ 1#64) ∗
      ((dstCur + 40#64) ↦₆₄ 0#64) ∗
      ((dstCur + 48#64) ↦₆₄ 0#64) ∗
      ((dstCur + 56#64) ↦₆₄ 1#64) ∗
      ((dstCur + 64#64) ↦₆₄ 0#64) ∗
      ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
      ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dstCur + 100#64) 4 ∗
      R2) ⊢
    (messageKeyAt A (gk, mkg) srcCur ∗
      messageKeyAt A (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dstCur ∗
      R1 ∗ R0 ∗ R0b ∗ R2) := by
  have hlt_seed : mkg.seed.length < 2 ^ 63 := by omega
  rw [← fold_cloned_messageKeyAt A mkg seedPtr' dstCur hpos hlt_seed hptr',
      messageKeyAt_eq_source A gk mkg srcCur]
  have hgroup :
      ((seedPtr' ↦ₛ mkg.seed) ∗
        (gk.seed.ptr ↦ₛ mkg.seed) ∗
        R0 ∗
        R0b ∗
        A.live seedPtr' mkg.seed.length 1 ∗
        ((srcCur + 16#64) ↦₆₄ 0#64) ∗
        ((srcCur + 40#64) ↦₆₄ 0#64) ∗
        ((srcCur + 64#64) ↦₆₄ 0#64) ∗
        ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
        ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
        messageKeySourceFrame A gk mkg srcCur ∗
        R1 ∗
        (dstCur ↦₆₄ 0#64) ∗
        ((dstCur + 8#64) ↦₆₄ 1#64) ∗
        ((dstCur + 16#64) ↦₆₄ 0#64) ∗
        ((dstCur + 24#64) ↦₆₄ 0#64) ∗
        ((dstCur + 32#64) ↦₆₄ 1#64) ∗
        ((dstCur + 40#64) ↦₆₄ 0#64) ∗
        ((dstCur + 48#64) ↦₆₄ 0#64) ∗
        ((dstCur + 56#64) ↦₆₄ 1#64) ∗
        ((dstCur + 64#64) ↦₆₄ 0#64) ∗
        ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
        ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
        memRegion (dstCur + 100#64) 4 ∗
        R2) =
      ((((srcCur + 16#64) ↦₆₄ 0#64) ∗
          ((srcCur + 40#64) ↦₆₄ 0#64) ∗
          ((srcCur + 64#64) ↦₆₄ 0#64) ∗
          ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
          messageKeySourceFrame A gk mkg srcCur) ∗
        ((dstCur ↦₆₄ 0#64) ∗
          ((dstCur + 8#64) ↦₆₄ 1#64) ∗
          ((dstCur + 16#64) ↦₆₄ 0#64) ∗
          ((dstCur + 24#64) ↦₆₄ 0#64) ∗
          ((dstCur + 32#64) ↦₆₄ 1#64) ∗
          ((dstCur + 40#64) ↦₆₄ 0#64) ∗
          ((dstCur + 48#64) ↦₆₄ 0#64) ∗
          ((dstCur + 56#64) ↦₆₄ 1#64) ∗
          ((dstCur + 64#64) ↦₆₄ 0#64) ∗
          ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
          ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
          memRegion (dstCur + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗
          (seedPtr' ↦ₛ mkg.seed)) ∗
        R1 ∗ R0 ∗ R0b ∗ R2) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (Entails.pure_right ⟨hpos, hle, hlt, hptr⟩ (Entails.refl _))

private theorem chain_clone_mk_loop {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hshim := shim_ok_at hA
  have halloc := alloc_ok_at hA
  have hmemcpy := memcpy_ok_at hA
  have hpanic824 := fun s P => chain_clone_panic_824 (b := b) (A := A)
    (ext := ext) (Q := Q) x s0 s P R
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  clone_fetches_range b ext hfn 87 108
  clone_fetches_range b ext hfn 148 172
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic824 hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic824 hcont ⊢
  examples_hide_fetches
  induction rem generalizing s doneLen srcCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := entry + bv% (660))
    wp_steps
    wp_call hshim ()
    have htr_sf : sf.trace = s0.trace := by reg_chain
    wp_compact
    wp_steps
    wp_call halloc (mkg.seed.length, 1)
    rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
    wp_compact
    apply SepWP.done ‹_› ‹_›
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_mid fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (824))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine hpanic824 _ _ ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace_oom
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod, htrace1⟩ => ?_
      rw [List.length_cons,
          memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
          memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun d => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (404))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 Reg.x0, gk.seed.ptr, mkg.seed)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
          (sf_1.readReg64 (Reg.gpr 0#5))
        refine SepWPp.weaken_pre
          (fold_iter_messageKeys A gk mkg srcCur
            (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _
            hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64) ?_
        rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
        cases rem' with
        | nil =>
          simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
            sepConj_emp, emp_sepConj, sepConj_assoc]
          apply SepWPp.of_sepWP (mid := entry + bv% (688))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · refine SepWPp.weaken_pre ?_
              (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simp only [List.map, List.zip_cons_cons, List.zip_nil_right,
                arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
              exact Entails.refl _
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
        | cons p2 rem'' =>
          have hrem'_pos : 0 < (p2 :: rem'').length := by simp
          have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem'_pos
              (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
          apply SepWPp.of_sepWP (mid := entry + bv% (408))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
              simp at htot ⊢; omega
            refine SepWPp.weaken_pre ?_
              (ih (by simp) (doneLen + 1) htot' _ (srcCur + 104#64) 0#64 1#64 mkg.counter
                (messageKeyAt A (gk, mkg) srcCur ∗
                  messageKeyAt A (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f => ?_)
            · exact Entails.of_eq (by ac_rfl)
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
                (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f
              rw [List.map_cons, List.zip_cons_cons,
                arrayAt_cons (x := (gk, mkg)),
                arrayAt_cons (x := (gk', (gk, mkg).2)),
                ptr_off_add_104] at hdone
              dsimp only at hdone
              simp only [sepConj_assoc] at hdone
              refine SepWPp.weaken_pre ?_ hdone
              exact Entails.of_eq (by ac_rfl)

/-! ### `message_keys` Allocation, Loop Wrapper, and Empty Fast Path -/

private theorem vecBuf_mk_nil_eq (A : RustAlloc) :
    vecBuf A 104 8 (messageKeyAt A) 0#64 8#64 [] = emp := by
  unfold vecBuf
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

private theorem vecBuf_mk_pos_eq (A : RustAlloc) (mkPtr' : BitVec 64)
    (xs : List (MessageKeyGhost × MessageKeyGenerator))
    (hpos : 0 < xs.length) (hmax : xs.length ≤ maxMessageKeys) (hptr' : mkPtr' ≠ 0#64) :
    vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 xs.length) mkPtr' xs =
      A.live mkPtr' (104 * xs.length) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr' xs := by
  unfold vecBuf
  have hlt64 : xs.length < 2 ^ 64 := by unfold maxMessageKeys at hmax; omega
  have htoNat : (BitVec.ofNat 64 xs.length).toNat = xs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne0 : BitVec.ofNat 64 xs.length ≠ 0 := ofNat_ne_zero_of_pos hpos hlt64
  have hptr_ne : mkPtr' ≠ 0 := hptr'
  have hcap_lt : xs.length * 104 < 2 ^ 63 := by unfold maxMessageKeys at hmax; omega
  have hmul_comm : xs.length * 104 = 104 * xs.length := Nat.mul_comm _ _
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hcap_lt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _

private def chainMkSourceFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
  memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
    ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

private theorem chainAt_eq_mk_source (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
        gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
      ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
      arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
      chainMkSourceFrame A gc a := by
  unfold protoChainAt chainMkSourceFrame vecAt vecHeader vecBuf
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [hne, ↓reduceIte, sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

private structure SpillSlots where
  v0 : BitVec 64
  w1a : BitVec 32
  w1b : BitVec 32
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64

private theorem spillSlotsExist_eq_struct (sp : BitVec 64) :
    spillSlotsExist sp =
      ∃∗ s : SpillSlots,
        ((sp - 208#64) ↦₆₄ s.v0) ∗
        ((sp - 200#64) ↦₃₂ s.w1a) ∗
        ((sp - 196#64) ↦₃₂ s.w1b) ∗
        ((sp - 192#64) ↦₆₄ s.v2) ∗
        ((sp - 184#64) ↦₆₄ s.v3) ∗
        ((sp - 176#64) ↦₆₄ s.v4) ∗
        ((sp - 168#64) ↦₆₄ s.v5) ∗
        ((sp - 160#64) ↦₆₄ s.v6) ∗
        ((sp - 152#64) ↦₆₄ s.v7) := by
  unfold spillSlotsExist
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun w1a => ?_
    refine entails_pull_exists fun w1b => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    rw [sepExists_sepConj_right]
    refine entails_sepExists_left fun v7 => ?_
    apply Entails.sepExists_right ⟨v0, w1a, w1b, v2, v3, v4, v5, v6, v7⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun s => ?_
    exact sepConj_mono (Entails.sepExists_right s.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1a (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1b (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v6 (Entails.refl _))
      (Entails.sepExists_right s.v7 (Entails.refl _)))))))))

private def savedRegsCore (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
  (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a)

private theorem savedRegsOnStack_eq_core (s0 : State) :
    savedRegsOnStack s0 =
      ∃∗ p : BitVec 64 × BitVec 32,
        ((s0.sp - 120#64) ↦₆₄ p.1) ∗
        ((s0.sp - 108#64) ↦₃₂ p.2) ∗
        savedRegsCore s0 := by
  unfold savedRegsOnStack savedRegsCore
  rw [show (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) =
      ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a))) by ac_rfl]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v11 => ?_
    refine entails_pull_exists fun w12b => ?_
    apply Entails.sepExists_right (v11, w12b)
    rw [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun p => ?_
    exact sepConj_mono (Entails.sepExists_right p.1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right p.2 (Entails.refl _)))

private theorem map_snd_zip_of_length_eq {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs' ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih ys' (Nat.succ.inj hlen)

private theorem mul_104_eq (n : Nat) :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (104 * n) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

private theorem toNat_mul_104 {n : Nat} (hmax : n ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * n)).toNat = 104 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxMessageKeys at hmax; omega)]

/-- Fast path when `x.gc.2.messageKeys = []` at `+0x2dc` (`0x38748: mov w9, #8`). -/
private theorem chain_clone_mks_nil {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  clone_fetches_range b ext hfn 183 184
  clear hfn
  have hep := fun s' => chain_clone_epilogue (b := b) (A := A)
    (ext := ext) (Qp := Qp)
    x s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  unfold tripleRatchetProgAtExt at hpc hep ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (736))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · refine SepWPp.weaken_pre ?_
      (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · have hbuf_nil :
          vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
            ([].zip x.gc.2.messageKeys) = emp := by
        simpa [hnil] using vecBuf_mk_nil_eq A
      rw [hbuf_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
    · exact htrace
    · simp only [wp_norm]; assumption

/-- Non-empty `message_keys` allocation, loop, and register reload (`0x38570 .. 0x38734`). -/
private theorem chain_clone_mks_nonempty {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hshim := shim_ok_at (b := b) (A := A) (ext := ext) hA
  have halloc := alloc_ok_at (b := b) (A := A) (ext := ext) hA
  have hpanic860 := fun s P => chain_clone_panic_860 (b := b) (A := A)
    (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_mk_loop (b := b) (A := A) (ext := ext)
      (Q := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      hA x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      s' srcCur mkPtr' v11 v13 w12b F R
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_epilogue (b := b) (A := A)
      (ext := ext)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  dsimp only [sessionShimSpec] at hshim
  clone_fetches_range b ext hfn 65 87
  clone_fetches_range b ext hfn 172 179
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hpanic860 hloop hep ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic860 hloop hep ⊢
  examples_hide_fetches
  rw [chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) =
      (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hmk_le, hmk_lt, hmk_ptr⟩ => ?_
  have hmul_eq : BitVec.ofNat 64 x.gc.2.messageKeys.length * 104#64 =
      BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length) :=
    mul_104_eq x.gc.2.messageKeys.length
  have hmul_toNat : (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)).toNat =
      104 * x.gc.2.messageKeys.length :=
    toNat_mul_104 hmax
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hmk_lay : LayoutOk (104 * x.gc.2.messageKeys.length) 8 :=
    ⟨by omega, hpow8, by unfold maxMessageKeys at hmax; omega⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (308))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  wp_compact
  wp_steps
  wp_call halloc (104 * x.gc.2.messageKeys.length, 8)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (860))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic860 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod8, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (408))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.weaken_pre ?_
        (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
          (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            chainMkSourceFrame A x.gc x.src ∗
            ((s0.sp - 208#64) ↦₆₄ x28) ∗
            ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
            ((s0.sp - 196#64) ↦₃₂ w27) ∗
            ((s0.sp - 192#64) ↦₆₄ x25) ∗
            ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
            ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
            ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            savedRegsCore s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l => ?_)
      · rw [hzip_len, BitVec.add_zero]
        exact Entails.of_eq (by dsimp only [mkPtr']; ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm, hzip_len]
      · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      · exact htrace1
      · simp only [wp_norm]; assumption
      · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
        have hsp_l_align : sf_l.spAligned = true := by
          rw [State.spAligned, hsp_l]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
          (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
        simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
          map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
          sepConj_assoc]
        apply SepWPp.of_sepWP (mid := entry + bv% (736))
        wp_steps
        refine SepWP.done ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · refine SepWPp.weaken_pre ?_
            (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
              simp [hklen]
            have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
              rw [hzip'_len]; exact hpos
            have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
              rw [hzip'_len]; exact hmax
            have hbuf_eq := vecBuf_mk_pos_eq A mkPtr' (keys'.zip x.gc.2.messageKeys)
              hzip'_pos hzip'_max hoom64
            rw [hzip'_len] at hbuf_eq
            rw [hbuf_eq,
                chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
                spillSlotsExist_eq_struct s0.sp,
                savedRegsOnStack_eq_core s0]
            have hsp_fold :
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ⊢
                (∃∗ s : SpillSlots,
                  ((s0.sp - 208#64) ↦₆₄ s.v0) ∗
                  ((s0.sp - 200#64) ↦₃₂ s.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ s.w1b) ∗
                  ((s0.sp - 192#64) ↦₆₄ s.v2) ∗
                  ((s0.sp - 184#64) ↦₆₄ s.v3) ∗
                  ((s0.sp - 176#64) ↦₆₄ s.v4) ∗
                  ((s0.sp - 168#64) ↦₆₄ s.v5) ∗
                  ((s0.sp - 160#64) ↦₆₄ s.v6) ∗
                  ((s0.sp - 152#64) ↦₆₄ s.v7)) := by
              apply Entails.sepExists_right
                ⟨x28, spSlots.w1a, w27, x25, privPtr',
                  BitVec.ofNat 64 x.gc.1.priv.bytes.length, srkPtr',
                  BitVec.ofNat 64 x.gc.1.srk.bytes.length, x.dst⟩
              dsimp only
              exact Entails.refl _
            have hsr_fold :
                (((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  savedRegsCore s0) ⊢
                (∃∗ p : BitVec 64 × BitVec 32,
                  ((s0.sp - 120#64) ↦₆₄ p.1) ∗
                  ((s0.sp - 108#64) ↦₃₂ p.2) ∗
                  savedRegsCore s0) := by
              apply Entails.sepExists_right (v11', w12b')
              dsimp only
              exact Entails.refl _
            have hsrc_fold :
                (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) ⊢
                (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
                    x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) :=
              Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
            have hgroup_pre :
                (arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                  memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  chainMkSourceFrame A x.gc x.src ∗
                  ((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  savedRegsCore s0) =
                (memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                    arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                    arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                    chainMkSourceFrame A x.gc x.src) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  (((s0.sp - 208#64) ↦₆₄ x28) ∗
                    ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                    ((s0.sp - 196#64) ↦₃₂ w27) ∗
                    ((s0.sp - 192#64) ↦₆₄ x25) ∗
                    ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                    ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                    ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                    ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                    ((s0.sp - 152#64) ↦₆₄ x.dst)) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  (((s0.sp - 120#64) ↦₆₄ v11') ∗
                    ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                    savedRegsCore s0)) := by
              ac_rfl
            rw [hgroup_pre]
            exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsrc_fold
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsp_fold
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right hsr_fold))))))))))))
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · rw [State.spAligned] at hsp_l_align ⊢; simp only [wp_norm]; exact hsp_l_align
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · unfold State.readReg32; simp only [wp_norm, htrunc32]
          · exact htr_l
          · simp only [wp_norm]; exact hvregs_l

/-! ## 7. `chain_key`, `priv`, and Full `Chain::clone` Proof (`0x3846c`) -/

private def chainMkLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

private theorem chainAt_eq_mk_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      chainMkLenFrame A gc a := by
  unfold protoChainAt chainMkLenFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

private def chainCkSomeFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

private theorem chainAt_eq_ck_some (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗
      (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
      chainCkSomeFrame A gc a := by
  unfold protoChainAt chainCkSomeFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hck_pos : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have ha96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  have ha100 : a + 72#64 + 28#64 = a + 100#64 := by bv_omega
  rw [hzip_len, hck]
  simp only [optChainKeyAt]
  rw [vecU8At_eq_of_pos A (a + 72#64) gc.1.ck.cap gc.1.ck.ptr (keyToBytes32 ck.key) hck_pos,
      hck_len, ha56, ha64, ha80, ha88, ha96, ha100]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

/-- `chain_key = none` path (`0x38560 .. 0x3856c`, `k ∈ [61, 65)`). -/
private theorem chain_clone_ck_none {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil (b := b) (A := A) (ext := ext)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty (b := b) (A := A) (ext := ext) hA x s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck R
      hsrk hmax hsrc_klen hpos
  clone_fetches_range b ext hfn 61 65
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hmks_nil hmks_ne ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hmks_nil hmks_ne ⊢
  examples_hide_fetches
  rw [chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
  simp only [sepConj_assoc]
  have hck_buf :
      clonedOptChainKeyBuf A x.gc.1.ck optChainKeyNone
        (s.readReg64 (Reg.gpr 28#5)) (s.readReg32 (Reg.gpr 27#5)) x.gc.2.chainKey = emp := by
    rw [hck]; simp only [clonedOptChainKeyBuf, pure_true]
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPp.of_sepWP (mid := entry + bv% (732))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine SepWPp.weaken_pre ?_
        (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen, hlen0]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPp.of_sepWP (mid := entry + bv% (260))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · refine SepWPp.weaken_pre ?_
        (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption

/-- `chain_key = some ck` path (`0x38500 .. 0x38540`, `k ∈ [37, 54)`). -/
private theorem chain_clone_ck_some {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (ck : ChainKey) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hshim := shim_ok_at (b := b) (A := A) (ext := ext) hA
  have halloc := alloc_ok_at (b := b) (A := A) (ext := ext) hA
  have hmemcpy := memcpy_ok_at (b := b) (A := A) (ext := ext) hA
  have hpanic812 := fun s P => chain_clone_panic_812 (b := b) (A := A)
    (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil (b := b) (A := A) (ext := ext)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty (b := b) (A := A) (ext := ext) hA x s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩ R
      hsrk hmax hsrc_klen hpos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  clone_fetches_range b ext hfn 37 54
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic812 hmks_nil hmks_ne ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic812 hmks_nil hmks_ne ⊢
  examples_hide_fetches
  rw [chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply SepWPp.of_sepWP (mid := entry + bv% (180))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  wp_compact
  wp_steps
  wp_call halloc (32, 1)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (812))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic812 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_ck_post :
        ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live ckPtr' 32 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          chainCkSomeFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      have hck_buf_eq :
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
            A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
        rw [hck]
        simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
        have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
        have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
        have hv := vecU8Buf_pos_eq A ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
        rw [hck_len] at hv
        exact hv
      rw [hck_buf_eq,
          chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
      have hsrc_ent :
          (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) ⊢
          (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) :=
        Entails.pure_right ⟨hck_le, hck_lt, hck_ptr⟩ (Entails.refl _)
      have hgroup :
          ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live ckPtr' 32 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            chainCkSomeFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            (A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key)) ∗
            (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
              ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
              ((x.src + 88#64) ↦₆₄ 32#64) ∗
              ((x.src + 96#64) ↦₃₂ ck.index) ∗
              (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
              chainCkSomeFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsrc_ent))))
    by_cases hmk_nil : x.gc.2.messageKeys = []
    · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
      apply SepWPp.of_sepWP (mid := entry + bv% (732))
      wp_steps
      wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre
          (Entails.trans (by rw [hlen0]; exact Entails.refl _) hfold_ck_post)
          (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
        · exact htr_sf2
        · simp only [wp_norm]; assumption
    · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
      have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
      apply SepWPp.of_sepWP (mid := entry + bv% (260))
      wp_steps
      wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre hfold_ck_post
          (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
        · exact htr_sf2
        · simp only [wp_norm]; assumption

private theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

private def chainCkNoneCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  memRegion (a + 72#64 + 8#64) 24

private theorem chainAt_eq_ck_none_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = none) :
    protoChainAt A gc a =
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      chainCkNoneCapFrame A gc a := by
  unfold protoChainAt chainCkNoneCapFrame
  rw [hck]
  dsimp only [optChainKeyAt, optChainKeyNone]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

private def chainCkSomeCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) : SepProp :=
  ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
  ((a + 88#64) ↦₆₄ 32#64) ∗
  ((a + 96#64) ↦₃₂ ck.index) ∗
  (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

private theorem chainAt_eq_ck_some_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
      ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
      chainCkSomeCapFrame A gc ck a := by
  rw [chainAt_eq_ck_some A gc ck a hsrk hmax hklen hck]
  unfold chainCkSomeFrame chainCkSomeCapFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right hlt
    rw [show (((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact sepConj_mono_right (Entails.pure_right ⟨hle, hptr⟩ (Entails.refl _))
  · apply Entails.pure_left; intro hlt
    rw [show (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hptr⟩
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

private def chainPrivLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
  vecU8Buf A gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

private theorem chainAt_eq_priv_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      chainPrivLenFrame A gc a := by
  unfold protoChainAt chainPrivLenFrame
  dsimp only [vecGhostAt, vecU8At, vecU8Buf, vecAt, vecHeader]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

private def chainPrivPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
  memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
    (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

private theorem chainAt_eq_priv_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.1.priv.bytes.length) :
    protoChainAt A gc a =
      ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
        gc.1.priv.cap.toNat < 2 ^ 63 ∧
        gc.1.priv.ptr ≠ 0⌝ ∗
      ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
      chainPrivPosFrame A gc a := by
  unfold protoChainAt chainPrivPosFrame
  dsimp only [vecGhostAt]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [vecU8At_eq_of_pos A (a + 24#64) gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes hpos,
      ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

/-- `priv = []` path (`0x384c4 .. 0x384c8` and `0x38550 .. 0x3855c`, `k ∈ [22, 24) ∪ [57, 61)`). -/
private theorem chain_clone_priv_nil {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none (b := b) (A := A) (ext := ext) hA x s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some (b := b) (A := A) (ext := ext) hA x ck s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  clone_fetches_range b ext hfn 22 24
  clone_fetches_range b ext hfn 57 61
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hck_none hck_some ⊢
  examples_hide_fetches
  have hpriv_buf :
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := entry + bv% (232))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · have hfold_priv :
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 40#64) ↦₆₄ 0#64) ∗
          chainPrivLenFrame A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
      ac_rfl
    rw [hfold_priv]
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_none _ hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by ac_rfl)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm, hpriv_len0]
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace
        · simp only [wp_norm]; assumption
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                  ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          exact Entails.pure_right hck_lt (Entails.refl _)
        · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm, hpriv_len0]
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace
        · simp only [wp_norm]; assumption

/-- `0 < priv.length` path (`0x384c4 .. 0x384fc`, `k ∈ [22, 37)`). -/
private theorem chain_clone_priv_pos {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hshim := shim_ok_at (b := b) (A := A) (ext := ext) hA
  have halloc := alloc_ok_at (b := b) (A := A) (ext := ext) hA
  have hmemcpy := memcpy_ok_at (b := b) (A := A) (ext := ext) hA
  have hpanic800 := fun s P => chain_clone_panic_800 (b := b) (A := A)
    (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none (b := b) (A := A) (ext := ext) hA x s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some (b := b) (A := A) (ext := ext) hA x ck s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  clone_fetches_range b ext hfn 22 37
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic800 hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic800 hck_none hck_some ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic800 hck_none hck_some ⊢
  examples_hide_fetches
  rw [chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (116))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  wp_compact
  wp_steps
  wp_call halloc (x.gc.1.priv.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (800))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic800 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_priv_post :
        ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          chainPrivPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64,
          chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
      have hsrc_ent :
          (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
              x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
              x.gc.1.priv.ptr ≠ 0⌝ ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ (Entails.refl _)
      have hgroup :
          ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            chainPrivPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            (A.live privPtr' x.gc.1.priv.bytes.length 1 ∗ (privPtr' ↦ₛ x.gc.1.priv.bytes)) ∗
            (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
              ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
              (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
              chainPrivPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hsrc_ent)))
    apply SepWPp.of_sepWP (mid := entry + bv% (136))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.priv.ptr, x.gc.1.priv.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_priv_post ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_none _ privPtr' hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by ac_rfl)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · exact htr_sf2
        · simp only [wp_norm]; assumption
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                  ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          exact Entails.pure_right hck_lt (Entails.refl _)
        · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · exact htr_sf2
        · simp only [wp_norm]; assumption

private theorem sepWPp_pure_second {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B) Q Qp) :
    SepWPp prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp := by
  rw [show A ∗ ⌜φ⌝ ∗ B = ⌜φ⌝ ∗ A ∗ B by ac_rfl]
  exact SepWPp.pure_elim h

private theorem chainAt_eq_pure_sep (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    protoChainAt A gc a =
      ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
      protoChainAt A gc a := by
  unfold protoChainAt
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hp
    exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
  · apply Entails.pure_left; intro _
    exact Entails.refl _

private def chainSrkPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  (a ↦₆₄ gc.1.srk.cap) ∗
  A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
  memRegion (gc.1.srk.ptr + BitVec.ofNat 64 gc.1.srk.bytes.length)
    (gc.1.srk.cap.toNat - gc.1.srk.bytes.length) ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

private theorem chainAt_eq_srk_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧
        gc.1.srk.cap.toNat < 2 ^ 63 ∧
        gc.1.srk.ptr ≠ 0⌝ ∗
      ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      (gc.1.srk.ptr ↦ₛ gc.1.srk.bytes) ∗
      chainSrkPosFrame A gc a := by
  have hpos : 0 < gc.1.srk.bytes.length := srk_length_pos hsrk
  unfold protoChainAt chainSrkPosFrame
  dsimp only [vecGhostAt]
  rw [vecU8At_eq_of_pos A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes hpos]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)

private def deadStackSlots (sp : BitVec 64) : SepProp :=
  (∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
  (∃∗ w12a : BitVec 32, (sp - 112#64) ↦₃₂ w12a) ∗
  (∃∗ w12b : BitVec 32, (sp - 108#64) ↦₃₂ w12b)

private theorem stackAt_chainClone_eq_entry (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      stackAt (sp - 208#64) allocHookStack ∗
      spillSlotsExist sp ∗
      deadStackSlots sp ∗
      (∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
      (∃∗ v13 : BitVec 64, (sp - 104#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (sp - 96#64) ↦₆₄ v14) ∗
      (∃∗ v15 : BitVec 64, (sp - 88#64) ↦₆₄ v15) ∗
      (∃∗ v16 : BitVec 64, (sp - 80#64) ↦₆₄ v16) ∗
      (∃∗ v17 : BitVec 64, (sp - 72#64) ↦₆₄ v17) ∗
      (∃∗ v18 : BitVec 64, (sp - 64#64) ↦₆₄ v18) ∗
      (∃∗ v19 : BitVec 64, (sp - 56#64) ↦₆₄ v19) ∗
      (∃∗ v20 : BitVec 64, (sp - 48#64) ↦₆₄ v20) ∗
      (∃∗ v21 : BitVec 64, (sp - 40#64) ↦₆₄ v21) ∗
      (∃∗ v22 : BitVec 64, (sp - 32#64) ↦₆₄ v22) ∗
      (∃∗ v23 : BitVec 64, (sp - 24#64) ↦₆₄ v23) ∗
      (∃∗ v24 : BitVec 64, (sp - 16#64) ↦₆₄ v24) ∗
      (∃∗ v25 : BitVec 64, (sp - 8#64) ↦₆₄ v25) := by
  rw [stackAt_chainClone_eq sp]
  unfold spillSlotsExist deadStackSlots
  ac_rfl

/-- Entry and `srk` clone path (`0x3846c .. 0x384c0`, `k ∈ [0, 22)`). -/
private theorem chain_clone_entry {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr chainCloneName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") :=
    libsignalSessionCode_fnOff_sym_3846c
  have hshim := shim_ok_at (b := b) (A := A) (ext := ext) hA
  have halloc := alloc_ok_at (b := b) (A := A) (ext := ext) hA
  have hmemcpy := memcpy_ok_at (b := b) (A := A) (ext := ext) hA
  have hpanic848 := fun s P => chain_clone_panic_848 (b := b) (A := A)
    (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = []) =>
    chain_clone_priv_nil (b := b) (A := A) (ext := ext) hA x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length) =>
    chain_clone_priv_pos (b := b) (A := A) (ext := ext) hA x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv_pos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  clone_fetches_range b ext hfn 0 22
  have := libsignalSessionCode_fetch_fnAddr_entry (b := b)
    (H := Rust.withPanics ext)
    hfn (by decide) (ls_decode% chainCloneBin (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"))
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneName = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  examples_hide_fetches
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  rw [chainAt_eq_pure_sep A x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  rw [chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 =>
    SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v22 => SepWPp.exists_elim fun v23 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat = x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hsrk_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (68))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (x.gc.1.srk.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, ‹sf.trace = s0.trace›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (848))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic848 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_srk_post :
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          deadStackSlots s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
          chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen]
      unfold savedRegsOnStack deadStackSlots
      have hsrc_ent :
          (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.srk.bytes.length ≤ x.gc.1.srk.cap.toNat ∧
              x.gc.1.srk.cap.toNat < 2 ^ 63 ∧
              x.gc.1.srk.ptr ≠ 0⌝ ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      have hgroup :
          ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            chainSrkPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
            ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
          (memRegion x.dst 104 ∗
            (A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ (srkPtr' ↦ₛ x.gc.1.srk.bytes)) ∗
            (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
              ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
              (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
              chainSrkPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
              ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
              ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
              ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
              (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent))
    apply SepWPp.of_sepWP (mid := entry + bv% (88))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_srk_post ?_
    by_cases hpriv_nil : x.gc.1.priv.bytes = []
    · refine hpriv_nil_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_nil
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align
    · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
      refine hpriv_pos_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_pos
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align

private theorem protoChain_clone_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    ProtoChainCloneOkExt b A ext := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hs0_align
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack,
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, fun R' hm' hloaded => ?_⟩
  rcases chain_clone_entry hA x s0 hs0_align R hpc hrun hx0 hx1 R' hm' hloaded with
    ⟨sf, hsteps, ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hrun_f, P_f, hmem_f,
      ⟨fun hm_R => Satisfies.mono (sepConj_mono_left hpost_f) hm_R, hsp_f, hcc_f⟩⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem chain_clone_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    ChainCloneOkExt b A ext :=
  chainClone_of_protoChainClone_ext (protoChain_clone_ok_ext hA)

/-- `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]`
    (`0x3846c`, 218 instructions) satisfies `ChainCloneOk`. -/
theorem chain_clone_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    ChainCloneOk b C A ctl abs :=
  chain_clone_ok_ext (AllocContracts.of_tripleRatchetProgAt' hA)

theorem senderChain_clone_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    SenderChainCloneOkExt b A ext :=
  senderChainClone_of_chainClone_ext optSenderChainAt_some_eq_chainAt (protoChain_clone_ok_ext hA)

/-- Sender-chain clone (`sender_chain.is_some()` specialization) satisfies `SenderChainCloneOk`. -/
theorem senderChain_clone_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    SenderChainCloneOk b C A ctl abs :=
  senderChain_clone_ok_ext (AllocContracts.of_tripleRatchetProgAt' hA)

/-! ## 8. Relocatable (`[LibsignalPlacement]`) Proofs for `Chain::clone [local#2]` (Block `161`) -/

private theorem chain_clone_placed_epilogue [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_161).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx9 : s.readReg64 (Reg.gpr 9#5) = mkPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨by simp_all, ?_, ?_⟩
  · constructor <;> simp_all
  · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
    refine Entails.trans ?_
      (epilogue_post_entails A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

private theorem panic_at_handle_error_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ((blkPC_161).rebase (blkPl_161).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := by
  rw [ls_externAt?_of_mem, hpanic]

private theorem chain_clone_placed_panic_800 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_placed_panic_812 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_placed_panic_824 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_placed_panic_836 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_placed_panic_848 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_placed_panic_860 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem chain_clone_placed_mk_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (blkPl_161).base + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (blkPl_161).base + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic824 := fun s P => chain_clone_placed_panic_824 (A := A)
    (H := H) (Q := Q) hpanic x s0 s P R
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic824 hcont ⊢
  induction rem generalizing s doneLen srcCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (660))
    wp_steps
    wp_call hshim ()
    have htr_sf : sf.trace = s0.trace := by reg_chain
    wp_compact
    wp_steps
    wp_call halloc (mkg.seed.length, 1)
    rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
    wp_compact
    apply SepWP.done ‹_› ‹_›
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_mid fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (824))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine hpanic824 _ _ ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace_oom
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod, htrace1⟩ => ?_
      rw [List.length_cons,
          memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
          memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun d => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (404))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 Reg.x0, gk.seed.ptr, mkg.seed)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
          (sf_1.readReg64 (Reg.gpr 0#5))
        refine SepWPp.weaken_pre
          (fold_iter_messageKeys A gk mkg srcCur
            (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _
            hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64) ?_
        rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
        cases rem' with
        | nil =>
          simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
            sepConj_emp, emp_sepConj, sepConj_assoc]
          apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (688))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · refine SepWPp.weaken_pre ?_
              (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simp only [List.map, List.zip_cons_cons, List.zip_nil_right,
                arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
              exact Entails.refl _
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
        | cons p2 rem'' =>
          have hrem'_pos : 0 < (p2 :: rem'').length := by simp
          have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem'_pos
              (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
          apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (408))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
              simp at htot ⊢; omega
            refine SepWPp.weaken_pre ?_
              (ih (by simp) (doneLen + 1) htot' _ (srcCur + 104#64) 0#64 1#64 mkg.counter
                (messageKeyAt A (gk, mkg) srcCur ∗
                  messageKeyAt A (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f => ?_)
            · exact Entails.of_eq (by ac_rfl)
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
            · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
                (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f
              rw [List.map_cons, List.zip_cons_cons,
                arrayAt_cons (x := (gk, mkg)),
                arrayAt_cons (x := (gk', (gk, mkg).2)),
                ptr_off_add_104] at hdone
              dsimp only at hdone
              simp only [sepConj_assoc] at hdone
              refine SepWPp.weaken_pre ?_ hdone
              exact Entails.of_eq (by ac_rfl)

private theorem chain_clone_placed_mks_nil [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (blkPl_161).base + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hep := fun s' => chain_clone_placed_epilogue (A := A) (H := H) (Qp := Qp)
    x s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (736))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · refine SepWPp.weaken_pre ?_
      (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · have hbuf_nil :
          vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
            ([].zip x.gc.2.messageKeys) = emp := by
        simpa [hnil] using vecBuf_mk_nil_eq A
      rw [hbuf_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
    · exact htrace
    · simp only [wp_norm]; assumption

private theorem chain_clone_placed_mks_nonempty [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_161).base + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic860 := fun s P => chain_clone_placed_panic_860 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_placed_mk_loop (A := A) (H := H)
      (Q := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      hshim halloc hmemcpy hpanic x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      s' srcCur mkPtr' v11 v13 w12b F R
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_placed_epilogue (A := A) (H := H)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  dsimp only [sessionShimSpec] at hshim
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic860 hloop hep ⊢
  rw [chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) =
      (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hmk_le, hmk_lt, hmk_ptr⟩ => ?_
  have hmul_eq : BitVec.ofNat 64 x.gc.2.messageKeys.length * 104#64 =
      BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length) :=
    mul_104_eq x.gc.2.messageKeys.length
  have hmul_toNat : (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)).toNat =
      104 * x.gc.2.messageKeys.length :=
    toNat_mul_104 hmax
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hmk_lay : LayoutOk (104 * x.gc.2.messageKeys.length) 8 :=
    ⟨by omega, hpow8, by unfold maxMessageKeys at hmax; omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (308))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  wp_compact
  wp_steps
  wp_call halloc (104 * x.gc.2.messageKeys.length, 8)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (860))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic860 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod8, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (408))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.weaken_pre ?_
        (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
          (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            chainMkSourceFrame A x.gc x.src ∗
            ((s0.sp - 208#64) ↦₆₄ x28) ∗
            ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
            ((s0.sp - 196#64) ↦₃₂ w27) ∗
            ((s0.sp - 192#64) ↦₆₄ x25) ∗
            ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
            ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
            ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            savedRegsCore s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l => ?_)
      · rw [hzip_len, BitVec.add_zero]
        exact Entails.of_eq (by dsimp only [mkPtr']; ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm, hzip_len]
      · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      · exact htrace1
      · simp only [wp_norm]; assumption
      · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
        have hsp_l_align : sf_l.spAligned = true := by
          rw [State.spAligned, hsp_l]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
          (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
        simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
          map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
          sepConj_assoc]
        apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (736))
        wp_steps
        refine SepWP.done ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · refine SepWPp.weaken_pre ?_
            (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
              simp [hklen]
            have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
              rw [hzip'_len]; exact hpos
            have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
              rw [hzip'_len]; exact hmax
            have hbuf_eq := vecBuf_mk_pos_eq A mkPtr' (keys'.zip x.gc.2.messageKeys)
              hzip'_pos hzip'_max hoom64
            rw [hzip'_len] at hbuf_eq
            rw [hbuf_eq,
                chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
                spillSlotsExist_eq_struct s0.sp,
                savedRegsOnStack_eq_core s0]
            have hsp_fold :
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ⊢
                (∃∗ s : SpillSlots,
                  ((s0.sp - 208#64) ↦₆₄ s.v0) ∗
                  ((s0.sp - 200#64) ↦₃₂ s.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ s.w1b) ∗
                  ((s0.sp - 192#64) ↦₆₄ s.v2) ∗
                  ((s0.sp - 184#64) ↦₆₄ s.v3) ∗
                  ((s0.sp - 176#64) ↦₆₄ s.v4) ∗
                  ((s0.sp - 168#64) ↦₆₄ s.v5) ∗
                  ((s0.sp - 160#64) ↦₆₄ s.v6) ∗
                  ((s0.sp - 152#64) ↦₆₄ s.v7)) := by
              apply Entails.sepExists_right
                ⟨x28, spSlots.w1a, w27, x25, privPtr',
                  BitVec.ofNat 64 x.gc.1.priv.bytes.length, srkPtr',
                  BitVec.ofNat 64 x.gc.1.srk.bytes.length, x.dst⟩
              dsimp only
              exact Entails.refl _
            have hsr_fold :
                (((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  savedRegsCore s0) ⊢
                (∃∗ p : BitVec 64 × BitVec 32,
                  ((s0.sp - 120#64) ↦₆₄ p.1) ∗
                  ((s0.sp - 108#64) ↦₃₂ p.2) ∗
                  savedRegsCore s0) := by
              apply Entails.sepExists_right (v11', w12b')
              dsimp only
              exact Entails.refl _
            have hsrc_fold :
                (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) ⊢
                (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
                    x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) :=
              Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
            have hgroup_pre :
                (arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                  memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  chainMkSourceFrame A x.gc x.src ∗
                  ((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  savedRegsCore s0) =
                (memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                    arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                    arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                    chainMkSourceFrame A x.gc x.src) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  (((s0.sp - 208#64) ↦₆₄ x28) ∗
                    ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                    ((s0.sp - 196#64) ↦₃₂ w27) ∗
                    ((s0.sp - 192#64) ↦₆₄ x25) ∗
                    ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                    ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                    ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                    ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                    ((s0.sp - 152#64) ↦₆₄ x.dst)) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  (((s0.sp - 120#64) ↦₆₄ v11') ∗
                    ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                    savedRegsCore s0)) := by
              ac_rfl
            rw [hgroup_pre]
            exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsrc_fold
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsp_fold
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right hsr_fold))))))))))))
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · rw [State.spAligned] at hsp_l_align ⊢; simp only [wp_norm]; exact hsp_l_align
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · unfold State.readReg32; simp only [wp_norm, htrunc32]
          · exact htr_l
          · simp only [wp_norm]; exact hvregs_l

private theorem chain_clone_placed_ck_none [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hpc : s.pc = (blkPl_161).base + 244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_placed_mks_nil (A := A) (H := H)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_placed_mks_nonempty (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck R
      hsrk hmax hsrc_klen hpos
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hmks_nil hmks_ne ⊢
  rw [chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
  simp only [sepConj_assoc]
  have hck_buf :
      clonedOptChainKeyBuf A x.gc.1.ck optChainKeyNone
        (s.readReg64 (Reg.gpr 28#5)) (s.readReg32 (Reg.gpr 27#5)) x.gc.2.chainKey = emp := by
    rw [hck]; simp only [clonedOptChainKeyBuf, pure_true]
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (732))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine SepWPp.weaken_pre ?_
        (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen, hlen0]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (260))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · refine SepWPp.weaken_pre ?_
        (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption

private theorem chain_clone_placed_ck_some [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (ck : ChainKey) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hpc : s.pc = (blkPl_161).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic812 := fun s P => chain_clone_placed_panic_812 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_placed_mks_nil (A := A) (H := H)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_placed_mks_nonempty (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩ R
      hsrk hmax hsrc_klen hpos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic812 hmks_nil hmks_ne ⊢
  rw [chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (180))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  wp_compact
  wp_steps
  wp_call halloc (32, 1)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (812))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic812 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_ck_post :
        ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live ckPtr' 32 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          chainCkSomeFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      have hck_buf_eq :
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
            A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
        rw [hck]
        simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
        have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
        have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
        have hv := vecU8Buf_pos_eq A ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
        rw [hck_len] at hv
        exact hv
      rw [hck_buf_eq,
          chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
      have hsrc_ent :
          (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) ⊢
          (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) :=
        Entails.pure_right ⟨hck_le, hck_lt, hck_ptr⟩ (Entails.refl _)
      have hgroup :
          ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live ckPtr' 32 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            chainCkSomeFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            (A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key)) ∗
            (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
              ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
              ((x.src + 88#64) ↦₆₄ 32#64) ∗
              ((x.src + 96#64) ↦₃₂ ck.index) ∗
              (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
              chainCkSomeFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsrc_ent))))
    by_cases hmk_nil : x.gc.2.messageKeys = []
    · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (732))
      wp_steps
      wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre
          (Entails.trans (by rw [hlen0]; exact Entails.refl _) hfold_ck_post)
          (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
        · exact htr_sf2
        · simp only [wp_norm]; assumption
    · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
      have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (260))
      wp_steps
      wp_call hmemcpy (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre hfold_ck_post
          (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
        · exact htr_sf2
        · simp only [wp_norm]; assumption

private theorem chain_clone_placed_priv_nil [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (blkPl_161).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_placed_ck_none (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_placed_ck_some (A := A) (H := H) hshim halloc hmemcpy hpanic x ck s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hck_none hck_some ⊢
  have hpriv_buf :
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (232))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · have hfold_priv :
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 40#64) ↦₆₄ 0#64) ∗
          chainPrivLenFrame A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
      ac_rfl
    rw [hfold_priv]
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_none _ hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by ac_rfl)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm, hpriv_len0]
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace
        · simp only [wp_norm]; assumption
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                  ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          exact Entails.pure_right hck_lt (Entails.refl _)
        · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm, hpriv_len0]
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace
        · simp only [wp_norm]; assumption

private theorem chain_clone_placed_priv_pos [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (blkPl_161).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic800 := fun s P => chain_clone_placed_panic_800 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_placed_ck_none (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_placed_ck_some (A := A) (H := H) hshim halloc hmemcpy hpanic x ck s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic800 hck_none hck_some ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic800 hck_none hck_some ⊢
  rw [chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (116))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by reg_chain
  wp_compact
  wp_steps
  wp_call halloc (x.gc.1.priv.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (800))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic800 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_priv_post :
        ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          chainPrivPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64,
          chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
      have hsrc_ent :
          (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
              x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
              x.gc.1.priv.ptr ≠ 0⌝ ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ (Entails.refl _)
      have hgroup :
          ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            chainPrivPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            (A.live privPtr' x.gc.1.priv.bytes.length 1 ∗ (privPtr' ↦ₛ x.gc.1.priv.bytes)) ∗
            (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
              ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
              (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
              chainPrivPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hsrc_ent)))
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (136))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.priv.ptr, x.gc.1.priv.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_priv_post ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_none _ privPtr' hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by ac_rfl)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · exact htr_sf2
        · simp only [wp_norm]; assumption
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                  ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          exact Entails.pure_right hck_lt (Entails.refl _)
        · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · exact htr_sf2
        · simp only [wp_norm]; assumption

private theorem chain_clone_placed_entry [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (blkPl_161).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp ((blkPC_161).rebase (blkPl_161).base H) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic848 := fun s P => chain_clone_placed_panic_848 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = []) =>
    chain_clone_placed_priv_nil (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length) =>
    chain_clone_placed_priv_pos (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv_pos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  rw [chainAt_eq_pure_sep A x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  rw [chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 =>
    SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v22 => SepWPp.exists_elim fun v23 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat = x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hsrk_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (68))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (x.gc.1.srk.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, ‹sf.trace = s0.trace›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (848))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic848 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_srk_post :
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          deadStackSlots s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
          chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen]
      unfold savedRegsOnStack deadStackSlots
      have hsrc_ent :
          (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.srk.bytes.length ≤ x.gc.1.srk.cap.toNat ∧
              x.gc.1.srk.cap.toNat < 2 ^ 63 ∧
              x.gc.1.srk.ptr ≠ 0⌝ ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      have hgroup :
          ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            chainSrkPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
            ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
          (memRegion x.dst 104 ∗
            (A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ (srkPtr' ↦ₛ x.gc.1.srk.bytes)) ∗
            (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
              ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
              (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
              chainSrkPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
              ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
              ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
              ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
              (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent))
    apply SepWPp.of_sepWP (mid := (blkPl_161).base + bv% (88))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by reg_chain
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_srk_post ?_
    by_cases hpriv_nil : x.gc.1.priv.bytes = []
    · refine hpriv_nil_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_nil
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align
    · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
      refine hpriv_pos_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_pos
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align

private theorem protoChain_clone_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsRustNoAllocShimSym) CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (blkPl_161).base
      (protoChainCloneSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hs0_align
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack,
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, fun R' hm' hloaded => ?_⟩
  rcases chain_clone_placed_entry hshim halloc hmemcpy hpanic x s0 hs0_align R hpc hrun hx0 hx1 R' hm' hloaded with
    ⟨sf, hsteps, ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hrun_f, P_f, hmem_f,
      ⟨fun hm_R => Satisfies.mono (sepConj_mono_left hpost_f) hm_R, hsp_f, hcc_f⟩⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem protoChain_clone_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (blkPl_161).base
      (protoChainCloneSpec A) :=
  protoChain_clone_placed_ok_of_hooks
    (ls_hook_ok_of_mem hshim)
    (ls_hook_ok_of_mem halloc)
    (ls_hook_ok_of_mem hmemcpy)
    hpanic

theorem chain_clone_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsRustNoAllocShimSym) CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (blkPl_161).base
      (chainCloneSpec A) :=
  chainClone_of_protoChainClone_gen (protoChain_clone_placed_ok_of_hooks hshim halloc hmemcpy hpanic)

/-- Block `161`: `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]`
    (`0x3846c`, 218 instructions) satisfies `chainCloneSpec A` under `[LibsignalPlacement]`. -/
theorem chain_clone_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (blkPl_161).base
      (chainCloneSpec A) :=
  chainClone_of_protoChainClone_gen (protoChain_clone_placed_ok hshim halloc hmemcpy hpanic)

theorem senderChain_clone_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsRustNoAllocShimSym) CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_161).rebase (blkPl_161).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (blkPl_161).base
      (senderChainCloneSpec A) :=
  senderChainClone_of_chainClone_gen optSenderChainAt_some_eq_chainAt
    (protoChain_clone_placed_ok_of_hooks hshim halloc hmemcpy hpanic)

/-- Block `161`: Sender-chain clone (`sender_chain.is_some()` specialization) satisfies
    `senderChainCloneSpec A` under `[LibsignalPlacement]`. -/
theorem senderChain_clone_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_161).rebase (blkPl_161).base H) (blkPl_161).base
      (senderChainCloneSpec A) :=
  senderChainClone_of_chainClone_gen optSenderChainAt_some_eq_chainAt
    (protoChain_clone_placed_ok hshim halloc hmemcpy hpanic)

end CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
