/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs

/-!
# Protocol-Error Tail Continuation Combinators (`encTail_run`)

Defines `EncTailV` continuation combinators (`encTail_run`, `segExit_of_run`,
`encTail_run_withEncCommon`) and the `encCommonFr` stack/pool split used by the T5 error tails.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

/-! ## Tail Entry State and Continuation Combinators -/

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- A tail entry state, parameterized by `kit`, `st0`, `ikit`, and `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV {img : Obj.Image} {A : RustAlloc} (kit : SessionStoreSpec A img.base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  s.pc = pc ∧ encMidMeta img x s0 s ∧ regs sp s ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨ slots sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗
      (encStoreExtra kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
        ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R))

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTail (A : RustAlloc) (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit) (pc : BitVec 64)
    (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp) (s0 s : State) :
    Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) () C ctl parse S
    x answers pc regs slots R s0 s

/-- **A straight-line run between two tail states**: if `hwp` runs the active part `Act sp` of
`slots sp = Act sp ∗ Fr sp` from `pc` to `pc'` (the frame base, `x19`, `x29` and the trace kept, the
registers then meet `regs'`) and ends with `Act'` such that `Act' ∗ Fr sp ⊢ slots' sp`, then a tail
state at `pc` steps to a tail state at `pc'`, with the trace unchanged. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_trap {img : Obj.Image} {A : RustAlloc} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {C : Crypto} {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' Act Fr : BitVec 64 → SepProp}
    {Act' : BitVec 64 → SepProp} {R : SepProp} {s0 s : State}
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc regs slots R s0 s)
    (hsplit : ∀ sp, slots sp ⊢ Act sp ∗ Fr sp)
    (hjoin : ∀ sp, Act' sp ∗ Fr sp ⊢ slots' sp)
    (hwp : ∀ sp, s.pc = pc → encMidMeta img x s0 s → regs sp s → sp = s0.sp - 0xbe0#64 →
      SepWP (trTrapProgAt img.base C abs) pc' s (Act sp)
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' sp s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' sp ∗ F)))
    (hL : (trTrapProgAt img.base C abs).CodeLoaded s.mem) :
    ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧ s'.trace = s.trace ∧
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc' regs' slots' R s0 s' := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV at hs
  obtain ⟨hpc, hmeta, hregs, hstk, hmem⟩ := hs
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hfr, hsym, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act (s0.sp - 0xbe0#64) ∗ (Fr (s0.sp - 0xbe0#64) ∗
      (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗
        (encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
          ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R))) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hsplit _)) hmem
  obtain ⟨s', hsteps, ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ | ⟨_, _hoom⟩⟩ :=
    (hwp _ hpc hmeta hregs rfl).elim hmem2 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV
  refine ⟨hpc', ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
    hsteps.frozenLoaded hfr, hsteps.symtab_eq.trans hsym, hvregs'.trans hvregs⟩, hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    exact Satisfies.mono (sepConj_mono_left (hjoin _)) h1

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run {img : Obj.Image} {A : RustAlloc} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {C : Crypto} {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' Act Fr : BitVec 64 → SepProp}
    {Act' : BitVec 64 → SepProp} {R : SepProp} {s0 s : State}
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc regs slots R s0 s)
    (hsplit : ∀ sp, slots sp ⊢ Act sp ∗ Fr sp)
    (hjoin : ∀ sp, Act' sp ∗ Fr sp ⊢ slots' sp)
    (hwp : ∀ sp, s.pc = pc → encMidMeta img x s0 s → regs sp s → sp = s0.sp - 0xbe0#64 →
      SepWP (tripleRatchetProgAt img.base C ctl abs) pc' s (Act sp)
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' sp s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' sp ∗ F)))
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧ s'.trace = s.trace ∧
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc' regs' slots' R s0 s' := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV at hs
  obtain ⟨hpc, hmeta, hregs, hstk, hmem⟩ := hs
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hfr, hsym, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act (s0.sp - 0xbe0#64) ∗ (Fr (s0.sp - 0xbe0#64) ∗
      (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗
        (encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
          ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R))) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hsplit _)) hmem
  obtain ⟨s', hsteps, ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ | ⟨_, _hoom⟩⟩ :=
    (hwp _ hpc hmeta hregs rfl).elim hmem2 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV
  refine ⟨hpc', ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
    hsteps.frozenLoaded hfr, hsteps.symtab_eq.trans hsym, hvregs'.trans hvregs⟩, hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    exact Satisfies.mono (sepConj_mono_left (hjoin _)) h1

/-- **A run into a tail**: if every loaded state `s` steps (trace unchanged) to a state meeting
`next`, and from every such state with `TailModel` the tail exits, then the tail exits from `s`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.segExit_of_run_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit}
    {res : Except (ApiError AddrVal Unit) CiphertextMessage} {next : State → Prop}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hrun : (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧ s'.trace = s.trace ∧ next s')
    (hnext : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s' → next s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  intro hL
  obtain ⟨s', h1, htr, hn⟩ := hrun hL
  obtain ⟨sf, h2, hout⟩ := hnext s' ⟨hm.1, htr.trans hm.2⟩ hn (h1.codeLoaded hL)
  exact ⟨sf, h1.trans h2, hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.segExit_of_run {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit}
    {res : Except (ApiError AddrVal Unit) CiphertextMessage} {next : State → Prop}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hrun : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧ s'.trace = s.trace ∧ next s')
    (hnext : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s' → next s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  intro hL
  obtain ⟨s', h1, htr, hn⟩ := hrun hL
  obtain ⟨sf, h2, hout⟩ := hnext s' ⟨hm.1, htr.trans hm.2⟩ hn (h1.codeLoaded hL)
  exact ⟨sf, h1.trans h2, hout⟩

/-- `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run` for a run that also uses `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon` (the allocator pool and the callees'
stack): the split / join are of `slots sp ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon` at the frame base. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_withEncCommon_trap {img : Obj.Image} {A : RustAlloc} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {C : Crypto} {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' : BitVec 64 → SepProp}
    {Act Act' Fr : SepProp} {R : SepProp} {s0 s : State}
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc regs slots R s0 s)
    (hsplit : slots (s0.sp - 0xbe0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ⊢ Act ∗ Fr)
    (hjoin : Act' ∗ Fr ⊢ slots' (s0.sp - 0xbe0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0)
    (hwp : s.pc = pc → encMidMeta img x s0 s → regs (s0.sp - 0xbe0#64) s →
      SepWP (trTrapProgAt img.base C abs) pc' s Act
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' (s0.sp - 0xbe0#64) s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' ∗ F)))
    (hL : (trTrapProgAt img.base C abs).CodeLoaded s.mem) :
    ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧ s'.trace = s.trace ∧
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc' regs' slots' R s0 s' := by
  let R' := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV at hs
  obtain ⟨hpc, hmeta, hregs, hstk, hmem⟩ := hs
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hfr, hsym, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act ∗ (Fr ∗ (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗ R')) := by
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left hsplit) ?_
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; ac_rfl)) hmem
  obtain ⟨s', hsteps, ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ | ⟨_, _hoom⟩⟩ :=
    (hwp hpc hmeta hregs).elim hmem2 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV
  refine ⟨hpc', ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
    hsteps.frozenLoaded hfr, hsteps.symtab_eq.trans hsym, hvregs'.trans hvregs⟩, hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    have h2 := Satisfies.mono (sepConj_mono_left hjoin) h1
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; ac_rfl)) h2

set_option linter.unusedVariables false in

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_withEncCommon {img : Obj.Image} {A : RustAlloc} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {C : Crypto} {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' : BitVec 64 → SepProp}
    {Act Act' Fr : SepProp} {R : SepProp} {s0 s : State}
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc regs slots R s0 s)
    (hsplit : slots (s0.sp - 0xbe0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ⊢ Act ∗ Fr)
    (hjoin : Act' ∗ Fr ⊢ slots' (s0.sp - 0xbe0#64) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0)
    (hwp : s.pc = pc → encMidMeta img x s0 s → regs (s0.sp - 0xbe0#64) s →
      SepWP (tripleRatchetProgAt img.base C ctl abs) pc' s Act
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' (s0.sp - 0xbe0#64) s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' ∗ F)))
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧ s'.trace = s.trace ∧
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers pc' regs' slots' R s0 s' := by
  let R' := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV at hs
  obtain ⟨hpc, hmeta, hregs, hstk, hmem⟩ := hs
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hfr, hsym, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act ∗ (Fr ∗ (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗ R')) := by
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left hsplit) ?_
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; ac_rfl)) hmem
  obtain ⟨s', hsteps, ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ | ⟨_, _hoom⟩⟩ :=
    (hwp hpc hmeta hregs).elim hmem2 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV
  refine ⟨hpc', ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
    hsteps.frozenLoaded hfr, hsteps.symtab_eq.trans hsym, hvregs'.trans hvregs⟩, hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    have h2 := Satisfies.mono (sepConj_mono_left hjoin) h1
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; ac_rfl)) h2

set_option linter.unusedVariables false in
/-- `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon` less the pool and the top `n` bytes of the callees' stack. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) (n : Nat) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
    memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - n) ∗
    encSavedRegs s0.sp s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) (n : Nat) (hn : n ≤ encSubStack) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 =
      (A.pool ∗ stackAt (s0.sp - 0xbe0#64) n) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr A ctl img x draws s0 n := by
  have h := stackAt_split_bottom (s0.sp - 0xbe0#64) n (encSubStack - n) (by
    simp only [encSubStack, withStoresEncStack, entryStack, encFrameSize] at hn ⊢; omega)
  rw [show n + (encSubStack - n) = encSubStack by omega] at h
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr
  rw [h]
  ac_rfl

gen_decodes libsignalSessionCode_tree protocolErrBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 3092) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3188), (ls_off% "libsignal_cli_ratchet::encrypt" + 3392) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3404), (ls_off% "libsignal_cli_ratchet::encrypt" + 3624) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3636), (ls_off% "libsignal_cli_ratchet::encrypt" + 3884) → (ls_off% "libsignal_cli_ratchet::encrypt" + 3896)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
