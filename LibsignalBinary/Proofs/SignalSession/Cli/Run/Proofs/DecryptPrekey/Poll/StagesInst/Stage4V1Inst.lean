/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4

/-!
# Poll Path B Stage P4 Instantiation

Instantiates `Poll.StageP4MatchedExtStmt` via `Matched.stageP4_matched_ok` and
`Poll.StageP4MatchedXExtStmt` via `Matched.stageP4_matched_x_ok`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession.Cli.RunProofs

private theorem stageP4MatchedBranch_of_matched
    {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64}
    {opkHi kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)}
    {peer : AddrGhost}
    {remoteIk : IdentityKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {ss : Session (List (BitVec 8))}
    {sf : State} {Pf : SepProp}
    (h : Matched.StageP4MatchedBranch img kit ikit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
      ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
      sst0 ist0 ss sf Pf) :
    StageP4MatchedBranch img kit ikit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
      ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
      sst0 ist0 ss sf Pf := by
  cases h with
  | ok c hsave hstore htr hpost => exact .ok c hsave hstore htr hpost
  | saveErr hsave htr hpost => exact .saveErr hsave htr hpost
  | storeErr c hsave hstore htr hpost => exact .storeErr c hsave hstore htr hpost

/-- Instantiates `Poll.StageP4MatchedExtStmt` via `Matched.stageP4_matched_ok`. -/
theorem stageP4Matched_inst : StageP4MatchedExtStmt := by
  intro A img ext Scope encRecord kit ikit hA hDrop hSkit hSvt hIkit hIvt himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hb hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hfz hsym hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hwp := Matched.stageP4_matched_ok img ext kit ikit hA hDrop hSkit hSvt hIkit hIvt himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hb hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hfz hsym hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hs6, hbr⟩ | hpan
  · exact Or.inl ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hs6,
      stageP4MatchedBranch_of_matched hbr⟩
  · exact Or.inr hpan

/-- Lifts an `AllocHooks`-backed `Matched.StageP4MatchedBranch` proof to
`Poll.StageP4MatchedXExtStmt`. -/
theorem stageP4Matched_x_of_matched
    (hMatched : ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
      {Scope : SessionRecord (List (BitVec 8)) → Prop}
      {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
      (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base),
      AllocHooks A ext →
      DropSessionStructure3OkExt img.base A ext →
      SessionOnlyKitOkSE kit Scope encRecord ext →
      SessionOnlyVtablesOk img kit →
      IdentityStoreKitOkIE img ikit ext →
      IdentityVtablesOk img ikit →
      Obj.Loads libsignalSessionImage img →
      ∀ (s0 s : State)
        (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
         kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
        (peer : AddrGhost) (remoteIk : IdentityKey)
        (sst0 : kit.StoreState) (ist0 : ikit.IdState)
        (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
        img.base &&& 0xfff#64 = 0#64 →
        SessionExtraRel G ss →
        kit.RecOk ⟨some ss⟩ →
        kit.addrOk peer.val →
        ikit.addrOk peer.val →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Matched.stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
        FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
          (tripleRatchetProgAtExt img.base ext) s →
        img.FrozenLoaded s →
        s.symtab = img.symtab →
        s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
          Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
        s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true →
        s0.trace <+: s.trace →
        s.readReg64 .x19 = coroPtr →
        s.readReg64 .x24 = s.sp + 0x370#64 →
        s.readReg64 .x25 = s.sp + 0x210#64 →
        s.readReg64 .x26 = outPtr →
        s.readReg64 .x27 = ctxPtr →
        s.readReg64 .x28 = 0xfffffffffffffffe#64 →
        calleeSavedVRegs s = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
          (Matched.stageP4MatchedPre img kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
            remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
            opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
            sst0 ist0 g G ss.state)
          (fun sf Pf =>
            Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            ClosureCalleeSavedP4 s0 sf ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
            img.FrozenLoaded sf ∧
            sf.symtab = img.symtab ∧
            Matched.StageP4MatchedBranch img kit ikit encRecord s0 s coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
              ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
              sst0 ist0 ss sf Pf)
          (PanicOomProp s0)) :
    StageP4MatchedXExtStmt := by
  intro A img ext Scope encRecord kit ikit hA hDrop hSkit hSvt hIkit hIvt himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hb hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hfz hsym hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hwp := hMatched img ext kit ikit hA hDrop hSkit hSvt hIkit hIvt himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hb hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hfz hsym hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hs6, hbr⟩ | hpan
  · exact Or.inl ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hs6,
      stageP4MatchedBranch_of_matched hbr⟩
  · exact Or.inr hpan

/-- Instantiates `Poll.StageP4MatchedXExtStmt` via `Matched.stageP4_matched_x_ok`. -/
theorem stageP4Matched_x_inst : StageP4MatchedXExtStmt := by
  intro A img ext Scope encRecord kit ikit hA hDrop hSkit hSvt hIkit hIvt himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hb hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hfz hsym hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hwp := Matched.stageP4_matched_x_ok img ext kit ikit hA hDrop hSkit hSvt hIkit hIvt himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hb hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hfz hsym hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hs6, hbr⟩ | hpan
  · exact Or.inl ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hs6,
      stageP4MatchedBranch_of_matched hbr⟩
  · exact Or.inr hpan

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
