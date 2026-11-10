/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir

/-!
# Bob's pre-key `recv` over a session that does not match: `CliSpecPqxdhNoMatch`

**Trusted: the statement.** Extends `CliSpecPqxdh` (`PqDir.lean`) to `recv <peer>` of a canonical
pre-key message `m` when the party holds a non-matching session (`¬ PqSessionMatches`, DEV-CLI11; see
`Computational/docs/TRUSTED_BASE.md`).

When `promote_matching_session` finds no matching session (and `encodeRecordUnderExtras` encodes no
previous sessions), libsignal runs a fresh PQXDH handshake independent of the existing session,
archives the old session on success, and decrypts the inner message solely under the new session.
Accordingly, `CliSpecPqxdhNoMatch` relates the outcome to `pqRecvPrekeyModel` at `{ st with session := none }`:
* on accept: exit `0` with the no-session model's stdout and files at every canonical path except
  `sessionFile (partyAddress st.party.other)` (`Outcome.AgreeExcept`);
* on reject or panic: exact agreement with `pqxdhExpectedOutcome` (exit `1` with all files unchanged,
  or `aborted`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-- **Two outcomes agree at every path except `p`**: both abort, or both exit with the same code
and stdout, and their files agree at every path that is not a spelling of `p`, i.e. whose canonical
form (`Arm64.normalizePath`) differs from `p`'s. Paths are compared in canonical form because the
files of both outcomes are read through `fsView` (`Run.lean`), which looks a path up by its
canonical form: with raw `String` inequality, another spelling of `p` (e.g. `"./" ++ p`) would be
a path "other than `p`" at which `fsView` reads `p`'s file, so the files would have to agree at `p`
too. -/
def Outcome.AgreeExcept (p : String) : Outcome → Outcome → Prop
  | .aborted, .aborted => True
  | .exited c out fs, .exited c' out' fs' =>
      c = c' ∧ out = out' ∧ ∀ q, Arm64.normalizePath q ≠ Arm64.normalizePath p → fs q = fs' q
  | _, _ => False

/-- **The run's outcome `o` against the model's answer `r` on the inputs `i`, the file at `p`
excepted on an accept**: if `r` accepts, `o` agrees with `pqxdhExpectedOutcome W i r` at every path except `p`
(`Outcome.AgreeExcept`); if `r` rejects or panics, `o` is `pqxdhExpectedOutcome W i r` (exit `1` with every file
unchanged, or abort). -/
def OutcomeMatchesModelExceptPath (W : PEParams) (i : Inputs) (p : String)
    (r : Option (Option (PqParty × List (BitVec 8)))) (o : Outcome) : Prop :=
  match r with
  | some (some _) => Outcome.AgreeExcept p o (pqxdhExpectedOutcome W i r)
  | _ => o = pqxdhExpectedOutcome W i r

/-- **Bob's pre-key `recv` over a session that does not match** (`run` is any
implementation; the real one is the engine process of the CLI's ELF). For every model primitives
`W` and model extras `X`, every party state `st` in the domain (`PqxdhPartyInSpecDomain`) that holds a session `(x, g)`,
and every typed pre-key message `m` that the session does not match (`¬ PqSessionMatches x g m`)
whose inner message is below `2^32 - 2048` bytes, with coins `rc`: if `(3 ‖ m.bytes).length >
stdinCapBytes` (`2^20`), `recv <peer>` exits `2` (`read_stdin` cap) with empty stdout and every
file unchanged (the session file included); otherwise the run of `recv <peer>` of
`3 ‖ m.bytes` has an outcome, and it is `pqRecvPrekeyModel X W` on `st` with no session, the
session file excepted on an accept (`OutcomeMatchesModelExceptPath`). `m`'s registration id, ids, keys and inner
message are any values (the adversary's).

**DEV-CLI11 (libsignal): after a pre-key `recv` over a session that does not match it is accepted,
the session file and the party's later calls are not claimed.** libsignal archives the old session
as the new record's previous session, which `encodeRecordUnderExtras` cannot write (one current session,
`DEV-C-PREV`). So on an accept the session file's bytes are excepted (`OutcomeMatchesModelExceptPath`), and the
party's directory is then outside `PqxdhPartyInSpecDomain`: no spec covers its later calls. A game must exclude them,
and leaks of that file, until the file is deleted. No trusted statement about the binary claims
the bytes of this session file: `CliPqxdhElfCorrectPlaced` (`CliBinaryPq.lean`) excepts them as
this spec does. In the CLI refinement
(`Symbolic/Specifications/Refinement/Statement.lean`), Bob makes no call after such
an accept until the environment deletes the file (`BobCallAllowed`, D2(c)), and the file's current
session may be leaked meanwhile. A claim about the file or those calls would be a separate
statement over the same inputs, and this one would not change. -/
def CliSpecPqxdhNoMatch (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain W st →
    ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
    ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      ¬ PqSessionMatches x g m →
      if (wirePrekey :: m.bytes).length > stdinCapBytes then
        run (pqRecvInputs W st (wirePrekey :: m.bytes) rc) =
          some (.exited 2 [] (filesOf (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files))
      else
        ∃ o, run (pqRecvInputs W st (wirePrekey :: m.bytes) rc) = some o ∧
          OutcomeMatchesModelExceptPath W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
            (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X W { st with session := none } m rc) o

end CryptoVerification.SignalSession
