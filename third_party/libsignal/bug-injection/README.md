# Bug injection: known libsignal bugs as patches

Inputs of the bug-injection framework ([`Symbolic/BugInjection/README.md`](../../../Symbolic/BugInjection/README.md)).
Runner: `scripts/bug_injection.py`.

| path | what | license |
|---|---|---|
| [`bugs.toml`](bugs.toml) | the registry: bugs (Rust diffs) and witnesses (statement, inputs, expected status) | Google |
| `patches/<bug>/upstream-<sha>.diff` | the fix commit's diff, byte-identical to `https://github.com/signalapp/libsignal/commit/<sha>.diff`; applied **reversed**, it puts the bug back | libsignal: `AGPL-3.0-only`, [`../LICENSE`](../LICENSE) |
| `patches/<bug>/v0.105.4.diff` | the same reversal ported to libsignal v0.105.4, used when the upstream diff no longer applies there | libsignal: `AGPL-3.0-only`, [`../LICENSE`](../LICENSE) |
| `witnesses/<witness>.json` | a witness's inputs: the environment's calls and the attacker's bytes | Google |
| [`harness/`](harness) | the generic replayer: drives a statement's entry points from witness inputs and records the machine events | Google, `Apache-2.0` |

Nothing here is part of a verified image or of `lake build`. The runner applies a patch only to a
clone of the pinned libsignal checkout inside the gitignored `.lake/bug-injection/`.
