# AI use

The Ramanujan Challenge submissions behind this library were made by Jeromie Beasley with AI
tools (Claude and ChatGPT) used as research assistants; the same tools wrote and repaired the
Lean proofs here and organised this repository. The Problem 2.1 analysis
(`RamanujanChallenge/Problem21.lean`, `RamanujanChallenge/Euler21.lean`, `scripts/precheck3.py`,
three false controls) was written on
17 October 2026 by Grok Bot, an AI agent working for the author. It found the
creative-telescoping certificate and the dominance bound in SymPy, checked them there, and then
had the Lean kernel check them.

No statement here rests on an AI's say-so. Every proof is checked by the Lean kernel and
replayed by an independent kernel checker on every push, every theorem's axioms are audited,
and every false control must be rejected for the check to pass. What the statements mean, and
what they do not claim, is set out in plain words in `README.md` and `LIMITATIONS.md`.
