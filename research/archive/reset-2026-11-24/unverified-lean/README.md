# Unverified bridge source snapshot

These four modules were added in PR #1 after the previous formal baseline. They are preserved **byte-for-byte** from [d198628](https://github.com/vltanh/lean4-morrey/tree/d198628ecccb10fb1f2ded5ecd99f37e55c55e16) but are not part of the active Lean library after the research reset. The old PR build failed at LegendreHadamard.lean:62:4; subsequent audit steps did not run ([CI job](https://github.com/vltanh/lean4-morrey/actions/runs/45497494928/job/138811746229)). Their interfaces may be useful later; reintroduce them against current main only when needed, repair the proof, and check CI. Do not cite as verified declarations.

- [Morrey/Common/Basic/CalculusOfVariations/LegendreHadamard.lean](Morrey/Common/Basic/CalculusOfVariations/LegendreHadamard.lean)
- [Morrey/Pedregal/Bridges.lean](Morrey/Pedregal/Bridges.lean)
- [Morrey/Pedregal/CounterexampleCertificate.lean](Morrey/Pedregal/CounterexampleCertificate.lean)
- [Morrey/Pedregal/Jensen.lean](Morrey/Pedregal/Jensen.lean)

The active audit script and all active proof files are the current main versions. The original full source tree and old audit script remain available in the pinned commit above.
