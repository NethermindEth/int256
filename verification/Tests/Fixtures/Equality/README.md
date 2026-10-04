Equality fixtures reuse the production contracts and handwritten execution proofs for all 24 selected equality APIs. Cases are registered once in `Cases.props`; every build selects the same `Public.cs` and `Core.cs` sources with an explicit symbol. Unknown cases fail before compilation.

Run from the repository root:

```text
python verification/Tests/Fixtures/Equality/checks.py --method EqUInt256UInt256 --profile scalar
python verification/Tests/Fixtures/Equality/checks.py --method EqualsUInt256Value --profile x64-sse41
python verification/Tests/Fixtures/Equality/checks.py --method EqUInt256Int32 --profile x64-vector256
```

Each run establishes fresh production and fixture baselines, then checks applicable cases. Positive cases rename and extract a helper, replace scalar reductions with limb comparisons, or use equivalent vector reductions. They must change the extracted program while retaining identical handwritten proof hashes.

Negative witnesses cover ignored lanes, incorrect reductions, signed embedding, inequality polarity, the instance receiver and by-value snapshots. A concrete execution observation refutes the full contract at every successful fuel before the public verifier is required to reject the fixture and remove its report. Syntax/import errors and resource exhaustion are inconclusive failures.

`Witnesses.json` contains concrete inputs and targeted changed signatures. The native driver checks the same return and unchanged caller bytes, and prints actual hardware capabilities; native observations do not replace the Lean proof or establish machine-code correctness.
