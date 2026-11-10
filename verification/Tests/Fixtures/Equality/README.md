# Equality regression coverage

Every production equality method/profile still has its own compiled certificate: 24 scalar,
24 x64-v3 and four SSE entries. Regression fixtures test implementation changes and rejection
behaviour, rather than repeating every helper mutation through every public wrapper.

`EqualityCoverage.cs` maps each overload explicitly to its direct `Equals` implementation.
Unknown overloads and fixtures fail selection. `TestVerification.cs` checks that the selected
representative exists and is applicable on the same profile, that positive proof files exist,
and that all wrapper-local polarity mutations and the snapshot mutation remain selected.

| Fixture | Retained coverage |
| --- | --- |
| Baseline / Renamed | Direct signed/unsigned 32/64-bit `Equals`, reference and by-value `Equals`; reversed signed `EqInt32UInt256`, primitive negation `NeUInt256UInt64`, nested reference negation `NeUInt256UInt256` |
| EquivalentReduction | The same representatives on vector profiles; scalar has no such transformation |
| WrongLane / WrongReduction | `EqualsUInt256Ref` on scalar, SSE and AVX, exercising each distinct reduction implementation |
| WrongReceiver | `EqualsUInt256Ref` on all three profiles, where the receiver is changed |
| WrongSignedEmbedding | `EqualsInt32` and `EqualsInt64` on scalar and AVX, where the signed conversion is changed |
| WrongPolarity | Every registered inequality operator on its profile; the mutation changes each wrapper itself |
| WrongNarrowing | `EqUInt256UInt256` on all three profiles; truncating the encoded true result `256` to a byte changes it to false |
| WrongSnapshot | `EqualsUInt256Value` on all three profiles; this changes the by-value receiver handling |

All selected negative cases prove a concrete checked counterexample and require the production
proof to fail without leaving a certificate. No negative mutation kind is removed. The scalar,
SSE and AVX implementations stay separate; bit widths, signedness and by-value storage are not
treated as interchangeable. The baseline body comparison still checks fixture/production
agreement for every selected representative.

Unselected combinations no longer receive independent mutation certificates. Their unmodified
production wrappers remain certified, and selected positive wrapper cases test composition.
This is deliberate regression-test reduction, not a claim that one fixture certificate certifies
all omitted extracted programs. Changed receiver, polarity, conversion and snapshot handling
cannot be justified merely by a helper result.

`UInt256.Methods.Equality.WrapperObservation.forward` transports a concrete child invocation
through an exactly matched two-argument wrapper, including reversed arguments and optional
Boolean negation. It checks argument validity and unspecified-value restrictions, and composes
checked execution without unfolding the child. The polarity refutations use it with the actual
mutated wrapper body (no negation), then contradict the production contract. Helper observations
remain checked against the compiled extraction, and each selected production-proof rejection
still exercises the verifier end to end.

| Profile | Representative cases / requests |
| --- | ---: |
| scalar | 34 / 50 |
| x64-v3 | 43 / 59 |
| x64-sse42 | 15 / 21 |
| Total | 92 / 130 |

Shared leaf proofs live in `Shared/`, while each retained binding states the production contract
verbatim.
