# GitHub Copilot Instructions for Int256 Repository

## Project Overview

This repository contains **Nethermind.Int256**, a high-performance .NET library implementing 256-bit integer types for blockchain and cryptographic applications. The library provides both signed (`Int256`) and unsigned (`UInt256`) 256-bit integer implementations optimized for performance using hardware intrinsics and vectorization.

### Key Features
- **High Performance**: Leverages SIMD instructions, vectorization, and hardware intrinsics
- **Complete API**: Implements all standard arithmetic, bitwise, and comparison operations
- **.NET Integration**: Full compatibility with .NET numeric interfaces and conversion patterns
- **Cross-Platform**: Supports multiple architectures with optimized code paths
- **Memory Efficient**: Struct-based design with minimal allocation overhead

## Architecture and Core Components

### Core Types
- **`UInt256`**: 256-bit unsigned integer (primary implementation)
- **`Int256`**: 256-bit signed integer (wrapper around UInt256)
- **`IInteger<T>`**: Common interface for integer operations
- **`BigIntegerExtensions`**: Extensions for System.Numerics.BigInteger integration

### Internal Structure
```csharp
// UInt256 uses explicit layout with 4 ulong components
[StructLayout(LayoutKind.Explicit)]
public readonly struct UInt256
{
    [FieldOffset(0)] public readonly ulong u0;  // Least significant
    [FieldOffset(8)] public readonly ulong u1;
    [FieldOffset(16)] public readonly ulong u2;
    [FieldOffset(24)] public readonly ulong u3; // Most significant
}
```

### Performance Optimizations
- **Hardware Intrinsics**: Uses `Vector256<T>` when available
- **Conditional Compilation**: Hardware intrinsics can be disabled via `DOTNET_EnableHWIntrinsic=0`
- **Unsafe Operations**: Leverages unsafe code for optimal performance
- **Branch Optimization**: Minimizes conditional branches in hot paths

## Development Environment

### Requirements
- **.NET 9.0 SDK** (specified in global.json)
- **Visual Studio 2022** or **VS Code** with C# extension
- **Git** for version control

### Project Structure
```
src/
├── Nethermind.Int256/              # Core library
│   ├── Int256.cs                   # Signed 256-bit integer
│   ├── UInt256.cs                  # Unsigned 256-bit integer (main implementation)
│   ├── IInteger.cs                 # Common interface
│   └── BigIntegerExtensions.cs     # BigInteger helpers
├── Nethermind.Int256.Tests/        # Unit tests
└── Nethermind.Int256.Benchmark/    # Performance benchmarks
```

### Build Commands
```bash
# Restore dependencies
dotnet restore

# Build (from src directory)
dotnet build

# Run tests
dotnet run -c Debug --project src/Nethermind.Int256.Tests

# Run benchmarks
dotnet run -c Release --project src/Nethermind.Int256.Benchmark
```

## Coding Standards and Conventions

### Code Style
- **Latest C# Language Version**: Uses `<LangVersion>latest</LangVersion>`
- **Nullable Reference Types**: Enabled throughout the project
- **Unsafe Blocks**: Allowed for performance-critical sections
- **Warnings as Errors**: `<TreatWarningsAsErrors>true</TreatWarningsAsErrors>`
- **Formatting**: 4-space indentation for C# files, LF line endings, UTF-8 encoding
- **Interface Naming**: Interfaces should begin with 'I' (e.g., `IInteger<T>`)
- **Type Naming**: PascalCase for types, methods, and properties

### Naming Conventions
- **Internal Fields**: Use `u0, u1, u2, u3` for UInt256 components (little-endian order)
- **Constants**: Use PascalCase (e.g., `MaxValue`, `MinValue`)
- **Static Readonly**: Use for compile-time constants
- **Private Static**: Use `s_` prefix for static fields (e.g., `s_instanceRandom`)

### Performance Guidelines
1. **Prefer Struct Operations**: Avoid boxing/unboxing
2. **Use ReadOnlySpan<T>**: For byte array operations
3. **Leverage Vector Operations**: When `Vector256<T>.IsSupported`
4. **Minimize Allocations**: Use `Unsafe.SkipInit()` when appropriate
5. **Branch Optimization**: Structure code to minimize conditional branches

### Memory Layout Considerations
```csharp
// Always consider endianness
public UInt256(ReadOnlySpan<byte> bytes, bool isBigEndian)

// Use explicit field offsets for predictable layout
[FieldOffset(0)] public readonly ulong u0; // Little-endian: LSB first
```

## Testing Guidelines

### Test Organization
- **Unit Tests**: Located in `Nethermind.Int256.Tests`
- **Test Categories**: Organized by operation type (Binary, Unary, Ternary, Convertibles)
- **Hardware Intrinsics Testing**: Tests run with both enabled and disabled intrinsics
- **Template Pattern**: Uses `UInt256TestsTemplate<T>` for shared test logic
- **FluentAssertions**: Uses FluentAssertions for readable test assertions
- **NUnit Framework**: All tests use NUnit attributes and framework

### Test Naming
```csharp
[Test]
public void OperationName_Scenario_ExpectedResult()
{
    // Arrange, Act, Assert pattern
    // Use FluentAssertions for readable assertions
    result.Should().Be(expected);
}

[TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
public void Add((BigInteger A, BigInteger B) test)
{
    // Use test case sources for comprehensive testing
}
```

### Test Data
- **TestNumbers.cs**: Contains predefined test values and edge cases
- **Comprehensive Coverage**: Tests include overflow, underflow, and boundary conditions
- **Cross-Platform**: Tests verify behavior across different hardware configurations

### Writing New Tests
When adding operations, ensure tests cover:
1. **Basic Operations**: Normal cases with typical values
2. **Edge Cases**: Zero, maximum/minimum values, overflow conditions
3. **Conversion Tests**: To/from other numeric types
4. **Performance Tests**: For critical path operations

## Performance Considerations

### Optimization Priorities
1. **Hot Path Operations**: Arithmetic operations (+, -, *, /, %)
2. **Comparison Operations**: Equality, less than, greater than
3. **Bitwise Operations**: AND, OR, XOR, shifts
4. **Conversion Operations**: To/from BigInteger, primitive types

### Hardware Intrinsics Usage
```csharp
if (Vector256<uint>.IsSupported)
{
    // Use vectorized operations
    Unsafe.As<ulong, Vector256<uint>>(ref this.u0) = Vector256.Create(...);
}
else
{
    // Fallback to scalar operations
}
```

### Memory Access Patterns
- **Sequential Access**: Prefer when possible for cache efficiency
- **Alignment**: Struct layout ensures proper alignment
- **Avoid Indirection**: Direct field access over property chains

## Build and CI Process

### GitHub Actions Workflow
- **Matrix Testing**: Tests against Debug/Release builds
- **Hardware Intrinsics**: Tests with `DOTNET_EnableHWIntrinsic=0` and `=1`
- **Cross-Platform**: Linux-based testing environment
- **NuGet Publishing**: Automated on releases

### Local Development
```bash
# Run full test matrix locally
DOTNET_EnableHWIntrinsic=0 dotnet run -c Debug --project src/Nethermind.Int256.Tests
DOTNET_EnableHWIntrinsic=1 dotnet run -c Release --project src/Nethermind.Int256.Tests

# Run performance benchmarks
dotnet run -c Release --project src/Nethermind.Int256.Benchmark
```

### Benchmarking
- **BenchmarkDotNet**: Uses BenchmarkDotNet for performance testing
- **Hardware Variants**: Benchmarks test both with and without hardware intrinsics
- **Baseline Comparisons**: Compare against System.Numerics.BigInteger where applicable

### Package Configuration
- **Package ID**: `Nethermind.Numerics.Int256`
- **Target Framework**: net9.0
- **Dependencies**: Minimal (Microsoft.SourceLink.GitHub for debugging)

## Common Patterns and Examples

### Creating UInt256 Values
```csharp
// From primitive types
UInt256 value1 = 42ul;
UInt256 value2 = new UInt256(0x12345678, 0x9ABCDEF0, 0, 0);

// From byte array
var bytes = new byte[32];
UInt256 value3 = new UInt256(bytes, isBigEndian: true);

// From BigInteger
BigInteger big = BigInteger.Parse("123456789012345678901234567890");
UInt256 value4 = (UInt256)big;
```

### Arithmetic Operations
```csharp
UInt256 a = 100;
UInt256 b = 200;
UInt256 sum = a + b;
UInt256 product = a * b;
bool isEqual = a == b;
```

### Performance-Critical Code Patterns
```csharp
// Use in/out parameters to avoid copies
public static void Add(in UInt256 left, in UInt256 right, out UInt256 result)

// Leverage hardware intrinsics when available
if (Vector256<ulong>.IsSupported)
{
    // Vectorized implementation
}
else
{
    // Scalar fallback
}

// Follow the IInteger<T> interface pattern for consistency
public void Add(in T a, out T res)
{
    // Implementation
}
```

## Contributing Guidelines

### License and Copyright
- **License**: MIT License (see LICENSE file)
- **Copyright**: Demerzel Solutions Limited
- **File Headers**: Not required (unlike some other Nethermind projects)

### Before Making Changes
1. **Understand Performance Impact**: Profile changes affecting hot paths
2. **Test Hardware Variants**: Ensure compatibility with/without intrinsics
3. **Maintain API Compatibility**: Preserve existing public interfaces
4. **Follow Existing Patterns**: Consistency with established code style

### Code Review Focus Areas
- **Performance**: No regression in benchmark results
- **Correctness**: Comprehensive test coverage
- **Security**: Proper handling of edge cases and overflow
- **Maintainability**: Clear, readable implementation

---

This library is a critical component for blockchain and cryptographic applications where performance and correctness are paramount. Always prioritize these concerns when making contributions.

## Quick Reference

### Key Files to Understand
- `UInt256.cs` - Primary implementation with all core operations
- `Int256.cs` - Signed wrapper around UInt256
- `IInteger.cs` - Common interface defining operation patterns
- `TestNumbers.cs` - Constants and edge cases for testing

### Common Operations Pattern
```csharp
// All operations follow this pattern for consistency and performance
public void OperationName(in UInt256 other, out UInt256 result)
{
    // Implementation using 'in' parameters to avoid copies
    // and 'out' parameters for results
}
```