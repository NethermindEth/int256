// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

namespace UInt256Verification;

/// <summary>A worker's fresh Lake workspace; only dependencies checked in this session may be reused.</summary>
internal sealed class ProofSession(Workspace workspace) : IDisposable
{
    internal string Directory { get; } = System.IO.Directory.CreateTempSubdirectory("int256-proof-worker-").FullName;
    private readonly int _owner = Environment.CurrentManagedThreadId;
    private Dictionary<string, string>? _inputs;
    private string[] _paths = [];
    internal int Uses { get; private set; }

    internal string[] Prepare(IReadOnlyDictionary<string, string> inputs)
    {
        if (Environment.CurrentManagedThreadId != _owner) throw new InvalidOperationException("Proof session belongs to another worker");
        if (_inputs is null)
        {
            _paths = workspace.CopyProofSources(Directory, inputs);
            _inputs = new(inputs);
        }
        else if (!Workspace.SameInputs(_inputs, inputs)) throw new InvalidOperationException("Proof session has stale source inputs");
        Workspace.CheckProofSnapshot(Directory, _paths, inputs);
        foreach (string relative in new[] { "generated/Extracted.lean", "generated/artifact.json", "UInt256/Methods/SelectedGate.lean", "UInt256/Methods/SelectedSafetyGate.lean" })
        {
            if (_paths.Contains(relative)) throw new InvalidOperationException("Generated audit would overwrite handwritten source");
            string target = Path.Combine(Directory, relative);
            if (System.IO.Directory.Exists(Path.GetDirectoryName(target))) File.Delete(target);
        }
        Uses++;
        return _paths;
    }

    public void Dispose() => System.IO.Directory.Delete(Directory, recursive: true);
}
