using Mono.Cecil;

if (args.Length is < 2 or > 4) throw new ArgumentException("Usage: Extractor assembly.dll output-directory [Add|Subtract] [profile]");
string entrySignature = MetadataValidation.SelectedEntry(args.Length >= 3 ? args[2] : "Add");
FeatureProfile profile = FeatureProfile.Select(args.Length == 4 ? args[3] : "scalar");
using ModuleDefinition module = ModuleDefinition.ReadModule(args[0]);
(TypeDefinition type, MethodDefinition[] methods) = MetadataValidation.Validate(module, entrySignature, profile);
Directory.CreateDirectory(args[1]);
(string lean, List<object> coverage) = LeanEmitter.Generate(methods, entrySignature, profile);
File.WriteAllText(Path.Combine(args[1], "Extracted.lean"), lean);
string hash = ArtifactReport.Write(module, type, methods, coverage, args[0], args[1], entrySignature, profile);
Console.WriteLine($"Extracted {methods.Length} methods from {hash}");
