using Mono.Cecil;

if (args.Length is < 2 or > 3) throw new ArgumentException("Usage: Extractor assembly.dll output-directory [Add|Subtract]");
string entrySignature = MetadataValidation.SelectedEntry(args.Length == 3 ? args[2] : "Add");
using ModuleDefinition module = ModuleDefinition.ReadModule(args[0]);
(TypeDefinition type, MethodDefinition[] methods) = MetadataValidation.Validate(module, entrySignature);
Directory.CreateDirectory(args[1]);
(string lean, List<object> coverage) = LeanEmitter.Generate(methods, entrySignature);
File.WriteAllText(Path.Combine(args[1], "Extracted.lean"), lean);
string hash = ArtifactReport.Write(module, type, methods, coverage, args[0], args[1], entrySignature);
Console.WriteLine($"Extracted {methods.Length} methods from {hash}");
