using Mono.Cecil;

if (args.Length != 2) throw new ArgumentException("Usage: Extractor assembly.dll output-directory");
using ModuleDefinition module = ModuleDefinition.ReadModule(args[0]);
(TypeDefinition type, MethodDefinition[] methods) = MetadataValidation.Validate(module);
Directory.CreateDirectory(args[1]);
(string lean, List<object> coverage) = LeanEmitter.Generate(methods);
File.WriteAllText(Path.Combine(args[1], "Extracted.lean"), lean);
string hash = ArtifactReport.Write(module, type, methods, coverage, args[0], args[1]);
Console.WriteLine($"Extracted {methods.Length} methods from {hash}");
