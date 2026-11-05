fixture = __DIR__
output = Path.join(fixture, "proofs")

prepared =
  Lynx.Rustler.prepare!(fixture, "experiment-nif",
    lean_project: output,
    module_prefix: "RustWorkspace.Facade",
    proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"]
  )

# BEAM uses the .so suffix on macOS too. Preserve the actual Cargo cdylib.
File.mkdir_p!(Path.join(fixture, "priv"))
File.cp!(prepared.library, Path.join(fixture, "priv/libexperiment_nif.so"))
File.cp!(prepared.expanded, Path.join(output, "facade-expanded.rs"))
File.write!(Path.join(output, "facade-bindings.json"), JSON.encode!(prepared.bindings))
