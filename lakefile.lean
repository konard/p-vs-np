import Lake
open Lake DSL

package «p-vs-np» where
  -- P vs NP formal proofs package

@[default_target]
lean_lib «proofs» where
  globs := #[.submodules `proofs]
  -- Automatically discovers and builds all .lean files in proofs/
