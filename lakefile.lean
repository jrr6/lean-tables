import Lake
open Lake DSL

package table {
  -- add configuration options here
}

@[default_target]
lean_lib Table {
  roots := #[`Table]
  globs := #[Glob.submodules `Table]
}
