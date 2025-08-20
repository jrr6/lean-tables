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

@[test_driver]
lean_lib Tests {
  globs := #[Glob.submodules `Tests]
}
