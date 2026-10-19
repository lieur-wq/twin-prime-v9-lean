import Lake
open Lake DSL

package twinPrimeV9 where
  version := v!"0.1.0"

-- Exact public stable release.  Commit lake-manifest.json after the
-- initial `lake update` to lock Mathlib's transitive dependencies too.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib TPCV9 where
  roots := #[`TPCV9] -- TPCV9.lean imports every source in the reviewed build.
