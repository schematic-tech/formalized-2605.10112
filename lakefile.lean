import Lake
open Lake DSL

package DominatingFourColour where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "9d44f295b1de1c2a2c91bcb7dae8d5b0b15839c4"
require SchematicMath from git
  "git@github.com:schematic-rs/math.git" @
    "fa493430f626140dd5043753d465bf8c9cfa15ab"
require FourColorTheorem from git
  "git@github.com:schematic-rs/formalized-fct.git" @
    "fbd89b9f6d9bfdb17e0d24a0400404affa8bf87a" with
  NameMap.empty.insert `nativeDecide ((get_config? nativeDecide).getD "false")

@[default_target]
lean_lib DominatingFourColour where
  roots := #[`DominatingFourColour]
