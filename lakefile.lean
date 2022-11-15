import Lake
open Lake DSL

package YatimaStdLib

require std from git
  "https://github.com/leanprover/std4/" @ "d83e97c7843deb1cf4a6b2a2c72aaf2ece0b4ce8"

@[default_target]
lean_lib YatimaStdLib
