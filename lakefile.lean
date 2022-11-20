import Lake
open Lake DSL

package YatimaStdLib

require std from git
  "https://github.com/leanprover/std4/" @ "d83e97c7843deb1cf4a6b2a2c72aaf2ece0b4ce8"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

@[default_target]
lean_lib YatimaStdLib
