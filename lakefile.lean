import Lake
open Lake DSL

package YatimaStdLib

@[default_target]
lean_lib YatimaStdLib where
  precompileModules := true

def ffiC := "ffi.c"
def ffiO := "ffi.o"

target importTarget (pkg : Package) : FilePath := do
  let oFile := pkg.oleanDir / pkg.name.toString / "FFI" / ffiO
  let srcJob ← inputFile $ pkg.srcDir / pkg.name.toString / "FFI" / ffiC
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO ffiC oFile srcFile flags

extern_lib ffi (pkg : Package) := do
  let name := nameToStaticLib "ffi"
  let job ← fetch <| pkg.target ``importTarget
  buildStaticLib (pkg.buildDir / defaultLibDir / name) #[job]

require std from git
  "https://github.com/leanprover/std4/" @ "d83e97c7843deb1cf4a6b2a2c72aaf2ece0b4ce8"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"
