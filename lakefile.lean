import Lake
open Lake DSL

package YatimaStdLib

@[default_target]
lean_lib YatimaStdLib where
  precompileModules := true

def ffiC := "ffi.c"
def ffiO := "ffi.o"

target importTarget (pkg : Package) : FilePath := do
  let oFile := pkg.oleanDir / ffiO
  let srcJob ← inputFile $ pkg.dir / ffiC
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO ffiC oFile srcFile flags

extern_lib ffi (pkg : Package) := do
  let name := nameToStaticLib "ffi"
  let job ← fetch <| pkg.target ``importTarget
  buildStaticLib (pkg.buildDir / defaultLibDir / name) #[job]

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

section ImportAll

open System
open Lean (RBTree)

partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getLeanFilePaths dir.path acc) acc
  else return if fp.extension == some "lean" then acc.push fp else acc

def getAllFiles : ScriptM $ List String := do
  let paths := (← getLeanFilePaths ⟨"YatimaStdLib"⟩).map toString
  let paths : RBTree String compare := RBTree.ofList paths.toList -- ordering
  return paths.toList

def getImportsString : ScriptM String := do
  let paths ← getAllFiles
  let imports := paths.map fun p =>
    "import " ++ (p.splitOn ".").head!.replace "/" "."
  return s!"{"\n".intercalate imports}\n"

script import_all do
  IO.FS.writeFile ⟨"YatimaStdLib.lean"⟩ (← getImportsString)
  return 0

script import_all? do
  let importsFromUser ← IO.FS.readFile ⟨"YatimaStdLib.lean"⟩
  let expectedImports ← getImportsString
  if importsFromUser != expectedImports then
    IO.eprintln "Invalid import list in 'YatimaStdLib.lean'"
    IO.eprintln "Try running 'lake run import_all'"
    return 1
  return 0

end ImportAll

/- Tests -/
lean_exe Tests.Arithmetic
lean_exe Tests.AddChain
lean_exe Tests.ByteArray
lean_exe Tests.ByteVector
lean_exe Tests.Int
lean_exe Tests.Nat
lean_exe Tests.Polynomial
lean_exe Tests.SparseMatrix
lean_exe Tests.UInt

/- Benchmarks -/
lean_exe Benchmarks.AddChain
lean_exe Benchmarks.ByteArray
lean_exe Benchmarks.Matrix
lean_exe Benchmarks.SparseMatrix
