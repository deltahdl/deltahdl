#pragma once

#include <filesystem>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "parser/ast.h"

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct RtlirDesign;

// §33.5.3: binding a design whose cells a separate compilation tool has
// already compiled.
//
// This use model puts compiling and binding in different runs of different
// tools, and everything here follows from that split. The compiler tool leaves
// each cell it compiles in a compiled form somewhere in the filesystem, so a
// bind starts by reading those forms back rather than by parsing source: one
// LoadLibrary call per form, and as many calls as there were invocations of
// the compiler. The binding tool is then handed nothing but the name of each
// top-level cell -- no source description, and no account of what lies beneath
// -- so it reads the subinstances of a cell out of that cell's precompiled
// form and descends on what it finds there.
//
// Because no source description reaches a bind, a cell that an instance names
// and no loaded library holds can never be supplied later. The restriction
// this model carries is therefore that every cell of the design is precompiled
// before the bind begins, and Bind checks it: it walks the hierarchy first and
// binds nothing until it has found a cell for every name that walk reaches,
// naming the cells that were absent rather than stopping at whichever instance
// the binding order happened to reach first.
class SeparateCompilationBinder {
 public:
  SeparateCompilationBinder(SourceManager& mgr, Arena& arena, DiagEngine& diag);

  // Reads one compiled form back and adds the cells it holds to those this
  // binder can bind against. Cells accumulate across calls, so a design whose
  // cells were compiled by several invocations of the compiler -- into several
  // files, or under several library names -- is bound by loading each form in
  // turn. Reading a form does not consume it: it stays in the filesystem for
  // the next tool that wants it.
  //
  // Returns false, having reported, when the file is not a compiled form this
  // tool wrote or when what it holds does not read back.
  bool LoadLibrary(const std::filesystem::path& path);

  // Binds the design rooted at the named top-level cells and returns it, or
  // nullptr having reported. Those names are the whole description of the
  // design this call is given: every cell it binds, the tops included, comes
  // from the forms LoadLibrary has read.
  //
  // A cell no named top reaches is not bound. It stays among the loaded cells,
  // available to a later bind that names it, but it roots no hierarchy of its
  // own -- the tops of this design are the ones this call names.
  RtlirDesign* Bind(const std::vector<std::string_view>& top_names);

  // Binds the design the named configuration describes and returns it, or
  // nullptr having reported. This is the other thing a binding tool can be
  // given instead of the names of the top-level cells: the configuration says
  // which cells root the design and how the instances below them bind, so the
  // name of the configuration is by itself a whole description of the design.
  //
  // The configuration is looked for among the cells LoadLibrary has read,
  // because a bind is given no source description to read one out of. A
  // configuration that no compiled form holds therefore cannot be used here
  // and is reported, as is one whose cells are not all precompiled -- the same
  // restriction the rest of this model carries, applied to the cells the
  // configuration's design statement names.
  RtlirDesign* BindConfig(std::string_view config_name);

  // The cells the last Bind needed and no loaded library held, in name order.
  // Every one of them is found before any binding starts, so a design missing
  // several names them all rather than stopping at the first. Empty after a
  // Bind that went on to bind.
  const std::vector<std::string>& CellsNotPrecompiled() const {
    return not_precompiled_;
  }

 private:
  // How far a descent from the named tops has got: the cell names it has
  // reached already, so a cell two instances name is examined once and a cycle
  // among cells terminates, and the declarations whose own subinstances it has
  // still to look at.
  struct Descent {
    std::unordered_set<std::string_view> reached;
    std::vector<ModuleDecl*> pending;
  };

  // Carries a seeded descent through to the end of the hierarchy it roots,
  // then reports every name it reached that no loaded library holds a cell
  // for. Returns false if there was one.
  bool RunDescent(Descent& descent);

  // Descends from the named tops through the loaded cells, recording every
  // name the descent reaches that no loaded library holds a cell for. Reports
  // each such name and returns false if there was one.
  bool AllCellsPrecompiled(const std::vector<std::string_view>& top_names);

  // The same descent from the cells a configuration's design statement names,
  // each looked for in the library that statement put in front of it. A design
  // statement is the other thing a bind can be handed in place of the names of
  // the top-level cells, and it says which library each of them comes from as
  // well as what each is called -- so a cell of that name in another library
  // heads a hierarchy this design does not have and is not what gets walked.
  bool DesignCellsPrecompiled(const ConfigDecl* cfg);

  // Looks at what `decl` instantiates, wherever the instance sits -- among its
  // items or inside a generate alternative. A cell `decl` declares itself is
  // already accounted for by `decl`'s own compiled form; of the rest, each one
  // not reached before is either queued for the descent to continue through or
  // recorded as one no loaded library holds.
  void ReachSubinstances(const ModuleDecl* decl, Descent& descent);

  SourceManager& mgr_;
  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit unit_;
  std::vector<std::string> not_precompiled_;
};

}  // namespace delta
