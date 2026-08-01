#pragma once

#include <filesystem>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_scratch_dir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

// Puts every element of `from` at the end of `into`.
template <typename T>
void AppendAll(std::vector<T>& into, const std::vector<T>& from) {
  into.insert(into.end(), from.begin(), from.end());
}

// One compilation unit assembled out of several source files, the way a tool
// handed several files assembles one.
//
// §33.3 gives a library map the say over which library holds a source file and
// §33.4 has a configuration's clauses resolve against those libraries, so a
// test about either writes its map and its files to disk and reads the outcome
// back off the elaborated design. Each file is parsed on its own and the cells
// it describes are tagged with the library its path maps to, which is what
// makes the library named in an expectation one a map established rather than
// one the test wrote onto a cell.
struct LibraryDesign {
  SourceManager sources;
  Arena arena;
  DiagEngine diag{sources};
  LibraryMap map;
  CompilationUnit* unit = nullptr;

  // Parses `text` as the file at `path`, tags what it declares through the
  // loaded map, and folds it into the assembled unit. Returns false when the
  // file does not parse or parsing raised a diagnostic.
  bool AddFile(const std::filesystem::path& path, const std::string& text);

  // The same for a file the test has yet to write: `text` goes into `tmp`
  // under `name` first.
  bool Add(ScratchDir& tmp, const std::string& name, const std::string& text);

  // The configuration `name` names, or nullptr when the unit holds none of
  // that name.
  const ConfigDecl* ConfigNamed(std::string_view name) const;
};

inline bool LibraryDesign::AddFile(const std::filesystem::path& path,
                                   const std::string& text) {
  auto file = path.string();
  auto fid = sources.AddFile(file, text);
  Lexer lexer(sources.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  auto* parsed = parser.Parse();
  if (parsed == nullptr || diag.HasErrors()) return false;
  map.TagCompilationUnit(*parsed, file);
  if (unit == nullptr) {
    unit = parsed;
    return true;
  }
  // Every kind of design element a library holds as a cell is carried over,
  // together with the configurations: a configuration parsed out of one file
  // has to reach the cells parsed out of the others for a clause naming one to
  // find anything.
  AppendAll(unit->modules, parsed->modules);
  AppendAll(unit->interfaces, parsed->interfaces);
  AppendAll(unit->programs, parsed->programs);
  AppendAll(unit->checkers, parsed->checkers);
  AppendAll(unit->udps, parsed->udps);
  AppendAll(unit->packages, parsed->packages);
  AppendAll(unit->configs, parsed->configs);
  return true;
}

inline bool LibraryDesign::Add(ScratchDir& tmp, const std::string& name,
                               const std::string& text) {
  return AddFile(tmp.Write(name, text), text);
}

inline const ConfigDecl* LibraryDesign::ConfigNamed(
    std::string_view name) const {
  if (unit == nullptr) return nullptr;
  for (const auto* cfg : unit->configs) {
    if (cfg->name == name) return cfg;
  }
  return nullptr;
}

// Writes a map holding the topping file in rtlLib and `base`.vg in gateLib,
// then parses both of the files it covers. A test putting the only description
// of the cell under test in the gate-level file states its libraries this way:
// a binding that lands there is one a configuration's clause reached, since no
// default list the test writes carries gateLib. Returns false when the map does
// not load or a file does not parse.
inline bool BuildTwoLibraryDesign(ScratchDir& tmp, LibraryDesign& design,
                                  const std::string& base,
                                  const std::string& text,
                                  const std::string& top) {
  std::string map_text = "library rtlLib top.v;\n";
  map_text += "library gateLib " + base + ".vg;\n";
  if (!design.map.LoadMapFile(tmp.Write("lib.map", map_text))) return false;
  if (!design.Add(tmp, base + ".vg", text)) return false;
  return design.Add(tmp, "top.v", top);
}

// Elaborates `cfg` with the search order the loaded map yields already
// installed on the elaborator. Installing that order is what leaves a
// configuration's clauses something to override: without it a test could not
// tell a clause being obeyed from a map order that happened to agree.
inline RtlirDesign* ElaborateConfig(LibraryDesign& design,
                                    const ConfigDecl* cfg) {
  if (cfg == nullptr) return nullptr;
  Elaborator elab(design.arena, design.diag, design.unit);
  elab.SetLibraryDeclarationOrder(design.map.ResolveSearchOrder({}));
  return elab.Elaborate(cfg);
}

// Parses `config_text` into the assembled unit and elaborates the first
// configuration it declares.
//
// The configuration's own file matches no file path specification a test's map
// writes, so no library the map declares holds the configuration and it cannot
// itself be what supplies a cell.
inline RtlirDesign* ElaborateConfigText(ScratchDir& tmp, LibraryDesign& design,
                                        const std::string& config_text) {
  if (!design.Add(tmp, "cfg.sv", config_text)) return nullptr;
  if (design.unit->configs.empty()) return nullptr;
  return ElaborateConfig(design, design.unit->configs.front());
}

// The same for a file declaring more than one configuration, where which of
// them is elaborated is part of what the test states.
inline RtlirDesign* ElaborateNamedConfig(ScratchDir& tmp, LibraryDesign& design,
                                         const std::string& config_text,
                                         std::string_view name) {
  if (!design.Add(tmp, "cfg.sv", config_text)) return nullptr;
  return ElaborateConfig(design, design.ConfigNamed(name));
}

// The one top module an elaborated design holds, or nullptr when it holds none
// or holds several.
inline RtlirModule* OnlyTop(RtlirDesign* design) {
  if (design == nullptr) return nullptr;
  if (design->top_modules.size() != 1u) return nullptr;
  return design->top_modules.front();
}

// The cell bound to the instance `inst` names under `parent`, or nullptr when
// `parent` holds no such instance or that instance bound nothing.
inline RtlirModule* ChildBoundTo(RtlirModule* parent, std::string_view inst) {
  for (const auto& child : parent->children) {
    if (child.inst_name == inst) return child.resolved;
  }
  return nullptr;
}

// The cell bound at `path` -- instance names separated by dots, counted down
// from the design's one top module -- or nullptr when a step of the path names
// no instance or the instance it names bound nothing.
inline RtlirModule* CellAt(RtlirDesign* design, std::string_view path) {
  auto* mod = OnlyTop(design);
  while (mod != nullptr && !path.empty()) {
    auto dot = path.find('.');
    mod = ChildBoundTo(mod, path.substr(0, dot));
    if (dot == std::string_view::npos) break;
    path.remove_prefix(dot + 1);
  }
  return mod;
}

// The libraries the instances `insts` names bound out of, in the order given.
// An empty string stands for an instance that bound nothing.
inline std::vector<std::string> LibrariesBound(
    RtlirModule* top, std::initializer_list<std::string_view> insts) {
  std::vector<std::string> libraries;
  for (std::string_view inst : insts) {
    auto* bound = ChildBoundTo(top, inst);
    libraries.emplace_back(bound == nullptr ? "" : bound->library);
  }
  return libraries;
}

// The libraries the instances `leaves` names bound out of beneath each of
// `parents`, parent by parent. Reading them all at once is what a claim about
// every cell of a name, rather than about one instance of one, comes to. Empty
// when a parent instance bound nothing, since the leaves beneath a cell that
// was never bound are not bindings a test can read.
inline std::vector<std::string> LibrariesBoundBeneath(
    RtlirModule* top, std::initializer_list<std::string_view> parents,
    std::initializer_list<std::string_view> leaves) {
  std::vector<std::string> libraries;
  for (std::string_view parent_inst : parents) {
    auto* parent = ChildBoundTo(top, parent_inst);
    if (parent == nullptr) return {};
    for (std::string_view leaf : leaves) {
      auto* bound = ChildBoundTo(parent, leaf);
      libraries.emplace_back(bound == nullptr ? "" : bound->library);
    }
  }
  return libraries;
}

// Whether `decls` holds a declaration named `name` that lives in `library`.
// Every kind of design element carries both, so one walk serves them all.
template <typename Decls>
bool AnyDeclNamed(const Decls& decls, std::string_view name,
                  std::string_view library) {
  for (const auto* decl : decls) {
    if (decl->name != name) continue;
    if (decl->library == library) return true;
  }
  return false;
}

// Whether the assembled unit holds a cell named `name` in `library`, over
// every kind of design element a library holds as a cell. A test claiming a
// rule moved a binding off some description first states that the design held
// that description, so a design that never held it cannot pass for one whose
// description was overridden.
inline bool DesignHoldsCell(const CompilationUnit* unit, std::string_view name,
                            std::string_view library) {
  return AnyDeclNamed(unit->modules, name, library) ||
         AnyDeclNamed(unit->interfaces, name, library) ||
         AnyDeclNamed(unit->programs, name, library) ||
         AnyDeclNamed(unit->checkers, name, library) ||
         AnyDeclNamed(unit->udps, name, library);
}
