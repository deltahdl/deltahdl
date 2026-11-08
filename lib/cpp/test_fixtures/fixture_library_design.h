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
#include "fixture_diagnosed.h"
#include "fixture_scratch_dir.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

template <typename T>
void AppendAll(std::vector<T>& into, const std::vector<T>& from) {
  into.insert(into.end(), from.begin(), from.end());
}

struct LibraryDesign {
  SourceManager sources;
  Arena arena;
  DiagEngine diag{sources};
  Diagnosed diagnosed{diag};
  LibraryMap map;
  CompilationUnit* unit = nullptr;

  bool AddFile(const std::filesystem::path& path, const std::string& text);

  bool Add(ScratchDir& tmp, const std::string& name, const std::string& text);

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

inline RtlirDesign* ElaborateConfig(LibraryDesign& design,
                                    const ConfigDecl* cfg) {
  if (cfg == nullptr) return nullptr;
  Elaborator elab(design.arena, design.diag, design.unit);
  elab.SetLibraryDeclarationOrder(design.map.ResolveSearchOrder({}));
  return elab.Elaborate(cfg);
}

inline RtlirDesign* ElaborateConfigText(ScratchDir& tmp, LibraryDesign& design,
                                        const std::string& config_text) {
  if (!design.Add(tmp, "cfg.sv", config_text)) return nullptr;
  if (design.unit->configs.empty()) return nullptr;
  return ElaborateConfig(design, design.unit->configs.front());
}

inline RtlirDesign* ElaborateNamedConfig(ScratchDir& tmp, LibraryDesign& design,
                                         const std::string& config_text,
                                         std::string_view name) {
  if (!design.Add(tmp, "cfg.sv", config_text)) return nullptr;
  return ElaborateConfig(design, design.ConfigNamed(name));
}

inline RtlirModule* OnlyTop(RtlirDesign* design) {
  if (design == nullptr) return nullptr;
  if (design->top_modules.size() != 1u) return nullptr;
  return design->top_modules.front();
}

inline RtlirModule* ChildBoundTo(RtlirModule* parent, std::string_view inst) {
  for (const auto& child : parent->children) {
    if (child.inst_name == inst) return child.resolved;
  }
  return nullptr;
}

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

inline std::vector<std::string> LibrariesBound(
    RtlirModule* top, std::initializer_list<std::string_view> insts) {
  std::vector<std::string> libraries;
  for (std::string_view inst : insts) {
    auto* bound = ChildBoundTo(top, inst);
    libraries.emplace_back(bound == nullptr ? "" : bound->library);
  }
  return libraries;
}

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

template <typename Decls>
bool AnyDeclNamed(const Decls& decls, std::string_view name,
                  std::string_view library) {
  for (const auto* decl : decls) {
    if (decl->name != name) continue;
    if (decl->library == library) return true;
  }
  return false;
}

inline bool DesignHoldsCell(const CompilationUnit* unit, std::string_view name,
                            std::string_view library) {
  return AnyDeclNamed(unit->modules, name, library) ||
         AnyDeclNamed(unit->interfaces, name, library) ||
         AnyDeclNamed(unit->programs, name, library) ||
         AnyDeclNamed(unit->checkers, name, library) ||
         AnyDeclNamed(unit->udps, name, library);
}
