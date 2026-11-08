#include "elaborator/library_cell_writes.h"

#include <cstdint>
#include <format>
#include <map>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_design.h"

namespace delta {

namespace {

using CellKey = std::pair<std::string_view, std::string_view>;

enum class CellList : std::uint8_t {
  kModules,
  kInterfaces,
  kPrograms,
  kPrimitives,
  kCheckers
};

struct WrittenCell {
  const void* decl;
  SourceLoc loc;
  CellList list;
};

struct CellWrites {
  std::map<CellKey, WrittenCell> held;
  std::map<CellKey, int> modules_given;
  std::unordered_set<const void*> overwritten;
};

bool EncounteredLater(const SourceLoc& a, const SourceLoc& b) {
  return std::tie(a.file_id, a.line, a.column) >
         std::tie(b.file_id, b.line, b.column);
}

void WarnIfModuleGivenAgain(const CellKey& key, SourceLoc loc,
                            CellWrites& writes, DiagEngine& diag) {
  int& given = writes.modules_given[key];
  ++given;
  if (given == 1) return;
  diag.Warning(loc,
               std::format("module '{}' is written to library '{}' more than "
                           "once in this invocation",
                           key.second, key.first),
               Subclause("33.3.1.1"));
}

template <typename Decl>
void WriteCells(const std::vector<Decl*>& decls, CellList list,
                CellWrites& writes, DiagEngine& diag) {
  for (const Decl* d : decls) {
    if (d->is_extern) continue;
    const CellKey kKey{d->library, d->name};
    const SourceLoc kLoc = d->range.start;
    if (list == CellList::kModules) {
      WarnIfModuleGivenAgain(kKey, kLoc, writes, diag);
    }
    auto [it, fresh] =
        writes.held.try_emplace(kKey, WrittenCell{d, kLoc, list});
    if (fresh) continue;
    WrittenCell& held = it->second;
    if (held.list == list || EncounteredLater(kLoc, held.loc)) {
      writes.overwritten.insert(held.decl);
      held = WrittenCell{d, kLoc, list};
    } else {
      writes.overwritten.insert(d);
    }
  }
}

template <typename Decl>
void DropOverwritten(std::vector<Decl*>& decls,
                     const std::unordered_set<const void*>& overwritten) {
  std::erase_if(
      decls, [&overwritten](const Decl* d) { return overwritten.contains(d); });
}

}  // namespace

void WriteCellsToLibraries(CompilationUnit& unit, DiagEngine& diag) {
  CellWrites writes;
  WriteCells(unit.modules, CellList::kModules, writes, diag);
  WriteCells(unit.interfaces, CellList::kInterfaces, writes, diag);
  WriteCells(unit.programs, CellList::kPrograms, writes, diag);
  WriteCells(unit.udps, CellList::kPrimitives, writes, diag);
  DropOverwritten(unit.modules, writes.overwritten);
  DropOverwritten(unit.interfaces, writes.overwritten);
  DropOverwritten(unit.programs, writes.overwritten);
  DropOverwritten(unit.udps, writes.overwritten);
  CellWrites checker_writes;
  WriteCells(unit.checkers, CellList::kCheckers, checker_writes, diag);
  DropOverwritten(unit.checkers, checker_writes.overwritten);
}

}  // namespace delta
