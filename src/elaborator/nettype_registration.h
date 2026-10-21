#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "elaborator/type_eval.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct ModuleItem;

// What a nettype declaration leaves behind, keyed by the name the nettype is
// reached by: the set of nettype names, the resolution function each nettype
// resolves its drivers through (§6.6.7), and the nettype each one matches under
// §6.22.6, its canonical nettype.
struct NettypeTables {
  std::unordered_set<std::string_view>& names;
  std::unordered_map<std::string_view, std::string_view>& resolve_funcs;
  std::unordered_map<std::string_view, std::string_view>& canonical;
};

// Records the resolution function and canonical nettype of the nettype `item`
// declares, under `key`, which `tables.names` already holds. `home` is the
// package declaring the nettype, or empty for one a module or the compilation
// unit declares. A with clause naming its function with no scope names one
// `home` declares.
//
// §6.6.7 gives two forms. A nettype declared over a data type, a typedef name
// included, is a nettype of its own, which §6.22.6 matches to no other. One
// whose named source is itself a nettype renames that nettype: it resolves
// through the source's function and matches the source.
void RegisterNettype(const ModuleItem& item, std::string_view key,
                     std::string_view home, const NettypeTables& tables,
                     Arena& arena);

// Enters the nettype recorded under `from` under `to` as well, with its data
// type in `typedefs`, its resolution function and its canonical nettype, so
// that the two names are one nettype, which §6.22.6 matches to itself. An
// import gives a package's nettype its bare name this way (§26.3), and
// `$unit ::` reaches a compilation-unit nettype (§3.12.1). Nothing is entered
// when no nettype is recorded under `from`.
void CopyNettype(std::string_view from, std::string_view to,
                 TypedefMap& typedefs, const NettypeTables& tables);

// Records each nettype a package declares under "P::nt" in `tables`, and its
// data type under the same key in `typedefs`. §26.3 reaches a package's
// declaration by that name whether or not the package is imported, and
// RegisterPackageTypedefs records a package's typedefs the same way.
void RegisterPackageNettypes(const CompilationUnit* unit, TypedefMap& typedefs,
                             const NettypeTables& tables, Arena& arena);

}  // namespace delta
