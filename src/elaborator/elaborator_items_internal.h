#pragma once

#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

struct RtlirModule;

// State threaded into RegisterImportedEnumLiterals: the compilation unit (to
// find imported packages), the arena and enum-member name set used to emit
// backing variables, and the typedef map used to size each enum.
struct ImportedEnumCtx {
  const CompilationUnit* unit;
  Arena& arena;
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& enum_member_names;
};

// §6.19/§26.6: a wildcard package import makes the package's enumeration
// literals visible by their unqualified names. Emit a backing variable per such
// literal into `mod` (the same representation used for a locally declared enum)
// so a bare reference like `COLOR_GREEN` resolves to its value. Covers both
// header and body wildcard imports. Defined in elaborator_typedef.cpp.
void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx);

// Maps a net data-type kind to its RTLIR net type, defaulting to kWire for any
// kind that is not a net type. Defined once in elaborator_decls.cpp and shared
// by the translation units that lower net declarations and validate operations.
NetType DataTypeToNetType(DataTypeKind kind);

// Shared file-local helper for the elaborator_items translation units: a name
// is "declared" in a module if it matches any variable, net, or port already
// recorded on the module. Defined once in elaborator_items.cpp; used there and
// by the module-instantiation/port-binding and generate translation units.
bool IsNameDeclared(std::string_view name, const RtlirModule* mod);

// §6.20.5: specify parameters declared inside a specify block are named
// constants of the enclosing module, exactly like specparams in the main module
// body. Registers each ordinary specparam of the given specify-block item as a
// module constant (recorded as a 32-bit variable carrying its value
// expression), and notes its name in the specparam and constant name sets so it
// resolves and rejects illegal assignment like a body specparam. PATHPULSE$
// entries are path-pulse limits rather than named constants and are skipped. A
// specify block cannot appear in a generate scope, so the bare name is used.
// Defined in elaborator_validate_specify.cpp.
void RegisterSpecifyBlockSpecparams(
    const ModuleItem* item, RtlirModule* mod,
    std::unordered_set<std::string_view>& specparam_names,
    std::unordered_set<std::string_view>& const_names);

}  // namespace delta
