#pragma once

#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

// §7.8: the set of user-defined type names an unpacked dimension may name as a
// user-defined associative index — the typedef table and the set of class
// names that together form the type-name resolution context.
struct TypeNameContext {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

// §23.2.2.1: bundle of name-table state that a net/variable declaration checks
// against (and updates) for redeclaration and partial-port reconciliation.
struct DeclNameTables {
  const std::unordered_set<std::string_view>& ansi_port_names;
  const std::unordered_set<std::string_view>& non_ansi_complete_ports;
  const std::unordered_map<std::string_view, uint32_t>& non_ansi_partial_ports;
  std::unordered_set<std::string_view>& declared_names;
  // §27.4: the declaration's generate-prefixed name, used as the redeclaration
  // key so distinct loop-iteration instances do not collide. Equals the bare
  // name for an unprefixed top-level declaration.
  std::string_view scoped_name;
};

// §23.2.2.1: the declared type whose vector width is reconciled against an
// earlier partial port declaration — the data type paired with the typedef
// table needed to evaluate its width.
struct DeclTypeRef {
  const DataType& dtype;
  const TypedefMap& typedefs;
};

// §7.4.2/§7.8: everything one unpacked dimension is resolved against — the
// type-name context a user-defined associative index is looked up in, the
// constant scope its bounds are folded in, and where a bound that does not
// fold is reported.
struct UnpackedDimContext {
  const TypeNameContext& types;
  const ScopeMap& scope;
  DiagEngine& diag;
  SourceLoc loc;
};

void ComputeUnpackedDims(const std::vector<Expr*>& dims, RtlirVariable& var,
                         const UnpackedDimContext& ctx);
void InferDynArraySize(const std::vector<Expr*>& dims, const Expr* init,
                       RtlirVariable& var);

void CheckDeclRedeclaration(const ModuleItem* item,
                            const DeclTypeRef& decl_type, DeclNameTables tables,
                            std::string_view kind_word, DiagEngine& diag);

}  // namespace delta
