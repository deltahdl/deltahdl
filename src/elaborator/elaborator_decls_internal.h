#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

void RecordVarSelectShape(
    const ModuleItem* item, const TypedefMap& typedefs,
    std::unordered_map<std::string_view, VarSelectShape>& shapes);

bool DeclaresScalar(const DataType& dtype, const TypedefMap& typedefs);

struct TypeNameContext {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

struct DeclNameTables {
  const std::unordered_set<std::string_view>& ansi_port_names;
  const std::unordered_set<std::string_view>& non_ansi_complete_ports;
  const std::unordered_map<std::string_view, uint32_t>& non_ansi_partial_ports;
  std::unordered_set<std::string_view>& declared_names;
  std::string_view scoped_name;
  bool redeclares_net_or_variable;
};

struct DeclTypeRef {
  const DataType& dtype;
  const TypedefMap& typedefs;
};

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

void ElaborateUnpackedDims(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims,
    const UnpackedDimContext& ctx, RtlirVariable& var);

void SetPackedTypedefTypeInfo(const ModuleItem* item, RtlirVariable& var,
                              const TypedefMap& typedefs, Arena& arena);

void CheckDeclRedeclaration(const ModuleItem* item,
                            const DeclTypeRef& decl_type, DeclNameTables tables,
                            std::string_view kind_word, DiagEngine& diag);

}  // namespace delta
