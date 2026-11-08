#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

std::optional<int64_t> FoldRealValueAsInteger(const Expr* expr,
                                              const ScopeMap& scope);

bool HasRealOperand(const Expr* expr);

struct InstanceParamAssignments {
  const Elaborator::ParamList& params;
  ScopeMap scope;
  const RtlirModule* module;
};

const Elaborator::ParamOverride* FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name);

DataType TypeParamOverrideToDataType(const Expr* expr,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag, SourceLoc loc);

bool ApplyParamOverride(RtlirParamDecl& pd,
                        const InstanceParamAssignments& assigns,
                        std::string_view pname, const DataType* dtype,
                        Arena& arena);

class BodyParamAssignmentsGuard {
 public:
  explicit BodyParamAssignmentsGuard(const InstanceParamAssignments* assigns);
  ~BodyParamAssignmentsGuard();
  BodyParamAssignmentsGuard(const BodyParamAssignmentsGuard&) = delete;
  BodyParamAssignmentsGuard& operator=(const BodyParamAssignmentsGuard&) =
      delete;

 private:
  const InstanceParamAssignments* prev_;
};

const InstanceParamAssignments* BodyParamAssignments();

std::vector<std::string_view> OverridableParamNames(const ModuleDecl* decl);

void PushInstParamAssignment(const ModuleDecl* child_decl,
                             std::string_view pname, const Expr* pexpr,
                             const ScopeMap& parent_scope,
                             Elaborator::ParamList& child_params);

std::vector<std::pair<std::string_view, Expr*>> AssignableConfigParams(
    const ModuleDecl* child_decl,
    const std::vector<std::pair<std::string_view, Expr*>>& override_params,
    SourceLoc loc, DiagEngine& diag);

void FoldParamUnpackedBounds(RtlirParamDecl& pd, const ScopeMap& scope);

void RecordTypeParamActual(RtlirParamDecl& pd,
                           const std::vector<RtlirParamDecl>& earlier,
                           const TypedefMap& typedefs, Arena& arena);

}  // namespace delta
