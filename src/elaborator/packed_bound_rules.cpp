#include "elaborator/packed_bound_rules.h"

#include <algorithm>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using BoundPair = std::pair<const Expr*, const Expr*>;

void CollectBoundPairs(const DataType& dtype, std::vector<BoundPair>& pairs) {
  pairs.emplace_back(dtype.packed_dim_left, dtype.packed_dim_right);
  for (const auto& [left, right] : dtype.extra_packed_dims) {
    pairs.emplace_back(left, right);
  }
  for (const StructMember& member : dtype.struct_members) {
    pairs.emplace_back(member.packed_dim_left, member.packed_dim_right);
    for (const auto& [left, right] : member.extra_packed_dims) {
      pairs.emplace_back(left, right);
    }
    if (member.nested_type != nullptr) {
      CollectBoundPairs(*member.nested_type, pairs);
    }
  }
}

bool BoundReadsVariable(const Expr* e, const PackedBoundNames& names) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return names.names_variable(e);
  if (e->kind == ExprKind::kMemberAccess) {
    return e->is_scope_resolution && names.names_variable(e);
  }
  if (e->kind == ExprKind::kSystemCall && IsConstantWhateverItsArguments(e)) {
    return false;
  }
  auto reads = [&](const Expr* child) {
    return BoundReadsVariable(child, names);
  };
  if (e->kind == ExprKind::kAssignmentPattern) {
    return std::ranges::any_of(e->elements, reads);
  }
  return AnyExprChild(e, reads);
}

bool CallsNonConstantSystemFunction(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kSystemCall && !IsConstantSysFunc(e->callee)) {
    return true;
  }
  return AnyExprChild(e, [](const Expr* child) {
    return CallsNonConstantSystemFunction(child);
  });
}

bool BoundIsNoConstantInteger(const Expr* bound,
                              const PackedBoundNames& names) {
  if (bound->kind == ExprKind::kIntegerLiteral) return false;
  return BoundReadsVariable(bound, names) ||
         CallsNonConstantSystemFunction(bound) ||
         names.calls_non_constant_function(bound) ||
         IsRealValued(bound, names.real_params);
}

bool DeclaresVariable(const ModuleItem& item) {
  return (item.kind == ModuleItemKind::kVarDecl ||
          item.kind == ModuleItemKind::kNetDecl) &&
         !item.data_type.is_const && !item.is_genvar;
}

bool DeclaresRealParam(const ModuleItem& item) {
  if (item.kind != ModuleItemKind::kParamDecl) return false;
  if (IsRealType(item.data_type.kind)) return true;
  return item.data_type.kind == DataTypeKind::kImplicit &&
         item.init_expr != nullptr && IsRealValued(item.init_expr, {});
}

}  // namespace

bool NamesPackageVariable(const Expr* e, const CompilationUnit* unit) {
  if (unit == nullptr || e->lhs == nullptr || e->rhs == nullptr ||
      e->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  for (const PackageDecl* pkg : unit->packages) {
    if (pkg->name != e->lhs->text) continue;
    return std::ranges::any_of(pkg->items, [&](const ModuleItem* item) {
      return item->name == e->rhs->text && DeclaresVariable(*item);
    });
  }
  return false;
}

void ReportPackedBounds(const DataType& dtype, SourceLoc loc,
                        const PackedBoundNames& names, DiagEngine& diag) {
  std::vector<BoundPair> pairs;
  CollectBoundPairs(dtype, pairs);
  bool has_xz = false;
  bool non_constant = false;
  for (const auto& [left, right] : pairs) {
    for (const Expr* bound : {left, right}) {
      if (bound == nullptr) continue;
      has_xz = has_xz || ExprContainsXZ(bound);
      non_constant = non_constant || BoundIsNoConstantInteger(bound, names);
    }
  }
  if (has_xz) {
    diag.ErrorOnce(loc, "packed dimension range shall not contain x or z",
                   Subclause("7.4.1"));
  }
  if (non_constant) {
    diag.ErrorOnce(loc,
                   "packed dimension range shall be a constant integer "
                   "expression",
                   Subclause("7.4.1"));
  }
}

void ReportPackedBoundsOfItem(const ModuleItem& item, bool with_declarations,
                              const PackedBoundNames& names, DiagEngine& diag) {
  if (with_declarations && (item.kind == ModuleItemKind::kVarDecl ||
                            item.kind == ModuleItemKind::kNetDecl)) {
    ReportPackedBounds(item.data_type, item.loc, names, diag);
  }
  if (item.kind == ModuleItemKind::kTypedef) {
    ReportPackedBounds(item.typedef_type, item.loc, names, diag);
  }
  if (item.kind == ModuleItemKind::kFunctionDecl) {
    ReportPackedBounds(item.return_type, item.loc, names, diag);
  }
  ForEachProceduralStmt(&item, [&](const Stmt* s) {
    if (s->kind == StmtKind::kVarDecl) {
      ReportPackedBounds(s->var_decl_type, s->range.start, names, diag);
    }
  });
}

void ReportPackedBoundsInScope(const std::vector<ModuleItem*>& items,
                               const CompilationUnit* unit, DiagEngine& diag) {
  std::unordered_set<std::string_view> variables;
  RealParamKinds real_params;
  for (const ModuleItem* item : items) {
    if (DeclaresVariable(*item)) variables.insert(item->name);
    if (DeclaresRealParam(*item)) {
      real_params[item->name] = DataTypeKind::kReal;
    }
  }
  const PackedBoundNames kNames{[&](const Expr* e) {
                                  if (e->kind == ExprKind::kIdentifier) {
                                    return variables.contains(e->text);
                                  }
                                  return NamesPackageVariable(e, unit);
                                },
                                [](const Expr*) { return false; }, real_params};
  for (const ModuleItem* item : items) {
    ReportPackedBoundsOfItem(*item, true, kNames, diag);
  }
}

void ReportPackedBoundsInClass(const ClassDecl& cls,
                               const CompilationUnit* unit, DiagEngine& diag) {
  std::unordered_set<std::string_view> properties;
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kProperty && !member->is_param &&
        !member->data_type.is_const) {
      properties.insert(member->name);
    }
  }
  const RealParamKinds kNoRealParams;
  const PackedBoundNames kNames{[&](const Expr* e) {
                                  if (e->kind == ExprKind::kIdentifier) {
                                    return properties.contains(e->text);
                                  }
                                  return NamesPackageVariable(e, unit);
                                },
                                [](const Expr*) { return false; },
                                kNoRealParams};
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kProperty && !member->is_param) {
      ReportPackedBounds(member->data_type, member->loc, kNames, diag);
    }
    if (member->method != nullptr) {
      ReportPackedBoundsOfItem(*member->method, false, kNames, diag);
    }
    if (member->typedef_item != nullptr) {
      ReportPackedBoundsOfItem(*member->typedef_item, false, kNames, diag);
    }
  }
}

}  // namespace delta
