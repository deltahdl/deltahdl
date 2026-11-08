#include "elaborator/string_numeric_assign.h"

#include <array>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using VarTypes = std::unordered_map<std::string_view, DataTypeKind>;

struct VarTables {
  const VarTypes& kinds;
  const std::unordered_set<std::string_view>& arrays;
};

enum class ValueSide : uint8_t { kUnknown, kString, kNumeric };

constexpr std::array<std::string_view, 3> kStringResultMethods = {
    "substr", "toupper", "tolower"};

}  // namespace

static ValueSide SideOfKind(DataTypeKind kind) {
  if (kind == DataTypeKind::kString) return ValueSide::kString;
  if (IsIntegralType(kind) || IsRealType(kind)) return ValueSide::kNumeric;
  return ValueSide::kUnknown;
}

static ValueSide SideOfVar(std::string_view name, const VarTables& vars) {
  auto it = vars.kinds.find(name);
  return it == vars.kinds.end() ? ValueSide::kUnknown : SideOfKind(it->second);
}

static bool IsStringResultMethodCall(const Expr* call, const VarTables& vars) {
  if (call->lhs == nullptr || call->lhs->kind != ExprKind::kMemberAccess ||
      SideOfVar(ExprIdent(call->lhs->lhs), vars) != ValueSide::kString) {
    return false;
  }
  for (std::string_view method : kStringResultMethods) {
    if (call->lhs->rhs->text == method) return true;
  }
  return false;
}

static ValueSide SideOf(const Expr* e, const VarTables& vars);

static ValueSide SideOfSelect(const Expr* select, const VarTables& vars) {
  std::string_view array = ExprIdent(select->base);
  if (vars.arrays.count(array) != 0) return SideOfVar(array, vars);
  return SideOf(select->base, vars) == ValueSide::kUnknown
             ? ValueSide::kUnknown
             : ValueSide::kNumeric;
}

static ValueSide SideOf(const Expr* e, const VarTables& vars) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
      return ValueSide::kNumeric;
    case ExprKind::kIdentifier:
      return SideOfVar(e->text, vars);
    case ExprKind::kSelect:
      return SideOfSelect(e, vars);
    case ExprKind::kBinary:
      return SideOf(e->lhs, vars) == ValueSide::kNumeric ||
                     SideOf(e->rhs, vars) == ValueSide::kNumeric
                 ? ValueSide::kNumeric
                 : ValueSide::kUnknown;
    case ExprKind::kCall:
      return IsStringResultMethodCall(e, vars) ? ValueSide::kString
                                               : ValueSide::kUnknown;
    default:
      return ValueSide::kUnknown;
  }
}

static void CheckWrite(ValueSide target, const Expr* value, SourceLoc loc,
                       const VarTables& vars, DiagEngine& diag) {
  if (value == nullptr || target == ValueSide::kUnknown) return;
  ValueSide side = SideOf(value, vars);
  if (side == ValueSide::kUnknown || side == target) return;
  diag.Error(loc,
             "type-incompatible assignment between string and numeric type",
             Subclause("6.16"));
}

static void CheckStmt(const Stmt* s, const VarTables& vars, DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckWrite(SideOf(s->lhs, vars), s->rhs, s->range.start, vars, diag);
  } else if (s->kind == StmtKind::kVarDecl) {
    CheckWrite(SideOfKind(s->var_decl_type.kind), s->var_init, s->range.start,
               vars, diag);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) { CheckStmt(sub, vars, diag); });
}

void CheckStringNumericAssignments(
    const std::vector<ModuleItem*>& items, const VarTypes& var_types,
    const std::unordered_set<std::string_view>& arrays, DiagEngine& diag) {
  const VarTables kVars{var_types, arrays};
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl) {
      CheckWrite(SideOfKind(item->data_type.kind), item->init_expr, item->loc,
                 kVars, diag);
    }
    CheckStmt(item->body, kVars, diag);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, kVars, diag);
  }
}

}  // namespace delta
