#include "elaborator/covergroup_rules.h"

#include <algorithm>
#include <array>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using VarTypes = std::unordered_map<std::string_view, DataTypeKind>;

// The binary operators whose result is real when either operand is (§11.3.1):
// the arithmetic ones a real operand admits.
constexpr std::array<TokenKind, 5> kRealArithmetic = {
    TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar, TokenKind::kSlash,
    TokenKind::kPower};

// §19.7: the instance options that can be set only in the covergroup
// definition, and those that can be set only in the covergroup or coverpoint
// definition. Every other instance option may be assigned procedurally after
// the covergroup is instantiated.
constexpr std::array<std::string_view, 2> kCovergroupDefinitionOnly = {
    "per_instance", "get_inst_coverage"};
constexpr std::array<std::string_view, 3> kCoverpointDefinitionOnly = {
    "auto_bin_max", "detect_overlap", "cross_retain_auto_bins"};

// §19.7.1: the type options that can be set only in the covergroup definition.
// Every other type option may be assigned procedurally at any time.
constexpr std::array<std::string_view, 2> kTypeDefinitionOnly = {
    "strobe", "real_interval"};

template <typename Names>
bool Contains(const Names& names, auto value) {
  return std::find(names.begin(), names.end(), value) != names.end();
}

// §19.5: the names a covergroup's coverpoints go by, each one's label or,
// unlabelled, the variable its expression names.
std::unordered_set<std::string_view> CoverpointNames(const CovergroupDecl& cg) {
  std::unordered_set<std::string_view> names;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind != CoverageSpecKind::kCoverPoint) continue;
    const CoverPointDecl& cp = *item.cover_point;
    if (!cp.label.empty()) {
      names.insert(cp.label);
    } else if (cp.expr != nullptr && cp.expr->kind == ExprKind::kIdentifier) {
      names.insert(cp.expr->text);
    }
  }
  return names;
}

// The names a covergroup body reads: its own coverpoints; its formals, which
// shadow the names of the scope it is declared in; and then those names.
class CovergroupScope {
 public:
  CovergroupScope(const CovergroupDecl& cg, const CovergroupTypeOf& type_of)
      : cg_(cg), type_of_(type_of), coverpoints_(CoverpointNames(cg)) {}

  std::string_view Name() const { return cg_.name; }

  bool IsCoverpoint(std::string_view name) const {
    return coverpoints_.count(name) != 0;
  }

  std::optional<DataTypeKind> TypeOf(std::string_view name) const {
    for (const FunctionArg& formal : cg_.formals) {
      if (formal.name == name) return formal.data_type.kind;
    }
    return type_of_(name);
  }

  // Whether `e` is a real expression: a real literal, a name of a real type,
  // or real arithmetic on one.
  bool IsReal(const Expr* e) const {
    if (e->kind == ExprKind::kRealLiteral) return true;
    if (e->kind == ExprKind::kIdentifier) {
      auto type = TypeOf(e->text);
      return type.has_value() && IsRealType(*type);
    }
    return e->kind == ExprKind::kBinary && Contains(kRealArithmetic, e->op) &&
           (IsReal(e->lhs) || IsReal(e->rhs));
  }

 private:
  const CovergroupDecl& cg_;
  const CovergroupTypeOf& type_of_;
  std::unordered_set<std::string_view> coverpoints_;
};

// §19.5: a coverpoint whose explicit data type is real, or which has none and
// whose expression is real, is a coverpoint of a real expression.
bool IsRealCoverpoint(const CoverPointDecl& cp, const CovergroupScope& scope) {
  if (cp.has_data_type) return IsRealType(cp.data_type.kind);
  return cp.expr != nullptr && scope.IsReal(cp.expr);
}

// §19.5, §19.5.1, §19.5.1.1: the rules the bins of a real coverpoint obey.
void CheckRealCoverpoint(const CoverPointDecl& cp, DiagEngine& diag) {
  bool has_bins = false;
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) continue;
    has_bins = has_bins || bins.keyword == BinsKeyword::kBins;
    if (bins.kind == BinsOrOptionsKind::kDefault && bins.is_array) {
      diag.Error(bins.loc,
                 "a default bin of a real coverpoint shall not be an array of "
                 "bins",
                 Subclause("19.5.1"));
    }
    if (bins.with_expr != nullptr ||
        bins.kind == BinsOrOptionsKind::kCoverPointWith) {
      diag.Error(bins.loc,
                 "a bin of a real coverpoint takes no 'with' expression",
                 Subclause("19.5.1.1"));
    }
  }
  if (!has_bins) {
    diag.Error(cp.loc,
               "a coverpoint of a real expression has no automatic bins; it "
               "shall declare at least one 'bins'",
               Subclause("19.5"));
  }
}

// §19.6: each cross item is a coverpoint of the covergroup or a variable, and a
// variable crossed directly is integral.
void CheckCrossItems(const CoverCrossDecl& cross, const CovergroupScope& scope,
                     const CovergroupDeclared& declared, DiagEngine& diag) {
  for (const CrossItem& item : cross.items) {
    if (scope.IsCoverpoint(item.name)) continue;
    if (auto type = scope.TypeOf(item.name)) {
      if (IsRealType(*type)) {
        diag.Error(item.loc,
                   std::format("cross item '{}' is a real variable; a cross "
                               "shall not include a real variable directly",
                               item.name),
                   Subclause("19.6"));
      }
      continue;
    }
    if (declared(item.name)) continue;
    diag.Error(item.loc,
               std::format("cross item '{}' is neither a coverpoint of "
                           "covergroup '{}' nor a variable",
                           item.name, scope.Name()),
               Subclause("19.6"));
  }
}

// The member a procedural write sets where its target is `<v>.option.<member>`
// or `<v>.<item>.option.<member>` with `<v>` a variable of a covergroup type;
// empty for any other target.
std::string_view CovergroupOptionWritten(
    const Expr* target,
    const std::unordered_set<std::string_view>& covergroup_vars) {
  if (target == nullptr || target->kind != ExprKind::kMemberAccess) return {};
  const Expr* option = target->lhs;
  if (option->kind != ExprKind::kMemberAccess || option->rhs->text != "option")
    return {};
  const Expr* root = option->lhs;
  if (root->kind == ExprKind::kMemberAccess) root = root->lhs;
  if (root->kind != ExprKind::kIdentifier ||
      covergroup_vars.count(root->text) == 0) {
    return {};
  }
  return target->rhs->text;
}

// §19.7: reports each procedural write in `s` to an option the definition
// alone may set.
void CheckOptionWrites(
    const Stmt* s, const std::unordered_set<std::string_view>& covergroup_vars,
    DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    std::string_view member = CovergroupOptionWritten(s->lhs, covergroup_vars);
    if (Contains(kCovergroupDefinitionOnly, member)) {
      diag.Error(s->range.start,
                 std::format("option '{}' can be set only in the covergroup "
                             "definition",
                             member),
                 Subclause("19.7"));
    } else if (Contains(kCoverpointDefinitionOnly, member)) {
      diag.Error(s->range.start,
                 std::format("option '{}' can be set only in the covergroup "
                             "or coverpoint definition",
                             member),
                 Subclause("19.7"));
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckOptionWrites(sub, covergroup_vars, diag);
  });
}

// §19.8 and §19.7.1: the covergroup type the selection `access` is made
// through, `cg` in `cg::m` or `cg::x::m`, where `visible` names it a covergroup
// type; empty for any other expression.
std::string_view CovergroupTypeScoped(const Expr* access,
                                      const CovergroupTypeVisible& visible) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      !access->is_scope_resolution || access->lhs == nullptr) {
    return {};
  }
  const Expr* scope = access->lhs;
  if (scope->kind == ExprKind::kMemberAccess && scope->is_scope_resolution) {
    scope = scope->lhs;
  }
  if (scope->kind != ExprKind::kIdentifier || !visible(scope->text)) return {};
  return scope->text;
}

// §19.8: the covergroup type the call `call` is made through, `cg` in
// `cg::m()` or `cg::x::m()`, where `visible` names it a covergroup type; empty
// for any other call.
std::string_view CovergroupTypeCalled(const Expr* call,
                                      const CovergroupTypeVisible& visible) {
  if (call->kind != ExprKind::kCall) return {};
  return CovergroupTypeScoped(call->lhs, visible);
}

// §19.7.1: the type option a procedural write sets where its target is
// `cg::type_option.<member>` or `cg::x::type_option.<member>` with `cg` a
// covergroup type `visible` names; empty for any other target.
std::string_view CovergroupTypeOptionWritten(
    const Expr* target, const CovergroupTypeVisible& visible) {
  if (target == nullptr || target->kind != ExprKind::kMemberAccess ||
      target->lhs == nullptr) {
    return {};
  }
  const Expr* access = target->lhs;
  if (access->rhs == nullptr || access->rhs->text != "type_option" ||
      CovergroupTypeScoped(access, visible).empty()) {
    return {};
  }
  return target->rhs->text;
}

// §19.7.1: reports `s` where it is a procedural write through a covergroup
// type to a type option the definition alone may set.
void CheckTypeOptionWrite(const Stmt* s, const CovergroupTypeVisible& visible,
                          DiagEngine& diag) {
  if (s->kind != StmtKind::kBlockingAssign &&
      s->kind != StmtKind::kNonblockingAssign) {
    return;
  }
  std::string_view member = CovergroupTypeOptionWritten(s->lhs, visible);
  if (!Contains(kTypeDefinitionOnly, member)) return;
  diag.Error(s->range.start,
             std::format("type option '{}' can be set only in the covergroup "
                         "definition",
                         member),
             Subclause("19.7.1"));
}

// §19.8: reports each call in `e` made through a covergroup type to a method
// other than get_coverage(), the one static covergroup method.
void CheckTypeCallsIn(const Expr* e, const CovergroupTypeVisible& visible,
                      DiagEngine& diag) {
  if (e == nullptr) return;
  std::string_view type = CovergroupTypeCalled(e, visible);
  if (!type.empty() && e->lhs->rhs->text != "get_coverage") {
    diag.Error(e->range.start,
               std::format("method '{}' cannot be called through the "
                           "covergroup type '{}'; only get_coverage() can",
                           e->lhs->rhs->text, type),
               Subclause("19.8"));
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckTypeCallsIn(child, visible, diag); });
}

// §19.8 and §19.7.1: CheckTypeCallsIn over every expression of `s`, and
// CheckTypeOptionWrite over `s`, and both over the statements it holds.
void CheckTypeCalls(const Stmt* s, const CovergroupTypeVisible& visible,
                    DiagEngine& diag) {
  if (s == nullptr) return;
  CheckTypeOptionWrite(s, visible, diag);
  ForEachChildExpr(s,
                   [&](const Expr* e) { CheckTypeCallsIn(e, visible, diag); });
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CheckTypeCalls(sub, visible, diag); });
}

// The module's variables declared with one of its covergroups as their type.
std::unordered_set<std::string_view> CovergroupVariables(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> covergroups;
  std::unordered_set<std::string_view> vars;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) {
      covergroups.insert(item->name);
    } else if (item->kind == ModuleItemKind::kVarDecl &&
               covergroups.count(item->data_type.type_name) != 0) {
      vars.insert(item->name);
    }
  }
  return vars;
}

// §19.4.1: the coverpoints a derived covergroup `cg` of `cls` inherits, those
// of the covergroups of its name the classes `cls` extends embed; none for a
// covergroup that extends none.
std::unordered_set<std::string_view> InheritedCoverpoints(
    const ClassDecl* cls, const CovergroupDecl& cg,
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> names;
  if (cg.extends_base.empty()) return names;
  for (const ClassDecl* base = FindClassDecl(cls->base_class, unit);
       base != nullptr; base = FindClassDecl(base->base_class, unit)) {
    for (const ClassMember* m : base->members) {
      if (m->kind != ClassMemberKind::kCovergroup || m->name != cg.name)
        continue;
      names.merge(CoverpointNames(*m->covergroup));
    }
  }
  return names;
}

}  // namespace

void ValidateCovergroup(const CovergroupDecl& cg,
                        const CovergroupTypeOf& type_of,
                        const CovergroupDeclared& declared, DiagEngine& diag) {
  CovergroupScope scope(cg, type_of);
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      if (IsRealCoverpoint(*item.cover_point, scope)) {
        CheckRealCoverpoint(*item.cover_point, diag);
      }
    } else if (item.kind == CoverageSpecKind::kCoverCross) {
      CheckCrossItems(*item.cover_cross, scope, declared, diag);
    }
  }
}

void ValidateModuleCovergroups(const ModuleDecl* decl,
                               const VarTypes& var_types,
                               const CovergroupDeclared& declared,
                               DiagEngine& diag) {
  CovergroupTypeOf type_of =
      [&](std::string_view name) -> std::optional<DataTypeKind> {
    auto it = var_types.find(name);
    if (it == var_types.end()) return std::nullopt;
    return it->second;
  };
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kCovergroupDecl) continue;
    ValidateCovergroup(*item->covergroup, type_of, declared, diag);
  }
  std::unordered_set<std::string_view> covergroup_vars =
      CovergroupVariables(decl);
  ForEachBodyOwningItem(decl->items, [&](const auto* body_item) {
    CheckOptionWrites(body_item->body, covergroup_vars, diag);
    for (const Stmt* s : body_item->func_body_stmts) {
      CheckOptionWrites(s, covergroup_vars, diag);
    }
  });
}

void ValidateCovergroupTypeCalls(const ModuleDecl* decl,
                                 const CovergroupTypeVisible& visible,
                                 DiagEngine& diag) {
  ForEachBodyOwningItem(decl->items, [&](const auto* body_item) {
    CheckTypeCalls(body_item->body, visible, diag);
    for (const Stmt* s : body_item->func_body_stmts) {
      CheckTypeCalls(s, visible, diag);
    }
  });
}

void ValidateEmbeddedCovergroups(const ClassDecl* cls,
                                 const std::vector<ModuleItem*>& scope_items,
                                 const CompilationUnit* unit,
                                 DiagEngine& diag) {
  CovergroupTypeOf type_of =
      [&](std::string_view name) -> std::optional<DataTypeKind> {
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return m->data_type.kind;
    }
    for (const ModuleItem* item : scope_items) {
      if (item->name == name) return item->data_type.kind;
    }
    return std::nullopt;
  };
  for (const ClassMember* m : cls->members) {
    if (m->kind != ClassMemberKind::kCovergroup) continue;
    // §19.4.1: a derived covergroup refers to the components of its base, so
    // a cross of it names the base's coverpoints as its own.
    std::unordered_set<std::string_view> inherited =
        InheritedCoverpoints(cls, *m->covergroup, unit);
    CovergroupDeclared declared = [&](std::string_view name) {
      return inherited.contains(name) || type_of(name).has_value();
    };
    ValidateCovergroup(*m->covergroup, type_of, declared, diag);
  }
}

}  // namespace delta
