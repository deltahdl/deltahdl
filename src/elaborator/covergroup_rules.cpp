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
#include "elaborator/coverage_option_rules.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/covergroup_expression_rules.h"
#include "elaborator/covergroup_instance_rules.h"
#include "elaborator/coverpoint_bin_set_expression.h"
#include "elaborator/coverpoint_rules.h"
#include "elaborator/cross_bin_rules.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/embedded_covergroup_rules.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "elaborator/value_kind.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr std::array<TokenKind, 5> kRealArithmetic = {
    TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar, TokenKind::kSlash,
    TokenKind::kPower};

constexpr std::array<std::string_view, 2> kCovergroupDefinitionOnly = {
    "per_instance", "get_inst_coverage"};
constexpr std::array<std::string_view, 3> kCoverpointDefinitionOnly = {
    "auto_bin_max", "detect_overlap", "cross_retain_auto_bins"};

constexpr std::array<std::string_view, 2> kTypeDefinitionOnly = {
    "strobe", "real_interval"};

constexpr std::array<std::string_view, 11> kIndexTypeKeywords = {
    "*",       "string", "int",   "integer", "byte", "shortint",
    "longint", "bit",    "logic", "reg",     "time"};

template <typename Names>
bool Contains(const Names& names, auto value) {
  return std::find(names.begin(), names.end(), value) != names.end();
}

std::optional<SetExpressionArrayKind> ArrayKindOf(
    const std::vector<Expr*>& dims, const CovergroupDeclared& is_type) {
  if (dims.empty()) return std::nullopt;
  const Expr* dim = dims.front();
  if (dim == nullptr) return SetExpressionArrayKind::kDynamic;
  if (IsQueueDim(dim)) return SetExpressionArrayKind::kQueue;
  if (dim->kind == ExprKind::kIdentifier &&
      (Contains(kIndexTypeKeywords, dim->text) || is_type(dim->text))) {
    return SetExpressionArrayKind::kAssociative;
  }
  return SetExpressionArrayKind::kFixedSize;
}

std::unordered_set<std::string_view> CoverpointNames(const CovergroupDecl& cg) {
  std::unordered_set<std::string_view> names;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind != CoverageSpecKind::kCoverPoint) continue;
    std::string_view name = CoverpointName(*item.cover_point);
    if (!name.empty()) names.insert(name);
  }
  return names;
}

using OwnNames = std::unordered_map<std::string_view, SetExpressionNameOrigin>;

void AddCoverpointOwnNames(const CoverPointDecl& cp, OwnNames& names) {
  if (!cp.label.empty()) {
    names.emplace(cp.label, SetExpressionNameOrigin::kCoverpointIdentifier);
  }
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) continue;
    names.emplace(bins.name, SetExpressionNameOrigin::kBinIdentifier);
  }
}

OwnNames CovergroupOwnNames(const CovergroupDecl& cg) {
  OwnNames names;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      AddCoverpointOwnNames(*item.cover_point, names);
      continue;
    }
    if (item.kind != CoverageSpecKind::kCoverCross) continue;
    for (const CrossBodyItem& body : item.cover_cross->body) {
      if (body.kind != CrossBodyItemKind::kBinsSelection) continue;
      names.emplace(body.bins.name, SetExpressionNameOrigin::kBinIdentifier);
    }
  }
  return names;
}

class CovergroupScope {
 public:
  CovergroupScope(const CovergroupDecl& cg, const CovergroupTypeOf& type_of)
      : cg_(cg), type_of_(type_of), coverpoints_(CoverpointNames(cg)) {}

  std::string_view Name() const { return cg_.name; }

  bool IsCoverpoint(std::string_view name) const {
    return coverpoints_.count(name) != 0;
  }

  const FunctionArg* Formal(std::string_view name) const {
    return FindCovergroupFormal(cg_, name);
  }

  std::optional<DataTypeKind> TypeOf(std::string_view name) const {
    if (const FunctionArg* formal = Formal(name)) return formal->data_type.kind;
    return type_of_(name);
  }

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

bool IsRealCoverpoint(const CoverPointDecl& cp, const CovergroupScope& scope) {
  if (cp.has_data_type) return IsRealType(cp.data_type.kind);
  return scope.IsReal(cp.expr);
}

void CheckRealBin(const BinsOrOptions& bins, DiagEngine& diag) {
  if (bins.kind == BinsOrOptionsKind::kDefault && bins.is_array) {
    diag.Error(bins.loc,
               "a real coverpoint's default bin is a single bin and cannot "
               "be declared as an array",
               Subclause("19.5.1"));
  }
  if (bins.with_expr != nullptr) {
    diag.Error(bins.loc,
               "a bin of a real coverpoint takes no 'with' expression",
               Subclause("19.5.1.1"));
  }
  if (bins.kind == BinsOrOptionsKind::kTransitions) {
    diag.Error(bins.loc,
               "a coverpoint of a real expression takes no transition bin",
               Subclause("19.5.2"));
  }
  if (bins.wildcard) {
    diag.Error(bins.loc, "a bin of a real coverpoint cannot be 'wildcard'",
               Subclause("19.5.4"));
  }
}

void CheckRealCoverpoint(const CoverPointDecl& cp, DiagEngine& diag) {
  bool has_bins = false;
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) continue;
    has_bins = has_bins || bins.keyword == BinsKeyword::kBins;
    CheckRealBin(bins, diag);
  }
  if (!has_bins) {
    diag.Error(cp.loc,
               "nothing creates bins for a coverpoint of a real expression, so "
               "declare at least one 'bins' for it",
               Subclause("19.5"));
  }
}

void CheckCrossItems(const CoverCrossDecl& cross, const CovergroupScope& scope,
                     const CovergroupDeclared& declared, DiagEngine& diag) {
  for (const CrossItem& item : cross.items) {
    if (scope.IsCoverpoint(item.name)) continue;
    if (auto type = scope.TypeOf(item.name)) {
      if (IsRealType(*type)) {
        diag.Error(item.loc,
                   std::format("cross item '{}' is a real variable, which a "
                               "cross can reach only through a coverpoint",
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

struct SetExpressionScope {
  const CovergroupScope& scope;
  OwnNames own_names;
  const CovergroupDeclared& declared;
  const CovergroupArrays& arrays;
};

SetExpressionNameOrigin SetExpressionNameOf(const Expr* e,
                                            const SetExpressionScope& s) {
  auto it = s.own_names.find(e->text);
  if (it == s.own_names.end() || s.scope.Formal(e->text) != nullptr ||
      s.declared(e->text)) {
    return SetExpressionNameOrigin::kExternal;
  }
  return it->second;
}

std::optional<SetExpressionArrayKind> ArrayKindRead(
    std::string_view name, const SetExpressionScope& s) {
  if (const FunctionArg* formal = s.scope.Formal(name)) {
    return ArrayKindOf(formal->unpacked_dims, s.arrays.is_type);
  }
  return s.arrays.kind_of(name);
}

bool IsBuiltinValueKind(DataTypeKind kind) {
  return (IsIntegralType(kind) && kind != DataTypeKind::kEnum) ||
         IsRealType(kind) || kind == DataTypeKind::kString;
}

bool ElementsAssignable(DataTypeKind coverpoint, DataTypeKind element) {
  if (!IsBuiltinValueKind(coverpoint) || !IsBuiltinValueKind(element)) {
    return true;
  }
  DataType coverpoint_type;
  coverpoint_type.kind = coverpoint;
  DataType element_type;
  element_type.kind = element;
  return SetExpressionElementTypeAllowed(coverpoint_type, element_type);
}

std::optional<DataTypeKind> CoverpointKind(const CoverPointDecl& cp,
                                           const CovergroupScope& scope) {
  if (cp.has_data_type) return cp.data_type.kind;
  if (cp.expr->kind == ExprKind::kIdentifier) {
    return scope.TypeOf(cp.expr->text);
  }
  return std::nullopt;
}

void CheckSetExpressionArray(const Expr* name,
                             std::optional<DataTypeKind> coverpoint,
                             const SetExpressionScope& s, DiagEngine& diag) {
  std::optional<SetExpressionArrayKind> kind = ArrayKindRead(name->text, s);
  if (!kind.has_value()) return;
  if (!SetExpressionArrayKindAllowed(*kind)) {
    diag.Error(name->range.start,
               std::format("the associative array '{}' cannot define the "
                           "bins of a set_covergroup_expression",
                           name->text),
               Subclause("19.5.1.2"));
  }
  std::optional<DataTypeKind> element = s.scope.TypeOf(name->text);
  if (coverpoint.has_value() && element.has_value() &&
      !ElementsAssignable(*coverpoint, *element)) {
    diag.Error(name->range.start,
               std::format("the elements of '{}' are not assignment "
                           "compatible with the coverpoint's type",
                           name->text),
               Subclause("19.5.1.2"));
  }
}

void CheckSetExpression(const BinsOrOptions& bins,
                        std::optional<DataTypeKind> coverpoint,
                        const SetExpressionScope& s, DiagEngine& diag) {
  const Expr* e = bins.set_expr;
  if (e->kind == ExprKind::kIdentifier) {
    CheckSetExpressionArray(e, coverpoint, s, diag);
  }
  std::vector<const Expr*> reads;
  CollectBareIdents(e, reads);
  for (const Expr* read : reads) {
    if (SetExpressionNameVisible(SetExpressionNameOf(read, s))) continue;
    diag.Error(read->range.start,
               std::format("'{}' is declared within covergroup '{}' and is not "
                           "visible in a set_covergroup_expression",
                           read->text, s.scope.Name()),
               Subclause("19.5.1.2"));
  }
}

void CheckSetExpressions(const CoverPointDecl& cp, const SetExpressionScope& s,
                         DiagEngine& diag) {
  std::optional<DataTypeKind> coverpoint = CoverpointKind(cp, s.scope);
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kSetExpression &&
        bins.set_expr != nullptr) {
      CheckSetExpression(bins, coverpoint, s, diag);
    }
  }
}

void CollectSetExpressionReads(const CoverPointDecl& cp,
                               std::vector<const Expr*>& reads) {
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kSetExpression) {
      CollectBareIdents(bins.set_expr, reads);
    }
  }
}

void ReportUnresolvedSetExpressionReads(const CovergroupDecl& cg,
                                        const CovergroupDeclared& declared,
                                        DiagEngine& diag) {
  std::vector<const Expr*> reads;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      CollectSetExpressionReads(*item.cover_point, reads);
    }
  }
  OwnNames own_names = CovergroupOwnNames(cg);
  for (const Expr* read : reads) {
    if (own_names.contains(read->text) ||
        FindCovergroupFormal(cg, read->text) != nullptr ||
        declared(read->text)) {
      continue;
    }
    diag.Error(
        read->range.start,
        std::format("reference to unresolved identifier '{}'", read->text),
        Subclause("23.9"));
  }
}

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
    } else if (!member.empty() && !IsCovergroupOptionMember(member, false)) {
      diag.Error(s->range.start,
                 std::format("option has no member '{}'", member),
                 Subclause("19.10"));
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckOptionWrites(sub, covergroup_vars, diag);
  });
}

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

std::string_view CovergroupTypeCalled(const Expr* call,
                                      const CovergroupTypeVisible& visible) {
  if (call->kind != ExprKind::kCall) return {};
  return CovergroupTypeScoped(call->lhs, visible);
}

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

void CheckTypeOptionWrite(const Stmt* s, const CovergroupTypeVisible& visible,
                          DiagEngine& diag) {
  if (s->kind != StmtKind::kBlockingAssign &&
      s->kind != StmtKind::kNonblockingAssign) {
    return;
  }
  std::string_view member = CovergroupTypeOptionWritten(s->lhs, visible);
  if (member.empty()) return;
  if (!IsCovergroupOptionMember(member, true)) {
    diag.Error(s->range.start,
               std::format("type_option has no member '{}'", member),
               Subclause("19.10"));
    return;
  }
  if (!Contains(kTypeDefinitionOnly, member)) return;
  diag.Error(s->range.start,
             std::format("type option '{}' can be set only in the covergroup "
                         "definition",
                         member),
             Subclause("19.7.1"));
}

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

void CheckTypeCalls(const Stmt* s, const CovergroupTypeVisible& visible,
                    DiagEngine& diag) {
  if (s == nullptr) return;
  CheckTypeOptionWrite(s, visible, diag);
  ForEachChildExpr(s,
                   [&](const Expr* e) { CheckTypeCallsIn(e, visible, diag); });
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CheckTypeCalls(sub, visible, diag); });
}

bool ItemsDeclareType(const std::vector<ModuleItem*>& items,
                      std::string_view name) {
  return std::ranges::any_of(items, [&](const ModuleItem* item) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      return item->class_decl != nullptr && item->class_decl->name == name;
    }
    return item->kind == ModuleItemKind::kTypedef && item->name == name;
  });
}

std::optional<SetExpressionArrayKind> ItemsArrayKind(
    const std::vector<ModuleItem*>& items, std::string_view name,
    const CovergroupDeclared& is_type) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == name) {
      return ArrayKindOf(item->unpacked_dims, is_type);
    }
  }
  return std::nullopt;
}

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

const ModuleItem* ItemNamed(const std::vector<ModuleItem*>& items,
                            std::string_view name, ModuleItemKind kind) {
  for (const ModuleItem* item : items) {
    if (item->kind == kind && item->name == name) return item;
  }
  return nullptr;
}

struct ClassCovergroupScope {
  const ClassDecl* cls;
  const std::vector<ModuleItem*>& scope_items;
  const CompilationUnit* unit;

  std::optional<DataTypeKind> TypeOf(std::string_view name) const {
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return m->data_type.kind;
    }
    for (const ModuleItem* item : scope_items) {
      if (item->name == name) return item->data_type.kind;
    }
    return std::nullopt;
  }

  bool DeclaresType(std::string_view name) const {
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return m->kind == ClassMemberKind::kTypedef ||
             m->kind == ClassMemberKind::kClassDecl;
    }
    return FindClassDecl(name, unit) != nullptr ||
           ItemsDeclareType(scope_items, name);
  }

  std::optional<SetExpressionArrayKind> ArrayKind(std::string_view name) const {
    CovergroupDeclared is_type = [this](std::string_view n) {
      return DeclaresType(n);
    };
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return ArrayKindOf(m->unpacked_dims, is_type);
    }
    return ItemsArrayKind(scope_items, name, is_type);
  }

  const DataType* VariableType(std::string_view name) const {
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return &m->data_type;
    }
    const ModuleItem* item =
        ItemNamed(scope_items, name, ModuleItemKind::kVarDecl);
    return item != nullptr ? &item->data_type : nullptr;
  }

  ValueKind ValueKindOf(const Expr* e) const {
    if (e->kind != ExprKind::kIdentifier) return ValueKind::kUnknown;
    const DataType* type = VariableType(e->text);
    if (type == nullptr) return ValueKind::kUnknown;
    return KindOfDeclaredType(*type, [this](std::string_view n) {
      return FindClassDecl(n, unit) != nullptr;
    });
  }

  bool NonConstant(std::string_view name) const {
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return !m->is_const && !m->is_param;
    }
    const ModuleItem* item =
        ItemNamed(scope_items, name, ModuleItemKind::kVarDecl);
    return item != nullptr && !item->data_type.is_const;
  }

  const ModuleItem* Function(std::string_view name) const {
    if (const ClassMember* m = FindMemberInClass(cls, name, unit)) {
      return m->method;
    }
    return ItemNamed(scope_items, name, ModuleItemKind::kFunctionDecl);
  }
};

std::unordered_set<std::string_view> InheritedCoverpoints(
    const ClassDecl* cls, const CovergroupDecl& cg,
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> names;
  if (cg.extends_base.empty()) return names;
  for (const ClassDecl* base = FindBaseClass(cls, unit); base != nullptr;
       base = FindBaseClass(base, unit)) {
    for (const ClassMember* m : base->members) {
      if (m->kind != ClassMemberKind::kCovergroup || m->name != cg.name)
        continue;
      names.merge(CoverpointNames(*m->covergroup));
    }
  }
  return names;
}

}  // namespace

const FunctionArg* FindCovergroupFormal(const CovergroupDecl& cg,
                                        std::string_view name) {
  for (const FunctionArg& formal : cg.formals) {
    if (formal.name == name) return &formal;
  }
  return nullptr;
}

ValueKind KindOfDeclaredType(const DataType& type,
                             const CovergroupDeclared& is_class) {
  if (type.kind == DataTypeKind::kNamed && is_class(type.type_name)) {
    return ValueKind::kOther;
  }
  return KindOfTypeKind(type.kind);
}

bool IsRefCovergroupFormal(const CovergroupDecl& cg, std::string_view name) {
  Direction dir = Direction::kInput;
  for (const FunctionArg& formal : cg.formals) {
    if (formal.direction != Direction::kNone) dir = formal.direction;
    if (formal.name == name) return dir == Direction::kRef;
  }
  return false;
}

std::string_view CoverpointName(const CoverPointDecl& cp) {
  if (!cp.label.empty()) return cp.label;
  return cp.expr->kind == ExprKind::kIdentifier ? cp.expr->text
                                                : std::string_view{};
}

void ValidateCovergroup(const CovergroupDecl& cg, const CovergroupContext& ctx,
                        DiagEngine& diag) {
  CovergroupScope scope(cg, ctx.type_of);
  SetExpressionScope set_scope{scope, CovergroupOwnNames(cg), ctx.declared,
                               ctx.arrays};
  CheckCovergroupExpressions(cg, ctx, diag);
  CheckCoverageOptions(cg, ctx, diag);
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      if (IsRealCoverpoint(*item.cover_point, scope)) {
        CheckRealCoverpoint(*item.cover_point, diag);
      }
      CheckCoverpointRules(*item.cover_point, cg, ctx, diag);
      CheckSetExpressions(*item.cover_point, set_scope, diag);
    } else if (item.kind == CoverageSpecKind::kCoverCross) {
      CheckCrossItems(*item.cover_cross, scope, ctx.declared, diag);
      CheckCrossBinRules(*item.cover_cross, cg, ctx, diag);
    }
  }
}

void ValidateModuleCovergroups(const ModuleDecl* decl,
                               const ModuleCovergroupTables& tables,
                               const CovergroupDeclared& declared,
                               DiagEngine& diag) {
  const ValueScope& values = tables.values;
  CovergroupTypeOf type_of =
      [&](std::string_view name) -> std::optional<DataTypeKind> {
    auto it = values.var_types.find(name);
    if (it == values.var_types.end()) return std::nullopt;
    return it->second;
  };
  CovergroupDeclared is_type = [&](std::string_view name) {
    return ItemsDeclareType(decl->items, name);
  };
  const CovergroupContext kCtx{
      type_of,
      declared,
      {[&](std::string_view name) {
         return ItemsArrayKind(decl->items, name, is_type);
       },
       is_type},
      [&](const Expr* e) { return KindOfValue(e, values); },
      [&](std::string_view name) {
        return values.var_types.contains(name) &&
               !tables.const_names.contains(name);
      },
      [&](std::string_view name) -> const ModuleItem* {
        auto it = values.functions.find(name);
        return it != values.functions.end() ? it->second : nullptr;
      },
      [&](std::string_view name) { return values.class_names.contains(name); }};
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kCovergroupDecl) continue;
    ValidateCovergroup(*item->covergroup, kCtx, diag);
    ReportUnresolvedSetExpressionReads(*item->covergroup, declared, diag);
  }
  CheckModuleCovergroupInstances(decl, diag);
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
                                 const CovergroupDeclared& unit_declared,
                                 DiagEngine& diag) {
  ClassCovergroupScope scope{cls, scope_items, unit};
  CovergroupTypeOf type_of = [&](std::string_view name) {
    return scope.TypeOf(name);
  };
  for (const ClassMember* m : cls->members) {
    if (m->kind != ClassMemberKind::kCovergroup) continue;
    std::unordered_set<std::string_view> inherited =
        InheritedCoverpoints(cls, *m->covergroup, unit);
    const CovergroupContext kCtx{
        type_of,
        [&](std::string_view name) {
          return inherited.contains(name) || type_of(name).has_value();
        },
        {[&](std::string_view name) { return scope.ArrayKind(name); },
         [&](std::string_view name) { return scope.DeclaresType(name); }},
        [&](const Expr* e) { return scope.ValueKindOf(e); },
        [&](std::string_view name) { return scope.NonConstant(name); },
        [&](std::string_view name) { return scope.Function(name); },
        [&](std::string_view name) {
          return FindClassDecl(name, unit) != nullptr;
        }};
    ValidateCovergroup(*m->covergroup, kCtx, diag);
    ReportUnresolvedSetExpressionReads(*m->covergroup, unit_declared, diag);
  }
  CheckEmbeddedCovergroupUses(cls, unit, diag);
}

}  // namespace delta
