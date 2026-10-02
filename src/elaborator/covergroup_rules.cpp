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
#include "elaborator/coverpoint_bin_set_expression.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
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

// §7.8: the index types an associative array's dimension names by keyword,
// with `*` for a wildcard index (§7.8.1); a typedef or a class names any other.
constexpr std::array<std::string_view, 11> kIndexTypeKeywords = {
    "*",       "string", "int",   "integer", "byte", "shortint",
    "longint", "bit",    "logic", "reg",     "time"};

template <typename Names>
bool Contains(const Names& names, auto value) {
  return std::find(names.begin(), names.end(), value) != names.end();
}

// §7.4.2, §7.5, §7.8, §7.10: the kind of array the unpacked dimensions `dims`
// declare, from the first: `[]` dynamic, `[$]` a queue, an index type or `*`
// associative, and a size or range fixed; `is_type` answers whether a name is
// a type. Nothing where there is no unpacked dimension.
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

using OwnNames = std::unordered_map<std::string_view, SetExpressionNameOrigin>;

// §19.5.1.2: adds to `names` the label of `cp` and the names of its bins.
void AddCoverpointOwnNames(const CoverPointDecl& cp, OwnNames& names) {
  if (!cp.label.empty()) {
    names.emplace(cp.label, SetExpressionNameOrigin::kCoverpointIdentifier);
  }
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) continue;
    names.emplace(bins.name, SetExpressionNameOrigin::kBinIdentifier);
  }
}

// §19.5.1.2: the names declared within `cg` that a set_covergroup_expression
// cannot see, each with what it names: its coverpoints' labels, and the names
// of the bins of its coverpoints and crosses.
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

// The formal of `cg` named `name`, or null where it has none.
const FunctionArg* FindFormal(const CovergroupDecl& cg, std::string_view name) {
  for (const FunctionArg& formal : cg.formals) {
    if (formal.name == name) return &formal;
  }
  return nullptr;
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

  // The formal of the covergroup named `name`, or null where it has none.
  const FunctionArg* Formal(std::string_view name) const {
    return FindFormal(cg_, name);
  }

  std::optional<DataTypeKind> TypeOf(std::string_view name) const {
    if (const FunctionArg* formal = Formal(name)) return formal->data_type.kind;
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

// §19.5, §19.5.1, §19.5.1.1, §19.5.2: the rules the bins of a real coverpoint
// obey.
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
    if (bins.kind == BinsOrOptionsKind::kTransitions) {
      diag.Error(bins.loc,
                 "a coverpoint of a real expression takes no transition bin",
                 Subclause("19.5.2"));
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

// What a set_covergroup_expression of a covergroup reads (§19.5.1.2): the
// covergroup's scope, the names declared within it, whether a name is visible
// where it is declared, and the kind of array a name denotes there.
struct SetExpressionScope {
  const CovergroupScope& scope;
  OwnNames own_names;
  const CovergroupDeclared& declared;
  const CovergroupArrays& arrays;
};

// §19.5.1.2: a name `e` reads in a set_covergroup_expression that only a
// coverpoint or a bin of the covergroup declares is not visible there; a
// formal of the covergroup, or a name declared where it is, is read instead.
SetExpressionNameOrigin SetExpressionNameOf(const Expr* e,
                                            const SetExpressionScope& s) {
  auto it = s.own_names.find(e->text);
  if (it == s.own_names.end() || s.scope.Formal(e->text) != nullptr ||
      s.declared(e->text)) {
    return SetExpressionNameOrigin::kExternal;
  }
  return it->second;
}

// The kind of array `name`, read in a set_covergroup_expression, denotes: from
// the unpacked dimensions of the covergroup's formal of that name, or else of
// the declaration where the covergroup is declared.
std::optional<SetExpressionArrayKind> ArrayKindRead(
    std::string_view name, const SetExpressionScope& s) {
  if (const FunctionArg* formal = s.scope.Formal(name)) {
    return ArrayKindOf(formal->unpacked_dims, s.arrays.is_type);
  }
  return s.arrays.kind_of(name);
}

// The kinds whose assignment compatibility (§6.22.3) the kind alone settles:
// the built-in integral types but an enum, the real types and string. A named
// type is left to the rules of its declaration.
bool IsBuiltinValueKind(DataTypeKind kind) {
  return (IsIntegralType(kind) && kind != DataTypeKind::kEnum) ||
         IsRealType(kind) || kind == DataTypeKind::kString;
}

// §19.5.1.2: whether elements of kind `element` may define the bins of a
// coverpoint of kind `coverpoint`; true wherever either kind is not a
// built-in one.
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

// The kind of the type of coverpoint `cp`: the one its data type declares or
// else that of the variable it covers; nothing for any other expression.
std::optional<DataTypeKind> CoverpointKind(const CoverPointDecl& cp,
                                           const CovergroupScope& scope) {
  if (cp.has_data_type) return cp.data_type.kind;
  if (cp.expr != nullptr && cp.expr->kind == ExprKind::kIdentifier) {
    return scope.TypeOf(cp.expr->text);
  }
  return std::nullopt;
}

// §19.5.1.2: the rules the array `name` obeys where a
// set_covergroup_expression names it to define the bins of a coverpoint of
// kind `coverpoint`: it is no associative array, and its elements are
// assignment compatible with the coverpoint's type.
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

// §19.5.1.2: the rules the set_covergroup_expression of the bin `bins` of a
// coverpoint of kind `coverpoint` obeys: the array it names obeys
// CheckSetExpressionArray, and every name it reads is visible to it.
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

// §19.5.1.2: CheckSetExpression over each bin of `cp` a
// set_covergroup_expression defines.
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

// The names the set_covergroup_expressions of the bins of `cp` read, added to
// `reads`.
void CollectSetExpressionReads(const CoverPointDecl& cp,
                               std::vector<const Expr*>& reads) {
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kSetExpression) {
      CollectBareIdents(bins.set_expr, reads);
    }
  }
}

// §23.9 with §19.5.1.2: a set_covergroup_expression of a covergroup `cg` a
// module declares reads the names `declared` answers for, and one that is
// none of them, no formal of `cg` and no name of its own, which
// CheckSetExpression reports, resolves to nothing.
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
        FindFormal(cg, read->text) != nullptr || declared(read->text)) {
      continue;
    }
    diag.Error(
        read->range.start,
        std::format("reference to unresolved identifier '{}'", read->text),
        Subclause("23.9"));
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

// Whether one of `items` declares `name` a type: a typedef or a class.
bool ItemsDeclareType(const std::vector<ModuleItem*>& items,
                      std::string_view name) {
  return std::ranges::any_of(items, [&](const ModuleItem* item) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      return item->class_decl != nullptr && item->class_decl->name == name;
    }
    return item->kind == ModuleItemKind::kTypedef && item->name == name;
  });
}

// The kind of array the variable `name` is declared as among `items`, where
// `is_type` answers whether a name is a type; nothing where none of `items`
// declares it.
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

// The names a covergroup embedded in `cls` reads (§19.4): the class's members
// and those of the classes it extends, then `scope_items`, the declarations of
// the scope the class is declared in.
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

  // Whether `name` is a type there: a typedef or a class.
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
};

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
                        const CovergroupDeclared& declared,
                        const CovergroupArrays& arrays, DiagEngine& diag) {
  CovergroupScope scope(cg, type_of);
  SetExpressionScope set_scope{scope, CovergroupOwnNames(cg), declared, arrays};
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      if (IsRealCoverpoint(*item.cover_point, scope)) {
        CheckRealCoverpoint(*item.cover_point, diag);
      }
      CheckSetExpressions(*item.cover_point, set_scope, diag);
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
  CovergroupDeclared is_type = [&](std::string_view name) {
    return ItemsDeclareType(decl->items, name);
  };
  CovergroupArrays arrays{[&](std::string_view name) {
                            return ItemsArrayKind(decl->items, name, is_type);
                          },
                          is_type};
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kCovergroupDecl) continue;
    ValidateCovergroup(*item->covergroup, type_of, declared, arrays, diag);
    ReportUnresolvedSetExpressionReads(*item->covergroup, declared, diag);
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
                                 const CovergroupDeclared& unit_declared,
                                 DiagEngine& diag) {
  ClassCovergroupScope scope{cls, scope_items, unit};
  CovergroupTypeOf type_of = [&](std::string_view name) {
    return scope.TypeOf(name);
  };
  CovergroupArrays arrays{
      [&](std::string_view name) { return scope.ArrayKind(name); },
      [&](std::string_view name) { return scope.DeclaresType(name); }};
  for (const ClassMember* m : cls->members) {
    if (m->kind != ClassMemberKind::kCovergroup) continue;
    // §19.4.1: a derived covergroup refers to the components of its base, so
    // a cross of it names the base's coverpoints as its own.
    std::unordered_set<std::string_view> inherited =
        InheritedCoverpoints(cls, *m->covergroup, unit);
    CovergroupDeclared declared = [&](std::string_view name) {
      return inherited.contains(name) || type_of(name).has_value();
    };
    ValidateCovergroup(*m->covergroup, type_of, declared, arrays, diag);
    ReportUnresolvedSetExpressionReads(*m->covergroup, unit_declared, diag);
  }
}

}  // namespace delta
