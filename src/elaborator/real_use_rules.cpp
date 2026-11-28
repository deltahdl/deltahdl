#include "elaborator/real_use_rules.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kMaxClassDepth = 64;
constexpr int kMaxTypedefDepth = 64;

constexpr auto kRealSystemFunctions = std::to_array<std::string_view>(
    {"$realtime",     "$itor", "$bitstoreal", "$bitstoshortreal",
     "$get_coverage", "$ln",   "$log10",      "$exp",
     "$sqrt",         "$pow",  "$floor",      "$ceil",
     "$sin",          "$cos",  "$tan",        "$asin",
     "$acos",         "$atan", "$atan2",      "$hypot",
     "$sinh",         "$cosh", "$tanh",       "$asinh",
     "$acosh",        "$atanh"});

constexpr auto kRealCastTypes =
    std::to_array<std::string_view>({"real", "shortreal", "realtime"});

constexpr auto kRealArithmeticOps =
    std::to_array({TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar,
                   TokenKind::kSlash, TokenKind::kPower});

using Frame = std::unordered_map<std::string_view, RealTyped>;

size_t TypedefDimsOnChain(const DataType& type, const RealUseScope& scope) {
  size_t dims = 0;
  std::string_view name = type.type_name;
  for (int depth = 0; !name.empty() && depth < kMaxTypedefDepth; ++depth) {
    auto written = scope.typedef_dims.find(name);
    if (written != scope.typedef_dims.end()) dims += written->second.size();
    auto next = scope.typedefs.find(name);
    if (next == scope.typedefs.end()) break;
    name = next->second.type_name;
  }
  return dims;
}

struct Walk {
  const RealUseScope& scope;
  Frame names;
  const ClassDecl* this_class = nullptr;
};

template <typename Decl>
const Decl* FindByName(const std::vector<Decl*>& decls, std::string_view name) {
  auto it = std::ranges::find_if(
      decls, [name](const Decl* decl) { return decl->name == name; });
  return it == decls.end() ? nullptr : *it;
}

const ClassDecl* FindClass(std::string_view name, const RealUseScope& scope) {
  const ClassDecl* local = FindByName(scope.classes, name);
  if (local != nullptr || scope.unit == nullptr) return local;
  return FindByName(scope.unit->classes, name);
}

const PackageDecl* FindPackage(std::string_view name,
                               const RealUseScope& scope) {
  return scope.unit == nullptr ? nullptr
                               : FindByName(scope.unit->packages, name);
}

const ModuleDecl* FindModuleDecl(std::string_view name,
                                 const RealUseScope& scope) {
  return scope.unit == nullptr ? nullptr
                               : FindByName(scope.unit->modules, name);
}

std::string_view ItemName(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kModuleInst ? item->inst_name
                                                   : item->name;
}

bool NamesValue(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kVarDecl ||
         item->kind == ModuleItemKind::kNetDecl ||
         item->kind == ModuleItemKind::kParamDecl ||
         item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kModuleInst;
}

RealTyped TypedOfItem(const ModuleItem* item, const RealUseScope& scope) {
  if (item->kind == ModuleItemKind::kFunctionDecl) {
    RealTyped typed = RealTypedOfDecl(item->return_type, 0, scope);
    typed.is_function = true;
    return typed;
  }
  if (item->kind == ModuleItemKind::kModuleInst) {
    RealTyped typed;
    typed.scope = FindModuleDecl(item->inst_module, scope);
    typed.found = typed.scope != nullptr;
    return typed;
  }
  RealTyped typed =
      RealTypedOfDecl(item->data_type, item->unpacked_dims.size(), scope);
  typed.is_param = item->kind == ModuleItemKind::kParamDecl;
  return typed;
}

RealTyped TypedIn(const std::vector<ModuleItem*>& items, std::string_view name,
                  const RealUseScope& scope) {
  for (const ModuleItem* item : items) {
    if (ItemName(item) != name || !NamesValue(item)) continue;
    RealTyped typed = TypedOfItem(item, scope);
    if (typed.found) return typed;
  }
  return {};
}

RealTyped ImportedTyped(const std::vector<ModuleItem*>& items,
                        std::string_view name, const RealUseScope& scope) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (!imp.is_wildcard && imp.item_name != name) continue;
    const PackageDecl* pkg = FindPackage(imp.package_name, scope);
    RealTyped typed =
        pkg == nullptr ? RealTyped{} : TypedIn(pkg->items, name, scope);
    if (typed.found) return typed;
  }
  return {};
}

RealTyped TypedOfProperty(const ClassDecl* cls, std::string_view name,
                          const RealUseScope& scope) {
  for (int depth = 0; cls != nullptr && depth < kMaxClassDepth; ++depth) {
    for (const ClassMember* m : cls->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name != name) continue;
      RealTyped typed =
          RealTypedOfDecl(m->data_type, m->unpacked_dims.size(), scope);
      typed.is_param = m->is_param;
      return typed;
    }
    cls = FindClass(cls->base_class, scope);
  }
  return {};
}

RealTyped TypedOfStructMember(const DataType& aggregate, std::string_view name,
                              const RealUseScope& scope) {
  auto it =
      std::ranges::find(aggregate.struct_members, name, &StructMember::name);
  if (it == aggregate.struct_members.end()) return {};
  RealTyped typed;
  typed.found = true;
  typed.kind = it->type_kind;
  typed.unpacked = it->unpacked_dims.size();
  if (it->type_kind == DataTypeKind::kNamed) {
    DataType written;
    written.type_name = it->type_name;
    typed.unpacked += TypedefDimsOnChain(written, scope);
  }
  const DataType* own = MemberOwnType(*it, scope.typedefs);
  if (own != nullptr) {
    typed.kind = own->kind;
    typed.aggregate = own;
  }
  return typed;
}

RealTyped TypedInScopeItems(std::string_view name, const RealUseScope& scope) {
  static const std::vector<ModuleItem*> kNoItems;
  const std::vector<ModuleItem*>& unit_items =
      scope.unit == nullptr ? kNoItems : scope.unit->cu_items;
  for (const std::vector<ModuleItem*>* items : {&scope.items, &unit_items}) {
    RealTyped typed = TypedIn(*items, name, scope);
    if (!typed.found) typed = ImportedTyped(*items, name, scope);
    if (typed.found) return typed;
  }
  RealTyped typed;
  typed.scope = FindModuleDecl(name, scope);
  typed.found = typed.scope != nullptr;
  return typed;
}

RealTyped TypedOfName(std::string_view name, const Walk& w) {
  auto local = w.names.find(name);
  if (local != w.names.end()) return local->second;
  if (w.this_class != nullptr) {
    RealTyped typed;
    typed.cls = w.this_class;
    typed.found = name == "this";
    if (!typed.found) typed = TypedOfProperty(w.this_class, name, w.scope);
    if (typed.found) return typed;
  }
  if (w.scope.outer) {
    RealTyped typed = w.scope.outer(name);
    if (typed.found) return typed;
  }
  return TypedInScopeItems(name, w.scope);
}

RealTyped TypedOf(const Expr* e, const Walk& w);

RealTyped TypedOfScopedMember(const Expr* e, const Walk& w) {
  std::string_view outer = ExprIdent(e->lhs);
  std::string_view name = e->rhs->text;
  const PackageDecl* pkg = FindPackage(outer, w.scope);
  if (pkg != nullptr) return TypedIn(pkg->items, name, w.scope);
  const ClassDecl* cls = FindClass(outer, w.scope);
  return cls == nullptr ? RealTyped{} : TypedOfProperty(cls, name, w.scope);
}

RealTyped TypedOfMember(const Expr* e, const Walk& w) {
  if (e->is_scope_resolution) return TypedOfScopedMember(e, w);
  const RealTyped kBase = TypedOf(e->lhs, w);
  std::string_view name = e->rhs->text;
  if (kBase.unpacked != 0) return {};
  if (kBase.scope != nullptr) return TypedIn(kBase.scope->items, name, w.scope);
  if (kBase.cls != nullptr) return TypedOfProperty(kBase.cls, name, w.scope);
  return kBase.aggregate == nullptr
             ? RealTyped{}
             : TypedOfStructMember(*kBase.aggregate, name, w.scope);
}

RealTyped TypedOfSelect(const Expr* e, const Walk& w) {
  RealTyped base = TypedOf(e->base, w);
  if (base.unpacked == 0) return {};
  if (e->index_end == nullptr) --base.unpacked;
  return base;
}

RealTyped TypedOfIdentifier(const Expr* e, const Walk& w) {
  if (e->scope_prefix.empty()) return TypedOfName(e->text, w);
  if (e->scope_prefix != "$unit" || w.scope.unit == nullptr) return {};
  return TypedIn(w.scope.unit->cu_items, e->text, w.scope);
}

RealTyped TypedOf(const Expr* e, const Walk& w) {
  if (e->kind == ExprKind::kIdentifier) return TypedOfIdentifier(e, w);
  if (e->kind == ExprKind::kMemberAccess) return TypedOfMember(e, w);
  if (e->kind == ExprKind::kSelect) return TypedOfSelect(e, w);
  return {};
}

bool HoldsReal(const RealTyped& typed) {
  return IsRealType(typed.kind) && typed.unpacked == 0;
}

bool NamesRealVariable(const RealTyped& typed) {
  return HoldsReal(typed) && !typed.is_param && !typed.is_function;
}

std::string_view CastTypeName(const Expr* e) {
  return e->text.empty() ? ExprIdent(e->rhs) : e->text;
}

bool IsRealOperand(const Expr* e, const Walk& w) {
  return HoldsReal(TypedOf(e, w));
}

bool IsRealFunctionCall(const Expr* e, const Walk& w) {
  const RealTyped kTyped = TypedOfName(e->callee, w);
  return kTyped.is_function && HoldsReal(kTyped);
}

bool HoldsRealValue(const Expr* e, const Walk& w) {
  if (e == nullptr) return false;
  switch (e->kind) {
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    case ExprKind::kUnary:
      return (e->op == TokenKind::kPlus || e->op == TokenKind::kMinus) &&
             HoldsRealValue(e->lhs, w);
    case ExprKind::kBinary:
      return std::ranges::contains(kRealArithmeticOps, e->op) &&
             (HoldsRealValue(e->lhs, w) || HoldsRealValue(e->rhs, w));
    case ExprKind::kTernary:
      return HoldsRealValue(e->true_expr, w) ||
             HoldsRealValue(e->false_expr, w);
    case ExprKind::kCast:
      return std::ranges::contains(kRealCastTypes, CastTypeName(e));
    case ExprKind::kSystemCall:
      return std::ranges::contains(kRealSystemFunctions, e->callee);
    case ExprKind::kCall:
      return IsRealFunctionCall(e, w);
    default:
      return IsRealOperand(e, w);
  }
}

void CheckExpr(const Expr* e, const Walk& w);

void CheckSelect(const Expr* e, const Walk& w) {
  const RealTyped kBase = TypedOf(e->base, w);
  const bool kIsPartSelect = e->index_end != nullptr;
  if (NamesRealVariable(kBase)) {
    w.scope.diag.ErrorOnce(
        e->range.start,
        std::format("{} of a real variable is illegal",
                    kIsPartSelect ? "part-select" : "bit-select"),
        Subclause("6.12"));
    return;
  }
  if (kBase.unpacked != 0) return;
  const bool kIsRange =
      kIsPartSelect && !e->is_part_select_plus && !e->is_part_select_minus;
  if (HoldsRealValue(e->index, w) ||
      (kIsRange && HoldsRealValue(e->index_end, w))) {
    w.scope.diag.ErrorOnce(e->range.start, "real type used as index is illegal",
                           Subclause("6.12"));
  }
}

void CheckExpr(const Expr* e, const Walk& w) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSelect && e->base != nullptr) CheckSelect(e, w);
  ForEachExprChild(e, [&w](const Expr* child) { CheckExpr(child, w); });
}

void CheckEdges(const std::vector<EventExpr>& events, const Walk& w) {
  for (const EventExpr& ev : events) {
    if (ev.edge != Edge::kNone && ev.signal != nullptr &&
        NamesRealVariable(TypedOf(ev.signal, w))) {
      w.scope.diag.ErrorOnce(ev.signal->range.start,
                             "edge event on real type is illegal",
                             Subclause("6.12"));
    }
  }
}

void CheckEvents(const std::vector<EventExpr>& events, const Walk& w) {
  CheckEdges(events, w);
  for (const EventExpr& ev : events) {
    CheckExpr(ev.signal, w);
    CheckExpr(ev.iff_condition, w);
  }
}

void CheckStmt(const Stmt* s, Walk& w) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    w.names[s->var_name] =
        RealTypedOfDecl(s->var_decl_type, s->var_unpacked_dims.size(), w.scope);
  }
  CheckEdges(s->events, w);
  CheckEvents(s->assert_clock, w);
  ForEachChildExpr(s, [&w](const Expr* e) { CheckExpr(e, w); });
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
    Walk inner = w;
    ForEachChildStmt(s, [&inner](const Stmt* sub) { CheckStmt(sub, inner); });
    return;
  }
  ForEachChildStmt(s, [&w](const Stmt* sub) { CheckStmt(sub, w); });
}

void CheckItem(const ModuleItem* item, const Walk& w);

void CheckClass(const ClassDecl* cls, const Walk& outer) {
  Walk inner = outer;
  inner.this_class = cls;
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      CheckItem(m->method, inner);
    } else if (m->kind == ClassMemberKind::kClassDecl &&
               m->nested_class != nullptr) {
      CheckClass(m->nested_class, inner);
    }
  }
}

void CheckSubroutine(const ModuleItem* item, const Walk& outer) {
  Walk inner = outer;
  if (!item->method_class.empty()) {
    inner.this_class = FindClass(item->method_class, outer.scope);
  }
  for (const FunctionArg& arg : item->func_args) {
    inner.names[arg.name] =
        RealTypedOfDecl(arg.data_type, arg.unpacked_dims.size(), outer.scope);
  }
  for (const Stmt* s : item->func_body_stmts) CheckStmt(s, inner);
}

void CheckItem(const ModuleItem* item, const Walk& w) {
  if (item->kind == ModuleItemKind::kClassDecl) {
    if (item->class_decl != nullptr) CheckClass(item->class_decl, w);
    return;
  }
  if (item->kind == ModuleItemKind::kFunctionDecl ||
      item->kind == ModuleItemKind::kTaskDecl) {
    CheckSubroutine(item, w);
    return;
  }
  for (const std::vector<EventExpr>* events :
       {&item->sensitivity, &item->clocking_event, &item->prop_clock,
        &item->seq_clock}) {
    CheckEvents(*events, w);
  }
  CheckExpr(item->assign_lhs, w);
  CheckExpr(item->assign_rhs, w);
  CheckExpr(item->init_expr, w);
  Walk inner = w;
  CheckStmt(item->body, inner);
}

}  // namespace

RealTyped RealTypedOfDecl(const DataType& type, size_t unpacked,
                          const RealUseScope& scope) {
  RealTyped typed;
  typed.found = true;
  typed.unpacked = unpacked + TypedefDimsOnChain(type, scope);
  if (!type.type_name.empty()) typed.cls = FindClass(type.type_name, scope);
  if (typed.cls != nullptr) return typed;
  const DataType* end = TypeAtChainEnd(type, scope.typedefs);
  if (end == nullptr) return typed;
  typed.kind = end->kind;
  typed.aggregate = end;
  return typed;
}

void ReportRealUsesInItem(const ModuleItem* item, const RealUseScope& scope) {
  const Walk kWalk{scope, {}, nullptr};
  CheckItem(item, kWalk);
}

void ReportRealUsesInItems(const std::vector<ModuleItem*>& items,
                           const RealUseScope& scope) {
  for (const ModuleItem* item : items) ReportRealUsesInItem(item, scope);
}

void ReportRealUsesInClass(const ClassDecl* cls, const RealUseScope& scope) {
  const Walk kWalk{scope, {}, nullptr};
  CheckClass(cls, kWalk);
}

}  // namespace delta
