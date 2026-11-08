#include <algorithm>
#include <array>
#include <cstddef>
#include <format>
#include <functional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsCompoundAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

static const Expr* MethodAccess(const Expr* e) {
  const Expr* member = e;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    member = e->lhs;
  }
  if (member->kind != ExprKind::kMemberAccess) return nullptr;
  if (!member->rhs || member->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return member;
}

static bool IsEnumTypedMethodResult(const Expr* e) {
  if (!e) return false;
  const Expr* member = MethodAccess(e);
  if (member == nullptr) return false;
  std::string_view m = member->rhs->text;
  return m == "first" || m == "last" || m == "next" || m == "prev";
}

constexpr std::array<std::string_view, 6> kElementLocators = {
    "find", "find_first", "find_last", "min", "max", "unique"};

constexpr std::array<std::string_view, 4> kIndexLocators = {
    "find_index", "find_first_index", "find_last_index", "unique_index"};

static bool CallsMethodOn(const Expr* e, const NameSet& arrays,
                          std::span<const std::string_view> methods) {
  const Expr* member = MethodAccess(e);
  return member != nullptr && arrays.count(ExprIdent(member->lhs)) != 0 &&
         std::find(methods.begin(), methods.end(), member->rhs->text) !=
             methods.end();
}

static bool ItemDeclaresEnumMember(const ModuleItem& item,
                                   std::string_view name) {
  const DataType& type = item.kind == ModuleItemKind::kTypedef
                             ? item.typedef_type
                             : item.data_type;
  if (type.kind != DataTypeKind::kEnum) return false;
  return std::any_of(type.enum_members.begin(), type.enum_members.end(),
                     [name](const EnumMember& m) { return m.name == name; });
}

static bool IsPackageEnumMemberRef(const Expr* e, const CompilationUnit* unit) {
  if (unit == nullptr || e->kind != ExprKind::kMemberAccess ||
      !e->is_scope_resolution || e->lhs == nullptr || e->rhs == nullptr ||
      e->lhs->kind != ExprKind::kIdentifier ||
      e->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  for (const auto* pkg : unit->packages) {
    if (pkg->name != e->lhs->text) continue;
    for (const auto* item : pkg->items) {
      if (ItemDeclaresEnumMember(*item, e->rhs->text)) return true;
    }
  }
  return false;
}

static bool IsBareEnumAssignable(const Expr* e, const CompilationUnit* unit) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kAssignmentPattern) {
    if (e->elements.empty()) return false;
    for (const Expr* item : e->elements) {
      if (!IsBareEnumAssignable(item, unit)) return false;
    }
    return true;
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kCast ||
         IsPackageEnumMemberRef(e, unit) || IsEnumTypedMethodResult(e);
}

constexpr std::string_view kAssignedToEnum = "assigned to enum variable";

struct EnumOperandNames {
  const NameSet& enum_vars;
  const NameSet& enum_members;
  const CompilationUnit* unit;
};

static bool ExprHasEnumOperand(const Expr* e, const EnumOperandNames& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) {
    return names.enum_vars.count(e->text) != 0 ||
           names.enum_members.count(e->text) != 0;
  }
  if (IsEnumTypedMethodResult(e) || IsPackageEnumMemberRef(e, names.unit)) {
    return true;
  }
  if (e->kind == ExprKind::kMemberAccess || e->kind == ExprKind::kCall) {
    return false;
  }
  return AnyExprChild(e, [&names](const Expr* child) {
    return ExprHasEnumOperand(child, names);
  });
}

static std::string_view EnumValueSubclause(const Expr* value,
                                           const EnumOperandNames& names) {
  return ExprHasEnumOperand(value, names) ? "6.19.4" : "6.19.3";
}

static bool IsNonEnumVariableRead(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const EnumOperandNames& names) {
  if (e->kind != ExprKind::kIdentifier) return false;
  if (names.enum_vars.count(e->text) != 0 ||
      names.enum_members.count(e->text) != 0) {
    return false;
  }
  auto it = var_types.find(e->text);
  if (it == var_types.end()) return false;
  DataTypeKind kind = it->second;
  return (IsIntegralType(kind) && kind != DataTypeKind::kEnum) ||
         IsRealType(kind) || kind == DataTypeKind::kString;
}

struct EnumValueScreen {
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  EnumOperandNames names;
  const NameSet& enum_keyed_arrays;
  DiagEngine& diag;
};

static void ReportEnumValueWithoutCast(const Expr* value, SourceLoc loc,
                                       std::string_view bound,
                                       const EnumValueScreen& screen) {
  if (!IsBareEnumAssignable(value, screen.names.unit) &&
      !CallsMethodOn(value, screen.names.enum_vars, kElementLocators) &&
      !CallsMethodOn(value, screen.enum_keyed_arrays, kIndexLocators)) {
    screen.diag.Error(loc, std::format("integer {} without cast", bound),
                      Subclause(EnumValueSubclause(value, screen.names)));
    return;
  }
  if (IsNonEnumVariableRead(value, screen.var_types, screen.names)) {
    screen.diag.Error(
        loc,
        std::format("value of non-enum variable '{}' {} without cast",
                    value->text, bound),
        Subclause("6.19.3"));
  }
}

void Elaborator::CheckEnumAssignStmt(const Stmt* s) {
  auto name = ExprIdent(s->lhs);
  if (name.empty()) return;
  if (enum_var_names_.count(name) == 0) return;
  if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(s->rhs->op)) {
    diag_.Error(s->range.start,
                "compound assignment to enum variable without cast",
                Subclause("6.19.4"));
    return;
  }
  if (!s->rhs) return;
  ReportEnumValueWithoutCast(s->rhs, s->range.start, kAssignedToEnum,
                             {var_types_,
                              {enum_var_names_, enum_member_names_, unit_},
                              enum_keyed_arrays_,
                              diag_});
}

static bool FormalIsEnumType(const DataType& formal,
                             const TypedefMap& typedefs) {
  if (formal.kind == DataTypeKind::kEnum) return true;
  if (formal.kind != DataTypeKind::kNamed) return false;
  auto t = typedefs.find(formal.type_name);
  return t != typedefs.end() && t->second.kind == DataTypeKind::kEnum;
}

static bool CallUsesNamedArgs(const Expr* call) {
  for (auto name : call->arg_names) {
    if (!name.empty()) return true;
  }
  return false;
}

static void CheckEnumActualArg(const Expr* actual, DiagEngine& diag) {
  if (!actual) return;
  if (actual->kind == ExprKind::kIdentifier) return;
  if (actual->kind == ExprKind::kCast) return;
  diag.Error(actual->range.start,
             "integer value passed to enum argument without cast",
             Subclause("6.19.3"));
}

void Elaborator::CheckEnumCallArguments(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall) return;
  if (call->lhs && call->lhs->kind != ExprKind::kIdentifier) return;
  auto it = func_decls_.find(call->callee);
  if (it == func_decls_.end() || it->second == nullptr) return;
  const ModuleItem* fn = it->second;
  if (CallUsesNamedArgs(call)) return;
  size_t count = std::min(call->args.size(), fn->func_args.size());
  for (size_t i = 0; i < count; ++i) {
    if (!FormalIsEnumType(fn->func_args[i].data_type, typedefs_)) continue;
    CheckEnumActualArg(call->args[i], diag_);
  }
}

void Elaborator::WalkExprForEnumCalls(const Expr* e) {
  if (!e) return;
  CheckEnumCallArguments(e);
  WalkExprForEnumCalls(e->lhs);
  WalkExprForEnumCalls(e->rhs);
  WalkExprForEnumCalls(e->condition);
  WalkExprForEnumCalls(e->true_expr);
  WalkExprForEnumCalls(e->false_expr);
  WalkExprForEnumCalls(e->base);
  WalkExprForEnumCalls(e->index);
  WalkExprForEnumCalls(e->index_end);
  for (auto* a : e->args) WalkExprForEnumCalls(a);
  for (auto* el : e->elements) WalkExprForEnumCalls(el);
}

static bool DataTypeIsEnum(const DataType& dtype, const TypedefMap& typedefs) {
  if (dtype.kind == DataTypeKind::kEnum) return true;
  if (dtype.kind != DataTypeKind::kNamed) return false;
  auto it = typedefs.find(dtype.type_name);
  return it != typedefs.end() && it->second.kind == DataTypeKind::kEnum;
}

namespace {

bool StmtDeclaresEnumVar(const Stmt* s, const TypedefMap& typedefs) {
  return s->kind == StmtKind::kVarDecl &&
         DataTypeIsEnum(s->var_decl_type, typedefs);
}

bool StmtIsProceduralAssign(const Stmt* s) {
  return s->kind == StmtKind::kBlockingAssign ||
         s->kind == StmtKind::kNonblockingAssign;
}

bool StmtIsPostfixIncDec(const Stmt* s) {
  return s->kind == StmtKind::kExprStmt && s->expr &&
         s->expr->kind == ExprKind::kPostfixUnary;
}

void CheckEnumIncDecStmt(const Stmt* s,
                         const std::unordered_set<std::string_view>& enum_vars,
                         DiagEngine& diag) {
  auto name = ExprIdent(s->expr->lhs);
  if (!name.empty() && enum_vars.count(name) != 0) {
    diag.Error(s->range.start,
               "increment/decrement of enum variable without cast",
               Subclause("6.19.4"));
  }
}

void RegisterForHeaderEnumVars(
    const Stmt* s, const TypedefMap& typedefs,
    std::unordered_set<std::string_view>& enum_vars) {
  for (size_t k = 0; k < s->for_inits.size() && k < s->for_init_types.size();
       ++k) {
    if (!DataTypeIsEnum(s->for_init_types[k], typedefs)) continue;
    const Stmt* init = s->for_inits[k];
    if (init != nullptr && init->lhs != nullptr &&
        init->lhs->kind == ExprKind::kIdentifier) {
      enum_vars.insert(init->lhs->text);
    }
  }
}

struct EnumTypeLookup {
  const std::unordered_map<std::string_view, std::string_view>& var_types;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& locals;
};

std::string_view EnumTypedefBehind(std::string_view name,
                                   const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8; ++hops) {
    auto it = typedefs.find(name);
    if (it == typedefs.end()) return {};
    if (it->second.kind == DataTypeKind::kEnum) return name;
    if (it->second.kind != DataTypeKind::kNamed) return {};
    name = it->second.type_name;
  }
  return {};
}

bool KeyedByEnum(const std::vector<Expr*>& dims, const TypedefMap& typedefs) {
  return !dims.empty() &&
         !EnumTypedefBehind(ExprIdent(dims[0]), typedefs).empty();
}

std::string_view EnumTypedefDeclaringMember(std::string_view member,
                                            const TypedefMap& typedefs) {
  std::string_view found;
  for (const auto& [td, type] : typedefs) {
    if (type.kind != DataTypeKind::kEnum) continue;
    bool declares =
        std::any_of(type.enum_members.begin(), type.enum_members.end(),
                    [&](const EnumMember& em) { return em.name == member; });
    if (!declares) continue;
    if (!found.empty() && found != td) return {};
    found = td;
  }
  return found;
}

std::string_view EnumTypeOfName(std::string_view name,
                                const EnumTypeLookup& lookup) {
  if (name.empty() || lookup.locals.count(name) != 0) return {};
  auto var = lookup.var_types.find(name);
  if (var != lookup.var_types.end())
    return EnumTypedefBehind(var->second, lookup.typedefs);
  return EnumTypedefDeclaringMember(name, lookup.typedefs);
}

void ReportCrossEnumAssigns(const Stmt* s, const EnumTypeLookup& lookup,
                            DiagEngine& diag) {
  if (s == nullptr) return;
  if (StmtIsProceduralAssign(s) && s->rhs != nullptr &&
      s->rhs->kind == ExprKind::kIdentifier) {
    std::string_view to = EnumTypeOfName(ExprIdent(s->lhs), lookup);
    std::string_view from = EnumTypeOfName(s->rhs->text, lookup);
    if (!to.empty() && !from.empty() && to != from) {
      diag.Error(s->range.start,
                 std::format("value of enum type '{}' assigned to enum "
                             "variable of type '{}' without cast",
                             from, to),
                 Subclause("6.19.3"));
    }
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { ReportCrossEnumAssigns(sub, lookup, diag); });
}

}  // namespace

static void ForEachFunctionReturn(const Stmt* s,
                                  const std::function<void(const Stmt*)>& fn) {
  if (s == nullptr || s->kind == StmtKind::kRandsequence) return;
  if (s->kind == StmtKind::kReturn) {
    fn(s);
    return;
  }
  ForEachChildStmt(s,
                   [&fn](Stmt* const& sub) { ForEachFunctionReturn(sub, fn); });
}

static void ValidateEnumReturns(const ModuleItem* fn,
                                const EnumValueScreen& screen) {
  NameSet own;
  for (const FunctionArg& arg : fn->func_args) own.insert(arg.name);
  for (const Stmt* s : fn->func_body_stmts) CollectProcLocalNames(s, own);
  std::string bound = std::format("returned from enum function '{}'", fn->name);
  for (const Stmt* s : fn->func_body_stmts) {
    ForEachFunctionReturn(s, [&](const Stmt* ret) {
      if (ret->expr == nullptr) return;
      if (ret->expr->kind == ExprKind::kIdentifier &&
          own.count(ret->expr->text) != 0) {
        return;
      }
      ReportEnumValueWithoutCast(ret->expr, ret->range.start, bound, screen);
    });
  }
}

void Elaborator::WalkStmtsForEnumAssign(const Stmt* s) {
  if (!s) return;
  RegisterForHeaderEnumVars(s, typedefs_, enum_var_names_);
  if (s->kind == StmtKind::kVarDecl &&
      KeyedByEnum(s->var_unpacked_dims, typedefs_)) {
    enum_keyed_arrays_.insert(s->var_name);
  }
  WalkExprForEnumCalls(s->rhs);
  WalkExprForEnumCalls(s->expr);
  WalkExprForEnumCalls(s->condition);
  if (StmtDeclaresEnumVar(s, typedefs_)) {
    enum_var_names_.insert(s->var_name);
    if (s->var_init) {
      ReportEnumValueWithoutCast(s->var_init, s->range.start, kAssignedToEnum,
                                 {var_types_,
                                  {enum_var_names_, enum_member_names_, unit_},
                                  enum_keyed_arrays_,
                                  diag_});
    }
  } else if (StmtIsProceduralAssign(s)) {
    CheckEnumAssignStmt(s);
  } else if (StmtIsPostfixIncDec(s)) {
    CheckEnumIncDecStmt(s, enum_var_names_, diag_);
  }
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForEnumAssign(sub); });
}

void Elaborator::ValidateEnumAssignments(const ModuleDecl* decl) {
  enum_keyed_arrays_.clear();
  EnumValueScreen screen{var_types_,
                         {enum_var_names_, enum_member_names_, unit_},
                         enum_keyed_arrays_,
                         diag_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        KeyedByEnum(item->unpacked_dims, typedefs_)) {
      enum_keyed_arrays_.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kVarDecl &&
        enum_var_names_.count(item->name) != 0 && item->init_expr) {
      ReportEnumValueWithoutCast(item->init_expr, item->loc, kAssignedToEnum,
                                 screen);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl &&
        DataTypeIsEnum(item->return_type, typedefs_)) {
      ValidateEnumReturns(item, screen);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForEnumAssign(item->body);
      std::unordered_set<std::string_view> locals;
      CollectProcLocalNames(item->body, locals);
      ReportCrossEnumAssigns(item->body, {var_named_types_, typedefs_, locals},
                             diag_);
    }
  }
}

}  // namespace delta
