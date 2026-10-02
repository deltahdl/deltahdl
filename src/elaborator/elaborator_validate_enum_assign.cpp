// §6.19.3 and §6.19.4: the strong typing of an enum variable, held over the
// values a module assigns or initializes one with, passes to a subroutine's
// enum-typed formal, and returns from a function whose return type is an
// enumeration.

#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

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

// §6.19.5/§6.19.6: the first, last, next, and prev enumeration methods return a
// value of the same enumeration type, so assigning their result to an enum
// variable requires no cast. Recognizes both the no-parens member access
// (c.next) and the explicit call form (c.next()). The num/name methods return
// int/string and are intentionally excluded.
static bool IsEnumTypedMethodResult(const Expr* e) {
  if (!e) return false;
  const Expr* member = e;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    member = e->lhs;
  }
  if (member->kind != ExprKind::kMemberAccess) return false;
  if (!member->rhs || member->rhs->kind != ExprKind::kIdentifier) return false;
  std::string_view m = member->rhs->text;
  return m == "first" || m == "last" || m == "next" || m == "prev";
}

// §6.19: whether the enumeration `item` declares, through a typedef or as the
// type of a data declaration (Syntax 6-5), has a member named `name`.
static bool ItemDeclaresEnumMember(const ModuleItem& item,
                                   std::string_view name) {
  const DataType& type = item.kind == ModuleItemKind::kTypedef
                             ? item.typedef_type
                             : item.data_type;
  if (type.kind != DataTypeKind::kEnum) return false;
  return std::any_of(type.enum_members.begin(), type.enum_members.end(),
                     [name](const EnumMember& m) { return m.name == name; });
}

// §26.3: `pkg::name` written with the package scope resolution operator names
// package pkg's declaration of name from any scope, imported or not, and §6.19
// makes an enumeration's members constants of the package that writes the
// enumeration; so where pkg declares an enumeration with a member of that name
// the reference is the literal itself, of the enumeration's type, exactly as
// the bare name of a literal is. A package parameter named the same way is not
// a literal and stays an integer to §6.19.3. True for the literal alone.
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

// True when `e` may initialize or be assigned to an enum variable without a
// cast: an identifier (another value of the type), a package's enumeration
// literal named through its scope (§26.3), an explicit cast, or a call of an
// enumeration method whose declared result is the enumeration type (§6.19.5).
// §6.19.3 requires the cast for an expression of a different type, which none
// of these is. Every place that screens a value bound for an enum variable --
// an assignment, a module-item declaration's initializer, a procedural
// declaration's initializer -- asks this one question, so that the three
// cannot answer it differently.
//
// §10.9.1 with §7.4: a variable declared as an unpacked array of the enum takes
// an assignment pattern whose every item is one of those, `'{ON, OFF, ON}`,
// a keyed or default item included, and a nested pattern for a further
// dimension; each item initializes an element, an enum variable of its own.
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

// Where a value bound for an enum variable goes, as ReportEnumValueWithoutCast
// says it.
constexpr std::string_view kAssignedToEnum = "assigned to enum variable";

// What EnumValueSubclause reads to find an enum among a value's operands: the
// enum variables and enumeration members in scope, and the compilation unit
// that resolves a package-scoped member.
struct EnumOperandNames {
  const NameSet& enum_vars;
  const NameSet& enum_members;
  const CompilationUnit* unit;
};

// True when an enum variable, an enumeration member or an enumeration-typed
// method result is an operand of `e`: §6.19.4 has an enum identifier used as
// part of an expression auto-cast to the enumeration's base type. A member
// access or a call other than those methods is a value of its own type, so the
// walk stops there: the receiver of `c.num()` takes part in no arithmetic.
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

// The clause the cast a value bound for an enum variable lacks is stated in.
// Two clauses state it: §6.19.3, that an enum variable is not directly assigned
// a value outside its enumeration, and an arbitrary expression only through a
// cast; and §6.19.4, that an enum used as part of a numerical expression is
// auto-cast to the base type and a cast is required to assign an expression
// whose type is not the enumeration's back to an enum variable. A value that
// has an enum among its operands is §6.19.4's case, and any other value is
// §6.19.3's. The value is known not to be bare-assignable when this is asked.
static std::string_view EnumValueSubclause(const Expr* value,
                                           const EnumOperandNames& names) {
  return ExprHasEnumOperand(value, names) ? "6.19.4" : "6.19.3";
}

// §6.19.3: whether `e` is the bare name of a module's variable or net of a
// built-in type other than an enumeration, `i` of `int i;`.
// IsBareEnumAssignable accepts every bare name as another value of the
// enumeration, which such a variable's value is not. A name an enum variable or
// member goes by, a block's own among them, is not one.
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

// What ReportEnumValueWithoutCast reads: the type of each of the module's
// variables and nets, the enum variables and members in scope, and where the
// report goes.
struct EnumValueScreen {
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  EnumOperandNames names;
  DiagEngine& diag;
};

// §6.19.3, §6.19.4: reports `value`, bound at `loc` for an enum, where it
// reaches the enum without the cast those clauses require: an expression
// IsBareEnumAssignable refuses, or the bare name of a variable of a built-in
// type other than an enumeration. `bound` says where the value goes, as
// kAssignedToEnum does.
static void ReportEnumValueWithoutCast(const Expr* value, SourceLoc loc,
                                       std::string_view bound,
                                       const EnumValueScreen& screen) {
  if (!IsBareEnumAssignable(value, screen.names.unit)) {
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
    // §11.4.2 has `val += 1` stand for `val = val + 1`, so the variable is an
    // operand of the expression assigned to it and the case is §6.19.4's.
    diag_.Error(s->range.start,
                "compound assignment to enum variable without cast",
                Subclause("6.19.4"));
    return;
  }
  if (!s->rhs) return;
  ReportEnumValueWithoutCast(
      s->rhs, s->range.start, kAssignedToEnum,
      {var_types_, {enum_var_names_, enum_member_names_, unit_}, diag_});
}

static bool FormalIsEnumType(const DataType& formal,
                             const TypedefMap& typedefs) {
  if (formal.kind == DataTypeKind::kEnum) return true;
  if (formal.kind != DataTypeKind::kNamed) return false;
  auto t = typedefs.find(formal.type_name);
  return t != typedefs.end() && t->second.kind == DataTypeKind::kEnum;
}

static bool CallUsesNamedArgs(const Expr* call) {
  // Positional binding only; a named association is left for the general
  // argument-binding path and is not second-guessed by the strong-typing rule.
  for (auto name : call->arg_names) {
    if (!name.empty()) return true;
  }
  return false;
}

static void CheckEnumActualArg(const Expr* actual, DiagEngine& diag) {
  if (!actual) return;
  // Mirror the assignment rule: a bare name (an enum member or another enum
  // of the same family) and an explicit cast are accepted; a plain integral
  // value is rejected because it is not a member of the enumeration.
  if (actual->kind == ExprKind::kIdentifier) return;
  if (actual->kind == ExprKind::kCast) return;
  diag.Error(actual->range.start,
             "integer value passed to enum argument without cast",
             Subclause("6.19.3"));
}

void Elaborator::CheckEnumCallArguments(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall) return;
  // Restrict to free-function calls: a member/method receiver could share a
  // name with a module function and must not be matched here.
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

// True when a data type denotes an enumeration, either directly or via a
// typedef name.
static bool DataTypeIsEnum(const DataType& dtype, const TypedefMap& typedefs) {
  if (dtype.kind == DataTypeKind::kEnum) return true;
  if (dtype.kind != DataTypeKind::kNamed) return false;
  auto it = typedefs.find(dtype.type_name);
  return it != typedefs.end() && it->second.kind == DataTypeKind::kEnum;
}

// An initializer/RHS that is acceptable for an enum target without a cast:
// a bare name (enum member or sibling enum) or an explicit cast.

namespace {

// True when a procedural statement declares an enum variable (Stmt-level
// var_decl) — used to register the name and screen its initializer.
bool StmtDeclaresEnumVar(const Stmt* s, const TypedefMap& typedefs) {
  return s->kind == StmtKind::kVarDecl &&
         DataTypeIsEnum(s->var_decl_type, typedefs);
}

// True when a statement is a blocking or nonblocking assignment.
bool StmtIsProceduralAssign(const Stmt* s) {
  return s->kind == StmtKind::kBlockingAssign ||
         s->kind == StmtKind::kNonblockingAssign;
}

// True when a statement is a bare ++/-- expression statement.
bool StmtIsPostfixIncDec(const Stmt* s) {
  return s->kind == StmtKind::kExprStmt && s->expr &&
         s->expr->kind == ExprKind::kPostfixUnary;
}

// Reports an unguarded ++/-- on an enum variable (callers ensure the statement
// is a postfix unary expression statement). §11.4.2 has `val++` stand for
// `val = val + 1`, the variable being an operand of the expression assigned to
// it, so the cast it lacks is the one §6.19.4 states.
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

// §12.7.1 makes a variable declared in a for header local to the loop, so every
// use of it is inside the region §6.19.3 has to hold over. The parser records
// such a declaration as an assignment in Stmt::for_inits with its type in the
// matching Stmt::for_init_types entry, and not as a StmtKind::kVarDecl -- which
// is what StmtDeclaresEnumVar above looks for, so the name was never registered
// and nothing assigned to it anywhere in the loop was judged either.
//
// Only the names are taken here. The assignment the header holds is judged
// where every other assignment is, when the walk descends into for_inits, so an
// initializer draws the one report §6.19.3 asks for rather than two.
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

// What EnumTypeOfName reads: the module's variables declared with a type name,
// each with that name, the typedefs in scope, and the names the procedure
// declares, which hide the module's.
struct EnumTypeLookup {
  const std::unordered_map<std::string_view, std::string_view>& var_types;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& locals;
};

// The typedef that writes the enumeration the type name `name` stands for,
// through any chain of typedefs renaming it (§6.22.1 makes a renamed type the
// same type); empty where `name` stands for no enumeration. The hop limit
// keeps a cyclic typedef from looping.
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

// The enumeration typedef that declares `member` as a member; empty where none
// does, and where more than one does.
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

// The enumeration typedef the value named `name` is of: a module variable's
// declared enumeration, or the one of the typedef that declares `name` as a
// member. Empty for any other name, for a name the procedure declares, and
// for a member more than one typedef declares.
std::string_view EnumTypeOfName(std::string_view name,
                                const EnumTypeLookup& lookup) {
  if (name.empty() || lookup.locals.count(name) != 0) return {};
  auto var = lookup.var_types.find(name);
  if (var != lookup.var_types.end())
    return EnumTypedefBehind(var->second, lookup.typedefs);
  return EnumTypedefDeclaringMember(name, lookup.typedefs);
}

// §6.19.3 (printed page 122): an enum variable is not directly assigned a value
// outside its enumeration set, and a value of another enumerated type, a
// variable or a member of it, is one: `c = w;` with Colors c and Week w needs
// the cast. The bare name reaches IsBareEnumAssignable's acceptance, which
// asks no type, so this is the check that tells the two enumerations apart.
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

// The return statements of a function body `s` holds, given to `fn`. A return
// in a randsequence production's code block aborts the production rather than
// returning from the function (§18.17.6), so the walk stops there.
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

// §13.4.1 with §6.19.3: ReportEnumValueWithoutCast for each return of `fn`, a
// function whose return type is an enumeration.
static void ValidateEnumReturns(const ModuleItem* fn,
                                const EnumValueScreen& screen) {
  // A formal or a local of the function shadows the module's variable of its
  // name, so a bare name the function declares is not read as the module's.
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
  WalkExprForEnumCalls(s->rhs);
  WalkExprForEnumCalls(s->expr);
  WalkExprForEnumCalls(s->condition);
  if (StmtDeclaresEnumVar(s, typedefs_)) {
    enum_var_names_.insert(s->var_name);
    if (s->var_init) {
      ReportEnumValueWithoutCast(
          s->var_init, s->range.start, kAssignedToEnum,
          {var_types_, {enum_var_names_, enum_member_names_, unit_}, diag_});
    }
  } else if (StmtIsProceduralAssign(s)) {
    CheckEnumAssignStmt(s);
  } else if (StmtIsPostfixIncDec(s)) {
    CheckEnumIncDecStmt(s, enum_var_names_, diag_);
  }
  // §6.19.3 makes an enumerated type strongly typed: a value of any other
  // type reaches an enum variable only through a cast. The rule is stated of
  // the assignment and names no statement it is suspended in, so this descends
  // every link ForEachChildStmt in elaborator_validate_internal.h names and
  // writes out no link of its own. It used to write out six of the thirteen,
  // which left an assignment in a fork arm (§9.3.2), in a for-loop
  // initialization or step (A.6.8), in either arm of an immediate assertion's
  // action block (§16.3), in a randcase item (§18.16) or in a randsequence
  // production's code block (§18.17) unreached.
  //
  // That cost twice over, because this walk both reports the offending
  // assignment and collects the enum variables a statement declares into
  // enum_var_names_. A variable declared in one of those seven links never
  // entered that set, so a later assignment to it -- even one written in a link
  // the walk did read -- was unjudged as well as unreported.
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForEnumAssign(sub); });
}

void Elaborator::ValidateEnumAssignments(const ModuleDecl* decl) {
  EnumValueScreen screen{
      var_types_, {enum_var_names_, enum_member_names_, unit_}, diag_};
  for (const auto* item : decl->items) {
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
