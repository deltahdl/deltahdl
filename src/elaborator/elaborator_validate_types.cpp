#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static int64_t ParseLiteralWidth(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos || apos == 0) return 0;
  int64_t width = 0;
  for (size_t i = 0; i < apos; ++i) {
    if (txt[i] < '0' || txt[i] > '9') return 0;
    width = width * 10 + (txt[i] - '0');
  }
  return width;
}

static bool LiteralHasXZ(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos) return false;
  return txt.substr(apos + 1).find_first_of("xXzZ") != std::string_view::npos;
}

static bool ExprContainsXZ(const Expr* e) {
  if (!e) return false;
  // §6.19: a 4-state enum value may be x/z. The unbased unsized form ('x, 'z)
  // lexes as its own kind, not kIntegerLiteral, so it must be matched here too;
  // otherwise it is mistaken for an ordinary integer and folded into the
  // auto-increment/duplicate-value machinery (e.g. {XX = 'x} colliding with a
  // later explicit value).
  if ((e->kind == ExprKind::kIntegerLiteral ||
       e->kind == ExprKind::kUnbasedUnsizedLiteral) &&
      LiteralHasXZ(e->text)) {
    return true;
  }
  if (ExprContainsXZ(e->lhs)) return true;
  if (ExprContainsXZ(e->rhs)) return true;
  for (const auto* elem : e->elements) {
    if (ExprContainsXZ(elem)) return true;
  }
  return ExprContainsXZ(e->repeat_count);
}

static bool ExprContainsHierarchicalRef(const Expr* e);

static bool AnyScalarChildContainsHierarchicalRef(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,       e->base,       e->index,       e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count};
  for (const Expr* child : kChildren) {
    if (ExprContainsHierarchicalRef(child)) return true;
  }
  return false;
}

static bool ExprContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty()) return true;
  if (AnyScalarChildContainsHierarchicalRef(e)) return true;
  for (const auto* a : e->args) {
    if (ExprContainsHierarchicalRef(a)) return true;
  }
  for (const auto* elem : e->elements) {
    if (ExprContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

static std::string_view FindConstVarRef(
    const Expr* e, const std::unordered_set<std::string_view>& const_names);

static std::string_view FindConstVarRefInScalarChildren(
    const Expr* e, const std::unordered_set<std::string_view>& const_names) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,       e->base,       e->index,       e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count};
  for (const Expr* child : kChildren) {
    if (auto n = FindConstVarRef(child, const_names); !n.empty()) return n;
  }
  return {};
}

static std::string_view FindConstVarRef(
    const Expr* e, const std::unordered_set<std::string_view>& const_names) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier && e->scope_prefix.empty() &&
      const_names.count(e->text)) {
    return e->text;
  }
  if (auto n = FindConstVarRefInScalarChildren(e, const_names); !n.empty())
    return n;
  for (const auto* a : e->args) {
    if (auto n = FindConstVarRef(a, const_names); !n.empty()) return n;
  }
  for (const auto* elem : e->elements) {
    if (auto n = FindConstVarRef(elem, const_names); !n.empty()) return n;
  }
  return {};
}

bool Elaborator::ValidateEnumLiteral(const EnumMember& member,
                                     uint32_t base_width, bool is_2state) {
  if (member.value->kind == ExprKind::kIntegerLiteral) {
    auto width = ParseLiteralWidth(member.value->text);
    if (width > 0) {
      if (width != static_cast<int64_t>(base_width)) {
        diag_.Error(member.value->range.start,
                    std::format("enum literal width {} does not match "
                                "base type width {}",
                                width, base_width),
                    Subclause("6.19"));
      }
    }
  }
  bool has_xz = ExprContainsXZ(member.value);
  if (has_xz && is_2state) {
    diag_.Error(member.value->range.start,
                "x/z value in 2-state enum is illegal", Subclause("6.19"));
  }
  return has_xz;
}

static void CheckEnumBaseType(const DataType& dtype, SourceLoc loc,
                              const TypedefMap& typedefs, DiagEngine& diag) {
  if (dtype.enum_base_name.empty()) return;
  auto it = typedefs.find(dtype.enum_base_name);
  if (it == typedefs.end()) return;
  auto k = it->second.kind;
  bool integer_atom = k == DataTypeKind::kByte ||
                      k == DataTypeKind::kShortint || k == DataTypeKind::kInt ||
                      k == DataTypeKind::kLongint ||
                      k == DataTypeKind::kInteger || k == DataTypeKind::kTime;
  bool integer_vector = k == DataTypeKind::kLogic || k == DataTypeKind::kReg ||
                        k == DataTypeKind::kBit;
  if (!integer_atom && !integer_vector) {
    diag.Error(loc,
               std::format("enum base type '{}' is not an "
                           "integer_atom_type or integer_vector_type",
                           dtype.enum_base_name),
               Subclause("6.19"));
  } else if (integer_atom && dtype.packed_dim_left != nullptr) {
    diag.Error(loc,
               std::format("packed dimension not permitted on enum base "
                           "type '{}' that denotes an integer_atom_type",
                           dtype.enum_base_name),
               Subclause("6.19"));
  }
}

static void CheckEnumMemberName(
    const EnumMember& member, SourceLoc loc,
    std::unordered_set<std::string_view>& seen_names,
    const std::unordered_set<std::string_view>& declared, DiagEngine& diag) {
  if (member.range_start) return;
  if (!seen_names.insert(member.name).second) {
    diag.Error(loc, std::format("duplicate enum member name '{}'", member.name),
               Subclause("6.19"));
  } else if (declared.count(member.name)) {
    diag.Error(loc,
               std::format("enum member name '{}' is already declared "
                           "in this scope",
                           member.name),
               Subclause("6.19"));
  }
}

static void CheckEnumMemberValueRefs(
    const EnumMember& member,
    const std::unordered_set<std::string_view>& const_names, DiagEngine& diag) {
  if (!member.value) return;
  if (ExprContainsHierarchicalRef(member.value)) {
    diag.Error(member.value->range.start,
               "hierarchical name not allowed in enum named constant "
               "value",
               Subclause("6.19"));
  }
  auto const_name = FindConstVarRef(member.value, const_names);
  if (!const_name.empty()) {
    diag.Error(member.value->range.start,
               std::format("const variable '{}' not allowed in enum named "
                           "constant value",
                           const_name),
               Subclause("6.19"));
  }
}

static int64_t ComputeEnumRangeCount(const EnumMember& member, SourceLoc loc,
                                     DiagEngine& diag) {
  if (!member.range_start) return 1;
  auto n = ConstEvalInt(member.range_start).value_or(0);
  int64_t count = 1;
  if (member.range_end) {
    auto m = ConstEvalInt(member.range_end).value_or(0);
    // Table 6-10: for the name[N:M] form, both bounds shall be
    // non-negative integral numbers.
    if (n < 0 || m < 0) {
      diag.Error(loc,
                 std::format("enum range bounds of '{}' shall be "
                             "non-negative integral numbers",
                             member.name),
                 Subclause("6.19.2"));
    }
    count = (m >= n) ? (m - n + 1) : (n - m + 1);
  } else {
    // Table 6-10: for the name[N] form, N shall be a positive integral
    // number.
    if (n < 1) {
      diag.Error(loc,
                 std::format("enum range count of '{}' shall be a "
                             "positive integral number",
                             member.name),
                 Subclause("6.19.2"));
    }
    count = n;
  }
  return count < 1 ? 1 : count;
}

// Representable range of an enum base type (§6.19, Table 6-10).
struct EnumBaseRange {
  bool is_signed = false;
  uint32_t base_width = 0;
  uint64_t max_val = 0;
  int64_t signed_min = 0;
};

static EnumBaseRange ComputeEnumBaseRange(const DataType& dtype,
                                          uint32_t base_width) {
  EnumBaseRange range;
  range.is_signed = dtype.is_signed;
  range.base_width = base_width;
  range.max_val =
      dtype.is_signed
          ? (base_width > 0 ? (1ULL << (base_width - 1)) - 1 : 0)
          : (base_width < 64 ? (1ULL << base_width) - 1 : UINT64_MAX);
  range.signed_min = (dtype.is_signed && base_width > 0 && base_width < 64)
                         ? -(1LL << (base_width - 1))
                         : INT64_MIN;
  return range;
}

static bool EnumValueOutOfRange(int64_t v, const EnumBaseRange& range) {
  if (range.is_signed) {
    return v < range.signed_min || v > static_cast<int64_t>(range.max_val);
  }
  return v < 0 ||
         (range.base_width < 64 && static_cast<uint64_t>(v) > range.max_val);
}

static void CheckEnumDuplicateValues(int64_t start, int64_t count,
                                     std::unordered_set<int64_t>& seen,
                                     SourceLoc loc, DiagEngine& diag) {
  for (int64_t i = 0; i < count; ++i) {
    if (!seen.insert(start + i).second) {
      diag.Error(loc, std::format("duplicate enum member value {}", start + i),
                 Subclause("6.19"));
    }
  }
}

// Const-evaluates an explicitly-valued enum member, reports an out-of-range
// value, and updates the running auto-increment cursor. Called only after the
// member's literal width/x-z checks have passed.
static void CheckEnumMemberValueInRange(const EnumMember& member,
                                        const EnumBaseRange& range,
                                        int64_t& next_val, DiagEngine& diag) {
  auto v = ConstEvalInt(member.value);
  if (!v) return;
  if (EnumValueOutOfRange(*v, range)) {
    diag.Error(member.value->range.start,
               std::format("enum member '{}' value {} is outside the "
                           "representable range of the base type",
                           member.name, *v),
               Subclause("6.19"));
  }
  next_val = *v;
}

// §6.19: an enumeration declares its named constants once, however many
// declarators the declaration lists -- `enum {A, B} x, y;` declares A and B a
// single time and both x and y take that type. Only the declarator that
// declares them is measured against the names already in the scope; a later one
// in the same list would otherwise report those constants as clashing with
// themselves. Duplicates within the member list are still caught, by seen_names
// in the caller.
// A pointer rather than a reference, so that what is returned cannot outlive a
// temporary the caller built: scope_names is the caller's own long-lived set.
static const std::unordered_set<std::string_view>* NamesToClashAgainst(
    const std::unordered_set<std::string_view>& scope_names,
    bool declares_its_constants) {
  static const std::unordered_set<std::string_view> kNoDeclaredNames;
  return declares_its_constants ? &scope_names : &kNoDeclaredNames;
}

void Elaborator::ValidateEnumDecl(const DataType& dtype, SourceLoc loc,
                                  bool declares_its_constants) {
  CheckEnumBaseType(dtype, loc, typedefs_, diag_);
  auto base_width = EvalTypeWidth(dtype, typedefs_);
  bool is_2state = !Is4stateType(dtype, typedefs_);
  bool prev_had_xz = false;
  EnumBaseRange range = ComputeEnumBaseRange(dtype, base_width);
  std::unordered_set<std::string_view> seen_names;
  std::unordered_set<int64_t> seen_values;
  int64_t next_val = 0;
  const auto* declared =
      NamesToClashAgainst(enum_member_names_, declares_its_constants);
  for (const auto& member : dtype.enum_members) {
    CheckEnumMemberName(member, loc, seen_names, *declared, diag_);
    CheckEnumMemberValueRefs(member, const_var_names_, diag_);
    if (!member.value) {
      if (prev_had_xz) {
        diag_.Error(loc,
                    std::format("unassigned enum member '{}' follows member "
                                "with x/z value",
                                member.name),
                    Subclause("6.19"));
      }
      prev_had_xz = false;
    } else {
      prev_had_xz = ValidateEnumLiteral(member, base_width, is_2state);
      if (!prev_had_xz) {
        CheckEnumMemberValueInRange(member, range, next_val, diag_);
      }
    }
    int64_t count = ComputeEnumRangeCount(member, loc, diag_);
    if (!prev_had_xz) {
      CheckEnumDuplicateValues(next_val, count, seen_values, loc, diag_);
    }
    next_val += count;
    if (!prev_had_xz && next_val > 0 &&
        static_cast<uint64_t>(next_val) > range.max_val &&
        &member != &dtype.enum_members.back()) {
      diag_.Error(loc,
                  "enum auto-increment exceeds maximum representable "
                  "value of base type",
                  Subclause("6.19"));
    }
  }
}

void Elaborator::TrackEnumVariable(const ModuleItem* item) {
  if (item->data_type.kind == DataTypeKind::kEnum) {
    enum_var_names_.insert(item->name);
    for (const auto& m : item->data_type.enum_members) {
      enum_member_names_.insert(m.name);
    }
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto it = typedefs_.find(item->data_type.type_name);
  if (it != typedefs_.end() && it->second.kind == DataTypeKind::kEnum) {
    enum_var_names_.insert(item->name);
  }
}

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

// True when `e` may initialize or be assigned to an enum variable without a
// cast: an identifier (another value of the type), an explicit cast, or a call
// of an enumeration method whose declared result is the enumeration type
// (§6.19.5). §6.19.3 requires the cast for an expression of a different type,
// which none of these is. Every place that screens a value bound for an enum
// variable -- an assignment, a module-item declaration's initializer, a
// procedural declaration's initializer -- asks this one question, so that the
// three cannot answer it differently.
static bool IsBareEnumAssignable(const Expr* e) {
  return e && (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kCast ||
               IsEnumTypedMethodResult(e));
}

void Elaborator::CheckEnumAssignStmt(const Stmt* s) {
  auto name = ExprIdent(s->lhs);
  if (name.empty()) return;
  if (enum_var_names_.count(name) == 0) return;
  if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(s->rhs->op)) {
    diag_.Error(s->range.start,
                "compound assignment to enum variable without cast",
                Subclause("6.19.3"));
    return;
  }
  if (!s->rhs) return;
  if (IsBareEnumAssignable(s->rhs)) return;
  diag_.Error(s->range.start, "integer assigned to enum variable without cast",
              Subclause("6.19.3"));
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
// is a postfix unary expression statement).
void CheckEnumIncDecStmt(const Stmt* s,
                         const std::unordered_set<std::string_view>& enum_vars,
                         DiagEngine& diag) {
  auto name = ExprIdent(s->expr->lhs);
  if (!name.empty() && enum_vars.count(name) != 0) {
    diag.Error(s->range.start,
               "increment/decrement of enum variable without cast",
               Subclause("6.19.3"));
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

}  // namespace

void Elaborator::WalkStmtsForEnumAssign(const Stmt* s) {
  if (!s) return;
  RegisterForHeaderEnumVars(s, typedefs_, enum_var_names_);
  WalkExprForEnumCalls(s->rhs);
  WalkExprForEnumCalls(s->expr);
  WalkExprForEnumCalls(s->condition);
  if (StmtDeclaresEnumVar(s, typedefs_)) {
    enum_var_names_.insert(s->var_name);
    if (s->var_init && !IsBareEnumAssignable(s->var_init)) {
      diag_.Error(s->range.start,
                  "integer assigned to enum variable without cast",
                  Subclause("6.19.3"));
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
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        enum_var_names_.count(item->name) != 0 && item->init_expr &&
        !IsBareEnumAssignable(item->init_expr)) {
      diag_.Error(item->loc, "integer assigned to enum variable without cast",
                  Subclause("6.19.3"));
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForEnumAssign(item->body);
    }
  }
}

static bool HasPredefinedWidth(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

void Elaborator::ValidatePackedDimRange(const DataType& dtype, SourceLoc loc) {
  // §7.4.1 states this for "each packed dimension in a packed array
  // declaration", which covers the first dimension as squarely as the fifth,
  // so the dimension a range was written on does not change the clause. §6.9.1
  // states the same prohibition over a narrower subject, one range on a reg,
  // logic or bit vector, and §7.4 makes that subject a one-dimensional packed
  // array rather than a second rule. Nothing here reads the type kind or the
  // dimension count, so §7.4.1 is the clause true of every declaration these
  // three reports reach.
  if (dtype.packed_dim_left && ExprContainsXZ(dtype.packed_dim_left)) {
    diag_.Error(loc, "packed dimension range shall not contain x or z",
                Subclause("7.4.1"));
  }
  if (dtype.packed_dim_right && ExprContainsXZ(dtype.packed_dim_right)) {
    diag_.Error(loc, "packed dimension range shall not contain x or z",
                Subclause("7.4.1"));
  }
  for (const auto& [left, right] : dtype.extra_packed_dims) {
    if (ExprContainsXZ(left) || ExprContainsXZ(right)) {
      diag_.Error(loc, "packed dimension range shall not contain x or z",
                  Subclause("7.4.1"));
    }
  }
}

void Elaborator::ValidateUnpackedDimRange(const std::vector<Expr*>& dims,
                                          SourceLoc loc) {
  for (const auto* dim : dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      if (ExprContainsXZ(dim->lhs) || ExprContainsXZ(dim->rhs)) {
        diag_.Error(loc, "unpacked dimension range shall not contain x or z",
                    Subclause("7.4.2"));
      }
    } else if (ExprContainsXZ(dim)) {
      diag_.Error(loc, "unpacked dimension range shall not contain x or z",
                  Subclause("7.4.2"));
    }
  }
}

void Elaborator::ValidatePackedDimOnPredefinedType(const DataType& dtype,
                                                   SourceLoc loc) {
  if (!HasPredefinedWidth(dtype.kind)) return;
  if (!dtype.packed_dim_left) return;
  diag_.Error(loc,
              "integer type with predefined width shall not have packed "
              "array dimensions",
              Subclause("7.4.1"));
}

static bool IsAllowedPackedElementKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kString:
    case DataTypeKind::kChandle:
    case DataTypeKind::kEvent:
    case DataTypeKind::kVoid:
    case DataTypeKind::kVirtualInterface:
      return false;
    default:
      return true;
  }
}

void Elaborator::ValidatePackedDimOnDisallowedType(const DataType& dtype,
                                                   SourceLoc loc) {
  if (!dtype.packed_dim_left) return;
  if (IsAllowedPackedElementKind(dtype.kind)) return;
  diag_.Error(loc,
              "packed array element type must be a single-bit type, "
              "enum, or packed aggregate",
              Subclause("7.4.1"));
}

}  // namespace delta
