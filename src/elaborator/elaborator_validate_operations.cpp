#include <format>
#include <optional>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

NetType DataTypeToNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kWire;
  }
}

static std::string_view AggregateOperandName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect &&
      (e->index_end || e->is_part_select_plus || e->is_part_select_minus) &&
      e->base && e->base->kind == ExprKind::kIdentifier) {
    return e->base->text;
  }
  return {};
}

using NameMap = std::unordered_map<std::string_view, std::string_view>;
using WidthMap = std::unordered_map<std::string_view, uint32_t>;

// Two whole unpacked-array operands compare legally only when their element
// type and dimension sizes match (§6.22.2). A typedef array's dimensions are
// not recorded on the variable, so use the typedef's cached fixed unpacked
// width as the shape key: differing widths are necessarily non-equivalent.
// Returns true when both operands are unpacked-array typedef variables, i.e.
// the comparison was fully handled here.
static bool CheckArrayCompareOp(const Expr* expr, const NameMap& types,
                                const WidthMap& widths, DiagEngine& diag) {
  if (expr->lhs->kind != ExprKind::kIdentifier ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto lt = types.find(AggregateOperandName(expr->lhs));
  auto rt = types.find(AggregateOperandName(expr->rhs));
  if (lt == types.end() || rt == types.end()) return false;
  auto lw = widths.find(lt->second);
  auto rw = widths.find(rt->second);
  if (lw == widths.end() || rw == widths.end()) return false;
  if (lw->second != rw->second) {
    diag.Error(expr->range.start,
               "comparison of non-equivalent aggregate array types",
               Subclause("6.22.2"));
  }
  return true;
}

void ElaboratorOperationRules::CheckAggregateCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  auto l_name = AggregateOperandName(expr->lhs);
  auto r_name = AggregateOperandName(expr->rhs);
  if (l_name.empty() || r_name.empty()) return;
  if (CheckArrayCompareOp(expr, var_named_types_,
                          fixed_unpacked_typedef_widths_, diag_)) {
    return;
  }

  auto lit = var_named_types_.find(l_name);
  auto rit = var_named_types_.find(r_name);
  if (lit == var_named_types_.end() || rit == var_named_types_.end()) return;
  if (lit->second == rit->second) return;

  auto is_aggregate_var = [&](std::string_view name,
                              std::string_view type_name) {
    if (var_array_info_.count(name)) return true;
    auto it = typedefs_.find(type_name);
    return it != typedefs_.end() && IsAggregateType(it->second);
  };
  if (!is_aggregate_var(l_name, lit->second)) return;
  if (!is_aggregate_var(r_name, rit->second)) return;

  diag_.Error(expr->range.start,
              std::format("comparison of non-equivalent aggregate "
                          "types '{}' and '{}'",
                          lit->second, rit->second),
              Subclause("6.22.2"));
}

void ElaboratorOperationRules::WalkExprForAggregateCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary &&
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq)) {
    CheckAggregateCompareOp(expr);
  }
  WalkExprForAggregateCompare(expr->lhs);
  WalkExprForAggregateCompare(expr->rhs);
  WalkExprForAggregateCompare(expr->condition);
  WalkExprForAggregateCompare(expr->true_expr);
  WalkExprForAggregateCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForAggregateCompare(elem);
  for (auto* arg : expr->args) WalkExprForAggregateCompare(arg);
}

void ElaboratorOperationRules::WalkStmtsForAggregateCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForAggregateCompare(s->rhs);
  WalkExprForAggregateCompare(s->lhs);
  WalkExprForAggregateCompare(s->expr);
  WalkExprForAggregateCompare(s->condition);
  WalkExprForAggregateCompare(s->assert_expr);
  // §6.22.2 makes a comparison of two non-equivalent aggregate operands illegal
  // and names no statement the rule is suspended in, so this descends every
  // link ForEachChildStmt in elaborator_validate_internal.h names. It wrote out
  // six of the thirteen, so a comparison of two differently typed structures
  // written as a fork arm, as a randcase item or in a randsequence production
  // reached CheckAggregateCompareOp through nothing and elaborated clean.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForAggregateCompare(sub); });
}

void ElaboratorOperationRules::ValidateAggregateComparisons(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForAggregateCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForAggregateCompare(item->assign_rhs);
    }
  }
}

// §6.23 — A type reference used in an equality, inequality, case-equality,
// or case-inequality comparison shall only be compared with another type
// reference. Reject any such comparison whose other operand is a value
// expression rather than a kTypeRef node.
void ElaboratorOperationRules::CheckTypeRefCompareOp(const Expr* expr) {
  if (!expr->lhs || !expr->rhs) return;
  bool lhs_is_type = expr->lhs->kind == ExprKind::kTypeRef;
  bool rhs_is_type = expr->rhs->kind == ExprKind::kTypeRef;
  if (lhs_is_type == rhs_is_type) return;
  diag_.Error(expr->range.start,
              "type reference may be compared only with another type "
              "reference",
              Subclause("6.23"));
}

// §6.23 — a type_reference used in a comparison denotes a data type. Its inner
// operand parses either as a data type (a built-in keyword, kept in `text`) or,
// for a user name, as an identifier expression (kept in `lhs`). Map that to the
// concrete DataType, following the typedef/type-parameter tables so that a type
// parameter such as `parameter type T = int` compares as its bound type. A name
// that never resolves to a built-in or a table entry (for instance a plain
// variable used as `type(v)`) is left unresolved so the caller does not fold
// it.
std::optional<DataType> ElaboratorOperationRules::ResolveTypeRefOperandType(
    const Expr* op) const {
  if (!op || op->kind != ExprKind::kTypeRef) return std::nullopt;
  DataType dt;
  if (!op->text.empty()) {
    dt = TypeNameToDataType(op->text);
  } else if (op->lhs && op->lhs->kind == ExprKind::kIdentifier) {
    dt = TypeNameToDataType(op->lhs->text);
  } else {
    return std::nullopt;
  }
  for (int depth = 0; depth < 16 && dt.kind == DataTypeKind::kNamed; ++depth) {
    DataType builtin = TypeNameToDataType(dt.type_name);
    if (builtin.kind != DataTypeKind::kNamed) {
      dt = builtin;
      break;
    }
    auto it = typedefs_.find(dt.type_name);
    if (it == typedefs_.end()) break;
    dt = it->second;
  }
  if (dt.kind == DataTypeKind::kNamed) return std::nullopt;
  return dt;
}

// §6.23 — a comparison of two type references is a constant expression whose
// result is true exactly when the referenced types match per §6.22.1 (equality
// forms yield that truth value; inequality forms its negation). Fold such a
// comparison to 0/1 so it can drive an elaboration-time selection (e.g. a
// generate-if). Returns nullopt when this is not a two-type-reference
// comparison or either operand's type cannot be resolved.
std::optional<int64_t> ElaboratorOperationRules::EvalConstTypeRefCompare(
    const Expr* expr) const {
  if (!expr || expr->kind != ExprKind::kBinary) return std::nullopt;
  bool is_equality =
      expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq ||
      expr->op == TokenKind::kEqEqEq || expr->op == TokenKind::kBangEqEq;
  if (!is_equality) return std::nullopt;
  if (!expr->lhs || expr->lhs->kind != ExprKind::kTypeRef) return std::nullopt;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kTypeRef) return std::nullopt;
  auto lhs_type = ResolveTypeRefOperandType(expr->lhs);
  auto rhs_type = ResolveTypeRefOperandType(expr->rhs);
  if (!lhs_type || !rhs_type) return std::nullopt;
  bool matched = TypesMatch(*lhs_type, *rhs_type);
  bool is_negated =
      expr->op == TokenKind::kBangEq || expr->op == TokenKind::kBangEqEq;
  return (matched != is_negated) ? 1 : 0;
}

void ElaboratorOperationRules::WalkExprForTypeRefCompare(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool is_equality =
        expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq ||
        expr->op == TokenKind::kEqEqEq || expr->op == TokenKind::kBangEqEq;
    if (is_equality) {
      CheckTypeRefCompareOp(expr);
    } else if ((expr->lhs && expr->lhs->kind == ExprKind::kTypeRef) ||
               (expr->rhs && expr->rhs->kind == ExprKind::kTypeRef)) {
      // §A.10: a type_reference primary is restricted to the equality,
      // inequality, case-equality, and case-inequality operators (and to use
      // as the casting type of a static cast, which is not a binary operator).
      // Any other operator applied to a type_reference is illegal.
      diag_.Error(expr->range.start,
                  "a type reference may only be used with the equality, "
                  "inequality, and case equality/inequality operators",
                  Subclause("6.23"));
    }
  }
  WalkExprForTypeRefCompare(expr->lhs);
  WalkExprForTypeRefCompare(expr->rhs);
  WalkExprForTypeRefCompare(expr->condition);
  WalkExprForTypeRefCompare(expr->true_expr);
  WalkExprForTypeRefCompare(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForTypeRefCompare(elem);
  for (auto* arg : expr->args) WalkExprForTypeRefCompare(arg);
}

void ElaboratorOperationRules::WalkStmtsForTypeRefCompare(const Stmt* s) {
  if (!s) return;
  WalkExprForTypeRefCompare(s->rhs);
  WalkExprForTypeRefCompare(s->lhs);
  WalkExprForTypeRefCompare(s->expr);
  WalkExprForTypeRefCompare(s->condition);
  WalkExprForTypeRefCompare(s->assert_expr);
  // §6.23 admits a type reference in a comparison only against another type
  // reference, and A.10 restricts it to the four equality operators, neither
  // conditioned on the statement the comparison stands in, so this descends
  // every link ForEachChildStmt in elaborator_validate_internal.h names. It
  // wrote out six of the thirteen, so `type(T) == 5` written as a fork arm or
  // as an immediate assertion's else action was never compared at all.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForTypeRefCompare(sub); });
}

void ElaboratorOperationRules::ValidateTypeRefComparisons(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForTypeRefCompare(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForTypeRefCompare(item->assign_rhs);
    }
  }
}

// §6.23 — the expression supplied to the type operator shall not contain a
// hierarchical reference or a reference to an element of a dynamic object.
// A member-access subtree written with `.` is treated as a hierarchical
// reference; a select whose base names a dynamic array or associative array is
// treated as a reference to a dynamic-object element.
//
// §8.23 names the type operator as one of the contexts in which an incomplete
// forward type, a type defined by an interface-based typedef, or a type
// parameter may prefix the class scope resolution operator `::`, so a
// kMemberAccess node whose Expr::is_scope_resolution is true is not by itself a
// hierarchical reference. §6.20.3 draws the same distinction for a data type
// parameter: "Package references are allowed. Hierarchical names are not
// allowed."
// The descent into the children of a `::` node still runs, so `type(C::x.y)`
// and any `::` node holding a `.` node below it remain errors.
static bool IsHierarchicalMemberAccess(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution;
}

static bool TypeRefArgHasMemberAccess(const Expr* e) {
  if (!e) return false;
  if (IsHierarchicalMemberAccess(e)) return true;
  if (TypeRefArgHasMemberAccess(e->lhs)) return true;
  if (TypeRefArgHasMemberAccess(e->rhs)) return true;
  if (TypeRefArgHasMemberAccess(e->base)) return true;
  if (TypeRefArgHasMemberAccess(e->index)) return true;
  if (TypeRefArgHasMemberAccess(e->condition)) return true;
  if (TypeRefArgHasMemberAccess(e->true_expr)) return true;
  if (TypeRefArgHasMemberAccess(e->false_expr)) return true;
  for (const auto* elem : e->elements) {
    if (TypeRefArgHasMemberAccess(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (TypeRefArgHasMemberAccess(arg)) return true;
  }
  return false;
}

// True when this node is itself a select on a dynamic object; the recursive
// descent into children is handled separately by the caller. Dynamic arrays,
// queues, and associative arrays are all variable-size (dynamic) objects, so a
// select into any of them is a reference to an element of a dynamic object.
static bool TypeRefArgSelectsDynamicElement(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        array_info) {
  if (e->kind != ExprKind::kSelect || !e->base ||
      e->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto it = array_info.find(e->base->text);
  return it != array_info.end() &&
         (it->second.is_dynamic || it->second.is_assoc || it->second.is_queue);
}

bool ElaboratorOperationRules::TypeRefArgUsesDynamicElement(
    const Expr* e) const {
  if (!e) return false;
  if (TypeRefArgSelectsDynamicElement(e, var_array_info_)) return true;
  const Expr* const kChildren[] = {e->lhs,       e->rhs,       e->base,
                                   e->index,     e->condition, e->true_expr,
                                   e->false_expr};
  for (const Expr* child : kChildren) {
    if (TypeRefArgUsesDynamicElement(child)) return true;
  }
  for (const auto* elem : e->elements) {
    if (TypeRefArgUsesDynamicElement(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (TypeRefArgUsesDynamicElement(arg)) return true;
  }
  return false;
}

void ElaboratorOperationRules::CheckTypeRefArgInner(const Expr* inner,
                                                    SourceLoc loc) {
  if (!inner) return;
  if (TypeRefArgHasMemberAccess(inner)) {
    diag_.Error(loc,
                "type operator argument shall not contain a hierarchical "
                "reference",
                Subclause("6.23"));
    return;
  }
  if (TypeRefArgUsesDynamicElement(inner)) {
    diag_.Error(loc,
                "type operator argument shall not reference elements of "
                "dynamic objects",
                Subclause("6.23"));
  }
}

void ElaboratorOperationRules::WalkExprForTypeRefArg(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kTypeRef) {
    CheckTypeRefArgInner(expr->lhs, expr->range.start);
  }
  WalkExprForTypeRefArg(expr->lhs);
  WalkExprForTypeRefArg(expr->rhs);
  WalkExprForTypeRefArg(expr->condition);
  WalkExprForTypeRefArg(expr->true_expr);
  WalkExprForTypeRefArg(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForTypeRefArg(elem);
  for (auto* arg : expr->args) WalkExprForTypeRefArg(arg);
}

void ElaboratorOperationRules::WalkStmtsForTypeRefArg(const Stmt* s) {
  if (!s) return;
  WalkExprForTypeRefArg(s->lhs);
  WalkExprForTypeRefArg(s->rhs);
  WalkExprForTypeRefArg(s->expr);
  WalkExprForTypeRefArg(s->condition);
  WalkExprForTypeRefArg(s->assert_expr);
  if (s->var_decl_type.type_ref_expr) {
    CheckTypeRefArgInner(s->var_decl_type.type_ref_expr, s->range.start);
  }
  // §6.23 bars a hierarchical reference and a reference to an element of a
  // dynamic object from the operand of the type operator wherever the operator
  // is written, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names. It wrote out six of the thirteen, so
  // `type(d[0])` on a dynamic array `d` went unreported in a fork arm and in a
  // for-loop step.
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForTypeRefArg(sub); });
}

void ElaboratorOperationRules::ValidateTypeRefArgs(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->data_type.type_ref_expr) {
      CheckTypeRefArgInner(item->data_type.type_ref_expr, item->loc);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForTypeRefArg(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForTypeRefArg(item->assign_rhs);
    }
  }
}

// After the tagged keyword the BNF allows only a member identifier drawn from
// the target tagged union type. Given the name of a variable whose typedef is a
// tagged union, reject a tag name that is not declared in that union. Shared by
// the assignment-target and declaration-initializer positions, both of which
// supply the expression type from the target variable's declared type.
void ElaboratorOperationRules::CheckTaggedMemberName(std::string_view var_name,
                                                     const Expr* rhs) {
  if (!rhs || rhs->kind != ExprKind::kTagged) return;
  if (!rhs->rhs || rhs->rhs->kind != ExprKind::kIdentifier) return;

  auto vit = var_named_types_.find(var_name);
  if (vit == var_named_types_.end()) return;

  auto tit = typedefs_.find(vit->second);
  if (tit == typedefs_.end()) return;

  const auto& dt = tit->second;
  if (dt.kind != DataTypeKind::kUnion || !dt.is_tagged) return;

  auto tag_name = rhs->rhs->text;
  for (const auto& m : dt.struct_members) {
    if (m.name == tag_name) return;
  }

  diag_.Error(rhs->range.start,
              std::format("tagged union '{}' has no member named '{}'",
                          vit->second, tag_name),
              Subclause("11.9"));
}

void ElaboratorOperationRules::CheckTaggedExprMember(const Expr* lhs,
                                                     const Expr* rhs) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier) return;
  CheckTaggedMemberName(lhs->text, rhs);
}

void ElaboratorOperationRules::WalkStmtsForTaggedExpr(const Stmt* s) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->rhs) {
    CheckTaggedExprMember(s->lhs, s->rhs);
  }
  // §11.9, which §7.3.2 defers the rule to, requires the name after `tagged` to
  // be a member of the target's tagged union type, and neither clause
  // conditions that on the statement the assignment stands in, so this descends
  // every link ForEachChildStmt in elaborator_validate_internal.h names. It
  // wrote out six of the thirteen, so `u = tagged Bogus 1;` written as a fork
  // arm or as an immediate assertion's pass action named a member that does not
  // exist and was accepted.
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForTaggedExpr(sub); });
}

void ElaboratorOperationRules::ValidateTaggedUnionMembers(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    // §11.9: a declaration initializer is another position where the tagged
    // expression's type is known (from the declared variable), so the member
    // name after `tagged` must name a member of that union.
    if (item->kind == ModuleItemKind::kVarDecl && item->init_expr) {
      CheckTaggedMemberName(item->name, item->init_expr);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForTaggedExpr(item->body);
    }
  }
}

static bool IsRealVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && IsRealType(it->second);
}

static bool IsIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:

    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:

    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:

    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:

    case TokenKind::kPercent:
      return true;
    default:
      return false;
  }
}

static bool IsUnaryIllegalOnReal(TokenKind op) {
  switch (op) {
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

void ElaboratorOperationRules::WalkExprForRealOps(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kBinary) {
    bool lhs_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    bool rhs_real = expr->rhs && IsRealVar(expr->rhs, var_types_);
    if ((lhs_real || rhs_real) && IsIllegalOnReal(expr->op)) {
      // §11.3.1 states its rule as Table 11-1, which admits or bars each
      // operator separately, so the report names the operator it barred.
      // TokenKindName in src/lexer/keywords.cpp answers with the source
      // spelling the table lists, already quoted.
      //
      // The form is named too, because `&`, `|`, `^`, `~^` and `^~` are each
      // both a binary and a unary operator, and the spelling alone leaves the
      // reader to work out which reading the elaborator took.
      diag_.Error(expr->range.start,
                  std::format("binary operator {} is not allowed on real "
                              "operands",
                              TokenKindName(expr->op)),
                  Subclause("11.3.1"));
    }
  }
  if (expr->kind == ExprKind::kUnary) {
    bool operand_real = expr->lhs && IsRealVar(expr->lhs, var_types_);
    if (operand_real && IsUnaryIllegalOnReal(expr->op)) {
      diag_.Error(expr->range.start,
                  std::format("unary operator {} is not allowed on real "
                              "operands",
                              TokenKindName(expr->op)),
                  Subclause("11.3.1"));
    }
  }
  WalkExprForRealOps(expr->lhs);
  WalkExprForRealOps(expr->rhs);
  WalkExprForRealOps(expr->condition);
  WalkExprForRealOps(expr->true_expr);
  WalkExprForRealOps(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForRealOps(elem);
  for (auto* arg : expr->args) WalkExprForRealOps(arg);
}

void ElaboratorOperationRules::WalkStmtsForRealOps(const Stmt* s) {
  if (!s) return;
  WalkExprForRealOps(s->rhs);
  WalkExprForRealOps(s->lhs);
  WalkExprForRealOps(s->expr);
  WalkExprForRealOps(s->condition);
  WalkExprForRealOps(s->assert_expr);
  // §11.3.1's Table 11-1 decides which operators a real operand admits and
  // names no statement the table is suspended in, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names. It wrote out six
  // of the thirteen, so `c = a & b;` on real `a` and `b` was reported in a
  // begin-end block and accepted in a fork arm or a for-loop step.
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmtsForRealOps(sub); });
}

void ElaboratorOperationRules::ValidateRealOperatorRestrictions(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForRealOps(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_rhs) {
      WalkExprForRealOps(item->assign_rhs);
    }
  }
}

namespace {

// §6.24.1: a numeric size cast writes its target width as a constant_primary --
// an integer literal, a constant parameter, or a constant expression -- rather
// than a named type. The parser records these in the "node cast" form: the
// width expression is carried in rhs and the value being cast in lhs, leaving
// the type-name text empty. A cast that names a type (int', signed', or a
// user-defined type) sets the text field, and a cast whose operand is an
// assignment pattern (type'{...}) or whose casting type is a type reference is
// not a size cast either. Membership here is provisional: only a rhs that
// actually evaluates to a constant integer is treated as a size.
bool IsSizeCastForm(const Expr* cast) {
  return cast->text.empty() && cast->rhs != nullptr && cast->lhs != nullptr &&
         cast->lhs->kind != ExprKind::kAssignmentPattern &&
         cast->rhs->kind != ExprKind::kTypeRef;
}

// §6.24.1: signed'() and unsigned'() change only the signedness of the operand.
bool IsSigningCast(const Expr* cast) {
  return cast->text == "signed" || cast->text == "unsigned";
}

// §11.7: $signed() and $unsigned() are the system-function spelling of the same
// signedness change the signing cast writes, and the parser records a call to
// either one as a kSystemCall whose callee carries the leading '$'.
bool IsSigningSystemCall(const Expr* call) {
  return call->kind == ExprKind::kSystemCall &&
         (call->callee == "$signed" || call->callee == "$unsigned");
}

}  // namespace

// §6.24.1: a real value has no bit representation of its own, so the two casts
// that reinterpret an operand as a packed vector -- the size cast and the
// signing cast -- require an integral operand. A real variable or a real
// literal used directly as such an operand is rejected here at elaboration.
//
// A time literal is one of those real operands. §5.8 interprets it as a
// realtime value scaled to the current time unit, so 2.1ns is a real value and
// not a value of the type named time, which §6.11 defines as a 64-bit integral
// type. That reading is what this test used to have, admitting kRealLiteral
// alone and letting signed'(2.1ns), 8'(2.1ns) and $signed(2.1ns) through while
// the same conversions applied to a realtime variable were rejected.
bool ElaboratorOperationRules::CastOperandIsReal(const Expr* operand) const {
  if (!operand) return false;
  if (operand->kind == ExprKind::kRealLiteral ||
      operand->kind == ExprKind::kTimeLiteral) {
    return true;
  }
  return IsRealVar(operand, var_types_);
}

// §11.7: $signed and $unsigned shall return a one-dimensional packed array with
// the same number of bits and value as the input expression, so the input has
// to have bits to return and a real argument has none. The argument is rejected
// here by CastOperandIsReal, the same test the signing cast uses, which states
// above it which operands count as real.
//
// This spelling cites §11.7 and the cast spelling cites §6.24.1 because each
// clause states the requirement for the syntax it defines; §11.7 is what makes
// the two one conversion, defining these functions in terms of the signedness
// the cast applies. Left unreported, the argument reaches EvalSignCast in
// src/simulator/eval_systask.cpp, which sets is_signed on the real value it
// evaluated, and the result claims to be both a real and a signed integer.
void ElaboratorOperationRules::CheckSigningSystemCallExpr(const Expr* expr) {
  if (!expr || !IsSigningSystemCall(expr) || expr->args.empty()) return;
  if (!CastOperandIsReal(expr->args.front())) return;
  diag_.Error(expr->range.start,
              std::format("expression inside {} shall be an integral value",
                          expr->callee),
              Subclause("11.7"));
}

void ElaboratorOperationRules::CheckCastExpr(const Expr* expr) {
  // §11.7's system-function spelling of the signing conversion is checked from
  // here because WalkExprForCast in
  // src/elaborator/elaborator_validate_cast_ops.cpp visits every expression and
  // calls only this member, and the early return below drops every node that is
  // not a cast.
  CheckSigningSystemCallExpr(expr);
  if (!expr || expr->kind != ExprKind::kCast) return;

  if (IsSizeCastForm(expr)) {
    // A confirmed numeric size cast: the casting type evaluates to a constant
    // integer. If it does not evaluate here, the rhs may name a type or an
    // unresolved parameter, so no size rule is applied.
    auto size = ConstEvalInt(expr->rhs);
    if (size) {
      // §6.24.1: the size specified by a constant-expression casting type shall
      // be positive; a zero or negative size is an error.
      if (*size <= 0) {
        diag_.Error(expr->range.start,
                    "size cast target width must be a positive constant",
                    Subclause("6.24.1"));
      } else if (CastOperandIsReal(expr->lhs)) {
        // §6.24.1: the expression inside a size cast shall be integral.
        diag_.Error(expr->range.start,
                    "expression inside a size cast shall be an integral value",
                    Subclause("6.24.1"));
      }
    }
  } else if (IsSigningCast(expr) && CastOperandIsReal(expr->lhs)) {
    // §6.24.1: the expression inside a signing cast shall be integral.
    diag_.Error(expr->range.start,
                "expression inside a signing cast shall be an integral value",
                Subclause("6.24.1"));
  }
}

}  // namespace delta
