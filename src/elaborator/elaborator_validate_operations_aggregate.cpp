#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// The type `dtype` stands for at the end of its chain of typedefs, or null
// where a name on the way stands for nothing the table holds.
static const DataType* EndOfTypedefChain(const DataType& dtype,
                                         const TypedefMap& typedefs) {
  const DataType* d = &dtype;
  for (int hops = 0; hops < 16 && d->kind == DataTypeKind::kNamed; ++hops) {
    auto it = typedefs.find(d->type_name);
    if (it == typedefs.end()) return nullptr;
    d = &it->second;
  }
  return d->kind == DataTypeKind::kNamed ? nullptr : d;
}

static bool IsUnpackedStructOrUnion(const DataType* d) {
  return d != nullptr && !d->is_packed &&
         (d->kind == DataTypeKind::kStruct || d->kind == DataTypeKind::kUnion);
}

// §11.3 and §11.4.13: the variables of a module an operator is asked to take
// as a whole when it takes no aggregate -- those of an unpacked structure or
// union type, declared in place or through a name standing for one.
static std::unordered_set<std::string_view> UnpackedStructVars(
    const ModuleDecl* decl, const TypedefMap& typedefs) {
  std::unordered_set<std::string_view> names;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl || !item->unpacked_dims.empty())
      continue;
    if (IsUnpackedStructOrUnion(EndOfTypedefChain(item->data_type, typedefs)))
      names.insert(item->name);
  }
  return names;
}

namespace {

// The names an aggregate-operand check tells apart: the unpacked structures
// and unions, and the arrays of every kind (VarArrayInfo).
struct AggregateOperandNames {
  const std::unordered_set<std::string_view>& structs;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>& arrays;
};

// §11.3's Table 11-1: the operators whose operands are integral or real
// alone -- arithmetic, bitwise, logical, relational, shift, implication and
// equivalence, reduction and increment -- which an unpacked structure or union
// is not. The equality and case equality operators, `?:`, the assignments and
// `matches` (§12.6) take one, and are left out.
bool TakesIntegralOrRealOperands(TokenKind op) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kPower:
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTilde:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
    case TokenKind::kAmpAmp:
    case TokenKind::kPipePipe:
    case TokenKind::kBang:
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kLtEq:
    case TokenKind::kGtEq:
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
    case TokenKind::kPlusPlus:
    case TokenKind::kMinusMinus:
    case TokenKind::kArrow:
    case TokenKind::kLtDashGt:
      return true;
    default:
      return false;
  }
}

bool NamesIn(const Expr* e, const std::unordered_set<std::string_view>& set) {
  return e != nullptr && e->kind == ExprKind::kIdentifier &&
         set.count(e->text) != 0;
}

// §7.4.6: whether `e` is an unpacked array as a whole -- one `arrays` holds,
// named bare, a slice of one, or a select of one indexing fewer of its
// unpacked dimensions than it declares, `m[1]` of `int m[2][3]`. An
// associative array is left to CheckAssocOperandInBinaryExpr.
bool IsUnpackedArrayOperand(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        arrays) {
  uint32_t selects = 0;
  bool is_slice = e->kind == ExprKind::kSelect && e->index_end != nullptr;
  const Expr* base = e;
  for (; base->kind == ExprKind::kSelect && base->base != nullptr;
       base = base->base)
    ++selects;
  if (base->kind != ExprKind::kIdentifier) return false;
  auto it = arrays.find(base->text);
  if (it == arrays.end() || it->second.is_assoc) return false;
  uint32_t dims = it->second.num_unpacked_dims;
  return selects < dims || (is_slice && selects == dims);
}

// §7.4.6: whether `e` is plainly an integral value -- a number, or the result
// of an operator that takes and gives integral values.
bool IsIntegralOperand(const Expr* e) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
      return true;
    case ExprKind::kBinary:
    case ExprKind::kUnary:
      return TakesIntegralOrRealOperands(e->op);
    default:
      return false;
  }
}

bool IsEqualityOperator(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

// §7.4.6: an unpacked array is compared only with another array, so an
// equality whose one operand is an unpacked array and whose other is an
// integral value is an error, reported at the array.
void CheckUnpackedArrayComparison(const Expr* e, const AggregateOperandNames& n,
                                  DiagEngine& diag) {
  if (e->lhs == nullptr || e->rhs == nullptr) return;
  for (auto [array, other] :
       {std::pair{e->lhs, e->rhs}, std::pair{e->rhs, e->lhs}}) {
    if (IsUnpackedArrayOperand(array, n.arrays) && IsIntegralOperand(other)) {
      diag.Error(array->range.start,
                 "an unpacked array is compared only with another unpacked "
                 "array",
                 Subclause("7.4.6"));
    }
  }
}

// §7.4.6: an unpacked array is compared only with another array
// (CheckUnpackedArrayComparison), and is not treated as an integer by an
// operator TakesIntegralOrRealOperands lists.
void CheckUnpackedArrayOperand(const Expr* e, const AggregateOperandNames& n,
                               DiagEngine& diag) {
  bool binary = e->kind == ExprKind::kBinary;
  if (binary && IsEqualityOperator(e->op)) {
    CheckUnpackedArrayComparison(e, n, diag);
    return;
  }
  if ((!binary && e->kind != ExprKind::kUnary) ||
      !TakesIntegralOrRealOperands(e->op))
    return;
  for (const Expr* side : {e->lhs, binary ? e->rhs : nullptr}) {
    if (side == nullptr || !IsUnpackedArrayOperand(side, n.arrays)) continue;
    diag.Error(side->range.start,
               "an unpacked array is not an operand of this operator",
               Subclause("7.4.6"));
  }
}

// §11.4.13 makes the left operand of `inside` singular, which neither an
// unpacked array nor an unpacked structure is; §11.3's Table 11-1 keeps an
// unpacked structure or union out of the operators TakesIntegralOrRealOperands
// lists, and §7.4.6 an unpacked array (CheckUnpackedArrayOperand).
void CheckAggregateOperandNode(const Expr* e, const AggregateOperandNames& n,
                               DiagEngine& diag) {
  CheckUnpackedArrayOperand(e, n, diag);
  if (e->kind == ExprKind::kInside && e->lhs != nullptr &&
      e->lhs->kind == ExprKind::kIdentifier &&
      (n.arrays.count(e->lhs->text) != 0 || n.structs.count(e->lhs->text))) {
    diag.Error(e->lhs->range.start,
               "the left operand of inside shall be singular",
               Subclause("11.4.13"));
    return;
  }
  bool binary = e->kind == ExprKind::kBinary;
  if ((!binary && e->kind != ExprKind::kUnary) ||
      !TakesIntegralOrRealOperands(e->op))
    return;
  for (const Expr* side : {e->lhs, binary ? e->rhs : nullptr}) {
    if (!NamesIn(side, n.structs)) continue;
    diag.Error(
        side->range.start,
        "an unpacked structure or union is not an operand of this operator",
        Subclause("11.3"));
  }
}

void WalkExprForAggregateOperands(const Expr* e, const AggregateOperandNames& n,
                                  DiagEngine& diag) {
  if (e == nullptr) return;
  CheckAggregateOperandNode(e, n, diag);
  ForEachExprChild(e, [&](const Expr* child) {
    WalkExprForAggregateOperands(child, n, diag);
  });
}

// §11.3 and §11.4.13 name no statement their rules are suspended in, so every
// position ForEachChildExpr and ForEachChildStmt name is walked.
void WalkStmtForAggregateOperands(const Stmt* s, const AggregateOperandNames& n,
                                  DiagEngine& diag) {
  if (s == nullptr) return;
  ForEachChildExpr(
      s, [&](Expr* const& e) { WalkExprForAggregateOperands(e, n, diag); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtForAggregateOperands(sub, n, diag); });
}

}  // namespace

void ElaboratorOperationRules::ValidateAggregateOperands(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> structs =
      UnpackedStructVars(decl, typedefs_);
  AggregateOperandNames names{structs, var_array_info_};
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtForAggregateOperands(item->body, names, diag_);
    if (item->kind == ModuleItemKind::kContAssign)
      WalkExprForAggregateOperands(item->assign_rhs, names, diag_);
  }
}

}  // namespace delta
