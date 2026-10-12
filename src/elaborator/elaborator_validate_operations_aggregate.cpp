#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_helpers.h"
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

std::unordered_set<std::string_view> UnpackedStructVars(
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

// The type tables a declaration is classified against: the typedefs, those of
// them naming an unpacked array (§6.18), and the classes.
struct DeclarationTypes {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregate_typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

// §7.4.6: what a name stands for to the unpacked-array checks, as the module
// or the innermost block declaring it declares it -- an unpacked array of
// `unpacked_dims` dimensions, associative or not, or a variable of an integral
// type. A name that is neither is another kind of variable.
struct DeclaredName {
  uint32_t unpacked_dims = 0;
  bool is_assoc = false;
  bool is_integral = false;
};

using DeclaredNames = std::unordered_map<std::string_view, DeclaredName>;

// The names an aggregate-operand check tells apart: the unpacked structures
// and unions with their types, and every name in scope (DeclaredNames), the
// module's arrays of every kind among them.
struct AggregateOperandNames {
  const std::unordered_set<std::string_view>& structs;
  // The type each of `structs` is declared with, at the end of its typedef
  // chain.
  const std::unordered_map<std::string_view, const DataType*>& struct_types;
  const DeclaredNames& declared;
  const DeclarationTypes& types;
};

// §6.11.1: whether a variable or net of `dtype` is integral -- of an integer
// type, an enum, a packed structure or union, or a net type's implicit logic
// (§6.7.1), directly or through typedef names, none of which names an unpacked
// array. An interconnect net (§6.6.8) has no data type.
bool IsIntegralDeclaredType(const DataType& dtype, const DeclarationTypes& t) {
  if (dtype.is_interconnect) return false;
  if (IsNetTypeKind(dtype.kind)) return true;
  const DataType* d = &dtype;
  for (int hops = 0; hops < 16 && d->kind == DataTypeKind::kNamed; ++hops) {
    if (t.aggregate_typedefs.count(d->type_name) != 0) return false;
    auto it = t.typedefs.find(d->type_name);
    if (it == t.typedefs.end()) return false;
    d = &it->second;
  }
  if (d->kind == DataTypeKind::kStruct || d->kind == DataTypeKind::kUnion)
    return d->is_packed;
  return IsIntegralType(d->kind);
}

// §7.8: an unpacked dimension whose index is a data type or `*` declares an
// associative array. The integral index types §7.8.4 lists, `string` (§7.8.2)
// and a class (§7.8.3) are named directly; a typedef names any other.
bool IsAssocDimension(const Expr* dim, const DeclarationTypes& t) {
  if (dim == nullptr || dim->kind != ExprKind::kIdentifier) return false;
  std::string_view s = dim->text;
  return s == "*" || s == "string" || s == "int" || s == "integer" ||
         s == "byte" || s == "shortint" || s == "longint" || s == "bit" ||
         s == "logic" || s == "reg" || s == "time" ||
         t.typedefs.count(s) != 0 || t.class_names.count(s) != 0;
}

// The module's names: its arrays, as VarArrayInfo describes them, and its
// variables and nets of an integral type.
DeclaredNames ModuleDeclaredNames(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        arrays,
    const DeclarationTypes& t) {
  DeclaredNames names;
  for (const auto* item : decl->items) {
    bool declares = item->kind == ModuleItemKind::kVarDecl ||
                    item->kind == ModuleItemKind::kNetDecl;
    if (declares && item->unpacked_dims.empty() &&
        IsIntegralDeclaredType(item->data_type, t))
      names[item->name].is_integral = true;
  }
  for (const auto& [name, info] : arrays)
    names[name] = DeclaredName{info.num_unpacked_dims, info.is_assoc, false};
  return names;
}

// One variable a block declares, which hides any outer one of its name.
struct BlockDeclaration {
  std::string_view name;
  const DataType& type;
  const std::vector<Expr*>& unpacked_dims;
};

void DeclareBlockName(const BlockDeclaration& d, const DeclarationTypes& t,
                      DeclaredNames& names) {
  DeclaredName name;
  name.unpacked_dims = static_cast<uint32_t>(d.unpacked_dims.size());
  if (name.unpacked_dims == 0)
    name.is_integral = IsIntegralDeclaredType(d.type, t);
  else
    name.is_assoc = IsAssocDimension(d.unpacked_dims[0], t);
  names[d.name] = name;
}

// A.2.8's block_item_declaration and A.6.8's for_variable_declaration: each
// variable a begin-end block or a fork declares, as a kVarDecl statement, or a
// for loop's initialization declares, as an assignment whose for_init_types
// entry is a type, which the statements under it see in place of the enclosing
// scope's name of the same spelling.
template <typename Visit>
void ForEachBlockDeclaration(const Stmt* s, Visit visit) {
  for (const auto* list : {&s->stmts, &s->fork_stmts}) {
    for (const Stmt* sub : *list) {
      if (sub == nullptr || sub->kind != StmtKind::kVarDecl) continue;
      visit(BlockDeclaration{sub->var_name, sub->var_decl_type,
                             sub->var_unpacked_dims});
    }
  }
  static const std::vector<Expr*> kNoDims;
  for (size_t k = 0; k < s->for_inits.size() && k < s->for_init_types.size();
       ++k) {
    const Stmt* init = s->for_inits[k];
    if (s->for_init_types[k].kind == DataTypeKind::kImplicit ||
        init->lhs == nullptr || init->lhs->kind != ExprKind::kIdentifier)
      continue;
    visit(BlockDeclaration{init->lhs->text, s->for_init_types[k], kNoDims});
  }
}

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

// §7.4.6: the unpacked array `e` is as a whole, or null where it is none -- a
// name standing for one, a slice of one, or a select of one indexing fewer of
// its unpacked dimensions than it declares, `m[1]` of `int m[2][3]`.
const DeclaredName* UnpackedArrayOperand(const Expr* e,
                                         const DeclaredNames& declared) {
  uint32_t selects = 0;
  bool is_slice = e->kind == ExprKind::kSelect && e->index_end != nullptr;
  const Expr* base = e;
  for (; base->kind == ExprKind::kSelect && base->base != nullptr;
       base = base->base)
    ++selects;
  if (base->kind != ExprKind::kIdentifier) return nullptr;
  auto it = declared.find(base->text);
  if (it == declared.end()) return nullptr;
  uint32_t dims = it->second.unpacked_dims;
  bool whole = selects < dims || (is_slice && selects == dims);
  return whole ? &it->second : nullptr;
}

// §11.4.5 and §11.4.6: the equality, case equality and wildcard equality
// operators, each giving a 1-bit result.
bool IsEqualityOperator(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

// §7.4.6: whether `e` is plainly an integral value -- a number, a variable of
// an integral type, or the result of an operator that gives an integral value:
// one that takes integral operands, or an equality.
bool IsIntegralOperand(const Expr* e, const DeclaredNames& declared) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
      return true;
    case ExprKind::kIdentifier: {
      auto it = declared.find(e->text);
      return it != declared.end() && it->second.is_integral;
    }
    case ExprKind::kBinary:
      return TakesIntegralOrRealOperands(e->op) || IsEqualityOperator(e->op);
    case ExprKind::kUnary:
      return TakesIntegralOrRealOperands(e->op);
    default:
      return false;
  }
}

// §7.4.6: an unpacked array, an associative one among them, is compared only
// with another array, so an equality whose one operand is an unpacked array
// and whose other is an integral value is an error, reported at the array.
void CheckUnpackedArrayComparison(const Expr* e, const AggregateOperandNames& n,
                                  DiagEngine& diag) {
  if (e->lhs == nullptr || e->rhs == nullptr) return;
  for (auto [array, other] :
       {std::pair{e->lhs, e->rhs}, std::pair{e->rhs, e->lhs}}) {
    if (UnpackedArrayOperand(array, n.declared) != nullptr &&
        IsIntegralOperand(other, n.declared)) {
      diag.Error(array->range.start,
                 "an unpacked array is compared only with another unpacked "
                 "array",
                 Subclause("7.4.6"));
    }
  }
}

// §7.4.6: an unpacked array is compared only with another array
// (CheckUnpackedArrayComparison), and is not treated as an integer by an
// operator TakesIntegralOrRealOperands lists. An associative array, which
// §7.4.6 lets be read, written and compared as a whole, is to be selected down
// to an element first.
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
    const DeclaredName* array =
        side == nullptr ? nullptr : UnpackedArrayOperand(side, n.declared);
    if (array == nullptr) continue;
    diag.Error(side->range.start,
               array->is_assoc
                   ? "associative array operand requires an element "
                     "selection before use in this expression"
                   : "an unpacked array is not an operand of this operator",
               Subclause("7.4.6"));
  }
}

// §11.4.13 with §7.2: whether `e` selects, of one of the module's unpacked
// structures or unions, a member that is no singular value -- one declared with
// an unpacked dimension, or one of an unpacked structure or union type,
// written in place or through a typedef.
bool IsUnpackedMemberOperand(const Expr* e, const AggregateOperandNames& n) {
  if (e->kind != ExprKind::kMemberAccess || !NamesIn(e->lhs, n.structs))
    return false;
  const auto& members = n.struct_types.at(e->lhs->text)->struct_members;
  auto member = std::ranges::find(members, e->rhs->text, &StructMember::name);
  if (member == members.end()) return false;
  if (!member->unpacked_dims.empty()) return true;
  return IsUnpackedStructOrUnion(
      member->nested_type != nullptr
          ? member->nested_type
          : MemberNamedType(*member, n.types.typedefs));
}

// §11.4.11 (printed page 286): a conditional whose operands are neither
// integral, real nor class handles takes two of equivalent types (§6.22.2),
// which two unpacked structures declared through different typedefs are not.
void CheckConditionalStructOperands(const Expr* e,
                                    const AggregateOperandNames& n,
                                    DiagEngine& diag) {
  if (e->kind != ExprKind::kTernary || !NamesIn(e->true_expr, n.structs) ||
      !NamesIn(e->false_expr, n.structs) ||
      TypesEquivalent(*n.struct_types.at(e->true_expr->text),
                      *n.struct_types.at(e->false_expr->text)))
    return;
  diag.Error(e->range.start,
             "the operands of a conditional operator shall be of equivalent "
             "types",
             Subclause("11.4.11"));
}

// §11.4.13 makes the left operand of `inside` singular, which neither an
// unpacked array -- a name standing for one, or a select leaving one of its
// unpacked dimensions -- nor an unpacked structure, nor such a member of one
// is; §11.3's Table 11-1 keeps an
// unpacked structure or union out of the operators TakesIntegralOrRealOperands
// lists, and §7.4.6 an unpacked array (CheckUnpackedArrayOperand).
void CheckAggregateOperandNode(const Expr* e, const AggregateOperandNames& n,
                               DiagEngine& diag) {
  CheckUnpackedArrayOperand(e, n, diag);
  CheckConditionalStructOperands(e, n, diag);
  if (e->kind == ExprKind::kInside && e->lhs != nullptr &&
      (UnpackedArrayOperand(e->lhs, n.declared) != nullptr ||
       NamesIn(e->lhs, n.structs) || IsUnpackedMemberOperand(e->lhs, n))) {
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

// §10.9 gives an assignment pattern written without a type prefix no type of
// its own, §10.8 lists the assignment-like contexts that lend it one and allows
// no other, and §5.10 and §5.11 require a structure or array literal to have a
// type. An operator's operand and a system task's or function's argument are
// no such context, so a pattern there is reported. The right operand of
// `matches` and the left of a case item's `&&&` are §12.6 patterns, which share
// the spelling.
void ReportUntypedPattern(const Expr* operand, DiagEngine& diag) {
  if (operand == nullptr || operand->kind != ExprKind::kAssignmentPattern)
    return;
  diag.Error(operand->range.start,
             "assignment pattern without a type prefix outside an "
             "assignment-like context",
             Subclause("10.9"));
}

void CheckUntypedPatternOperand(const Expr* e, DiagEngine& diag) {
  std::vector<const Expr*> operands;
  bool is_pattern_operator =
      e->op == TokenKind::kKwMatches || e->op == TokenKind::kAmpAmpAmp;
  if (e->kind == ExprKind::kUnary ||
      (e->kind == ExprKind::kBinary && !is_pattern_operator)) {
    operands = {e->lhs, e->rhs};
  } else if (e->kind == ExprKind::kSystemCall ||
             e->kind == ExprKind::kConcatenation) {
    // §10.10.1 (printed page 265) asks a self-determined type of each item of
    // an unpacked array concatenation, and §11.4.12 of each operand of a
    // vector concatenation, which an untyped pattern does not have.
    const std::vector<Expr*>& list =
        e->kind == ExprKind::kSystemCall ? e->args : e->elements;
    operands.assign(list.begin(), list.end());
  } else if (e->kind == ExprKind::kTernary) {
    operands = {e->condition};
  } else if (e->kind == ExprKind::kSelect) {
    operands = {e->index, e->index_end};
  }
  for (const Expr* operand : operands) ReportUntypedPattern(operand, diag);
}

void WalkExprForAggregateOperands(const Expr* e, const AggregateOperandNames& n,
                                  DiagEngine& diag) {
  if (e == nullptr) return;
  CheckAggregateOperandNode(e, n, diag);
  CheckUntypedPatternOperand(e, diag);
  ForEachExprChild(e, [&](const Expr* child) {
    WalkExprForAggregateOperands(child, n, diag);
  });
}

void WalkStmtForAggregateOperands(const Stmt* s, const AggregateOperandNames& n,
                                  DiagEngine& diag);

// §11.3 and §11.4.13 name no statement their rules are suspended in, so every
// position ForEachChildExpr and ForEachChildStmt name is walked.
void WalkStmtChildrenForAggregateOperands(const Stmt* s,
                                          const AggregateOperandNames& n,
                                          DiagEngine& diag) {
  // A statement's condition is no assignment-like context either (§10.8).
  ReportUntypedPattern(s->condition, diag);
  ForEachChildExpr(
      s, [&](Expr* const& e) { WalkExprForAggregateOperands(e, n, diag); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtForAggregateOperands(sub, n, diag); });
}

// A statement that declares variables (ForEachBlockDeclaration) opens a scope,
// whose names the statements under it see in place of the enclosing ones.
void WalkStmtForAggregateOperands(const Stmt* s, const AggregateOperandNames& n,
                                  DiagEngine& diag) {
  if (s == nullptr) return;
  bool declares = false;
  ForEachBlockDeclaration(s, [&](const BlockDeclaration&) { declares = true; });
  if (!declares) {
    WalkStmtChildrenForAggregateOperands(s, n, diag);
    return;
  }
  DeclaredNames inner = n.declared;
  ForEachBlockDeclaration(s, [&](const BlockDeclaration& d) {
    DeclareBlockName(d, n.types, inner);
  });
  AggregateOperandNames scoped{n.structs, n.struct_types, inner, n.types};
  WalkStmtChildrenForAggregateOperands(s, scoped, diag);
}

}  // namespace

void ElaboratorOperationRules::ValidateAggregateOperands(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> structs =
      UnpackedStructVars(decl, typedefs_);
  DeclarationTypes types{typedefs_, aggregate_typedef_names_, class_names_};
  DeclaredNames declared = ModuleDeclaredNames(decl, var_array_info_, types);
  std::unordered_map<std::string_view, const DataType*> struct_types;
  for (const auto* item : decl->items) {
    if (structs.contains(item->name))
      struct_types[item->name] = EndOfTypedefChain(item->data_type, typedefs_);
  }
  AggregateOperandNames names{structs, struct_types, declared, types};
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtForAggregateOperands(item->body, names, diag_);
    if (item->kind == ModuleItemKind::kContAssign)
      WalkExprForAggregateOperands(item->assign_rhs, names, diag_);
  }
}

namespace {

// §7.4.6: the number of elements a slice of an unpacked array selects, from
// its two constant bounds or the width of an indexed form; empty where those do
// not fold.
std::optional<int64_t> SliceLength(const Expr* slice) {
  if (slice->is_part_select_plus || slice->is_part_select_minus)
    return ConstEvalInt(slice->index_end);
  auto last = ConstEvalInt(slice->index_end);
  return ConstEvalInt(slice->index).and_then([&last](int64_t first) {
    return last.transform(
        [first](int64_t end) { return std::abs(first - end) + 1; });
  });
}

// What §6.22.2 compares of an unpacked array operand: its declaration's
// record, which carries the element type and the kind of array, and the size
// of each unpacked dimension, the first being a slice's own length.
struct ArrayOperandShape {
  const ElaboratorData::VarArrayInfo* info;
  std::vector<std::optional<uint32_t>> dims;
};

std::optional<ArrayOperandShape> ArrayOperandShapeOf(
    const Expr* e,
    const std::unordered_map<std::string_view, ElaboratorData::VarArrayInfo>&
        arrays) {
  const bool kSlice = e->kind == ExprKind::kSelect && e->index_end != nullptr;
  auto it = arrays.find(ExprIdent(kSlice ? e->base : e));
  if (it == arrays.end()) return std::nullopt;
  ArrayOperandShape shape{&it->second, it->second.unpacked_shape};
  if (!kSlice) return shape;
  shape.dims.resize(std::max<size_t>(shape.dims.size(), 1));
  return SliceLength(e).transform([&shape](int64_t length) {
    shape.dims[0] = static_cast<uint32_t>(length);
    return shape;
  });
}

ElementTypeInfo ElementOf(const ElaboratorData::VarArrayInfo& info) {
  return {info.elem_type, info.elem_width, info.elem_is_signed,
          info.elem_is_4state, info.elem_type_name};
}

}  // namespace

// §6.22.2 (printed page 133): two unpacked fixed-size arrays are equivalent
// when their element types are and they have the same shape, the same number
// of elements in each unpacked dimension; dynamic arrays, queues and
// associative arrays when they are the same kind of array, an associative one
// with an equivalent index type, and their element types are equivalent.
std::optional<bool> ElaboratorOperationRules::ArrayOperandsEquivalent(
    const Expr* lhs, const Expr* rhs) const {
  auto l = ArrayOperandShapeOf(lhs, var_array_info_);
  auto r = ArrayOperandShapeOf(rhs, var_array_info_);
  if (!l || !r) return std::nullopt;
  const auto& li = *l->info;
  const auto& ri = *r->info;
  return ElementTypesEquivalent(ElementOf(li), ElementOf(ri)) &&
         std::tie(li.is_dynamic, li.is_queue, li.is_assoc, li.assoc_index_type,
                  l->dims) == std::tie(ri.is_dynamic, ri.is_queue, ri.is_assoc,
                                       ri.assoc_index_type, r->dims);
}

}  // namespace delta
