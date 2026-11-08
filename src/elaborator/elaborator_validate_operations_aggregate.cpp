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

struct DeclarationTypes {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregate_typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

struct DeclaredName {
  uint32_t unpacked_dims = 0;
  bool is_assoc = false;
  bool is_integral = false;
};

using DeclaredNames = std::unordered_map<std::string_view, DeclaredName>;

struct AggregateOperandNames {
  const std::unordered_set<std::string_view>& structs;
  const std::unordered_map<std::string_view, const DataType*>& struct_types;
  const DeclaredNames& declared;
  const DeclarationTypes& types;
};

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

bool IsAssocDimension(const Expr* dim, const DeclarationTypes& t) {
  if (dim == nullptr || dim->kind != ExprKind::kIdentifier) return false;
  std::string_view s = dim->text;
  return s == "*" || s == "string" || s == "int" || s == "integer" ||
         s == "byte" || s == "shortint" || s == "longint" || s == "bit" ||
         s == "logic" || s == "reg" || s == "time" ||
         t.typedefs.count(s) != 0 || t.class_names.count(s) != 0;
}

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

bool IsEqualityOperator(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

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

bool NamesUnpackedAggregate(const Expr* e, const AggregateOperandNames& n) {
  return NamesIn(e, n.structs) ||
         UnpackedArrayOperand(e, n.declared) != nullptr;
}

void CheckConditionalStructOperands(const Expr* e,
                                    const AggregateOperandNames& n,
                                    DiagEngine& diag) {
  if (e->kind != ExprKind::kTernary) return;
  const Expr* t = e->true_expr;
  const Expr* f = e->false_expr;
  bool differ = false;
  if (NamesIn(t, n.structs) && NamesIn(f, n.structs)) {
    differ = !TypesEquivalent(*n.struct_types.at(t->text),
                              *n.struct_types.at(f->text));
  } else {
    differ =
        (NamesUnpackedAggregate(t, n) && IsIntegralOperand(f, n.declared)) ||
        (NamesUnpackedAggregate(f, n) && IsIntegralOperand(t, n.declared));
  }
  if (!differ) return;
  diag.Error(e->range.start,
             "the operands of a conditional operator shall be of equivalent "
             "types",
             Subclause("11.4.11"));
}

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

void WalkStmtChildrenForAggregateOperands(const Stmt* s,
                                          const AggregateOperandNames& n,
                                          DiagEngine& diag) {
  ReportUntypedPattern(s->condition, diag);
  ForEachChildExpr(
      s, [&](Expr* const& e) { WalkExprForAggregateOperands(e, n, diag); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtForAggregateOperands(sub, n, diag); });
}

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

std::optional<int64_t> SliceLength(const Expr* slice) {
  if (slice->is_part_select_plus || slice->is_part_select_minus)
    return ConstEvalInt(slice->index_end);
  auto last = ConstEvalInt(slice->index_end);
  return ConstEvalInt(slice->index).and_then([&last](int64_t first) {
    return last.transform(
        [first](int64_t end) { return std::abs(first - end) + 1; });
  });
}

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
