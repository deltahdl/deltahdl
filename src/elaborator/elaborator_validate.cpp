#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <initializer_list>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/force_lhs.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_key_match.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

const Expr* PatternReplication(const Expr* pattern) {
  if (pattern->elements.size() != 1) return nullptr;
  const Expr* only = pattern->elements[0];
  return only->is_pattern_replication ? only : nullptr;
}

std::optional<int64_t> PositionalItemCount(const Expr* pattern) {
  const Expr* rep = PatternReplication(pattern);
  if (rep == nullptr) return static_cast<int64_t>(pattern->elements.size());
  auto times = ConstEvalInt(rep->repeat_count);
  if (!times) return std::nullopt;
  return *times * static_cast<int64_t>(rep->elements.size());
}

static std::optional<int64_t> RangeSize(const Expr* left, const Expr* right) {
  auto left_value = ConstEvalInt(left);
  auto right_value = ConstEvalInt(right);
  if (left_value && right_value)
    return std::abs(*left_value - *right_value) + 1;
  return std::nullopt;
}

std::optional<int64_t> ComputeDimSize(const Expr* dim) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon)
    return RangeSize(dim->lhs, dim->rhs);
  return ConstEvalInt(dim);
}

namespace {
struct PatternDim {
  std::optional<int64_t> size;
  bool packed = false;
};
}  // namespace

static void AppendPackedDims(const DataType& dtype,
                             std::vector<PatternDim>& dims) {
  if (dtype.packed_dim_left == nullptr) return;
  dims.push_back(
      {RangeSize(dtype.packed_dim_left, dtype.packed_dim_right), true});
  for (const auto& [left, right] : dtype.extra_packed_dims)
    dims.push_back({RangeSize(left, right), true});
}

static void AppendElementPackedDims(const ArrayPatternCheck& check,
                                    const DataType& dtype,
                                    std::vector<PatternDim>& dims) {
  AppendPackedDims(dtype, dims);
  std::vector<std::string_view> names;
  FollowTypedefs(dtype, check.typedefs, names);
  for (std::string_view name : names) {
    auto it = check.typedefs.find(name);
    if (it == check.typedefs.end() || check.aggregate_typedefs.contains(name))
      return;
    AppendPackedDims(it->second, dims);
  }
}

static bool TypeKeyCoversElement(std::string_view key, const DataType& elem,
                                 const TypedefMap& typedefs) {
  if (TypeKeyMatchesType(key, elem, typedefs)) return true;
  std::vector<std::string_view> names;
  const DataType* agg = FollowTypedefs(elem, typedefs, names);
  if (agg == nullptr || agg->struct_members.empty()) return false;
  return std::ranges::all_of(agg->struct_members, [&](const StructMember& m) {
    return TypeKeyMatchesMember(key, m, typedefs);
  });
}

static void CheckArrayPatternCoverage(const ArrayPatternCheck& check,
                                      const Expr* pattern,
                                      const DataType& elem_type,
                                      const PatternDim& dim, SourceLoc loc) {
  const TypedefMap& typedefs = check.typedefs;
  if (!dim.size) return;

  bool has_default = false;
  bool has_type_key = false;
  std::unordered_set<std::string> index_keys;
  int64_t unidentified_keys = 0;
  for (const auto* key : pattern->pattern_keys) {
    if (key->text == "default") {
      has_default = true;
    } else if (IsTypeKey(key->text, typedefs)) {
      has_type_key = has_type_key || dim.packed ||
                     TypeKeyCoversElement(key->text, elem_type, typedefs);
    } else if (auto identity = ArrayPatternKeyIdentity(key)) {
      index_keys.insert(*identity);
    } else {
      ++unidentified_keys;
    }
  }
  if (has_default || has_type_key) return;
  if (static_cast<int64_t>(index_keys.size()) + unidentified_keys < *dim.size) {
    check.diag.Error(loc, "keyed array pattern does not cover all elements",
                     Subclause("10.9.1"));
  }
}

static bool IsUnpackedStructType(const DataType& dt,
                                 const TypedefMap& typedefs) {
  const DataType* t = &dt;
  if (t->kind == DataTypeKind::kNamed) {
    auto td = typedefs.find(t->type_name);
    if (td == typedefs.end()) return false;
    t = &td->second;
  }
  return t->kind == DataTypeKind::kStruct && !t->is_packed;
}

static bool IsElementThatIsNoStruct(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    case ExprKind::kIdentifier: {
      auto it = var_types.find(e->text);
      if (it == var_types.end()) return false;
      DataTypeKind kind = it->second;
      return (IsIntegralType(kind) && kind != DataTypeKind::kImplicit) ||
             IsRealType(kind) || kind == DataTypeKind::kString;
    }
    default:
      return false;
  }
}

static bool ReportsFlatStructPattern(const ArrayPatternCheck& check,
                                     const Expr* pattern,
                                     const DataType& elem_type, SourceLoc loc) {
  if (!IsUnpackedStructType(elem_type, check.typedefs)) return false;
  for (const auto* e : pattern->elements) {
    if (IsElementThatIsNoStruct(e, check.var_types)) {
      check.diag.Error(loc,
                       "assignment pattern for an array of structures shall "
                       "nest a pattern per structure",
                       Subclause("5.10"));
      return true;
    }
  }
  return false;
}

static void CheckPatternDims(const ArrayPatternCheck& check,
                             const Expr* pattern, const DataType& elem_type,
                             std::span<const PatternDim> dims, SourceLoc loc) {
  if (pattern->kind != ExprKind::kAssignmentPattern || dims.empty()) return;
  if (!pattern->pattern_keys.empty()) {
    CheckArrayPatternIndexKeys(check, pattern, loc);
    CheckArrayPatternCoverage(check, pattern, elem_type, dims[0], loc);
    return;
  }
  if (ReportsFlatStructPattern(check, pattern, elem_type, loc)) return;
  const std::optional<int64_t> kDimSize = dims[0].size;
  if (!kDimSize) return;
  auto count = PositionalItemCount(pattern);
  if (count && *count != *kDimSize) {
    check.diag.Error(loc,
                     std::format("assignment pattern has {} elements, but "
                                 "array dimension requires {}",
                                 *count, *kDimSize),
                     Subclause("10.9.1"));
  }
  for (const Expr* e : pattern->elements)
    CheckPatternDims(check, e, elem_type, dims.subspan(1), loc);
}

static void CheckAgainstUnpackedDims(const ArrayPatternCheck& check,
                                     const Expr* pattern,
                                     const DataType& elem_type,
                                     std::vector<PatternDim> dims,
                                     SourceLoc loc) {
  AppendElementPackedDims(check, elem_type, dims);
  CheckPatternDims(check, pattern, elem_type, dims, loc);
}

void ArrayPatternCheck::Check(const Expr* pattern, const DataType& elem_type,
                              const std::vector<Expr*>& dims,
                              SourceLoc loc) const {
  std::vector<PatternDim> pattern_dims;
  pattern_dims.reserve(dims.size());
  for (const Expr* dim : dims) {
    pattern_dims.push_back(
        {dim == nullptr ? std::nullopt : ComputeDimSize(dim), false});
  }
  CheckAgainstUnpackedDims(*this, pattern, elem_type, std::move(pattern_dims),
                           loc);
}

void ArrayPatternCheck::CheckSized(const Expr* pattern,
                                   const DataType& elem_type,
                                   std::span<const uint32_t> unpacked_sizes,
                                   SourceLoc loc) const {
  std::vector<PatternDim> pattern_dims;
  pattern_dims.reserve(unpacked_sizes.size());
  for (uint32_t size : unpacked_sizes) pattern_dims.push_back({size, false});
  CheckAgainstUnpackedDims(*this, pattern, elem_type, std::move(pattern_dims),
                           loc);
}

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  ArrayPatternCheck{typedefs_, aggregate_typedef_names_, var_types_, diag_}
      .Check(item->init_expr, item->data_type, item->unpacked_dims, item->loc);
}

std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

std::string_view LhsBaseName(const Expr* e) {
  while (e) {
    if (e->kind == ExprKind::kIdentifier)
      return (e->text == "this" || e->text == "super") ? std::string_view{}
                                                       : e->text;
    if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      e = e->lhs;
      continue;
    }
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
      continue;
    }
    break;
  }
  return {};
}

static void CollectLhsBaseNames(
    const Expr* e, SourceLoc loc,
    std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kStreamingConcat) {
    for (const auto* elem : e->elements) CollectLhsBaseNames(elem, loc, out);
    return;
  }
  auto name = LhsBaseName(e);
  if (!name.empty()) out.emplace(name, loc);
}

static void ForEachBodyTarget(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    std::initializer_list<StmtKind> kinds,
    const std::function<void(std::string_view, SourceLoc)>& visit) {
  BodyDeclScopes scopes(false);
  for (const auto& arg : formals) scopes.DeclareFormal(arg);
  std::unordered_map<std::string_view, SourceLoc> written;
  for (const Stmt* s : body) {
    scopes.Walk(s, [&](const Stmt* st) {
      if (std::ranges::find(kinds, st->kind) == kinds.end()) return;
      written.clear();
      CollectLhsBaseNames(st->lhs, st->range.start, written);
      for (const auto& [name, loc] : written)
        if (scopes.Find(name) == nullptr) visit(name, loc);
    });
  }
}

void CollectProcTargets(const std::vector<FunctionArg>& formals,
                        const std::vector<Stmt*>& body,
                        std::unordered_map<std::string_view, SourceLoc>& out) {
  ForEachBodyTarget(
      formals, body, {StmtKind::kBlockingAssign, StmtKind::kNonblockingAssign},
      [&out](std::string_view name, SourceLoc loc) { out.emplace(name, loc); });
}

void CollectProcContAssignTargets(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    std::unordered_map<std::string_view, SourceLoc>& out) {
  ForEachBodyTarget(
      formals, body, {StmtKind::kAssign},
      [&out](std::string_view name, SourceLoc loc) { out.emplace(name, loc); });
}

void ReportProcContAssignNets(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  ForEachBodyTarget(formals, body, {StmtKind::kAssign, StmtKind::kDeassign},
                    [&](std::string_view name, SourceLoc loc) {
                      if (net_names.count(name) == 0) return;
                      diag.Error(loc,
                                 std::format("net '{}' cannot be the target "
                                             "of a procedural assign or "
                                             "deassign",
                                             name),
                                 Subclause("10.6.1"));
                    });
}

void CollectForceReleaseTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease) {
    CollectLhsBaseNames(s->lhs, s->range.start, out);
  }
  ForEachChildStmt(
      s, [&out](const Stmt* sub) { CollectForceReleaseTargets(sub, out); });
}

void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease ||
      s->kind == StmtKind::kAssign || s->kind == StmtKind::kDeassign) {
    if (ExprUsesInterconnect(s->lhs, interconnect_names)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in procedural "
                 "continuous assignment",
                 Subclause("6.6.8"));
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckInterconnectProcContAssign(sub, interconnect_names, diag);
  });
}

void CheckInterconnectProceduralRead(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  const Expr* reads[] = {s->rhs,      s->condition,          s->for_cond,
                         s->delay,    s->cycle_delay,        s->expr,
                         s->var_init, s->repeat_event_count, s->assert_expr};
  for (const Expr* e : reads) {
    if (ExprUsesInterconnect(e, interconnect_names)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in a procedural expression",
                 Subclause("6.6.8"));
      break;
    }
  }
  for (auto& ci : s->case_items)
    for (const auto* p : ci.patterns)
      if (ExprUsesInterconnect(p, interconnect_names)) {
        diag.Error(s->range.start,
                   "interconnect net cannot be used in a procedural expression",
                   Subclause("6.6.8"));
        break;
      }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckInterconnectProceduralRead(sub, interconnect_names, diag);
  });
}

static bool ProceduralAssignLhsHasSelect(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSelect) return true;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements)
      if (ProceduralAssignLhsHasSelect(elem)) return true;
  }
  return false;
}

void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kAssign && ProceduralAssignLhsHasSelect(s->lhs)) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }
  ForEachChildStmt(
      s, [&diag](const Stmt* sub) { CheckProceduralAssignLhs(sub, diag); });
}

enum class ForceVariableTarget : uint8_t { kSingular, kAggregate, kBits };

static ForceVariableTarget ClassifyForceVariableTarget(
    const Expr* e, const ForceLhsNames& names) {
  std::vector<const Expr*> selects;
  for (; e->kind == ExprKind::kSelect; e = e->base)
    selects.insert(selects.begin(), e);
  std::string_view name =
      e->kind == ExprKind::kIdentifier ? e->text : std::string_view{};
  auto var = std::ranges::find(names.mod.variables, name, &RtlirVariable::name);
  const DataType* written =
      var != names.mod.variables.end() ? var->written_type : nullptr;
  size_t dims = 0;
  bool aggregate_element = false;
  if (written != nullptr) {
    dims = var->num_unpacked_dims;
    std::vector<std::string_view> followed;
    aggregate_element =
        IsUnpackedAggregate(FollowTypedefs(*written, names.typedefs, followed));
  }
  for (size_t i = 0; i < std::min(dims, selects.size()); ++i)
    if (selects[i]->index_end != nullptr)
      return ForceVariableTarget::kAggregate;
  if (selects.size() != dims)
    return selects.size() > dims ? ForceVariableTarget::kBits
                                 : ForceVariableTarget::kAggregate;
  return aggregate_element ? ForceVariableTarget::kAggregate
                           : ForceVariableTarget::kSingular;
}

static void CheckForceVariableTarget(const Expr* e, const ForceLhsNames& names,
                                     SourceLoc loc, DiagEngine& diag) {
  switch (ClassifyForceVariableTarget(e, names)) {
    case ForceVariableTarget::kAggregate:
      diag.Error(loc,
                 "unpacked array, structure or union is not a legal force LHS",
                 Subclause("10.6.2"));
      break;
    case ForceVariableTarget::kBits:
      diag.Error(loc,
                 "bit-select or part-select of a variable is not a "
                 "legal force LHS",
                 Subclause("10.6.2"));
      break;
    default:
      break;
  }
}

static void CheckForceLhsOperand(const Expr* e, const ForceLhsNames& names,
                                 SourceLoc loc, DiagEngine& diag) {
  if (e->kind == ExprKind::kConcatenation) {
    for (auto* el : e->elements) CheckForceLhsOperand(el, names, loc, diag);
    return;
  }
  if (e->kind != ExprKind::kSelect && e->kind != ExprKind::kIdentifier) return;
  auto base_name = LhsBaseName(e);
  if (base_name.empty()) return;
  if (names.net_names.count(base_name) == 0) {
    CheckForceVariableTarget(e, names, loc, diag);
  } else if (e->kind != ExprKind::kSelect) {
    return;
  } else if (names.nettype_net_names.count(base_name) != 0) {
    diag.Error(loc,
               "bit-select or part-select of a net with a user-defined "
               "nettype is not a legal force LHS",
               Subclause("10.6.2"));
  } else if (!SelectPathIsConstant(e, names.scope)) {
    diag.Error(loc,
               "bit-select or part-select of a net in a force LHS must be "
               "constant",
               Subclause("10.6.2"));
  }
}

void CheckForceLhs(const Stmt* s, const ForceLhsNames& names,
                   DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce && s->lhs)
    CheckForceLhsOperand(s->lhs, names, s->range.start, diag);
  ForEachChildStmt(s,
                   [&](const Stmt* sub) { CheckForceLhs(sub, names, diag); });
}

static bool AnyExprUsesInterconnect(
    const std::vector<Expr*>& list,
    const std::unordered_set<std::string_view>& names) {
  for (auto* sub : list)
    if (ExprUsesInterconnect(sub, names)) return true;
  return false;
}

bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return names.count(e->text) > 0;
  for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                          e->false_expr, e->base, e->index, e->index_end}) {
    if (ExprUsesInterconnect(sub, names)) return true;
  }
  return AnyExprUsesInterconnect(e->args, names) ||
         AnyExprUsesInterconnect(e->elements, names);
}

bool IsRealType(DataTypeKind k) {
  return k == DataTypeKind::kReal || k == DataTypeKind::kShortreal ||
         k == DataTypeKind::kRealtime;
}

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

using NameSet = std::unordered_set<std::string_view>;

static void CheckRealSelectNode(const Expr* e, const TypeMap& types,
                                const SelectOperands& operands,
                                DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  const bool kIsRealVar = !name.empty() && operands.variables.count(name) != 0;
  const bool kIsRealParam =
      !name.empty() && operands.parameters.count(name) != 0;
  if (kIsRealVar || kIsRealParam) {
    const bool kIsBitSelect =
        !e->index_end && !e->is_part_select_plus && !e->is_part_select_minus;
    const char* const kConstruct = kIsBitSelect ? "bit-select" : "part-select";
    const char* const kOperand =
        kIsRealVar ? "real variable" : "real parameter";
    diag.Error(e->range.start,
               std::format("{} of a {} is illegal", kConstruct, kOperand),
               Subclause(kIsRealVar ? "6.12" : "11.5.1"));
    return;
  }
  if (!e->index) return;
  auto idx = ExprIdent(e->index);
  if (idx.empty()) return;
  auto it = types.find(idx);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start, "real type used as index is illegal",
               Subclause("6.12"));
  }
}

struct SelectChain {
  std::string_view name;
  size_t addresses = 0;
};

static SelectChain ResolveSelectChain(const Expr* e) {
  SelectChain chain;
  const Expr* n = e;
  while (n && n->kind == ExprKind::kSelect) {
    ++chain.addresses;
    n = n->base;
  }
  if (n && n->kind == ExprKind::kIdentifier) chain.name = n->text;
  return chain;
}

static void CheckElementSelectNode(const Expr* e, const SelectShapeMap& shapes,
                                   DiagEngine& diag) {
  if (!e->base || e->base->kind != ExprKind::kSelect) return;
  SelectChain chain = ResolveSelectChain(e);
  if (chain.name.empty()) return;
  auto it = shapes.find(chain.name);
  if (it == shapes.end()) return;
  if (chain.addresses != it->second.addressable_dims + 1) return;
  const bool kIsBitSelect =
      !e->index_end && !e->is_part_select_plus && !e->is_part_select_minus;
  if (it->second.element_is_real) {
    diag.Error(e->range.start,
               std::format("{} of a real variable is illegal",
                           kIsBitSelect ? "bit-select" : "part-select"),
               Subclause("6.12"));
    return;
  }
  if (it->second.element_is_scalar) {
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal",
               Subclause("11.5.1"));
  }
}

void CheckRealSelect(const Expr* e, const TypeMap& types,
                     const SelectOperands& operands, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base) {
    CheckRealSelectNode(e, types, operands, diag);
    CheckElementSelectNode(e, operands.shapes, diag);
  }
  ForEachExprChild(e, [&](const Expr* child) {
    CheckRealSelect(child, types, operands, diag);
  });
}

static void CheckScalarSelectNode(const Expr* e, const NameSet& scalars,
                                  DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (name.empty()) return;
  if (scalars.count(name) != 0)
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal",
               Subclause("11.5.1"));
}

void CheckScalarSelect(const Expr* e, const NameSet& scalars,
                       DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckScalarSelectNode(e, scalars, diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckScalarSelect(child, scalars, diag); });
}

static void CheckIndexedPartSelectWidthNode(const Expr* e,
                                            const ScopeMap& scope,
                                            DiagEngine& diag) {
  if (!e->index_end) return;
  if (!e->is_part_select_plus && !e->is_part_select_minus) return;
  auto width = ConstEvalInt(e->index_end, scope);
  if (!width.has_value()) {
    diag.Error(e->range.start,
               "indexed part-select width must be a constant expression",
               Subclause("11.5.1"));
    return;
  }
  if (*width <= 0)
    diag.Error(e->range.start,
               "indexed part-select width must be a positive constant",
               Subclause("11.5.1"));
}

void CheckIndexedPartSelectWidth(const Expr* e, const ScopeMap& scope,
                                 DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckIndexedPartSelectWidthNode(e, scope, diag);
  ForEachExprChild(e, [&](const Expr* child) {
    CheckIndexedPartSelectWidth(child, scope, diag);
  });
}

void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag) {
  if (!s) return;
  CheckScalarSelect(s->lhs, scalars, diag);
  CheckScalarSelect(s->rhs, scalars, diag);
  CheckScalarSelect(s->expr, scalars, diag);
  CheckScalarSelect(s->condition, scalars, diag);
  CheckScalarSelect(s->for_cond, scalars, diag);
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CheckScalarSelectStmt(sub, scalars, diag); });
}

void CheckRealSelectStmt(const Stmt* s, const TypeMap& types,
                         const SelectOperands& operands, DiagEngine& diag) {
  if (!s) return;
  CheckRealSelect(s->lhs, types, operands, diag);
  CheckRealSelect(s->rhs, types, operands, diag);
  CheckRealSelect(s->expr, types, operands, diag);
  CheckRealSelect(s->condition, types, operands, diag);
  CheckRealSelect(s->for_cond, types, operands, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckRealSelectStmt(sub, types, operands, diag);
  });
}

void CheckIndexedPartSelectWidthStmt(const Stmt* s, const ScopeMap& scope,
                                     DiagEngine& diag) {
  if (!s) return;
  CheckIndexedPartSelectWidth(s->lhs, scope, diag);
  CheckIndexedPartSelectWidth(s->rhs, scope, diag);
  CheckIndexedPartSelectWidth(s->expr, scope, diag);
  CheckIndexedPartSelectWidth(s->condition, scope, diag);
  CheckIndexedPartSelectWidth(s->for_cond, scope, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckIndexedPartSelectWidthStmt(sub, scope, diag);
  });
}

bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  return AnyExprChild(
      e, [name](const Expr* child) { return ExprContainsIdent(child, name); });
}

NettypeResolutionRule ValidateNettypeResolutionFunction(
    const NettypeResolutionSig& sig) {
  if (!sig.return_type_matches_nettype)
    return NettypeResolutionRule::kReturnType;
  if (!sig.single_input_argument) return NettypeResolutionRule::kArgumentCount;
  if (!sig.argument_is_input) return NettypeResolutionRule::kArgumentDirection;
  if (!sig.argument_is_dynamic_array)
    return NettypeResolutionRule::kArgumentIsDynamicArray;
  if (!sig.argument_element_type_matches)
    return NettypeResolutionRule::kArgumentElementType;
  if (!sig.is_automatic) return NettypeResolutionRule::kAutomaticLifetime;
  if (sig.is_class_method && !sig.is_static_method)
    return NettypeResolutionRule::kClassStaticMethod;
  return NettypeResolutionRule::kConforming;
}

}  // namespace delta
