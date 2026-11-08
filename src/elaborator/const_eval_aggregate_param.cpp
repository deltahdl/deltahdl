#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_key_match.h"
#include "elaborator/unit_aggregate_params.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kMaxAggregateHops = 64;

const TypedefMap& Typedefs() {
  static const TypedefMap kNone;
  const TypedefMap* map = RegisteredTypedefMap();
  return map != nullptr ? *map : kNone;
}

const DataType* ResolvedType(const DataType& type) {
  const DataType* resolved = &type;
  for (int hops = 0; hops < kMaxAggregateHops && resolved != nullptr &&
                     resolved->kind == DataTypeKind::kNamed;
       ++hops)
    resolved = FindNamedType(*resolved, Typedefs());
  return resolved;
}

bool HoldsAggregate(const DataType& type) {
  const DataType* resolved = ResolvedType(type);
  return resolved != nullptr && (resolved->kind == DataTypeKind::kStruct ||
                                 resolved->kind == DataTypeKind::kUnion);
}

struct ValueFrame {
  const RtlirModule* module = nullptr;
  const ScopeMap* scope = nullptr;
  std::vector<std::string_view> gen_prefixes;
  std::string_view unit_prefix;
};

class FrameGuard {
 public:
  explicit FrameGuard(const ValueFrame& frame)
      : module_(frame.module),
        gen_(frame.gen_prefixes),
        prefix_(frame.unit_prefix) {}

 private:
  ParamRangeRegistryGuard module_;
  RegisteredGenScopeGuard gen_;
  UnitNamePrefixGuard prefix_;
};

struct PartShape {
  DataType type;
  const std::vector<Expr*>* dims = nullptr;
  size_t dim_at = 0;
  const ScopeMap* scope = nullptr;

  [[nodiscard]] bool HasDims() const {
    return dims != nullptr && dim_at < dims->size();
  }
};

struct PartState {
  const Expr* value = nullptr;
  ValueFrame frame;
  PartShape shape;
  bool broadcast = false;
};

struct LocatedPart {
  PartState state;
  PartShape reader;
};

struct PartStep {
  std::string_view member;
  int64_t position = 0;
};

struct PickedItem {
  const Expr* value = nullptr;
  bool from_default = false;
};

const Expr* Untyped(const Expr* value) {
  bool typed = value->kind == ExprKind::kCast && value->lhs != nullptr &&
               value->lhs->kind == ExprKind::kAssignmentPattern;
  return typed ? value->lhs : value;
}

bool IsPattern(const Expr* value) {
  return Untyped(value)->kind == ExprKind::kAssignmentPattern;
}

bool IsPartStep(const Expr* expr) {
  if (expr->kind == ExprKind::kSelect)
    return expr->base != nullptr && expr->index != nullptr &&
           expr->index_end == nullptr;
  return expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution &&
         expr->lhs != nullptr && expr->rhs != nullptr;
}

const Expr* StepBase(const Expr* step) {
  return step->kind == ExprKind::kSelect ? step->base : step->lhs;
}

ValueFrame CurrentFrame(const ScopeMap& scope) {
  return ValueFrame{RegisteredModule(), &scope, RegisteredGenPrefixes(),
                    CurrentUnitNamePrefix()};
}

bool NamesDims(const std::vector<Expr*>* dims) {
  return dims != nullptr && !dims->empty();
}

const DataType* ParamValueType(const RtlirParamDecl& pd) {
  static const DataType kImplicit;
  if (pd.type_param_actual != nullptr) return pd.type_param_actual;
  return pd.decl_type != nullptr ? pd.decl_type : &kImplicit;
}

bool IsImplicitType(const DataType& type) {
  return type.kind == DataTypeKind::kImplicit && !type.is_signed &&
         type.packed_dim_left == nullptr;
}

std::optional<PartState> ModuleParamState(const RtlirParamDecl& pd,
                                          const ScopeMap& scope) {
  const DataType* type = ParamValueType(pd);
  if (pd.is_type_param) return std::nullopt;
  if (!NamesDims(pd.unpacked_dims) && !HoldsAggregate(*type))
    return std::nullopt;
  PartState state{pd.default_value, CurrentFrame(scope),
                  PartShape{*type, pd.unpacked_dims, 0, &scope}};
  if (pd.defparam_value_expr != nullptr) {
    state.value = pd.defparam_value_expr;
    state.frame = ValueFrame{pd.defparam_module,
                             &pd.defparam_value_scope,
                             pd.defparam_value_scopes,
                             {}};
  } else if (pd.override_expr != nullptr) {
    state.value = pd.override_expr;
    state.frame = ValueFrame{pd.override_module, &pd.override_scope, {}, {}};
  }
  if (state.value == nullptr) return std::nullopt;
  return state;
}

PartState UnitParamState(const UnitAggregateParam& param) {
  return PartState{param.value,
                   ValueFrame{nullptr, &param.scope, {}, param.prefix},
                   PartShape{param.type, param.dims, 0, &param.scope}};
}

const UnitAggregateParam* UnitRoot(const Expr* root) {
  if (root->kind == ExprKind::kMemberAccess) {
    if (!root->is_scope_resolution) return nullptr;
    std::optional<std::string> key = ScopedNameKey(root);
    return key ? FindUnitAggregateParam(*key) : nullptr;
  }
  if (root->kind != ExprKind::kIdentifier) return nullptr;
  if (root->scope_prefix == "$unit") return FindUnitAggregateParam(root->text);
  if (!root->scope_prefix.empty()) return nullptr;
  return FindUnitAggregateParamNamed(root->text);
}

std::optional<PartState> RootState(const Expr* root, const ScopeMap& scope) {
  if (root->kind == ExprKind::kIdentifier && root->scope_prefix.empty()) {
    if (const RtlirParamDecl* pd = RegisteredParamNamed(root->text))
      return ModuleParamState(*pd, scope);
  }
  const UnitAggregateParam* param = UnitRoot(root);
  if (param == nullptr ||
      (!NamesDims(param->dims) && !HoldsAggregate(param->type)))
    return std::nullopt;
  return UnitParamState(*param);
}

std::optional<RtlirUnpackedDim> ShapeDim(const PartShape& shape) {
  return FoldUnpackedDimBounds((*shape.dims)[shape.dim_at], *shape.scope);
}

std::optional<int64_t> PositionOf(const PartShape& shape, const Expr* index,
                                  const ScopeMap& scope) {
  std::optional<RtlirUnpackedDim> dim = ShapeDim(shape);
  std::optional<int64_t> idx = ConstEvalInt(index, scope);
  if (!dim || !idx) return std::nullopt;
  int64_t pos = dim->left <= dim->right ? *idx - dim->left : dim->left - *idx;
  if (pos < 0 || pos >= static_cast<int64_t>(dim->Size())) return std::nullopt;
  return pos;
}

std::optional<int64_t> IndexAt(const PartShape& shape, int64_t pos) {
  std::optional<RtlirUnpackedDim> dim = ShapeDim(shape);
  if (!dim) return std::nullopt;
  return dim->left <= dim->right ? dim->left + pos : dim->left - pos;
}

const StructMember* MemberNamed(const DataType& type, std::string_view name,
                                size_t& index) {
  const DataType* resolved = ResolvedType(type);
  if (resolved == nullptr || resolved->struct_members.empty()) return nullptr;
  const std::vector<StructMember>* members = &resolved->struct_members;
  auto it = std::ranges::find(*members, name, &StructMember::name);
  if (it == members->end()) return nullptr;
  index = static_cast<size_t>(it - members->begin());
  return &*it;
}

PartShape MemberShape(const PartShape& owner, const StructMember& member) {
  return PartShape{
      MemberWrittenType(member),
      member.unpacked_dims.empty() ? nullptr : &member.unpacked_dims, 0,
      owner.scope};
}

std::optional<PartStep> ReaderStep(const Expr* step, PartShape& shape,
                                   const ScopeMap& scope) {
  if (step->kind == ExprKind::kSelect) {
    if (!shape.HasDims()) return std::nullopt;
    std::optional<int64_t> pos = PositionOf(shape, step->index, scope);
    if (!pos) return std::nullopt;
    ++shape.dim_at;
    return PartStep{{}, *pos};
  }
  size_t index = 0;
  const StructMember* member =
      shape.HasDims() ? nullptr
                      : MemberNamed(shape.type, step->rhs->text, index);
  if (member == nullptr) return std::nullopt;
  std::string_view name = member->name;
  shape = MemberShape(shape, *member);
  return PartStep{name, 0};
}

bool IsDefaultKey(const Expr* key) {
  return key->kind == ExprKind::kIdentifier && key->text == "default";
}

bool IsTypeNameKey(const Expr* key) {
  return key->kind == ExprKind::kIdentifier && IsTypeKey(key->text, Typedefs());
}

bool IsKeyed(const Expr* pattern) {
  return !pattern->pattern_keys.empty() &&
         pattern->pattern_keys.size() == pattern->elements.size();
}

std::optional<PickedItem> DefaultItem(const Expr* pattern) {
  for (size_t i = 0; i < pattern->pattern_keys.size(); ++i) {
    if (IsDefaultKey(pattern->pattern_keys[i]))
      return PickedItem{pattern->elements[i], true};
  }
  return std::nullopt;
}

std::optional<PickedItem> PositionalItem(const Expr* pattern, size_t pos) {
  if (const Expr* rep = PatternReplication(pattern)) {
    if (rep->elements.empty()) return std::nullopt;
    return PickedItem{rep->elements[pos % rep->elements.size()], false};
  }
  if (pos >= pattern->elements.size()) return std::nullopt;
  return PickedItem{pattern->elements[pos], false};
}

std::optional<PickedItem> KeyedMember(const Expr* pattern,
                                      const StructMember& member) {
  const std::vector<Expr*>& keys = pattern->pattern_keys;
  for (size_t i = 0; i < keys.size(); ++i) {
    if (keys[i]->kind == ExprKind::kIdentifier && keys[i]->text == member.name)
      return PickedItem{pattern->elements[i], false};
  }
  for (size_t i = 0; i < keys.size(); ++i) {
    if (IsTypeNameKey(keys[i]) &&
        TypeKeyMatchesMember(keys[i]->text, member, Typedefs()))
      return PickedItem{pattern->elements[i], true};
  }
  return DefaultItem(pattern);
}

std::optional<PickedItem> KeyedElement(const Expr* pattern,
                                       const PartState& state, int64_t pos) {
  std::optional<int64_t> index = IndexAt(state.shape, pos);
  if (!index) return std::nullopt;
  const std::vector<Expr*>& keys = pattern->pattern_keys;
  for (size_t i = 0; i < keys.size(); ++i) {
    if (IsDefaultKey(keys[i]) || IsTypeNameKey(keys[i])) continue;
    std::optional<int64_t> key = ConstEvalInt(keys[i], *state.frame.scope);
    if (key && *key == *index) return PickedItem{pattern->elements[i], false};
  }
  bool element_is_leaf = state.shape.dim_at + 1 == state.shape.dims->size();
  for (size_t i = 0; element_is_leaf && i < keys.size(); ++i) {
    if (IsTypeNameKey(keys[i]) &&
        TypeKeyMatchesType(keys[i]->text, state.shape.type, Typedefs()))
      return PickedItem{pattern->elements[i], true};
  }
  return DefaultItem(pattern);
}

void TakeItem(PartState& state, const PickedItem& item) {
  state.value = item.value;
  state.broadcast = item.from_default && !IsPattern(item.value);
}

bool AdvanceMember(PartState& state, std::string_view name) {
  size_t index = 0;
  const StructMember* member = state.shape.HasDims()
                                   ? nullptr
                                   : MemberNamed(state.shape.type, name, index);
  if (member == nullptr) return false;
  if (!state.broadcast) {
    const Expr* pattern = Untyped(state.value);
    std::optional<PickedItem> item = IsKeyed(pattern)
                                         ? KeyedMember(pattern, *member)
                                         : PositionalItem(pattern, index);
    if (!item) return false;
    TakeItem(state, *item);
  }
  state.shape = MemberShape(state.shape, *member);
  return true;
}

bool AdvanceElement(PartState& state, int64_t pos) {
  if (!state.shape.HasDims()) return false;
  if (!state.broadcast) {
    const Expr* pattern = Untyped(state.value);
    std::optional<PickedItem> item =
        IsKeyed(pattern) ? KeyedElement(pattern, state, pos)
                         : PositionalItem(pattern, static_cast<size_t>(pos));
    if (!item) return false;
    TakeItem(state, *item);
  }
  ++state.shape.dim_at;
  return true;
}

bool Advance(PartState& state, const PartStep& step) {
  FrameGuard guard(state.frame);
  if (step.member.empty()) return AdvanceElement(state, step.position);
  return AdvanceMember(state, step.member);
}

std::optional<LocatedPart> LocatePart(const Expr* expr, const ScopeMap& scope,
                                      int depth);

bool Normalize(PartState& state, int depth) {
  for (int hop = 0; hop < kMaxAggregateHops; ++hop) {
    if (state.broadcast || IsPattern(state.value)) return true;
    std::optional<LocatedPart> followed;
    {
      FrameGuard guard(state.frame);
      followed = LocatePart(state.value, *state.frame.scope, depth + 1);
    }
    if (!followed) return false;
    state = std::move(followed->state);
  }
  return false;
}

std::optional<LocatedPart> LocatePart(const Expr* expr, const ScopeMap& scope,
                                      int depth) {
  if (depth > kMaxAggregateHops) return std::nullopt;
  std::vector<const Expr*> chain;
  const Expr* root = expr;
  while (IsPartStep(root)) {
    chain.push_back(root);
    root = StepBase(root);
  }
  std::optional<PartState> state = RootState(root, scope);
  if (!state) return std::nullopt;
  PartShape reader = state->shape;
  for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
    std::optional<PartStep> step = ReaderStep(*it, reader, scope);
    if (!step || !Normalize(*state, depth) || !Advance(*state, *step))
      return std::nullopt;
  }
  return LocatedPart{std::move(*state), std::move(reader)};
}

const DataType* LeafType(const PartShape& shape) {
  if (shape.HasDims()) return nullptr;
  const DataType* type = ResolvedType(shape.type);
  if (type == nullptr || IsUnpackedAggregateType(*type) ||
      IsRealType(type->kind))
    return nullptr;
  return type;
}

std::optional<ConstVal> FoldLeaf(const LocatedPart& part) {
  const DataType& type = part.reader.type;
  const PartState& state = part.state;
  FrameGuard guard(state.frame);
  const ScopeMap& scope = *state.frame.scope;
  if (IsImplicitType(type)) return ConstEvalFull(state.value, scope);
  const Expr* pattern = Untyped(state.value);
  std::optional<int64_t> folded =
      pattern->kind == ExprKind::kAssignmentPattern
          ? FoldPackedStructPattern(pattern, type, Typedefs(), scope)
          : FoldDeclaredParamValue(state.value, type, scope);
  if (!folded) return std::nullopt;
  uint32_t width = DeclaredParamTypeWidth(type, *part.reader.scope);
  return NormalizeConstVal(*folded, width == 0 ? 32 : width,
                           IsSignedType(type, Typedefs()));
}

}  // namespace

bool NamesAggregateParam(const Expr* expr) {
  static const ScopeMap kNoScope;
  return RootState(expr, kNoScope).has_value();
}

std::optional<ConstVal> ConstEvalAggregatePart(const Expr* expr,
                                               const ScopeMap& scope) {
  if (!IsPartStep(expr)) return std::nullopt;
  std::optional<LocatedPart> part = LocatePart(expr, scope, 0);
  if (!part || LeafType(part->reader) == nullptr) return std::nullopt;
  return FoldLeaf(*part);
}

std::optional<PackedRange> AggregatePartRange(const Expr* expr,
                                              const ScopeMap& scope) {
  if (!IsPartStep(expr)) return std::nullopt;
  std::optional<LocatedPart> part = LocatePart(expr, scope, 0);
  if (!part) return std::nullopt;
  const DataType* type = LeafType(part->reader);
  if (type == nullptr || type->packed_dim_left == nullptr ||
      type->packed_dim_right == nullptr)
    return std::nullopt;
  std::optional<int64_t> left =
      ConstEvalInt(type->packed_dim_left, *part->reader.scope);
  std::optional<int64_t> right =
      ConstEvalInt(type->packed_dim_right, *part->reader.scope);
  if (!left || !right) return std::nullopt;
  return PackedRange{*left, *right};
}

}  // namespace delta
