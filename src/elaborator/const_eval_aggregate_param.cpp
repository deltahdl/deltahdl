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
#include "elaborator/elaborator_items_params.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_key_match.h"
#include "elaborator/unit_param_values.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kMaxLocateDepth = 256;
int g_locate_depth = 0;

class LocateDepth {
 public:
  LocateDepth() { ++g_locate_depth; }
  ~LocateDepth() { --g_locate_depth; }
  LocateDepth(const LocateDepth&) = delete;
  LocateDepth& operator=(const LocateDepth&) = delete;
  LocateDepth(LocateDepth&&) = delete;
  LocateDepth& operator=(LocateDepth&&) = delete;
};

const DataType& ResolvedType(const DataType& type) {
  return LastTypeInChain(type, RegisteredTypedefsOrNone());
}

bool HoldsAggregate(const DataType& type) {
  const DataType& resolved = ResolvedType(type);
  return resolved.kind == DataTypeKind::kStruct ||
         resolved.kind == DataTypeKind::kUnion;
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
  LocalNameFrame names_;
};

struct PartShape {
  DataType type;
  std::vector<Expr*> dims;
  size_t dim_at = 0;
  const ScopeMap* scope = nullptr;

  [[nodiscard]] bool HasDims() const { return dim_at < dims.size(); }
};

struct PartState {
  const Expr* value = nullptr;
  ValueFrame frame;
  PartShape shape;
  bool inherited = false;
};

struct LocatedPart {
  PartState state;
  PartShape reader;
  uint32_t offset = 0;
};

struct Slot {
  size_t position = 0;
  const StructMember* member = nullptr;
  int64_t index = 0;
};

struct PickedItem {
  const Expr* value = nullptr;
  bool inherited = false;
};

struct PackedLevel {
  const Expr* left = nullptr;
  const Expr* right = nullptr;
  DataType element;
  bool is_signed = false;
};

struct PackedPart {
  ConstVal value{0, 0, false};
  uint32_t width = 0;
};

enum class LeafKind : uint8_t { kAggregate, kIntegral, kReal, kString };

bool IsTypedPattern(const Expr* value) {
  return value->kind == ExprKind::kCast &&
         value->lhs->kind == ExprKind::kAssignmentPattern;
}

const Expr* Untyped(const Expr* value) {
  return IsTypedPattern(value) ? value->lhs : value;
}

bool IsPattern(const Expr* value) {
  return Untyped(value)->kind == ExprKind::kAssignmentPattern;
}

bool IsPartStep(const Expr* expr) {
  if (expr->kind == ExprKind::kSelect) return expr->index_end == nullptr;
  return expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution;
}

const Expr* StepBase(const Expr* step) {
  return step->kind == ExprKind::kSelect ? step->base : step->lhs;
}

ValueFrame CurrentFrame(const ScopeMap& scope) {
  return ValueFrame{RegisteredModule(), &scope, RegisteredGenPrefixes(),
                    CurrentUnitNamePrefix()};
}

bool NamesDims(const std::vector<Expr*>* dims) { return dims != nullptr; }

std::vector<Expr*> DimsOf(const std::vector<Expr*>* dims) {
  return NamesDims(dims) ? *dims : std::vector<Expr*>{};
}

const DataType* ParamValueType(const RtlirParamDecl& pd) {
  return pd.type_param_actual != nullptr ? pd.type_param_actual : pd.decl_type;
}

std::optional<PartState> ModuleParamState(const RtlirParamDecl& pd,
                                          const ScopeMap& scope) {
  const DataType* type = ParamValueType(pd);
  if (type == nullptr ||
      (!NamesDims(pd.unpacked_dims) && !HoldsAggregate(*type)))
    return std::nullopt;
  PartState state{pd.default_value, CurrentFrame(scope),
                  PartShape{*type, DimsOf(pd.unpacked_dims), 0, &scope}};
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

PartState UnitParamState(const UnitParamValue& param) {
  return PartState{param.value,
                   ValueFrame{nullptr, &param.scope, {}, param.prefix},
                   PartShape{param.type, DimsOf(param.dims), 0, &param.scope}};
}

const UnitParamValue* ImportedByModule(const RtlirModule& mod,
                                       std::string_view name) {
  for (const RtlirImport& imp : mod.imports) {
    if (const UnitParamValue* found = FindUnitParamValueImported(
            {imp.package_name, imp.item_name, imp.is_wildcard}, name))
      return found;
  }
  return nullptr;
}

const UnitParamValue* NamedUnitRoot(std::string_view name) {
  if (const UnitParamValue* own = FindUnitParamValueOwn(name)) return own;
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return FindUnitParamValueInTheCompilationUnit(name);
  if (const UnitParamValue* imported = ImportedByModule(*mod, name))
    return imported;
  return FindUnitParamValue(name);
}

const UnitParamValue* UnitRoot(const Expr* root) {
  if (root->kind == ExprKind::kMemberAccess) {
    if (!root->is_scope_resolution) return nullptr;
    return FindUnitParamValue(ScopedNameKey(root).value_or(""));
  }
  if (root->kind != ExprKind::kIdentifier) return nullptr;
  if (root->scope_prefix == "$unit") return FindUnitParamValue(root->text);
  if (!root->scope_prefix.empty()) return nullptr;
  return NamedUnitRoot(root->text);
}

std::optional<PartState> RootState(const Expr* root, const ScopeMap& scope) {
  if (root->kind == ExprKind::kIdentifier && root->scope_prefix.empty()) {
    if (const RtlirParamDecl* pd = RegisteredParamNamed(root->text))
      return ModuleParamState(*pd, scope);
  }
  const UnitParamValue* param = UnitRoot(root);
  if (param == nullptr ||
      (!NamesDims(param->dims) && !HoldsAggregate(param->type)))
    return std::nullopt;
  return UnitParamState(*param);
}

std::optional<RtlirUnpackedDim> ShapeDim(const PartShape& shape) {
  return FoldUnpackedDimBounds(shape.dims[shape.dim_at], *shape.scope);
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

int64_t IndexAt(const PartShape& shape, int64_t pos) {
  RtlirUnpackedDim dim = ShapeDim(shape).value_or(RtlirUnpackedDim{});
  return dim.left <= dim.right ? dim.left + pos : dim.left - pos;
}

const StructMember* MemberNamed(const DataType& type, std::string_view name,
                                size_t& index) {
  const std::vector<StructMember>& members = ResolvedType(type).struct_members;
  auto it = std::ranges::find(members, name, &StructMember::name);
  if (it == members.end()) return nullptr;
  index = static_cast<size_t>(it - members.begin());
  return &*it;
}

PartShape MemberShape(const PartShape& owner, const StructMember& member) {
  return PartShape{MemberWrittenType(member), member.unpacked_dims, 0,
                   owner.scope};
}

std::optional<Slot> ReaderStep(const Expr* step, const PartShape& owner,
                               PartShape& shape, const ScopeMap& scope) {
  if (step->kind == ExprKind::kSelect) {
    if (!shape.HasDims()) return std::nullopt;
    std::optional<int64_t> pos = PositionOf(shape, step->index, scope);
    if (!pos) return std::nullopt;
    ++shape.dim_at;
    return Slot{static_cast<size_t>(*pos), nullptr, 0};
  }
  if (shape.HasDims()) return std::nullopt;
  Slot slot;
  slot.member = MemberNamed(owner.type, step->rhs->text, slot.position);
  if (slot.member == nullptr) return std::nullopt;
  shape = MemberShape(owner, *slot.member);
  return slot;
}

bool IsDefaultKey(const Expr* key) {
  return key->kind == ExprKind::kIdentifier && key->text == "default";
}

bool IsTypeNameKey(const Expr* key) {
  return key->kind == ExprKind::kIdentifier &&
         IsTypeKey(key->text, RegisteredTypedefsOrNone());
}

bool IsKeyed(const Expr* pattern) { return !pattern->pattern_keys.empty(); }

std::optional<PickedItem> PositionalItem(const Expr* pattern, size_t pos) {
  if (const Expr* rep = PatternReplication(pattern))
    return PickedItem{rep->elements[pos % rep->elements.size()], false};
  if (pos >= pattern->elements.size()) return std::nullopt;
  return PickedItem{pattern->elements[pos], false};
}

std::optional<PackedLevel> PackedOuter(const DataType& type) {
  const DataType& written =
      type.packed_dim_left != nullptr ? type : ResolvedType(type);
  if (written.packed_dim_left == nullptr) return std::nullopt;
  PackedLevel level{written.packed_dim_left, written.packed_dim_right, written,
                    written.is_signed};
  DataType& element = level.element;
  element.is_signed = false;
  element.packed_dim_left = nullptr;
  element.packed_dim_right = nullptr;
  if (!element.extra_packed_dims.empty()) {
    element.packed_dim_left = element.extra_packed_dims.front().first;
    element.packed_dim_right = element.extra_packed_dims.front().second;
    element.extra_packed_dims.erase(element.extra_packed_dims.begin());
  } else if (element.kind == DataTypeKind::kImplicit ||
             element.kind == DataTypeKind::kEnum) {
    element.kind = DataTypeKind::kLogic;
  }
  return level;
}

PackedRange LevelRange(const PackedLevel& level, const ScopeMap& bounds) {
  return PackedRange{ConstEvalInt(level.left, bounds).value_or(0),
                     ConstEvalInt(level.right, bounds).value_or(0)};
}

bool Opens(const PartShape& shape) {
  if (shape.HasDims()) return true;
  if (std::optional<PackedLevel> level = PackedOuter(shape.type)) {
    return ResolvedType(level->element).packed_dim_left != nullptr ||
           HoldsAggregate(level->element);
  }
  return ResolvedType(shape.type).kind == DataTypeKind::kStruct;
}

bool TypeKeyMatches(const Expr* key, const PartShape& target) {
  return !target.HasDims() && IsTypeNameKey(key) &&
         TypeKeyMatchesType(key->text, target.type, RegisteredTypedefsOrNone());
}

std::optional<LocatedPart> LocatePart(const Expr* expr, const ScopeMap& scope);

bool AppliesWhole(const Expr* value, const PartState& state) {
  if (IsTypedPattern(value)) return true;
  FrameGuard guard(state.frame);
  std::optional<LocatedPart> part = LocatePart(value, *state.frame.scope);
  return part.has_value() && Opens(part->reader);
}

std::optional<PickedItem> TypeOrDefault(const PartState& state,
                                        const PartShape& target) {
  const Expr* pattern = Untyped(state.value);
  const Expr* typed = nullptr;
  const Expr* fallback = nullptr;
  for (size_t i = 0; i < pattern->pattern_keys.size(); ++i) {
    const Expr* key = pattern->pattern_keys[i];
    if (IsDefaultKey(key))
      fallback = pattern->elements[i];
    else if (TypeKeyMatches(key, target))
      typed = pattern->elements[i];
  }
  if (typed != nullptr) return PickedItem{typed, false};
  if (Opens(target) && (fallback == nullptr || !AppliesWhole(fallback, state)))
    return PickedItem{state.value, true};
  if (fallback == nullptr) return std::nullopt;
  return PickedItem{fallback, false};
}

bool KeyNamesSlot(const Expr* key, const Slot& slot, const ScopeMap& scope) {
  if (slot.member != nullptr) return key->text == slot.member->name;
  return ConstEvalInt(key, scope) == slot.index;
}

std::optional<PickedItem> Pick(const PartState& state, const Slot& slot,
                               const PartShape& target) {
  if (state.inherited) return TypeOrDefault(state, target);
  const Expr* pattern = Untyped(state.value);
  if (!IsKeyed(pattern)) return PositionalItem(pattern, slot.position);
  for (size_t i = 0; i < pattern->pattern_keys.size(); ++i) {
    if (KeyNamesSlot(pattern->pattern_keys[i], slot, *state.frame.scope))
      return PickedItem{pattern->elements[i], false};
  }
  return TypeOrDefault(state, target);
}

bool Descend(PartState& state, const Slot& slot, PartShape target) {
  FrameGuard guard(state.frame);
  std::optional<PickedItem> item = Pick(state, slot, target);
  if (!item) return false;
  state.value = item->value;
  state.inherited = item->inherited;
  state.shape = std::move(target);
  return true;
}

bool Advance(PartState& state, Slot slot) {
  if (state.shape.HasDims() != (slot.member == nullptr)) return false;
  if (slot.member != nullptr)
    return Descend(state, slot, MemberShape(state.shape, *slot.member));
  slot.index = IndexAt(state.shape, static_cast<int64_t>(slot.position));
  PartShape target = state.shape;
  ++target.dim_at;
  return Descend(state, slot, std::move(target));
}

bool IsPackedLevel(const PartShape& shape) {
  return !shape.HasDims() && !IsUnpackedAggregateType(ResolvedType(shape.type));
}

uint32_t PartWidth(const DataType& type, const ScopeMap& scope) {
  uint32_t width = DeclaredParamTypeWidth(type, scope);
  return width == 0 ? 32 : width;
}

bool SliceElement(LocatedPart& part, const Expr* step, const ScopeMap& scope) {
  std::optional<PackedLevel> level = PackedOuter(part.reader.type);
  if (!level) return false;
  const ScopeMap& bounds = *part.reader.scope;
  const PackedRange kRange = LevelRange(*level, bounds);
  std::optional<int64_t> index = ConstEvalInt(step->index, scope);
  if (!index || !kRange.Contains(*index)) return false;
  part.offset += static_cast<uint32_t>(kRange.OffsetOf(*index)) *
                 PartWidth(level->element, bounds);
  part.reader.type = std::move(level->element);
  return true;
}

bool SliceStep(LocatedPart& part, const Expr* step, const ScopeMap& scope) {
  if (step->kind == ExprKind::kSelect) return SliceElement(part, step, scope);
  size_t index = 0;
  const StructMember* member =
      MemberNamed(part.reader.type, step->rhs->text, index);
  if (member == nullptr) return false;
  const DataType& owner = ResolvedType(part.reader.type);
  for (size_t i = index + 1;
       owner.kind == DataTypeKind::kStruct && i < owner.struct_members.size();
       ++i) {
    part.offset += PartWidth(MemberWrittenType(owner.struct_members[i]),
                             *part.reader.scope);
  }
  part.reader.type = MemberWrittenType(*member);
  return true;
}

bool Normalize(PartState& state) {
  if (state.inherited || IsPattern(state.value)) return true;
  LocateDepth depth;
  std::optional<LocatedPart> followed;
  {
    FrameGuard guard(state.frame);
    followed = LocatePart(state.value, *state.frame.scope);
  }
  if (!followed) return false;
  state = std::move(followed->state);
  return Normalize(state);
}

bool TakeStep(LocatedPart& part, const Expr* step, const ScopeMap& scope) {
  if (IsPackedLevel(part.reader)) return SliceStep(part, step, scope);
  const PartShape kOwner = part.reader;
  std::optional<Slot> slot = ReaderStep(step, kOwner, part.reader, scope);
  return slot && Normalize(part.state) && Advance(part.state, *slot);
}

std::optional<LocatedPart> LocatePart(const Expr* expr, const ScopeMap& scope) {
  LocateDepth depth;
  if (g_locate_depth > kMaxLocateDepth) return std::nullopt;
  std::vector<const Expr*> chain;
  const Expr* root = expr;
  while (IsPartStep(root)) {
    chain.push_back(root);
    root = StepBase(root);
  }
  std::optional<PartState> state = RootState(root, scope);
  if (!state) return std::nullopt;
  LocatedPart part{*state, state->shape};
  for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
    if (!TakeStep(part, *it, scope)) return std::nullopt;
  }
  return part;
}

std::optional<ConstVal> FoldPacked(const PartState& state);

bool AppendPart(std::vector<PackedPart>& parts, const PartState& owner,
                const Slot& slot, const PartShape& target) {
  PartState part = owner;
  if (!Descend(part, slot, target)) return false;
  std::optional<ConstVal> value = FoldPacked(part);
  if (!value) return false;
  parts.push_back(PackedPart{*value, PartWidth(target.type, *target.scope)});
  return true;
}

ConstVal JoinedParts(const std::vector<PackedPart>& parts, bool is_signed) {
  uint32_t total = 0;
  for (const PackedPart& part : parts) total += part.width;
  std::vector<uint64_t> words(total / 64 + 1, 0);
  uint32_t offset = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    for (uint32_t bit = 0; bit < it->width; ++bit) {
      if (ConstValBit(it->value, bit))
        words[(offset + bit) / 64] |= uint64_t{1} << ((offset + bit) % 64);
    }
    offset += it->width;
  }
  return ConstValOfWords(words, total, is_signed);
}

std::optional<ConstVal> ComposeMembers(const PartState& state) {
  const DataType& type = ResolvedType(state.shape.type);
  std::vector<PackedPart> parts;
  for (size_t i = 0; i < type.struct_members.size(); ++i) {
    const StructMember& member = type.struct_members[i];
    if (!AppendPart(parts, state, Slot{i, &member, 0},
                    MemberShape(state.shape, member)))
      return std::nullopt;
  }
  return JoinedParts(parts, type.is_signed);
}

std::optional<ConstVal> ComposeElements(const PartState& state,
                                        const PackedLevel& level) {
  const ScopeMap& bounds = *state.shape.scope;
  int64_t left = ConstEvalInt(level.left, bounds).value_or(0);
  int64_t right = ConstEvalInt(level.right, bounds).value_or(0);
  int64_t count = (left >= right ? left - right : right - left) + 1;
  PartShape element{level.element, {}, 0, state.shape.scope};
  std::vector<PackedPart> parts;
  for (int64_t pos = 0; pos < count; ++pos) {
    Slot slot{static_cast<size_t>(pos), nullptr,
              left <= right ? left + pos : left - pos};
    if (!AppendPart(parts, state, slot, element)) return std::nullopt;
  }
  return JoinedParts(parts, level.is_signed);
}

std::optional<ConstVal> FoldPacked(const PartState& state) {
  if (state.inherited || IsPattern(state.value)) {
    if (std::optional<PackedLevel> level = PackedOuter(state.shape.type))
      return ComposeElements(state, *level);
    return ComposeMembers(state);
  }
  FrameGuard guard(state.frame);
  const ScopeMap& scope = *state.frame.scope;
  const DataType& type = state.shape.type;
  if (TakesItsTypeFromItsValue(type)) return ConstEvalFull(state.value, scope);
  std::optional<int64_t> folded = FoldRealValueAsInteger(state.value, scope);
  if (!folded) folded = FoldDeclaredParamValue(state.value, type, scope);
  if (!folded) return std::nullopt;
  return NormalizeConstVal(*folded, PartWidth(type, *state.shape.scope),
                           IsSignedType(type, RegisteredTypedefsOrNone()));
}

ConstVal SlicedBits(const ConstVal& whole, uint32_t offset, uint32_t width,
                    bool is_signed) {
  std::vector<uint64_t> words(width / 64 + 1, 0);
  for (uint32_t bit = 0; bit < width; ++bit) {
    if (ConstValBit(whole, offset + bit))
      words[bit / 64] |= uint64_t{1} << (bit % 64);
  }
  return ConstValOfWords(words, width, is_signed);
}

LeafKind KindOfLeaf(const PartShape& reader) {
  const DataType& type = ResolvedType(reader.type);
  if (reader.HasDims() || IsUnpackedAggregateType(type))
    return LeafKind::kAggregate;
  if (IsRealType(type.kind)) return LeafKind::kReal;
  return type.kind == DataTypeKind::kString ? LeafKind::kString
                                            : LeafKind::kIntegral;
}

std::optional<ConstVal> FoldIntegral(const LocatedPart& part) {
  std::optional<ConstVal> whole = FoldPacked(part.state);
  const DataType& type = part.reader.type;
  if (!whole || TakesItsTypeFromItsValue(type)) return whole;
  return SlicedBits(*whole, part.offset, PartWidth(type, *part.reader.scope),
                    IsSignedType(type, RegisteredTypedefsOrNone()));
}

std::optional<ConstVal> FoldLeaf(const LocatedPart& part) {
  LeafKind kind = KindOfLeaf(part.reader);
  if (kind == LeafKind::kIntegral) return FoldIntegral(part);
  if (kind != LeafKind::kString) return std::nullopt;
  FrameGuard guard(part.state.frame);
  return ConstEvalStringLiteral(part.state.value, *part.state.frame.scope);
}

double AsReal(const ConstVal& value) {
  return static_cast<double>(value.value);
}

const UnitParamValue* ScalarUnitRoot(const Expr* expr) {
  const UnitParamValue* param = UnitRoot(expr);
  if (param == nullptr) return nullptr;
  LeafKind kind = KindOfLeaf(UnitParamState(*param).shape);
  return kind == LeafKind::kReal || kind == LeafKind::kString ? param : nullptr;
}

std::optional<PartShape> RootShape(const Expr* root, const ScopeMap& scope) {
  if (root->kind == ExprKind::kIdentifier && root->scope_prefix.empty()) {
    if (const RtlirParamDecl* pd = RegisteredParamNamed(root->text))
      return PartShape{*ParamValueType(*pd), DimsOf(pd->unpacked_dims), 0,
                       &scope};
  }
  const UnitParamValue* param = UnitRoot(root);
  if (param == nullptr) return std::nullopt;
  return UnitParamState(*param).shape;
}

std::optional<PackedLevel> PackedLevelOf(const PartShape& shape) {
  if (shape.HasDims()) return std::nullopt;
  return PackedOuter(shape.type);
}

std::optional<PartShape> StepShape(PartShape shape, const Expr* step,
                                   const ScopeMap& scope) {
  if (step->kind == ExprKind::kSelect) {
    if (std::optional<PackedLevel> level = PackedLevelOf(shape)) {
      shape.type = std::move(level->element);
      return shape;
    }
  }
  const PartShape kOwner = shape;
  return ReaderStep(step, kOwner, shape, scope)
      .transform([&shape](const Slot&) { return shape; });
}

std::optional<PartShape> ShapeOfRead(const Expr* expr, const ScopeMap& scope) {
  if (!IsPartStep(expr)) return RootShape(expr, scope);
  return ShapeOfRead(StepBase(expr), scope)
      .and_then([expr, &scope](PartShape shape) {
        return StepShape(std::move(shape), expr, scope);
      });
}

std::optional<LocatedPart> LocateRead(const Expr* expr, const ScopeMap& scope) {
  if (IsPartStep(expr)) return LocatePart(expr, scope);
  const UnitParamValue* param = ScalarUnitRoot(expr);
  if (param == nullptr || g_locate_depth > kMaxLocateDepth) return std::nullopt;
  PartState state = UnitParamState(*param);
  PartShape reader = state.shape;
  return LocatedPart{std::move(state), std::move(reader)};
}

}  // namespace

bool NamesAggregateParam(const Expr* expr) {
  static const ScopeMap kNoScope;
  return RootState(expr, kNoScope).has_value();
}

bool NamesScalarUnitParam(const Expr* expr) {
  return ScalarUnitRoot(expr) != nullptr;
}

std::optional<ConstVal> ConstEvalAggregatePart(const Expr* expr,
                                               const ScopeMap& scope) {
  LocateDepth depth;
  std::optional<LocatedPart> part = LocateRead(expr, scope);
  if (!part) return std::nullopt;
  return FoldLeaf(*part);
}

std::optional<double> ConstEvalAggregatePartReal(const Expr* expr,
                                                 const ScopeMap& scope) {
  if (NamesSpecializedClassParam(expr))
    return ConstEvalSpecializedClassParamReal(expr, scope);
  LocateDepth depth;
  std::optional<LocatedPart> part = LocateRead(expr, scope);
  if (!part) return ConstEvalFull(expr, scope).transform(AsReal);
  if (KindOfLeaf(part->reader) != LeafKind::kReal)
    return FoldLeaf(*part).transform(AsReal);
  FrameGuard guard(part->state.frame);
  bool is_short =
      ResolvedType(part->reader.type).kind == DataTypeKind::kShortreal;
  return ConstEvalReal(part->state.value, *part->state.frame.scope)
      .transform([is_short](double value) {
        return is_short ? static_cast<double>(static_cast<float>(value))
                        : value;
      });
}

bool IsRealAggregatePart(const Expr* expr) {
  LocateDepth depth;
  std::optional<LocatedPart> part = LocateRead(expr, RegisteredModuleScope());
  return part.has_value() && KindOfLeaf(part->reader) == LeafKind::kReal;
}

std::optional<std::string> ConstEvalAggregatePartString(const Expr* expr,
                                                        const ScopeMap& scope) {
  if (NamesSpecializedClassParam(expr))
    return ConstEvalSpecializedClassParamString(expr, scope);
  LocateDepth depth;
  std::optional<LocatedPart> part = LocateRead(expr, scope);
  if (!part || KindOfLeaf(part->reader) != LeafKind::kString)
    return std::nullopt;
  FrameGuard guard(part->state.frame);
  return ConstEvalString(part->state.value, *part->state.frame.scope);
}

std::optional<PackedSelectBase> PackedSelectBaseOf(const Expr* expr,
                                                   const ScopeMap& scope) {
  std::optional<PartShape> shape = ShapeOfRead(expr, scope);
  if (!shape) return std::nullopt;
  std::optional<PackedLevel> level = PackedLevelOf(*shape);
  if (!level) return std::nullopt;
  const ScopeMap& bounds = *shape->scope;
  return PackedSelectBase{
      LevelRange(*level, bounds),
      DeclaredParamTypeWidth(level->element, bounds),
      IsSignedType(level->element, RegisteredTypedefsOrNone())};
}

}  // namespace delta
