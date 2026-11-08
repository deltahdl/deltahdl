#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/dyn_struct_member.h"
#include "simulator/evaluation.h"
#include "simulator/pattern_type_key.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/variable.h"

namespace delta {

static Logic4Vec MemberBits(const Logic4Vec& val, uint32_t width,
                            Arena& arena) {
  if (val.fills_width && width > val.width)
    return FillUnbasedUnsized(val, width, arena);
  return ExtractBitField(arena, val, 0, width);
}

static Logic4Vec PackedArrayItem(const Expr* item,
                                 std::span<const uint32_t> inner,
                                 uint32_t elem_width, SimContext& ctx,
                                 Arena& arena) {
  if (item->kind == ExprKind::kAssignmentPattern && !inner.empty()) {
    if (auto nested =
            EvalPackedArrayPattern(item, inner, elem_width, ctx, arena))
      return *nested;
  }
  return MemberBits(EvalExpr(item, ctx, arena, elem_width), elem_width, arena);
}

std::optional<Logic4Vec> EvalPackedArrayPattern(const Expr* pattern,
                                                std::span<const uint32_t> spans,
                                                uint32_t width, SimContext& ctx,
                                                Arena& arena) {
  if (spans.empty() || pattern->repeat_count != nullptr ||
      !pattern->pattern_keys.empty())
    return std::nullopt;
  uint32_t count = spans.front();
  if (count == 0 || width % count != 0 || pattern->elements.size() != count)
    return std::nullopt;
  uint32_t elem_width = width / count;
  Logic4Vec result = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < count; ++i) {
    Logic4Vec bits = PackedArrayItem(pattern->elements[i], spans.subspan(1),
                                     elem_width, ctx, arena);
    DepositBitField(result, (count - 1 - i) * elem_width, bits, elem_width);
  }
  return result;
}

static Logic4Vec ElementBits(const StructFieldInfo& f, const Logic4Vec& val,
                             uint32_t width, Arena& arena) {
  if (f.type_kind == DataTypeKind::kString)
    return StringMemberHandle(val, arena);
  const bool kRealMember = IsRealMemberKind(f.type_kind);
  if (!kRealMember && !val.is_real) return MemberBits(val, width, arena);
  Logic4Vec converted = ConvertRealForKnownLhs(val, kRealMember, width, arena);
  converted.is_real = false;
  return converted;
}

static void PlaceFieldValue(Logic4Vec& result, const StructFieldInfo& f,
                            const Logic4Vec& val, Arena& arena,
                            uint32_t base = 0) {
  Logic4Vec bits = f.elem_count == 0 ? ElementBits(f, val, f.width, arena)
                                     : MemberBits(val, f.width, arena);
  DepositBitField(result, base + f.bit_offset, bits, f.width);
}

static void PlaceKeyValue(Logic4Vec& result, const StructFieldInfo& f,
                          const Logic4Vec& val, Arena& arena,
                          uint32_t base = 0) {
  if (f.elem_count == 0) {
    PlaceFieldValue(result, f, val, arena, base);
    return;
  }
  uint32_t ew = f.width / f.elem_count;
  Logic4Vec bits = ElementBits(f, val, ew, arena);
  for (uint32_t i = 0; i < f.elem_count; ++i)
    DepositBitField(result, base + f.bit_offset + i * ew, bits, ew);
}

static bool IsMemberNameKey(std::string_view key, const StructTypeInfo* info) {
  for (const auto& f : info->fields) {
    if (f.name == key) return true;
  }
  return false;
}

struct PatternState {
  Logic4Vec& result;
  std::vector<bool>& assigned;
  SimContext& ctx;
  Arena& arena;
};

static std::vector<const Expr*> ArrayPatternItems(const Expr* pattern,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  std::vector<const Expr*> items;
  for (const Expr* e : pattern->elements) {
    if (!e->is_pattern_replication) {
      items.push_back(e);
      continue;
    }
    uint64_t n = EvalExpr(e->repeat_count, ctx, arena).ToUint64();
    for (uint64_t r = 0; r < n; ++r) {
      items.insert(items.end(), e->elements.begin(), e->elements.end());
    }
  }
  return items;
}

static std::optional<Logic4Vec> EvalArrayMemberPattern(
    const Expr* pattern, const StructFieldInfo& field, SimContext& ctx,
    Arena& arena) {
  std::vector<const Expr*> items = ArrayPatternItems(pattern, ctx, arena);
  if (items.size() != field.elem_count) return std::nullopt;
  uint32_t ew = field.width / field.elem_count;
  bool strings = field.type_kind == DataTypeKind::kString;
  Logic4Vec result = MakeLogic4Vec(arena, field.width);
  for (size_t i = 0; i < items.size(); ++i) {
    Logic4Vec val = EvalExpr(items[i], ctx, arena, strings ? 0 : ew);
    DepositBitField(result,
                    static_cast<uint32_t>(field.elem_count - 1 - i) * ew,
                    ElementBits(field, val, ew, arena), ew);
  }
  return result;
}

Logic4Vec EvalStructMemberValue(const Expr* elem, const StructFieldInfo& field,
                                SimContext& ctx, Arena& arena) {
  if (field.is_dynamic) {
    Logic4Vec handle;
    QueueObject* q = NewDynMember(field, handle, arena);
    std::vector<Logic4Vec> elems;
    CollectQueueElements(elem, ctx, arena, elems);
    SizeAndOwnQueueElements(*q, elems, arena);
    q->elements = std::move(elems);
    q->AssignFreshIds();
    return handle;
  }
  const Expr* pattern = UnwrapTypedPattern(elem);
  if (field.nested != nullptr && pattern->kind == ExprKind::kAssignmentPattern)
    return EvalStructPatternValue(pattern, field.nested, ctx, arena);
  if (field.elem_count > 0 && pattern->kind == ExprKind::kAssignmentPattern) {
    if (auto val = EvalArrayMemberPattern(pattern, field, ctx, arena))
      return *val;
  }
  return EvalExpr(elem, ctx, arena);
}

static void ApplyMemberKeys(const Expr* expr, const StructTypeInfo* info,
                            PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size()) break;
    auto key = expr->pattern_keys[i]->text;
    if (!IsMemberNameKey(key, info)) continue;
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (info->fields[fi].name != key) continue;
      auto val = EvalStructMemberValue(expr->elements[i], info->fields[fi],
                                       s.ctx, s.arena);
      PlaceFieldValue(s.result, info->fields[fi], val, s.arena);
      s.assigned[fi] = true;
      break;
    }
  }
}

namespace {
struct TypeAndDefaultKeys {
  std::vector<std::pair<PatternKeyType, Logic4Vec>> types;
  bool has_default = false;
  Logic4Vec default_value;
  std::string_view default_type;
  const SimContext* ctx = nullptr;
};
}  // namespace

static std::string_view LayoutTypeName(std::string_view name, SimContext& ctx) {
  const Variable* var = ctx.FindVariable(name);
  if (var == nullptr || var->declared_type == nullptr ||
      var->declared_type->type_name.empty())
    return name;
  const DataType* t = var->declared_type;
  if (t->scope_name.empty()) return t->type_name;
  return *ctx.GetArena().Create<std::string>(std::string(t->scope_name) +
                                             "::" + std::string(t->type_name));
}

static std::string_view StructTypeOfValue(const Expr* value, SimContext& ctx) {
  if (value->kind != ExprKind::kIdentifier) return {};
  const StructTypeInfo* layout = ctx.GetVariableStructType(value->text);
  return layout != nullptr ? LayoutTypeName(layout->type_name, ctx)
                           : std::string_view{};
}

static TypeAndDefaultKeys CollectTypeAndDefaultKeys(const Expr* expr,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  TypeAndDefaultKeys keys;
  keys.ctx = &ctx;
  size_t n = std::min(expr->pattern_keys.size(), expr->elements.size());
  for (size_t ri = n; ri > 0; --ri) {
    size_t i = ri - 1;
    std::string_view key = expr->pattern_keys[i]->text;
    if (key == "default") {
      keys.has_default = true;
      keys.default_value = EvalExpr(expr->elements[i], ctx, arena);
      keys.default_type = StructTypeOfValue(expr->elements[i], ctx);
      continue;
    }
    std::optional<PatternKeyType> type = ResolvePatternKeyType(key, ctx);
    if (!type) continue;
    keys.types.emplace_back(*type, EvalExpr(expr->elements[i], ctx, arena));
  }
  return keys;
}

static void PlaceTypeOrDefault(Logic4Vec& result, const StructFieldInfo& f,
                               uint32_t base, const TypeAndDefaultKeys& keys,
                               Arena& arena) {
  for (const auto& [type, val] : keys.types) {
    if (!PatternKeyMatches(type, SubjectOfField(f, *keys.ctx))) continue;
    PlaceKeyValue(result, f, val, arena, base);
    return;
  }
  if (f.nested != nullptr &&
      (keys.default_type.empty() || f.nested->type_name != keys.default_type)) {
    for (const auto& sub : f.nested->fields)
      PlaceTypeOrDefault(result, sub, base + f.bit_offset, keys, arena);
    return;
  }
  if (keys.has_default) {
    PlaceKeyValue(result, f, keys.default_value, arena, base);
  }
}

static void ApplyTypeAndDefaultKeys(const Expr* expr,
                                    const StructTypeInfo* info,
                                    PatternState& s) {
  TypeAndDefaultKeys keys = CollectTypeAndDefaultKeys(expr, s.ctx, s.arena);
  for (size_t fi = 0; fi < info->fields.size(); ++fi) {
    if (s.assigned[fi]) continue;
    PlaceTypeOrDefault(s.result, info->fields[fi], 0, keys, s.arena);
  }
}

Logic4Vec EvalStructPattern(const Expr* expr, const StructTypeInfo* info,
                            SimContext& ctx, Arena& arena) {
  auto result = MakeLogic4Vec(arena, info->total_width);
  std::vector<bool> assigned(info->fields.size(), false);
  PatternState state{result, assigned, ctx, arena};
  ApplyMemberKeys(expr, info, state);
  ApplyTypeAndDefaultKeys(expr, info, state);
  return result;
}

void ApplyVariableLayoutDefaults(std::string_view name, Variable* var,
                                 SimContext& ctx, Arena& arena) {
  const StructTypeInfo* layout = ctx.GetVariableStructType(name);
  if (var != nullptr && layout != nullptr)
    ApplyLayoutDefaults(var->value, *layout, 0, ctx, arena);
}

void ApplyLayoutDefaults(Logic4Vec& value, const StructTypeInfo& layout,
                         uint32_t base, SimContext& ctx, Arena& arena) {
  if (layout.is_union) return;
  for (const auto& f : layout.fields) {
    if (f.default_expr != nullptr) {
      Logic4Vec v = EvalStructMemberValue(f.default_expr, f, ctx, arena);
      DepositBitField(value, base + f.bit_offset, MemberBits(v, f.width, arena),
                      f.width);
    } else if (f.nested != nullptr) {
      ApplyLayoutDefaults(value, *f.nested, base + f.bit_offset, ctx, arena);
    }
  }
}

Logic4Vec EvalItemForLayout(const Expr* item, const StructTypeInfo* layout,
                            SimContext& ctx, Arena& arena) {
  const Expr* pattern = UnwrapTypedPattern(item);
  if (layout != nullptr && pattern->kind == ExprKind::kAssignmentPattern)
    return EvalStructPatternValue(pattern, layout, ctx, arena);
  return EvalExpr(item, ctx, arena);
}

Logic4Vec EvalDefaultForElement(const Expr* value, const StructTypeInfo* layout,
                                SimContext& ctx, Arena& arena) {
  std::string_view value_type = StructTypeOfValue(value, ctx);
  if (layout == nullptr ||
      (!value_type.empty() &&
       value_type == LayoutTypeName(layout->type_name, ctx))) {
    return EvalExpr(value, ctx, arena);
  }
  auto* key = arena.Create<Expr>();
  key->kind = ExprKind::kIdentifier;
  key->text = "default";
  auto* pattern = arena.Create<Expr>();
  pattern->kind = ExprKind::kAssignmentPattern;
  pattern->range = value->range;
  pattern->pattern_keys.push_back(key);
  pattern->elements.push_back(const_cast<Expr*>(value));
  return EvalStructPatternValue(pattern, layout, ctx, arena);
}

static std::vector<const Expr*> PatternItems(const Expr* expr, SimContext& ctx,
                                             Arena& arena) {
  const Expr* rep = expr;
  if (expr->repeat_count == nullptr && expr->elements.size() == 1 &&
      expr->elements[0]->is_pattern_replication) {
    rep = expr->elements[0];
  }
  if (rep->repeat_count == nullptr) {
    return {expr->elements.begin(), expr->elements.end()};
  }
  auto count = EvalExpr(rep->repeat_count, ctx, arena).ToUint64();
  std::vector<const Expr*> items;
  for (uint64_t n = 0; n < count; ++n) {
    items.insert(items.end(), rep->elements.begin(), rep->elements.end());
  }
  return items;
}

Logic4Vec EvalStructPatternValue(const Expr* expr, const StructTypeInfo* info,
                                 SimContext& ctx, Arena& arena) {
  if (!expr->pattern_keys.empty())
    return EvalStructPattern(expr, info, ctx, arena);

  const std::vector<const Expr*> kItems = PatternItems(expr, ctx, arena);
  if (kItems.size() == info->fields.size()) {
    auto result = MakeLogic4Vec(arena, info->total_width);
    for (size_t i = 0; i < info->fields.size(); ++i) {
      auto val = EvalStructMemberValue(kItems[i], info->fields[i], ctx, arena);
      PlaceFieldValue(result, info->fields[i], val, arena);
    }
    return result;
  }
  return EvalAssignmentPattern(expr, ctx, arena);
}

}  // namespace delta
