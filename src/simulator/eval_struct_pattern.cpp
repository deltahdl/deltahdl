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

// §10.9.2's structure assignment patterns, and the packed array patterns that
// share their placement of a value at a member's bits.

namespace delta {

// §10.9.2 places a member's value at the bits the member occupies in the packed
// result. DepositBitField resolves the word each bit falls in and carries the
// bval plane, which is what the two halves of this need: a member of a struct
// wider than one word sits at a bit offset of 64 or more, where the shift this
// once made was undefined behaviour rather than a placement, and §6.3.1 lets
// every bit of a 4-state member be x or z, which a uint64_t value could not
// express and an OR into aval could not have cleared. ExtractBitField is the
// coercion the mask here used to be -- §10.9.2 evaluates each member expression
// as though it were assigned to that member's type -- zero-filling a narrower
// value and truncating a wider one across every word rather than the first.
//
// The deposit assigns each bit where the placements used to OR into a zeroed
// result. That is what makes an x depositable at all, and nothing accumulates
// across placements: §10.9.2's demand that one of these rules cover every
// member is exactly what PatternState::assigned enforces, so no two of the
// three rules write one member's bits.
// §10.9.2 (printed page 263) with §5.7.1 (printed 78): a member's value is
// the expression assigned to the member, so an unbased unsized literal,
// `'{default: '1}` or a positional `'1`, sets every bit of the member; any
// other value is the member's width of its low bits, as before.
static Logic4Vec MemberBits(const Logic4Vec& val, uint32_t width,
                            Arena& arena) {
  if (val.fills_width && width > val.width)
    return FillUnbasedUnsized(val, width, arena);
  return ExtractBitField(arena, val, 0, width);
}

// §10.9 with §10.9.1 (printed pages 261-262): a positional pattern for a
// packed array fills it element for element, each item converted to the
// element as an assignment to the element converts it, and an item that is
// itself a pattern fills its element over the next dimension the same way.
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

// §10.9.2 with §6.16: the bits one element of `f`'s type holds for `val`, a
// string (§7.2) as a handle to its text and any other value `width` bits of
// it, for a member that is no array or an element of one that is.
static Logic4Vec ElementBits(const StructFieldInfo& f, const Logic4Vec& val,
                             uint32_t width, Arena& arena) {
  return f.type_kind == DataTypeKind::kString ? StringMemberHandle(val, arena)
                                              : MemberBits(val, width, arena);
}

// §10.9.2: `val`, the member's whole value, placed as the member `f` of the
// structure `result` holds, a string member as a handle to the string; `base`
// is the offset within `result` of the substructure `f` belongs to. An array
// member's value already holds each element's bits, a string element's handle
// among them (EvalArrayMemberPattern), and is placed as it stands; taken as one
// string, an array of strings was one handle across every element.
static void PlaceFieldValue(Logic4Vec& result, const StructFieldInfo& f,
                            const Logic4Vec& val, Arena& arena,
                            uint32_t base = 0) {
  Logic4Vec bits = f.elem_count == 0 ? ElementBits(f, val, f.width, arena)
                                     : MemberBits(val, f.width, arena);
  DepositBitField(result, base + f.bit_offset, bits, f.width);
}

// §10.9.2 (printed page 264): the value of a type key or the default: key
// placed as the member `f`. For an unpacked array member the keys are applied
// by the rules for arrays (§10.9.1), so each element takes the value as an
// assignment to the element would; placed across the member as one value,
// `int a [2]` held a scalar in a[1] alone and `string v [2]` one handle that
// neither element read.
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

DataTypeKind PatternTypeKeyKind(std::string_view key) {
  if (key == "int") return DataTypeKind::kInt;
  if (key == "integer") return DataTypeKind::kInteger;
  if (key == "logic") return DataTypeKind::kLogic;
  if (key == "reg") return DataTypeKind::kReg;
  if (key == "byte") return DataTypeKind::kByte;
  if (key == "shortint") return DataTypeKind::kShortint;
  if (key == "longint") return DataTypeKind::kLongint;
  if (key == "bit") return DataTypeKind::kBit;
  if (key == "real") return DataTypeKind::kReal;
  if (key == "shortreal") return DataTypeKind::kShortreal;
  if (key == "string") return DataTypeKind::kString;
  if (key == "time") return DataTypeKind::kTime;
  if (key == "realtime") return DataTypeKind::kRealtime;
  return DataTypeKind::kImplicit;
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

// §10.9.2 (printed page 263): each member expression is evaluated in the
// context of an assignment to the type of the member it initializes, by
// position or by name, and §7.2.1 gives a member that is itself a structure a
// layout of its own (StructFieldInfo::nested). An element that is a pattern,
// bare or typed, for such a member was evaluated as any expression is, with
// no type to place it by, so its elements were concatenated in written order
// at their self-determined widths: `s = '{'{b: 2, a: 1}, 3}` swapped the
// nested members, and `'{p: '{8'd1, 8'd2}, c: 3}` packed two bytes into the
// low end of p. The value of the member's expression: a pattern for a nested
// structure placed by that structure's layout, as the enclosing pattern is by
// `info`'s, and any other expression evaluated as it was.
// §10.9.1: the items a pattern for an array lists, in order, a replication
// `'{4{1}}` or `'{2{a, b}}` giving its items that many times over.
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

// §10.9.1 with §7.2 and §7.4.2: a pattern for an unpacked array member gives
// each of its elements a value, left to right, each evaluated as assigned to
// the element's type, the leftmost element in the member's most significant
// bits. Concatenated at their own widths, `'{2, 3, 4, 5}` for `byte
// data[4]` left the four 32-bit values' low 32 bits, one byte of them 5.
// Nothing where the pattern lists other than one item per element. An element
// of strings holds a handle to its item's whole text (§6.16), the item
// evaluated at its own width; cut to the element's 64 bits, `"abcdefghij"`
// lost its first two characters and named no text.
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
  // §10.9.2 with §7.5: the item of a dynamic array member, a pattern or an
  // initializer, gives it the elements the item lists, held under a new
  // handle, which is the member's value.
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

// The type keys and the default key of one structure pattern, each value
// evaluated once: the last key written of each type, which §10.9.2 has
// override an earlier one, and the default with the name of the structure type
// its value has, empty where it has none.
namespace {
struct TypeAndDefaultKeys {
  std::vector<std::pair<PatternKeyType, Logic4Vec>> types;
  bool has_default = false;
  Logic4Vec default_value;
  std::string_view default_type;
  // The context the keys' typedef names and the members' are resolved in.
  const SimContext* ctx = nullptr;
};
}  // namespace

// The name of the type a structure layout registered as `name` is of. A
// variable's own layout is registered under the variable's name
// (RegisterAggregateLayout), which stands for the type its declaration wrote,
// spelled as a member's layout spells it, "scope::name" for a scoped one; any
// other registration is under the type's name. Taken as the type, a variable's
// registration matched no member's, so `'{default: pv}` spread pv over a
// member of pv's own type.
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

// The name of the structure type `value` has as a variable of one, which a
// default value carries whole onto a member of that type; empty for any other
// expression.
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
    // Syntax 10-5: a key is a built-in type keyword or a typedef name, and
    // the keys are gathered last written first, so the first that matches a
    // member is the one §10.9.2 has override the others.
    std::optional<PatternKeyType> type = ResolvePatternKeyType(key, ctx);
    if (!type) continue;
    keys.types.emplace_back(*type, EvalExpr(expr->elements[i], ctx, arena));
  }
  return keys;
}

// §10.9.2 (printed page 264): the value a member no member key named takes,
// with `base` the offset of the substructure it belongs to. A type key of the
// member's type gives it its value. Failing that, an unmatched member that is
// itself a structure has the type keys and the default applied to each of its
// members in turn -- unless the default's own type is that structure, which
// it is then assigned whole -- and any other member takes the default.
// Applied to the top-level members alone, the type keys never reached a
// nested structure's members, and a default of a member's own type was spread
// over its fields.
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

// §5.10 and §10.9.2: the items a positional pattern gives, one per member, a
// replication `'{N{a, b}}` -- held by the pattern itself or by its one
// element -- spelled out as its items N times over, so each member takes one.
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
  // Keyed form (member name / type / default keys): field-by-field placement.
  if (!expr->pattern_keys.empty())
    return EvalStructPattern(expr, info, ctx, arena);

  // §10.9.2: positional form -- element i initializes member i in declaration
  // order, each evaluated in the context of an assignment to that member's
  // type. Coercing each element to its member's width (rather than
  // concatenating at its self-determined width) is what keeps an over-wide
  // element from spilling into the following members, and a nested pattern
  // is placed by its member's own layout (EvalMemberExpr). A replication gives
  // the items PatternItems spells out, one per member as well; a pattern with
  // other than one item per member falls back to the width-summing
  // concatenation path. A structure wider than a word took
  // that path too, from before PlaceFieldValue deposited a member above the
  // first word; the placement now reaches any width, and the fallback left
  // `'{'{1, 2}, 3}` for a 96-bit structure concatenated, its nested pattern
  // never reaching the member's layout.
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
