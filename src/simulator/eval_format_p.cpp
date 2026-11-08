#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/assoc_index.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_format_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/variable.h"

namespace delta {

static bool IsSignedIntegerKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
      return true;
    default:
      return false;
  }
}

static std::string FormatSingularForP(const Logic4Vec& val, DataTypeKind kind) {
  if (kind == DataTypeKind::kString || val.is_string) {
    return "\"" + FormatValueAsString(val) + "\"";
  }
  if (val.is_real) return FormatArg(val, 'g');
  Logic4Vec v = val;
  if (IsSignedIntegerKind(kind)) v.is_signed = true;
  return FormatArg(v, 'd');
}

static Logic4Vec SliceField(const Logic4Vec& val, uint32_t offset,
                            uint32_t width, DataTypeKind kind, Arena& arena) {
  Logic4Vec out = MakeLogic4Vec(arena, width == 0 ? 1 : width);
  for (uint32_t i = 0; i < width; ++i) {
    uint32_t src = offset + i;
    uint32_t sw = src / 64, sb = src % 64;
    if (sw >= val.nwords) continue;
    uint32_t dw = i / 64, db = i % 64;
    if ((val.words[sw].aval >> sb) & 1) out.words[dw].aval |= uint64_t{1} << db;
    if ((val.words[sw].bval >> sb) & 1) out.words[dw].bval |= uint64_t{1} << db;
  }
  out.is_signed = IsSignedIntegerKind(kind);
  return out;
}

static std::string FormatEnumValueForP(const EnumTypeInfo& et,
                                       const Logic4Vec& val) {
  if (val.nwords > 0) {
    const Logic4Word& w = val.words[0];
    uint64_t mask = et.width == 0 || et.width >= 64
                        ? ~uint64_t{0}
                        : (uint64_t{1} << et.width) - 1;
    for (const auto& m : et.members) {
      if ((m.value & mask) == w.aval && m.xz == w.bval)
        return std::string(m.name);
    }
  }
  return FormatArg(val, 'd');
}

static std::string FormatStructValueForP(const StructTypeInfo& st,
                                         const Logic4Vec& val, SimContext& ctx);

static std::string FormatMember(const StructFieldInfo& f, const Logic4Vec& val,
                                SimContext& ctx) {
  Logic4Vec slice =
      SliceField(val, f.bit_offset, f.width, f.type_kind, ctx.GetArena());
  std::string label = std::string(f.name) + ":";
  if (f.nested != nullptr)
    return label + FormatStructValueForP(*f.nested, slice, ctx);
  if (!f.type_name.empty()) {
    if (const EnumTypeInfo* et = ctx.FindEnumType(f.type_name))
      return label + FormatEnumValueForP(*et, slice);
  }
  if (f.type_kind == DataTypeKind::kString)
    slice = StringMemberText(slice, ctx.GetArena());
  return label + FormatSingularForP(slice, f.type_kind);
}

static std::string FormatStructValueForP(const StructTypeInfo& st,
                                         const Logic4Vec& val,
                                         SimContext& ctx) {
  std::string out = "'{";
  size_t count =
      st.is_union ? std::min<size_t>(1, st.fields.size()) : st.fields.size();
  for (size_t i = 0; i < count; ++i) {
    if (i) out += ", ";
    out += FormatMember(st.fields[i], val, ctx);
  }
  out += "}";
  return out;
}

struct AggElemTypes {
  const StructTypeInfo* st;
  const EnumTypeInfo* et;
};

static std::string FormatAggElemForP(const Logic4Vec& val, DataTypeKind kind,
                                     const StructTypeInfo* st,
                                     const EnumTypeInfo* et, SimContext& ctx) {
  if (st != nullptr) return FormatStructValueForP(*st, val, ctx);
  if (et != nullptr) return FormatEnumValueForP(*et, val);
  return FormatSingularForP(val, kind);
}

static std::string FormatTaggedUnionForP(std::string_view tag,
                                         const StructTypeInfo* st,
                                         const Logic4Vec& val,
                                         const std::string& key,
                                         SimContext& ctx) {
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = val.width;
  const StructFieldInfo* f = st ? FindStructField(st, tag) : nullptr;
  if (f != nullptr) {
    kind = f->type_kind;
    width = f->width;
  }
  Logic4Vec slice = SliceField(val, 0, width, kind, ctx.GetArena());
  std::string member_key = key + "." + std::string(tag);
  std::string_view inner;
  if (f != nullptr && f->nested != nullptr && f->nested->is_union)
    inner = ctx.GetVariableTag(member_key);
  std::string member =
      inner.empty()
          ? FormatSingularForP(slice, kind)
          : FormatTaggedUnionForP(inner, f->nested, slice, member_key, ctx);
  return "'{" + std::string(tag) + ":" + member + "}";
}

static std::optional<std::string> BuildFormatPTaggedUnion(std::string_view name,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx) {
  std::string key = TagKeyOfName(name, ctx);
  auto tag = ctx.GetVariableTag(key);
  if (tag.empty()) return std::nullopt;
  return FormatTaggedUnionForP(tag, StructLayoutOfName(name, ctx), val, key,
                               ctx);
}

static std::optional<std::string> BuildFormatPStruct(std::string_view name,
                                                     const Logic4Vec& val,
                                                     SimContext& ctx) {
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
  if (st == nullptr) return std::nullopt;
  return FormatStructValueForP(*st, val, ctx);
}

static uint32_t LeftToRightAddress(uint32_t lo, uint32_t size, bool descending,
                                   uint32_t i) {
  return descending ? lo + size - 1 - i : lo + i;
}

static std::string FormatArrayDimForP(const std::string& prefix,
                                      const ArrayInfo& ai, size_t d,
                                      const AggElemTypes& types,
                                      SimContext& ctx) {
  std::string out = "'{";
  for (uint32_t i = 0; i < ai.dim_sizes[d]; ++i) {
    if (i) out += ", ";
    bool descending = d < ai.dim_descending.size() && ai.dim_descending[d];
    uint32_t idx =
        LeftToRightAddress(ai.dim_los[d], ai.dim_sizes[d], descending, i);
    std::string elem = prefix + "[" + std::to_string(idx) + "]";
    if (d + 1 < ai.dim_sizes.size()) {
      out += FormatArrayDimForP(elem, ai, d + 1, types, ctx);
      continue;
    }
    Variable* var = ctx.FindVariable(elem);
    Logic4Vec ev =
        var ? var->value : MakeLogic4VecVal(ctx.GetArena(), ai.elem_width, 0);
    out += FormatAggElemForP(ev, ai.elem_type_kind, types.st, types.et, ctx);
  }
  return out + "}";
}

static std::optional<std::string> BuildFormatPArray(std::string_view name,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  auto* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->size == 0) return std::nullopt;
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  if (ai->dim_sizes.size() >= 2)
    return FormatArrayDimForP(std::string(name), *ai, 0, {st, et}, ctx);
  std::string out = "'{";
  for (uint32_t i = 0; i < ai->size; ++i) {
    if (i) out += ", ";
    uint32_t idx = LeftToRightAddress(ai->lo, ai->size, ai->is_descending, i);
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(elem_name);
    Logic4Vec ev =
        elem ? elem->value : MakeLogic4VecVal(arena, ai->elem_width, 0);
    out += FormatAggElemForP(ev, ai->elem_type_kind, st, et, ctx);
  }
  out += "}";
  return out;
}

struct ElementTypeForP {
  DataTypeKind kind = DataTypeKind::kImplicit;
  AggElemTypes types{nullptr, nullptr};
};

static ElementTypeForP ElementTypeOfName(std::string_view name,
                                         SimContext& ctx) {
  ElementTypeForP type;
  if (ctx.FindQueue(name) != nullptr || ctx.FindAssocArray(name) != nullptr) {
    if (ctx.IsStringVariable(name)) type.kind = DataTypeKind::kString;
  } else if (const ArrayInfo* ai = ctx.FindArrayInfo(name)) {
    type.kind = ai->elem_type_kind;
  }
  type.types = {StructLayoutOfName(name, ctx), ctx.GetVariableEnumType(name)};
  return type;
}

static std::string FormatQueueForP(const QueueObject* q,
                                   const ElementTypeForP& type,
                                   SimContext& ctx);

static std::string FormatQueueElementForP(const QueueObject& q, size_t pos,
                                          const ElementTypeForP& type,
                                          SimContext& ctx) {
  if (!q.elements_are_queues)
    return FormatAggElemForP(q.elements[pos], type.kind, type.types.st,
                             type.types.et, ctx);
  return FormatQueueForP(ElementQueueOrDefault(q, pos, ctx.GetArena()), type,
                         ctx);
}

static std::string FormatQueueForP(const QueueObject* q,
                                   const ElementTypeForP& type,
                                   SimContext& ctx) {
  std::string out = "'{";
  for (size_t i = 0; q != nullptr && i < q->elements.size(); ++i) {
    if (i) out += ", ";
    out += FormatQueueElementForP(*q, i, type, ctx);
  }
  return out + "}";
}

static std::optional<std::string> BuildFormatPQueue(std::string_view name,
                                                    SimContext& ctx) {
  QueueObject* q = ctx.FindQueue(name);
  if (q == nullptr) return std::nullopt;
  return FormatQueueForP(q, ElementTypeOfName(name, ctx), ctx);
}

static std::optional<std::string> BuildFormatPAssoc(std::string_view name,
                                                    SimContext& ctx) {
  AssocArrayObject* aa = ctx.FindAssocArray(name);
  if (aa == nullptr) return std::nullopt;
  ElementTypeForP type = ElementTypeOfName(name, ctx);
  auto value_of = [&](const auto& queues, const auto& key, const Logic4Vec& v) {
    if (!aa->elements_are_queues)
      return FormatAggElemForP(v, type.kind, type.types.st, type.types.et, ctx);
    auto it = queues.find(key);
    return FormatQueueForP(it == queues.end() ? nullptr : it->second, type,
                           ctx);
  };
  std::string out = "'{";
  bool first = true;
  auto add_item = [&](const std::string& key, const std::string& value) {
    if (!first) out += ", ";
    first = false;
    out += key + ":" + value;
  };
  if (aa->is_string_key) {
    for (const auto& [k, v] : aa->str_data)
      add_item("\"" + k + "\"", value_of(aa->str_element_queues, k, v));
  } else {
    for (const auto& [k, v] : aa->int_data)
      add_item(FormatDecimalDigits(k.ToSignedVec(ctx.GetArena())),
               value_of(aa->int_element_queues, k, v));
  }
  out += "}";
  return out;
}

static std::optional<std::string> BuildFormatPClassHandle(std::string_view name,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx) {
  if (ctx.GetVariableClassType(name).empty()) return std::nullopt;
  if (val.IsKnown() && val.ToUint64() == 0) return "null";
  return FormatArg(val, 'd');
}

static std::optional<std::string> BuildFormatPVirtualInterface(
    std::string_view name, SimContext& ctx) {
  Variable* v = ctx.FindVariable(name);
  if (v == nullptr || !ctx.IsVirtualInterfaceVar(v)) return std::nullopt;
  if (!ctx.VirtualInterfaceIsBound(v)) return "null";
  return std::string(ctx.VirtualInterfaceBinding(v));
}

static std::optional<std::string> BuildFormatPChandle(std::string_view name,
                                                      const Logic4Vec& val,
                                                      SimContext& ctx) {
  if (!ctx.IsChandleVariable(name)) return std::nullopt;
  if (val.IsKnown() && val.ToUint64() == 0) return "null";
  return FormatArg(val, 'd');
}

static std::optional<std::string> BuildFormatPEnum(std::string_view name,
                                                   const Logic4Vec& val,
                                                   SimContext& ctx) {
  auto* et = ctx.GetVariableEnumType(name);
  if (et == nullptr) return std::nullopt;
  return FormatEnumValueForP(*et, val);
}

static std::optional<std::string> BuildFormatPNamed(std::string_view name,
                                                    const Logic4Vec& val,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  if (name.empty()) return std::nullopt;
  if (auto r = BuildFormatPTaggedUnion(name, val, ctx)) return r;
  if (auto r = BuildFormatPQueue(name, ctx)) return r;
  if (auto r = BuildFormatPAssoc(name, ctx)) return r;
  if (auto r = BuildFormatPArray(name, ctx, arena)) return r;
  if (auto r = BuildFormatPStruct(name, val, ctx)) return r;
  if (auto r = BuildFormatPClassHandle(name, val, ctx)) return r;
  if (auto r = BuildFormatPVirtualInterface(name, ctx)) return r;
  if (auto r = BuildFormatPChandle(name, val, ctx)) return r;
  return BuildFormatPEnum(name, val, ctx);
}

static std::optional<std::string> BuildFormatPMember(const Expr* arg,
                                                     const Logic4Vec& val,
                                                     SimContext& ctx) {
  if (arg->kind != ExprKind::kMemberAccess || arg->is_scope_resolution)
    return std::nullopt;
  std::string name;
  BuildLhsName(arg, name);
  size_t dot = MemberPathSplit(name, ctx);
  if (dot == std::string::npos) return std::nullopt;
  std::string_view base = std::string_view(name).substr(0, dot);
  const StructTypeInfo* info = StructLayoutOfName(base, ctx);
  if (info == nullptr) return std::nullopt;
  MemberLayout member = ResolveMemberLayout(
      base, info, std::string_view(name).substr(dot + 1), ctx);
  if (member.layout == nullptr) return std::nullopt;
  if (!member.tag.empty()) {
    std::string key = TagKeyOfName(base, ctx) + "." +
                      std::string(std::string_view(name).substr(dot + 1));
    return FormatTaggedUnionForP(member.tag, member.layout, val, key, ctx);
  }
  return FormatStructValueForP(*member.layout, val, ctx);
}

static std::optional<std::string> BuildFormatPElement(const Expr* arg,
                                                      const Logic4Vec& val,
                                                      SimContext& ctx) {
  if (arg->kind != ExprKind::kSelect || arg->index_end != nullptr ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  std::string_view name = arg->base->text;
  DataTypeKind kind = DataTypeKind::kImplicit;
  if (const ArrayInfo* ai = ctx.FindArrayInfo(name)) {
    if (ai->dim_sizes.size() >= 2) return std::nullopt;
    kind = ai->elem_type_kind;
  } else if (ctx.FindAssocArray(name) == nullptr &&
             ctx.FindQueue(name) == nullptr) {
    return std::nullopt;
  }
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  if (st == nullptr && et == nullptr) return std::nullopt;
  return FormatAggElemForP(val, kind, st, et, ctx);
}

static std::string FormatValuesForP(const std::vector<Logic4Vec>& elems,
                                    const ElementTypeForP& type,
                                    SimContext& ctx) {
  std::string out = "'{";
  for (size_t i = 0; i < elems.size(); ++i) {
    if (i) out += ", ";
    out += FormatAggElemForP(elems[i], type.kind, type.types.st, type.types.et,
                             ctx);
  }
  return out + "}";
}

static bool ElementsAreArrays(std::string_view name, SimContext& ctx) {
  if (const QueueObject* q = ctx.FindQueue(name)) return q->elements_are_queues;
  const ArrayInfo* ai = ctx.FindArrayInfo(name);
  return ai != nullptr && ai->dim_sizes.size() >= 2;
}

static std::optional<std::string> BuildFormatPSlice(const Expr* arg,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  if (arg->kind != ExprKind::kSelect || arg->index_end == nullptr ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  std::string_view name = arg->base->text;
  if ((ctx.FindQueue(name) == nullptr && ctx.FindArrayInfo(name) == nullptr) ||
      ElementsAreArrays(name, ctx))
    return std::nullopt;
  std::vector<Logic4Vec> elems;
  CollectQueueElements(arg, ctx, arena, elems);
  return FormatValuesForP(elems, ElementTypeOfName(name, ctx), ctx);
}

static bool ReturnsIndices(std::string_view method) {
  return method == "find_index" || method == "find_first_index" ||
         method == "find_last_index" || method == "unique_index";
}

static std::optional<std::string> BuildFormatPLocatorRows(const Expr* arg,
                                                          SimContext& ctx,
                                                          Arena& arena) {
  LocatorRows rows;
  if (!TryCollectLocatorRows(arg, ctx, arena, rows)) return std::nullopt;
  ElementTypeForP type = ElementTypeOfName(rows.array_name, ctx);
  std::string out = "'{";
  for (size_t i = 0; i < rows.offsets.size(); ++i) {
    if (i) out += ", ";
    if (rows.queue != nullptr) {
      out += FormatQueueElementForP(*rows.queue, rows.offsets[i], type, ctx);
      continue;
    }
    std::string row = std::string(rows.array_name) + "[" +
                      std::to_string(rows.info->dim_los[0] + rows.offsets[i]) +
                      "]";
    out += FormatArrayDimForP(row, *rows.info, 1, type.types, ctx);
  }
  return out + "}";
}

static std::optional<std::string> BuildFormatPLocator(const Expr* arg,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  const Expr* access = arg->kind == ExprKind::kCall ? arg->lhs : arg;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->rhs == nullptr ||
      access->lhs == nullptr)
    return std::nullopt;
  if (auto rows = BuildFormatPLocatorRows(arg, ctx, arena)) return rows;
  std::string_view method = access->rhs->text;
  std::string_view recv = access->lhs->kind == ExprKind::kIdentifier
                              ? std::string_view(access->lhs->text)
                              : std::string_view{};
  ElementTypeForP type;
  if (ReturnsIndices(method)) {
    const AssocArrayObject* aa = ctx.FindAssocArray(recv);
    if (aa != nullptr && aa->is_string_key) type.kind = DataTypeKind::kString;
  } else if (method != "map" && !recv.empty()) {
    if (ElementsAreArrays(recv, ctx)) return std::nullopt;
    type = ElementTypeOfName(recv, ctx);
  }
  std::vector<Logic4Vec> elems;
  if (!TryCollectLocatorResult(arg, ctx, arena, elems)) return std::nullopt;
  return FormatValuesForP(elems, type, ctx);
}

static std::optional<std::string> BuildFormatPPackageItem(const Expr* arg,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx,
                                                          Arena& arena) {
  if (arg->kind != ExprKind::kMemberAccess || !arg->is_scope_resolution)
    return std::nullopt;
  std::string key;
  BuildLhsName(arg, key);
  return BuildFormatPNamed(key, val, ctx, arena);
}

static std::optional<std::string> BuildFormatPProperty(const Expr* arg,
                                                       const Logic4Vec& val,
                                                       SimContext& ctx) {
  std::string name;
  if (arg->kind == ExprKind::kIdentifier) {
    name = std::string(arg->text);
  } else if (arg->kind == ExprKind::kMemberAccess &&
             !arg->is_scope_resolution) {
    BuildLhsName(arg, name);
  } else {
    return std::nullopt;
  }
  std::string key;
  const StructTypeInfo* layout = PropertyAggregateLayout(name, ctx, key);
  if (layout == nullptr) return std::nullopt;
  if (layout->is_union) {
    std::string_view tag = ctx.GetVariableTag(key);
    if (!tag.empty()) return FormatTaggedUnionForP(tag, layout, val, key, ctx);
  }
  return FormatStructValueForP(*layout, val, ctx);
}

static bool IsCallFreeHandlePath(const Expr* e) {
  while (e->kind == ExprKind::kMemberAccess) e = e->lhs;
  return e->kind == ExprKind::kIdentifier;
}

static std::optional<std::string> BuildFormatPClassArray(const Expr* arg,
                                                         SimContext& ctx,
                                                         Arena& arena) {
  if (arg->kind != ExprKind::kMemberAccess || !IsCallFreeHandlePath(arg->lhs))
    return std::nullopt;
  if (const QueueObject* q = FindQueueOfBase(arg, ctx, arena))
    return FormatQueueForP(q, {}, ctx);
  ClassArrayRef ref;
  if (!ResolveClassArray(arg, ctx, arena, ref)) return std::nullopt;
  std::string out = "'{";
  for (uint32_t i = 0; i < ref.size; ++i) {
    if (i) out += ", ";
    uint32_t idx = LeftToRightAddress(static_cast<uint32_t>(ref.lo), ref.size,
                                      ref.prop->array_descending, i);
    out += FormatAggElemForP(ReadClassArrayElement(ref, idx, ctx, arena),
                             DataTypeKind::kImplicit, nullptr, nullptr, ctx);
  }
  out += "}";
  return out;
}

std::string BuildFormatP(const Expr* arg, const Logic4Vec& val,
                         SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  std::string name = arg->kind == ExprKind::kIdentifier ? DeclaredKindsKey(arg)
                                                        : std::string();

  if (auto prop = BuildFormatPProperty(arg, val, ctx)) return *prop;
  if (auto named = BuildFormatPNamed(name, val, ctx, arena)) return *named;
  if (auto scoped = BuildFormatPPackageItem(arg, val, ctx, arena))
    return *scoped;
  if (auto elem = BuildFormatPElement(arg, val, ctx)) return *elem;
  if (auto member = BuildFormatPMember(arg, val, ctx)) return *member;
  if (auto slice = BuildFormatPSlice(arg, ctx, arena)) return *slice;
  if (auto found = BuildFormatPLocator(arg, ctx, arena)) return *found;
  if (auto array = BuildFormatPClassArray(arg, ctx, arena)) return *array;

  return FormatSingularForP(val, DataTypeKind::kImplicit);
}

}  // namespace delta
