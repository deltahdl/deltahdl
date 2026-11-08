#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/pattern_match.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

uint32_t StreamSliceSize(const Expr* size_expr, SimContext& ctx, Arena& arena) {
  if (!size_expr) return 1;
  if (size_expr->kind == ExprKind::kIdentifier &&
      ctx.FindVariable(size_expr->text) == nullptr) {
    return ResolveCastWidth(size_expr->text, ctx);
  }
  auto val = EvalExpr(size_expr, ctx, arena).ToUint64();
  auto sval = static_cast<int64_t>(val);
  if (val == 0 || sval < 0) {
    ctx.GetDiag().Error(size_expr->range.start,
                        "slice_size for streaming operator must be positive",
                        Subclause("11.4.14.2"));
    return 1;
  }
  return static_cast<uint32_t>(val);
}

static void AppendStreamPart(Logic4Vec& stream, uint32_t& bit_pos,
                             const Logic4Vec& part) {
  DepositBitField(stream, bit_pos, part, part.width);
  bit_pos += part.width;
}

struct StreamPartsSink {
  std::vector<Logic4Vec>& parts;
  uint32_t& total_width;
};

static void AppendElementValue(const std::string& elem_name,
                               uint32_t elem_width, SimContext& ctx,
                               StreamPartsSink& sink) {
  auto* var = ctx.FindVariable(elem_name);
  if (var) {
    sink.parts.push_back(var->value);
  } else {
    sink.parts.push_back(MakeLogic4Vec(ctx.GetArena(), elem_width));
  }
  sink.total_width += sink.parts.back().width;
}

static void ExpandMultiDimArrayLeaves(const std::string& prefix,
                                      const ArrayInfo* info, size_t dim,
                                      SimContext& ctx, StreamPartsSink& sink) {
  if (dim == info->dim_sizes.size()) {
    AppendElementValue(prefix, info->elem_width, ctx, sink);
    return;
  }
  uint32_t lo = info->dim_los[dim];
  for (uint32_t i = 0; i < info->dim_sizes[dim]; ++i) {
    ExpandMultiDimArrayLeaves(prefix + "[" + std::to_string(lo + i) + "]", info,
                              dim + 1, ctx, sink);
  }
}

static void ExpandArrayElements(std::string_view name, SimContext& ctx,
                                std::vector<Logic4Vec>& parts,
                                uint32_t& total_width) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  StreamPartsSink sink{parts, total_width};
  if (info->dim_sizes.size() >= 2) {
    ExpandMultiDimArrayLeaves(std::string(name), info, 0, ctx, sink);
    return;
  }
  for (uint32_t i = 0; i < info->size; ++i) {
    uint32_t idx =
        info->is_descending ? info->lo + info->size - 1 - i : info->lo + i;
    AppendElementValue(std::string(name) + "[" + std::to_string(idx) + "]",
                       info->elem_width, ctx, sink);
  }
}

static void ExpandArrayElementsSliced(std::string_view name, SimContext& ctx,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width,
                                      StreamSliceRange range) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  auto nonexistent = [&] {
    return info->is_4state
               ? MakeAllX(ctx.GetArena(), info->elem_width)
               : MakeLogic4VecVal(ctx.GetArena(), info->elem_width, 0);
  };
  uint32_t start = range.start;
  for (uint32_t i = 0; i < range.count; ++i) {
    const uint32_t kOffset =
        info->is_descending ? start + range.count - 1 - i : start + i;
    uint32_t abs_idx = info->lo + kOffset;
    if (kOffset < info->size) {
      std::string elem_name =
          std::string(name) + "[" + std::to_string(abs_idx) + "]";
      auto* var = ctx.FindVariable(elem_name);
      parts.push_back(var ? var->value : nonexistent());
    } else {
      parts.push_back(nonexistent());
    }
    total_width += info->elem_width;
  }
}

static void ExpandQueueElements(QueueObject* queue,
                                std::vector<Logic4Vec>& parts,
                                uint32_t& total_width, Arena&) {
  for (const auto& elem : queue->elements) {
    parts.push_back(elem);
    total_width += elem.width;
  }
}

static void ExpandQueueElementsSliced(QueueObject* queue,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width, Arena& arena,
                                      StreamSliceRange range) {
  uint32_t start = range.start;
  for (uint32_t i = 0; i < range.count; ++i) {
    if (start + i < queue->elements.size()) {
      parts.push_back(queue->elements[start + i]);
    } else {
      parts.push_back(NonexistentQueueElement(queue, arena));
    }
    total_width += queue->elem_width;
  }
}

static void ExpandAssocArrayElements(AssocArrayObject* aa,
                                     std::vector<Logic4Vec>& parts,
                                     uint32_t& total_width) {
  if (aa->is_string_key) {
    for (const auto& [key, val] : aa->str_data) {
      parts.push_back(val);
      total_width += val.width;
    }
  } else {
    for (const auto& [key, val] : aa->int_data) {
      parts.push_back(val);
      total_width += val.width;
    }
  }
}

static void ExpandStructFields(Variable* var, const StructTypeInfo* sinfo,
                               std::vector<Logic4Vec>& parts,
                               uint32_t& total_width, Arena& arena) {
  for (const auto& f : sinfo->fields) {
    parts.push_back(ExtractBitField(arena, var->value, f.bit_offset, f.width));
    total_width += f.width;
  }
}

static void ExpandUnionFirstMember(Variable* var, const StructTypeInfo* sinfo,
                                   std::vector<Logic4Vec>& parts,
                                   uint32_t& total_width, Arena& arena) {
  if (sinfo->fields.empty()) return;
  const auto& f = sinfo->fields[0];
  parts.push_back(ExtractBitField(arena, var->value, f.bit_offset, f.width));
  total_width += f.width;
}

static void ExpandClassProperties(ClassObject* obj, SimContext& ctx,
                                  std::vector<Logic4Vec>& parts,
                                  uint32_t& total_width);

static void ExpandClassArrayMember(const ClassObject* obj,
                                   const ClassTypeInfo::PropertyInfo& prop,
                                   std::vector<Logic4Vec>& parts,
                                   uint32_t& total_width, Arena& arena) {
  const uint32_t kSize =
      prop.is_dynamic ? ClassArraySize(obj, prop) : prop.array_size;
  const int64_t kLo = prop.is_dynamic ? 0 : prop.array_lo;
  for (uint32_t i = 0; i < kSize; ++i) {
    auto it = obj->properties.find(ClassArrayElementKey(prop.name, kLo + i));
    parts.push_back(it != obj->properties.end()
                        ? it->second
                        : MakeLogic4Vec(arena, prop.width));
    total_width += prop.width;
  }
}

static bool TryExpandClassCollectionMember(
    const ClassObject* obj, const ClassTypeInfo::PropertyInfo& prop,
    std::vector<Logic4Vec>& parts, uint32_t& total_width, Arena& arena) {
  if (auto q = obj->queue_properties.find(std::string(prop.name));
      q != obj->queue_properties.end()) {
    ExpandQueueElements(q->second, parts, total_width, arena);
    return true;
  }
  if (!prop.IsArray()) return false;
  ExpandClassArrayMember(obj, prop, parts, total_width, arena);
  return true;
}

static void ExpandClassMember(ClassObject* obj,
                              const ClassTypeInfo::PropertyInfo& prop,
                              SimContext& ctx, std::vector<Logic4Vec>& parts,
                              uint32_t& total_width) {
  Arena& arena = ctx.GetArena();
  if (TryExpandClassCollectionMember(obj, prop, parts, total_width, arena))
    return;
  auto it = obj->properties.find(std::string(prop.name));
  if (it == obj->properties.end()) {
    parts.push_back(MakeLogic4Vec(arena, prop.width));
    total_width += prop.width;
    return;
  }
  if (ctx.FindClassType(prop.type_name) != nullptr) {
    if (ClassObject* member = ctx.GetClassObject(it->second.ToUint64()))
      ExpandClassProperties(member, ctx, parts, total_width);
    return;
  }
  parts.push_back(it->second);
  total_width += it->second.width;
}

static void ExpandClassProperties(ClassObject* obj, SimContext& ctx,
                                  std::vector<Logic4Vec>& parts,
                                  uint32_t& total_width) {
  std::vector<const ClassTypeInfo*> chain;
  for (auto* t = obj->type; t; t = t->parent) chain.push_back(t);
  std::reverse(chain.begin(), chain.end());
  for (auto* t : chain) {
    for (const auto& prop : t->properties) {
      if (!prop.is_static)
        ExpandClassMember(obj, prop, ctx, parts, total_width);
    }
  }
}

struct StreamExpandSink {
  SimContext& ctx;
  Arena& arena;
  std::vector<Logic4Vec>& parts;
  uint32_t& total_width;
};

static void ExpandArrayAggregate(const Expr* elem, const ArrayInfo* ainfo,
                                 StreamExpandSink& sink) {
  if (elem->stream_range) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->stream_range, sink.ctx, sink.arena,
                     {ainfo->size, ainfo->lo}, r);
    ExpandArrayElementsSliced(elem->text, sink.ctx, sink.parts,
                              sink.total_width, r);
  } else {
    ExpandArrayElements(elem->text, sink.ctx, sink.parts, sink.total_width);
  }
}

static void ExpandQueueAggregate(const Expr* elem, QueueObject* queue,
                                 StreamExpandSink& sink) {
  if (elem->stream_range) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->stream_range, sink.ctx, sink.arena,
                     {static_cast<uint32_t>(queue->elements.size()), 0}, r);
    ExpandQueueElementsSliced(queue, sink.parts, sink.total_width, sink.arena,
                              r);
  } else {
    ExpandQueueElements(queue, sink.parts, sink.total_width, sink.arena);
  }
}

static bool TryExpandStructAggregate(const Expr* elem,
                                     const StructTypeInfo* sinfo,
                                     StreamExpandSink& sink) {
  auto* var = sink.ctx.FindVariable(elem->text);
  if (!var) return false;
  if (sinfo->is_packed || sinfo->is_soft) {
    sink.parts.push_back(var->value);
    sink.total_width += var->value.width;
    return true;
  }
  if (sinfo->is_union) {
    ExpandUnionFirstMember(var, sinfo, sink.parts, sink.total_width,
                           sink.arena);
  } else {
    ExpandStructFields(var, sinfo, sink.parts, sink.total_width, sink.arena);
  }
  return true;
}

static bool TryExpandClassAggregate(const Expr* elem, SimContext& ctx,
                                    std::vector<Logic4Vec>& parts,
                                    uint32_t& total_width) {
  auto* var = ctx.FindVariable(elem->text);
  if (!var) return false;
  uint64_t handle = var->value.ToUint64();
  if (handle == kNullClassHandle) {
    return true;
  }
  auto* obj = ctx.GetClassObject(handle);
  if (obj) {
    ExpandClassProperties(obj, ctx, parts, total_width);
    return true;
  }
  return false;
}

static bool TryExpandAggregateElement(const Expr* elem, SimContext& ctx,
                                      Arena& arena,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width) {
  StreamExpandSink sink{ctx, arena, parts, total_width};
  if (auto* ainfo = ctx.FindArrayInfo(elem->text);
      ainfo && !ainfo->is_dynamic) {
    ExpandArrayAggregate(elem, ainfo, sink);
    return true;
  }

  if (auto* queue = ctx.FindQueue(elem->text)) {
    ExpandQueueAggregate(elem, queue, sink);
    return true;
  }

  if (auto* aa = ctx.FindAssocArray(elem->text)) {
    ExpandAssocArrayElements(aa, parts, total_width);
    return true;
  }

  if (const StructTypeInfo* sinfo = StructLayoutOfName(elem->text, ctx)) {
    if (TryExpandStructAggregate(elem, sinfo, sink)) {
      return true;
    }
  }

  if (auto class_type = ctx.GetVariableClassType(elem->text);
      !class_type.empty()) {
    if (TryExpandClassAggregate(elem, ctx, parts, total_width)) {
      return true;
    }
  }

  return false;
}

static Logic4Vec StreamReorderSlices(const Logic4Vec& concat,
                                     uint32_t total_width, uint32_t slice_size,
                                     Arena& arena) {
  uint32_t nslices = (total_width + slice_size - 1) / slice_size;
  auto result = MakeLogic4Vec(arena, total_width);
  for (uint32_t i = 0; i < nslices; ++i) {
    uint32_t src_start = i * slice_size;
    uint32_t dst_start = total_width > (i + 1) * slice_size
                             ? total_width - (i + 1) * slice_size
                             : 0;
    uint32_t block_width = std::min(slice_size, total_width - src_start);
    DepositBitField(result, dst_start,
                    ExtractBitField(arena, concat, src_start, block_width),
                    block_width);
  }
  return result;
}

static bool TryExpandPropertyArray(const Expr* elem, SimContext& ctx,
                                   Arena& arena, std::vector<Logic4Vec>& parts,
                                   uint32_t& total_width) {
  if (elem->kind != ExprKind::kMemberAccess || elem->stream_range != nullptr)
    return false;
  std::vector<Logic4Vec> elems;
  if (!PropertyArrayElements(elem, ctx, arena, elems)) return false;
  for (const Logic4Vec& e : elems) {
    parts.push_back(e);
    total_width += e.width;
  }
  return true;
}

Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    if (elem->kind == ExprKind::kIdentifier &&
        TryExpandAggregateElement(elem, ctx, arena, parts, total_width)) {
      continue;
    }
    if (TryExpandPropertyArray(elem, ctx, arena, parts, total_width)) continue;
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 0);

  auto concat = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    AppendStreamPart(concat, bit_pos, *it);
  }

  if (expr->op != TokenKind::kLtLt) return concat;

  uint32_t ss = StreamSliceSize(expr->lhs, ctx, arena);
  return StreamReorderSlices(concat, total_width, ss, arena);
}

static Logic4Vec AssembleBitStreamParts(const std::vector<Logic4Vec>& parts,
                                        uint32_t total_width, Arena& arena) {
  if (total_width == 0) return MakeLogic4Vec(arena, 1);
  auto packed = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    AppendStreamPart(packed, bit_pos, *it);
  }
  return packed;
}

Logic4Vec PackBitStreamOperand(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg && arg->kind == ExprKind::kIdentifier) {
    if (auto* q = ctx.FindQueue(arg->text)) {
      std::vector<Logic4Vec> parts;
      uint32_t total_width = 0;
      ExpandQueueElements(q, parts, total_width, arena);
      return AssembleBitStreamParts(parts, total_width, arena);
    }
    std::vector<Logic4Vec> parts;
    uint32_t total_width = 0;
    if (TryExpandAggregateElement(arg, ctx, arena, parts, total_width)) {
      return AssembleBitStreamParts(parts, total_width, arena);
    }
  }
  if (std::vector<Logic4Vec> parts;
      PropertyArrayElements(arg, ctx, arena, parts)) {
    uint32_t total_width = 0;
    for (const auto& part : parts) total_width += part.width;
    return AssembleBitStreamParts(parts, total_width, arena);
  }
  return EvalExpr(arg, ctx, arena);
}

Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  std::vector<Logic4Vec> parts;
  uint32_t total_width = 0;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 0);

  return AssembleConcatParts(parts, total_width, arena);
}

Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::vector<PatternBinding> bindings;
  PatternMatchEnv env{TokenKind::kKwCase, MatchesClauseValueMatch, ctx, arena,
                      bindings};
  bool match =
      MatchPattern(expr->rhs, PatternSubjectOf(expr->lhs, ctx, arena), env);
  return MakeLogic4VecVal(arena, 1, match ? 1 : 0);
}

}  // namespace delta
