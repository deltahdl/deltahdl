#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

static uint32_t ParseDigitStr(std::string_view text) {
  if (text.empty() || text[0] < '0' || text[0] > '9') return 0;
  uint32_t n = 0;
  for (char c : text) {
    if (c >= '0' && c <= '9') n = n * 10 + (c - '0');
  }
  return n;
}

static uint32_t StreamSliceSize(const Expr* size_expr, SimContext& ctx,
                                Arena& arena) {
  if (!size_expr) return 1;
  if (size_expr->kind == ExprKind::kIdentifier) {
    uint32_t num = ParseDigitStr(size_expr->text);
    if (num > 0) return num;
    return ResolveCastWidth(size_expr->text, ctx);
  }
  auto val = EvalExpr(size_expr, ctx, arena).ToUint64();
  auto sval = static_cast<int64_t>(val);
  if (val == 0 || sval < 0) {
    ctx.GetDiag().Error({},
                        "slice_size for streaming operator must be positive");
    return 1;
  }
  return static_cast<uint32_t>(val);
}

static uint64_t ExtractSlice(const Logic4Vec& src, uint32_t start_bit,
                             uint32_t slice_size) {
  uint64_t result = 0;
  uint32_t bits_left = slice_size;
  uint32_t dst_bit = 0;
  while (bits_left > 0 && start_bit < src.width) {
    uint32_t word = start_bit / 64;
    uint32_t bit = start_bit % 64;
    uint32_t avail = 64 - bit;
    uint32_t take = (bits_left < avail) ? bits_left : avail;
    if (word < src.nwords) {
      uint64_t mask = (take >= 64) ? ~uint64_t{0} : (uint64_t{1} << take) - 1;
      result |= ((src.words[word].aval >> bit) & mask) << dst_bit;
    }
    dst_bit += take;
    start_bit += take;
    bits_left -= take;
  }
  return result;
}

static void PlaceSlice(Logic4Vec& dst, uint32_t start_bit, uint64_t val,
                       uint32_t slice_size) {
  uint32_t bits_left = slice_size;
  uint32_t src_bit = 0;
  while (bits_left > 0 && start_bit < dst.width) {
    uint32_t word = start_bit / 64;
    uint32_t bit = start_bit % 64;
    uint32_t avail = 64 - bit;
    uint32_t put = (bits_left < avail) ? bits_left : avail;
    if (word < dst.nwords) {
      uint64_t mask = (put >= 64) ? ~uint64_t{0} : (uint64_t{1} << put) - 1;
      dst.words[word].aval |= ((val >> src_bit) & mask) << bit;
    }
    src_bit += put;
    start_bit += put;
    bits_left -= put;
  }
}

static void ExpandArrayElements(std::string_view name, SimContext& ctx,
                                std::vector<Logic4Vec>& parts,
                                uint32_t& total_width) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  for (uint32_t i = 0; i < info->size; ++i) {
    std::string elem_name =
        std::string(name) + "[" + std::to_string(info->lo + i) + "]";
    auto* var = ctx.FindVariable(elem_name);
    if (var) {
      parts.push_back(var->value);
    } else {
      parts.push_back(MakeLogic4Vec(ctx.GetArena(), info->elem_width));
    }
    total_width += parts.back().width;
  }
}

// Half-open slice range [start, start + count) selected by a `with` clause.
struct StreamSliceRange {
  uint32_t start;
  uint32_t count;
};

static void ExpandArrayElementsSliced(std::string_view name, SimContext& ctx,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width,
                                      StreamSliceRange range) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  uint32_t start = range.start;
  for (uint32_t i = 0; i < range.count; ++i) {
    uint32_t abs_idx = info->lo + start + i;
    if (start + i < info->size) {
      std::string elem_name =
          std::string(name) + "[" + std::to_string(abs_idx) + "]";
      auto* var = ctx.FindVariable(elem_name);
      if (var) {
        parts.push_back(var->value);
      } else {
        parts.push_back(MakeLogic4Vec(ctx.GetArena(), info->elem_width));
      }
    } else {
      parts.push_back(MakeLogic4Vec(ctx.GetArena(), info->elem_width));
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
      parts.push_back(MakeLogic4Vec(arena, queue->elem_width));
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
    uint64_t val = var->value.ToUint64() >> f.bit_offset;
    uint64_t mask =
        (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
    parts.push_back(MakeLogic4VecVal(arena, f.width, val & mask));
    total_width += f.width;
  }
}

static void ExpandUnionFirstMember(Variable* var, const StructTypeInfo* sinfo,
                                   std::vector<Logic4Vec>& parts,
                                   uint32_t& total_width, Arena& arena) {
  if (sinfo->fields.empty()) return;
  const auto& f = sinfo->fields[0];
  uint64_t val = var->value.ToUint64() >> f.bit_offset;
  uint64_t mask = (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
  parts.push_back(MakeLogic4VecVal(arena, f.width, val & mask));
  total_width += f.width;
}

static void ExpandClassProperties(ClassObject* obj,
                                  std::vector<Logic4Vec>& parts,
                                  uint32_t& total_width, Arena& arena) {
  std::vector<const ClassTypeInfo*> chain;
  for (auto* t = obj->type; t; t = t->parent) chain.push_back(t);
  std::reverse(chain.begin(), chain.end());
  for (auto* t : chain) {
    for (const auto& prop : t->properties) {
      if (prop.is_static) continue;
      auto it = obj->properties.find(std::string(prop.name));
      if (it != obj->properties.end()) {
        parts.push_back(it->second);
        total_width += it->second.width;
      } else {
        parts.push_back(MakeLogic4Vec(arena, prop.width));
        total_width += prop.width;
      }
    }
  }
}

// Expands an unpacked-array identifier into its constituent element parts,
// honoring an optional `with` slice range.
static void ExpandArrayAggregate(const Expr* elem, const ArrayInfo* ainfo,
                                 SimContext& ctx, Arena& arena,
                                 std::vector<Logic4Vec>& parts,
                                 uint32_t& total_width) {
  if (elem->with_expr) {
    uint32_t start = 0, count = 0;
    ResolveWithRange(elem->with_expr, ctx, arena, ainfo->size, ainfo->lo, start,
                     count);
    ExpandArrayElementsSliced(elem->text, ctx, parts, total_width,
                              {start, count});
  } else {
    ExpandArrayElements(elem->text, ctx, parts, total_width);
  }
}

// Expands a queue identifier into its constituent element parts, honoring an
// optional `with` slice range.
static void ExpandQueueAggregate(const Expr* elem, QueueObject* queue,
                                 SimContext& ctx, Arena& arena,
                                 std::vector<Logic4Vec>& parts,
                                 uint32_t& total_width) {
  if (elem->with_expr) {
    uint32_t start = 0, count = 0;
    ResolveWithRange(elem->with_expr, ctx, arena,
                     static_cast<uint32_t>(queue->elements.size()), 0, start,
                     count);
    ExpandQueueElementsSliced(queue, parts, total_width, arena, {start, count});
  } else {
    ExpandQueueElements(queue, parts, total_width, arena);
  }
}

// Expands a struct/union variable identifier into its constituent field parts.
// Returns true if the named struct variable existed and was expanded.
static bool TryExpandStructAggregate(const Expr* elem,
                                     const StructTypeInfo* sinfo,
                                     SimContext& ctx, Arena& arena,
                                     std::vector<Logic4Vec>& parts,
                                     uint32_t& total_width) {
  auto* var = ctx.FindVariable(elem->text);
  if (!var) return false;
  if (sinfo->is_union) {
    ExpandUnionFirstMember(var, sinfo, parts, total_width, arena);
  } else {
    ExpandStructFields(var, sinfo, parts, total_width, arena);
  }
  return true;
}

// Expands a class-handle variable identifier into its non-static property
// parts. Returns true if the named class variable existed (a null handle
// contributes zero parts but is still considered handled).
static bool TryExpandClassAggregate(const Expr* elem, SimContext& ctx,
                                    Arena& arena, std::vector<Logic4Vec>& parts,
                                    uint32_t& total_width) {
  auto* var = ctx.FindVariable(elem->text);
  if (!var) return false;
  uint64_t handle = var->value.ToUint64();
  if (handle == kNullClassHandle) {
    return true;
  }
  auto* obj = ctx.GetClassObject(handle);
  if (obj) {
    ExpandClassProperties(obj, parts, total_width, arena);
    return true;
  }
  return false;
}

// Tries to expand an unpacked aggregate identifier (array/queue/assoc/struct/
// class) into its constituent parts. Returns true if the identifier named such
// an aggregate (and was handled, possibly contributing zero parts); false if
// the element should be evaluated as an ordinary expression by the caller.
static bool TryExpandAggregateElement(const Expr* elem, SimContext& ctx,
                                      Arena& arena,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width) {
  if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
    ExpandArrayAggregate(elem, ainfo, ctx, arena, parts, total_width);
    return true;
  }

  if (auto* queue = ctx.FindQueue(elem->text)) {
    ExpandQueueAggregate(elem, queue, ctx, arena, parts, total_width);
    return true;
  }

  if (auto* aa = ctx.FindAssocArray(elem->text)) {
    ExpandAssocArrayElements(aa, parts, total_width);
    return true;
  }

  if (auto* sinfo = ctx.GetVariableStructType(elem->text)) {
    if (TryExpandStructAggregate(elem, sinfo, ctx, arena, parts, total_width)) {
      return true;
    }
  }

  if (auto class_type = ctx.GetVariableClassType(elem->text);
      !class_type.empty()) {
    if (TryExpandClassAggregate(elem, ctx, arena, parts, total_width)) {
      return true;
    }
  }

  return false;
}

// Reverses the concatenation in slice_size-wide chunks (the `<<` streaming
// reorder), mapping each source slice to its mirrored destination position.
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
    uint64_t slice = ExtractSlice(concat, src_start, slice_size);
    PlaceSlice(result, dst_start, slice, slice_size);
  }
  return result;
}

Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    if (elem->kind == ExprKind::kIdentifier &&
        TryExpandAggregateElement(elem, ctx, arena, parts, total_width)) {
      continue;
    }
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);

  auto concat = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    PlaceSlice(concat, bit_pos, it->ToUint64(), it->width);
    bit_pos += it->width;
  }

  if (expr->op != TokenKind::kLtLt) return concat;

  uint32_t ss = StreamSliceSize(expr->lhs, ctx, arena);
  return StreamReorderSlices(concat, total_width, ss, arena);
}

Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->elements.empty()) return MakeLogic4Vec(arena, 0);

  std::vector<Logic4Vec> parts;
  uint32_t total_width = 0;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 0);

  return AssembleConcatParts(parts, total_width, arena);
}

static void PlaceFieldValue(Logic4Vec& result, const StructFieldInfo& f,
                            uint64_t val) {
  uint64_t mask = (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
  uint64_t bits = (val & mask) << f.bit_offset;
  result.words[0].aval |= bits;
}

static DataTypeKind TypeKeyToKind(std::string_view key) {
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

static void ApplyMemberKeys(const Expr* expr, const StructTypeInfo* info,
                            PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size()) break;
    if (!IsMemberNameKey(expr->pattern_keys[i], info)) continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (info->fields[fi].name != expr->pattern_keys[i]) continue;
      PlaceFieldValue(s.result, info->fields[fi], val.ToUint64());
      s.assigned[fi] = true;
      break;
    }
  }
}

static void ApplyTypeKeys(const Expr* expr, const StructTypeInfo* info,
                          PatternState& s) {
  size_t n = std::min(expr->pattern_keys.size(), expr->elements.size());
  bool seen[256] = {};
  for (size_t ri = n; ri > 0; --ri) {
    size_t i = ri - 1;
    auto kind = TypeKeyToKind(expr->pattern_keys[i]);
    if (kind == DataTypeKind::kImplicit) continue;
    auto u = static_cast<uint8_t>(kind);
    if (seen[u]) continue;
    seen[u] = true;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (s.assigned[fi] || info->fields[fi].type_kind != kind) continue;
      PlaceFieldValue(s.result, info->fields[fi], val.ToUint64());
      s.assigned[fi] = true;
    }
  }
}

static void ApplyDefaultKey(const Expr* expr, const StructTypeInfo* info,
                            PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size() || expr->pattern_keys[i] != "default")
      continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (s.assigned[fi]) continue;
      PlaceFieldValue(s.result, info->fields[fi], val.ToUint64());
    }
    return;
  }
}

Logic4Vec EvalStructPattern(const Expr* expr, const StructTypeInfo* info,
                            SimContext& ctx, Arena& arena) {
  auto result = MakeLogic4Vec(arena, info->total_width);
  std::vector<bool> assigned(info->fields.size(), false);
  PatternState state{result, assigned, ctx, arena};
  ApplyMemberKeys(expr, info, state);
  ApplyTypeKeys(expr, info, state);
  ApplyDefaultKey(expr, info, state);
  return result;
}

Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);

  uint64_t la = lhs_val.ToUint64();
  uint64_t ra = rhs_val.ToUint64();
  uint64_t rb = (rhs_val.nwords > 0) ? rhs_val.words[0].bval : 0;

  uint64_t mask = ~rb;
  bool match = (la & mask) == (ra & mask);
  return MakeLogic4VecVal(arena, 1, match ? 1 : 0);
}

}  // namespace delta
