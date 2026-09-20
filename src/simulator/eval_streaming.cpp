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
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
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
    ctx.GetDiag().Error(size_expr->range.start,
                        "slice_size for streaming operator must be positive",
                        Subclause("11.4.14.2"));
    return 1;
  }
  return static_cast<uint32_t>(val);
}

// §11.4.14.1 appends each stream_expression to the right-hand end of the
// generic stream, and §11.4.14 has a stream of 4-state data carry every x and
// z. The parts are placed from the last written upward, so `bit_pos` is the
// bit the next part's low end lands on and the placed part is `bit_pos` wider.
// DepositBitField moves both planes and every word: a part wider than 64 bits
// -- a 96-bit structure member, a 128-bit literal -- was once moved through a
// 64-bit carrier in two 64-bit takes, the second shifted by 64, which the
// hardware wraps to a shift by 0, so the part's second word landed OR'd over
// its first and the destination's second word read the low bits of that.
static void AppendStreamPart(Logic4Vec& stream, uint32_t& bit_pos,
                             const Logic4Vec& part) {
  DepositBitField(stream, bit_pos, part, part.width);
  bit_pos += part.width;
}

// §11.4.14.1: the stream being assembled from an unpacked array's elements --
// the per-element values in traversal order and the running total width.
struct StreamPartsSink {
  std::vector<Logic4Vec>& parts;
  uint32_t& total_width;
};

// Append one array element's value to the stream. An element with no
// materialized variable contributes an all-x value of the element width, so the
// stream keeps its shape.
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

// §11.4.14.1 / §12.7.3: a multidimensional fixed unpacked array is streamed in
// the order a foreach loop with a single index variable would traverse it, i.e.
// row-major with the outermost dimension varying slowest. Each leaf element is
// a per-index variable materialized at declaration (arr[i0][i1]...); recurse
// through the dimensions building that name and append each leaf's value.
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
  // A multidimensional array records every dimension in dim_sizes; its elements
  // live under fully-indexed leaf names, so walk all dimensions in turn rather
  // than the outermost only.
  if (info->dim_sizes.size() >= 2) {
    ExpandMultiDimArrayLeaves(std::string(name), info, 0, ctx, sink);
    return;
  }
  for (uint32_t i = 0; i < info->size; ++i) {
    AppendElementValue(
        std::string(name) + "[" + std::to_string(info->lo + i) + "]",
        info->elem_width, ctx, sink);
  }
}

// StreamSliceRange (half-open [start, start + count) `with` window) is declared
// in statement_assign_internal.h and shared with ResolveWithRange.

static void ExpandArrayElementsSliced(std::string_view name, SimContext& ctx,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width,
                                      StreamSliceRange range) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  // §7.4.5: a `with` range may reach past the array, and "reading from an
  // unpacked array of any kind with an invalid index shall return the value
  // specified in Table 7-1" -- 'x for a 4-state integral element type, '0 for a
  // 2-state one. A zero-filled vector is the 2-state answer given for both,
  // which turns an entry that does not exist into a known zero and loses the
  // distinction the stream is supposed to carry.
  auto nonexistent = [&] {
    return info->is_4state
               ? MakeAllX(ctx.GetArena(), info->elem_width)
               : MakeLogic4VecVal(ctx.GetArena(), info->elem_width, 0);
  };
  uint32_t start = range.start;
  for (uint32_t i = 0; i < range.count; ++i) {
    uint32_t abs_idx = info->lo + start + i;
    if (start + i < info->size) {
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

// §11.4.14.1: a struct is streamed by applying the procedure to each member in
// declaration order, and §11.4.14 packs 4-state data into a 4-state stream, so
// a member is taken as the window of the struct's storage at its own offset
// and width -- both the value and the unknown plane, however many words it
// spans. Read through ToUint64 the member came from the storage's first word
// alone with x and z flattened to 0, so a member wider than 64 bits, or one
// above bit 63, streamed truncated and an x bit streamed as a known 0.
static void ExpandStructFields(Variable* var, const StructTypeInfo* sinfo,
                               std::vector<Logic4Vec>& parts,
                               uint32_t& total_width, Arena& arena) {
  for (const auto& f : sinfo->fields) {
    parts.push_back(ExtractBitField(arena, var->value, f.bit_offset, f.width));
    total_width += f.width;
  }
}

// §11.4.14.1: an untagged union is streamed by applying the procedure to its
// first-declared member alone, taken as a window of the union's storage the
// same way as a struct member.
static void ExpandUnionFirstMember(Variable* var, const StructTypeInfo* sinfo,
                                   std::vector<Logic4Vec>& parts,
                                   uint32_t& total_width, Arena& arena) {
  if (sinfo->fields.empty()) return;
  const auto& f = sinfo->fields[0];
  parts.push_back(ExtractBitField(arena, var->value, f.bit_offset, f.width));
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

// Streaming-concatenation expansion sink (IEEE 1800 §11.4.14): the evaluation
// environment (ctx + arena) together with the growing concatenation result
// (the element parts and their accumulated bit width) that each aggregate
// expansion appends to.
struct StreamExpandSink {
  SimContext& ctx;
  Arena& arena;
  std::vector<Logic4Vec>& parts;
  uint32_t& total_width;
};

// Expands an unpacked-array identifier into its constituent element parts,
// honoring an optional `with` slice range.
static void ExpandArrayAggregate(const Expr* elem, const ArrayInfo* ainfo,
                                 StreamExpandSink& sink) {
  if (elem->with_expr) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->with_expr, sink.ctx, sink.arena,
                     {ainfo->size, ainfo->lo}, r);
    ExpandArrayElementsSliced(elem->text, sink.ctx, sink.parts,
                              sink.total_width, r);
  } else {
    ExpandArrayElements(elem->text, sink.ctx, sink.parts, sink.total_width);
  }
}

// Expands a queue identifier into its constituent element parts, honoring an
// optional `with` slice range.
static void ExpandQueueAggregate(const Expr* elem, QueueObject* queue,
                                 StreamExpandSink& sink) {
  if (elem->with_expr) {
    StreamSliceRange r{0, 0};
    ResolveWithRange(elem->with_expr, sink.ctx, sink.arena,
                     {static_cast<uint32_t>(queue->elements.size()), 0}, r);
    ExpandQueueElementsSliced(queue, sink.parts, sink.total_width, sink.arena,
                              r);
  } else {
    ExpandQueueElements(queue, sink.parts, sink.total_width, sink.arena);
  }
}

// Expands a struct/union variable identifier into its constituent field parts.
// Returns true if the named struct variable existed and was expanded.
static bool TryExpandStructAggregate(const Expr* elem,
                                     const StructTypeInfo* sinfo,
                                     StreamExpandSink& sink) {
  auto* var = sink.ctx.FindVariable(elem->text);
  if (!var) return false;
  if (sinfo->is_union) {
    ExpandUnionFirstMember(var, sinfo, sink.parts, sink.total_width,
                           sink.arena);
  } else {
    ExpandStructFields(var, sinfo, sink.parts, sink.total_width, sink.arena);
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
  StreamExpandSink sink{ctx, arena, parts, total_width};
  // §11.4.14.1: a dynamic array is an unpacked array whose elements are
  // streamed in turn, but its live elements are held in the backing
  // QueueObject, not in per-index leaf variables (the fixed-shape ArrayInfo it
  // registers carries no element count). Skip the fixed-array path for a
  // dynamic array so it falls through to the queue expansion below, which reads
  // the real elements.
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

  // §23.9: the operand resolves within the running instance, so its layout is
  // asked for by the key that instance's storage was created under; asked by
  // the bare name, a union of an instantiated module found no layout and was
  // streamed whole rather than as its first-declared member.
  if (const StructTypeInfo* sinfo = StructLayoutOfName(elem->text, ctx)) {
    if (TryExpandStructAggregate(elem, sinfo, sink)) {
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

// §11.4.14.2: the `<<` reorder slices the stream into blocks of slice_size
// bits from the right-most bit, reverses the order of the blocks and keeps the
// order of the bits within each; the last (left-most) block holds whatever bits
// remain and is neither padded nor truncated, so it is as wide as those bits
// and lands at bit 0 with nothing above it. Each block is moved whole through
// ExtractBitField and DepositBitField: a block of more than 64 bits -- a
// `{<< 96 {...}}`, or a slice_size naming a wide type -- went through the same
// 64-bit carrier AppendStreamPart describes and came out mangled the same way.
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
    AppendStreamPart(concat, bit_pos, *it);
  }

  if (expr->op != TokenKind::kLtLt) return concat;

  uint32_t ss = StreamSliceSize(expr->lhs, ctx, arena);
  return StreamReorderSlices(concat, total_width, ss, arena);
}

// Assembles collected element parts into one packed vector, placing the first
// part in the most-significant bits (the layout {>>{expression}} produces).
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

// §20.9: the expression argument to $countbits (and the related $countones,
// $onehot, $onehot0, and $isunknown) shall be of a bit-stream type, and for the
// purpose of computing the result it is treated as a vector of equal size
// assigned from {>>{expression}} (see §11.4.14). Pack an aggregate operand into
// that vector: a queue and a dynamic array both keep their live elements in a
// QueueObject (a dynamic array also registers a fixed-shape ArrayInfo whose
// element variables are never materialized), so pack those straight from the
// backing store; a fixed unpacked array, associative array, or packed/unpacked
// struct is expanded through the shared streaming-concat machinery. A plain
// vector operand has no aggregate to expand and is returned by ordinary
// evaluation. Bit order is irrelevant to the callers, which only count matching
// bits, but element 0 is kept in the most-significant bits for consistency with
// {>>{expression}}.
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
  return EvalExpr(arg, ctx, arena);
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

// §10.9.2 places a member's value at the bits the member occupies in the packed
// result. DepositBitField resolves the word each bit falls in and carries the
// bval plane, which is what the two halves of this need: a member of a struct
// wider than one word sits at a bit offset of 64 or more, where the shift this
// once made was undefined behaviour rather than a placement, and §6.3.1 lets
// every bit of a 4-state member be x or z, which a uint64_t value could not
// express and an OR into aval could not have cleared. ExtractBitField is the
// coercion the mask here used to be -- §10.9.2 evaluates each member expression
// "in the context of an assignment to the type of the corresponding member" --
// zero-filling a narrower value and truncating a wider one across every word
// rather than the first.
//
// The deposit assigns each bit where the placements used to OR into a zeroed
// result. That is what makes an x depositable at all, and nothing accumulates
// across placements: §10.9.2's "Every member shall be covered by one of these
// rules" is exactly what PatternState::assigned enforces, so no two of the
// three rules write one member's bits.
static void PlaceFieldValue(Logic4Vec& result, const StructFieldInfo& f,
                            const Logic4Vec& val, Arena& arena) {
  DepositBitField(result, f.bit_offset, ExtractBitField(arena, val, 0, f.width),
                  f.width);
}

// §10.9.2: when the default: key falls on an unmatched member that is itself a
// structure, the value is applied recursively to each member of the
// substructure rather than written flatly across the whole substructure field.
// `base` accumulates the enclosing fields' offsets so a leaf member lands at
// its absolute bit position within the packed result.
static void PlaceDefaultValue(Logic4Vec& result, const StructFieldInfo& f,
                              uint32_t base, const Logic4Vec& val,
                              Arena& arena) {
  if (f.nested) {
    for (const auto& sub : f.nested->fields)
      PlaceDefaultValue(result, sub, base + f.bit_offset, val, arena);
    return;
  }
  DepositBitField(result, base + f.bit_offset,
                  ExtractBitField(arena, val, 0, f.width), f.width);
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
    auto key = expr->pattern_keys[i]->text;
    if (!IsMemberNameKey(key, info)) continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (info->fields[fi].name != key) continue;
      PlaceFieldValue(s.result, info->fields[fi], val, s.arena);
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
    auto kind = TypeKeyToKind(expr->pattern_keys[i]->text);
    if (kind == DataTypeKind::kImplicit) continue;
    auto u = static_cast<uint8_t>(kind);
    if (seen[u]) continue;
    seen[u] = true;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (s.assigned[fi] || info->fields[fi].type_kind != kind) continue;
      PlaceFieldValue(s.result, info->fields[fi], val, s.arena);
      s.assigned[fi] = true;
    }
  }
}

static void ApplyDefaultKey(const Expr* expr, const StructTypeInfo* info,
                            PatternState& s) {
  for (size_t i = 0; i < expr->pattern_keys.size(); ++i) {
    if (i >= expr->elements.size() || expr->pattern_keys[i]->text != "default")
      continue;
    auto val = EvalExpr(expr->elements[i], s.ctx, s.arena);
    for (size_t fi = 0; fi < info->fields.size(); ++fi) {
      if (s.assigned[fi]) continue;
      PlaceDefaultValue(s.result, info->fields[fi], 0, val, s.arena);
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

Logic4Vec EvalStructPatternValue(const Expr* expr, const StructTypeInfo* info,
                                 SimContext& ctx, Arena& arena) {
  // Keyed form (member name / type / default keys): field-by-field placement.
  if (!expr->pattern_keys.empty())
    return EvalStructPattern(expr, info, ctx, arena);

  // §10.9.2: positional form -- element i initializes member i in declaration
  // order, each evaluated in the context of an assignment to that member's
  // type. Coercing each element to its member's width (rather than
  // concatenating at its self-determined width) is what keeps an over-wide
  // element from spilling into the following members. The replication form and
  // any struct too wide for a single word fall back to the width-summing
  // concatenation path.
  bool is_replication =
      expr->repeat_count || (expr->elements.size() == 1 &&
                             expr->elements[0]->kind == ExprKind::kReplicate);
  if (!is_replication && info->total_width <= 64 &&
      expr->elements.size() == info->fields.size()) {
    auto result = MakeLogic4Vec(arena, info->total_width);
    for (size_t i = 0; i < info->fields.size(); ++i) {
      auto val = EvalExpr(expr->elements[i], ctx, arena);
      PlaceFieldValue(result, info->fields[i], val, arena);
    }
    return result;
  }
  return EvalAssignmentPattern(expr, ctx, arena);
}

// §12.6: a constant expression pattern succeeds when the value equals the
// constant's value, and §12.6.2 matches `e matches p` the same way; the
// narrower operand is extended to the wider's width, as §12.5's case
// comparison is, and every word of the two is compared, not the first alone.
// A pattern bit that is x or z is taken as matching either value -- a grant
// §12.6.1 gives only casez and casex -- and a value bit that is x or z reads
// as 0, as ToUint64 reads it. The result is 1 bit, 0 or 1, never x or z.
Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  uint32_t width = std::max(lhs_val.width, rhs_val.width);
  bool sign_ext = lhs_val.is_signed && rhs_val.is_signed;
  if (lhs_val.width < width)
    lhs_val = ExtendVec(lhs_val, width, sign_ext, arena);
  if (rhs_val.width < width)
    rhs_val = ExtendVec(rhs_val, width, sign_ext, arena);

  bool match = true;
  uint32_t nwords = std::min(lhs_val.nwords, rhs_val.nwords);
  for (uint32_t i = 0; i < nwords && match; ++i) {
    uint64_t la = lhs_val.words[i].aval & ~lhs_val.words[i].bval;
    uint64_t mask = ~rhs_val.words[i].bval;
    match = (la & mask) == (rhs_val.words[i].aval & mask);
  }
  return MakeLogic4VecVal(arena, 1, match ? 1 : 0);
}

}  // namespace delta
