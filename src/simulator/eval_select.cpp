#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_select_assoc.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

Logic4Vec NonexistentQueueElement(const QueueObject* q, Arena& arena) {
  return q->is_4state ? MakeAllX(arena, q->elem_width)
                      : MakeLogic4VecVal(arena, q->elem_width, 0);
}

void TakeElementSignedness(const QueueObject& q, Logic4Vec& val) {
  if (val.is_string || val.is_real || q.holds_class_handles) return;
  val.is_signed = q.is_signed;
}

int64_t LongintValue(const Logic4Vec& val) {
  return val.is_signed ? SignExtend(val.ToUint64(), val.width)
                       : static_cast<int64_t>(val.ToUint64());
}

static bool HeldInSixtyFourBits(const Logic4Vec& val) {
  const int64_t kLow = LongintValue(val);
  const uint64_t kFill = kLow < 0 ? ~uint64_t{0} : 0;
  for (uint32_t w = 1; w < val.nwords; ++w) {
    const uint32_t kBits = std::min<uint32_t>(64, val.width - (w * 64));
    if (val.words[w].aval != (kFill >> (64 - kBits))) return false;
  }
  return val.is_signed || kLow >= 0;
}

int64_t SelectBoundValue(const Logic4Vec& val) {
  return HeldInSixtyFourBits(val) ? LongintValue(val) : kBeyondEveryBound;
}

static uint64_t ResolveQueueIdx(const Expr* idx_expr, QueueObject* q,
                                SimContext& ctx, Arena& arena,
                                bool* has_xz = nullptr) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  uint64_t last = q->elements.empty() ? 0 : q->elements.size() - 1;
  dv->value = MakeLogic4VecVal(arena, 32, last);
  auto val = EvalExpr(idx_expr, ctx, arena);
  ctx.PopScope();
  if (has_xz) *has_xz = HasUnknownBits(val);
  return static_cast<uint64_t>(q->PositionOf(SelectBoundValue(val)));
}

static bool TryQueueSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->index_end) return false;
  auto* q = FindQueueOfBase(expr->base, ctx, arena);
  if (!q) return false;

  bool idx_xz = false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz) {
    out = NonexistentElementOf(expr, q->is_4state, q->elem_width, ctx, arena);
    return true;
  }
  const std::vector<Logic4Vec>* sampled =
      ctx.AssertionSamples().ReadQueueWithinProperty(q, ctx.CurrentTime());
  const std::vector<Logic4Vec>& elements =
      sampled != nullptr ? *sampled : q->elements;
  out =
      (idx < elements.size())
          ? elements[idx]
          : NonexistentElementOf(expr, q->is_4state, q->elem_width, ctx, arena);
  TakeElementSignedness(*q, out);
  return true;
}

static std::string_view SelectRootKey(const Expr* expr, SimContext& ctx) {
  const Expr* root = expr->base;
  while (root && root->kind == ExprKind::kSelect) root = root->base;
  return ArrayRootKey(root, ctx.GetArena());
}

static const ArrayInfo* FindRootArrayInfo(const Expr* expr, SimContext& ctx) {
  std::string_view key = SelectRootKey(expr, ctx);
  return key.empty() ? nullptr : ctx.FindArrayInfo(key);
}

static Logic4Vec ElementDefault(bool is_4state, uint32_t elem_width,
                                Arena& arena) {
  return is_4state ? MakeAllX(arena, elem_width)
                   : MakeLogic4VecVal(arena, elem_width, 0);
}

static Logic4Vec NonexistentElement(std::string_view key, bool is_4state,
                                    uint32_t elem_width, SimContext& ctx,
                                    Arena& arena) {
  const StructTypeInfo* layout = StructLayoutOfName(key, ctx);
  if (layout != nullptr && !layout->is_packed)
    return NonexistentAggregateElement(*layout, ctx, arena);
  return ElementDefault(is_4state, elem_width, arena);
}

Logic4Vec NonexistentElementOf(const Expr* select, bool is_4state,
                               uint32_t elem_width, SimContext& ctx,
                               Arena& arena) {
  return NonexistentElement(SelectRootKey(select, ctx), is_4state, elem_width,
                            ctx, arena);
}

static FieldTarget SelectedPropertyTarget(const Expr* root, SimContext& ctx) {
  FieldTarget target;
  if (root->kind == ExprKind::kMemberAccess) {
    target = ResolveFieldTarget(root, ctx);
  } else if (root->kind == ExprKind::kIdentifier &&
             !NameDenotesVariable(root->text, ctx)) {
    target = ResolveBarePropertyTarget(root->text, ctx);
  }
  if (target.kind != FieldTarget::Kind::kProperty || target.obj == nullptr)
    return {};
  return target;
}

static std::optional<bool> SelectedPropertyIs4State(const Expr* root,
                                                    SimContext& ctx) {
  FieldTarget target = SelectedPropertyTarget(root, ctx);
  if (target.kind != FieldTarget::Kind::kProperty) return std::nullopt;
  const ClassTypeInfo* type = target.type ? target.type : target.obj->type;
  const ClassTypeInfo::PropertyInfo* prop =
      type != nullptr ? type->FindProperty(target.field) : nullptr;
  if (prop == nullptr || !prop->width_is_declared) return std::nullopt;
  return prop->is_4state;
}

static bool SelectBaseIs4State(const Expr* expr, SimContext& ctx) {
  const Expr* root = expr->base;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  if (root != nullptr) {
    if (std::optional<bool> prop = SelectedPropertyIs4State(root, ctx))
      return *prop;
  }
  std::string_view key = SelectRootKey(expr, ctx);
  if (key.empty()) return true;
  if (auto* info = ctx.FindArrayInfo(key)) return info->is_4state;
  if (auto* var = ctx.FindVariable(key)) return var->is_4state;
  return true;
}

static bool TryArrayElementSelect(const Expr* expr, uint64_t idx,
                                  SimContext& ctx, Arena& arena,
                                  Logic4Vec& out) {
  if (!expr->base || expr->index_end) return false;
  std::string_view key = ArrayRootKey(expr->base, arena);
  if (key.empty()) return false;
  auto* info = ctx.FindArrayInfo(key);
  if (!info) return false;
  auto elem_name = std::string(key) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(elem_name);
  bool elem_is_string = info->elem_type_kind == DataTypeKind::kString;
  if (!elem) {
    if (elem_is_string) {
      out = MakeLogic4VecVal(arena, 8, 0);
      out.is_string = true;
      return true;
    }
    out =
        NonexistentElement(key, info->is_4state, info->elem_width, ctx, arena);
    return true;
  }
  out = elem->value;
  if (const Logic4Vec* sampled =
          ctx.AssertionSamples().ReadWithinProperty(elem, ctx.CurrentTime())) {
    out = *sampled;
  }
  out.is_signed = elem->is_signed;
  if (elem_is_string) out.is_string = true;
  return true;
}

static bool BuildCompoundName(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& name, bool* has_xz = nullptr) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundName(expr->base, ctx, arena, name, has_xz)) return false;
  auto idx_val = EvalExpr(expr->index, ctx, arena);

  if (HasUnknownBits(idx_val)) {
    if (has_xz) *has_xz = true;
    return false;
  }
  name += "[" + std::to_string(idx_val.ToUint64()) + "]";
  return true;
}

static bool TryCompoundDefaultElem(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  const ArrayInfo* info = FindRootArrayInfo(expr, ctx);
  if (info == nullptr) return false;
  out =
      NonexistentElementOf(expr, info->is_4state, info->elem_width, ctx, arena);
  return true;
}

static bool ChainStandsOnElement(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  for (const Expr* p = expr->base; p != nullptr && p->kind == ExprKind::kSelect;
       p = p->base) {
    std::string name;
    if (BuildCompoundName(p, ctx, arena, name) && ctx.FindVariable(name))
      return true;
  }
  return false;
}

static bool TryCompoundArraySelect(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kSelect) return false;
  if (expr->index_end) return false;
  std::string compound;
  bool xz = false;
  if (!BuildCompoundName(expr, ctx, arena, compound, &xz)) {
    if (!xz) return false;
    return TryCompoundDefaultElem(expr, ctx, arena, out);
  }
  auto* elem = ctx.FindVariable(compound);
  if (elem) {
    out = elem->value;
    if (const Logic4Vec* sampled = ctx.AssertionSamples().ReadWithinProperty(
            elem, ctx.CurrentTime())) {
      out = *sampled;
    }
    out.is_signed = elem->is_signed;
    return true;
  }
  if (ChainStandsOnElement(expr, ctx, arena)) return false;
  return TryCompoundDefaultElem(expr, ctx, arena, out);
}

std::pair<uint32_t, uint32_t> SelectRange(const Expr* expr, SimContext& ctx,
                                          Arena& arena) {
  auto start =
      static_cast<uint32_t>(EvalExpr(expr->index, ctx, arena).ToUint64());
  auto end_val =
      static_cast<uint32_t>(EvalExpr(expr->index_end, ctx, arena).ToUint64());
  if (expr->is_part_select_plus) return {start, end_val};
  if (expr->is_part_select_minus) return {start - end_val + 1, end_val};
  auto lo = std::min(start, end_val);
  return {lo, std::max(start, end_val) - lo + 1};
}

struct UnpackedSliceRun {
  std::string base;
  uint32_t lo;
  uint32_t count;
  uint32_t elem_width;
  bool is_descending;
  bool is_4state;
};

static bool ResolveUnpackedSliceRun(const Expr* expr, SimContext& ctx,
                                    Arena& arena, UnpackedSliceRun& out) {
  if (!expr || expr->kind != ExprKind::kSelect) return false;
  if (!expr->index_end || !expr->base) return false;
  const ArrayInfo* info = nullptr;
  bool compound = expr->base->kind == ExprKind::kSelect;
  if (expr->base->kind == ExprKind::kIdentifier) {
    out.base = std::string(expr->base->text);
    info = ctx.FindArrayInfo(out.base);
  } else if (compound) {
    if (!BuildCompoundName(expr->base, ctx, arena, out.base)) return false;
    if (ctx.FindVariable(out.base)) return false;
    info = FindRootArrayInfo(expr, ctx);
  }
  if (!info) return false;
  auto [lo, count] = SelectRange(expr, ctx, arena);
  out.lo = lo;
  out.count = count;
  out.elem_width = info->elem_width;
  out.is_descending = info->is_descending;
  out.is_4state = info->is_4state;
  return !compound ||
         ctx.FindVariable(out.base + "[" + std::to_string(lo) + "]") != nullptr;
}

bool CollectUnpackedSliceElements(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  UnpackedSliceRun run;
  if (!ResolveUnpackedSliceRun(expr, ctx, arena, run)) return false;
  for (uint32_t i = 0; i < run.count; ++i) {
    uint32_t idx =
        run.is_descending ? (run.lo + run.count - 1 - i) : (run.lo + i);
    auto n = run.base + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(n);
    out.push_back(v ? OwnRhsWords(v->value, arena)
                    : ElementDefault(run.is_4state, run.elem_width, arena));
  }
  return true;
}

static bool TryArraySliceSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  UnpackedSliceRun run;
  if (!ResolveUnpackedSliceRun(expr, ctx, arena, run)) return false;
  uint32_t ew = run.elem_width;
  out = MakeLogic4Vec(arena, run.count * ew);
  for (uint32_t i = 0; i < run.count; ++i) {
    auto n = run.base + "[" + std::to_string(run.lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    Logic4Vec elem = v != nullptr ? ExtractBitField(arena, v->value, 0, ew)
                                  : ElementDefault(run.is_4state, ew, arena);
    DepositBitField(out, i * ew, elem, ew);
  }
  return true;
}

static void MarkOutOfRangeBitsX(Logic4Vec* result, uint32_t base_width,
                                int64_t lo_off, uint32_t width) {
  if (result->nwords == 0) return;
  for (uint32_t b = 0; b < width; ++b) {
    int64_t off = lo_off + b;
    if (off >= 0 && off < static_cast<int64_t>(base_width)) continue;
    result->words[b / 64].aval |= uint64_t{1} << (b % 64);
    result->words[b / 64].bval |= uint64_t{1} << (b % 64);
  }
}

static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, int64_t idx,
                                int64_t end_idx, Arena& arena) {
  int64_t lo = std::min(idx, end_idx);
  int64_t hi = std::max(idx, end_idx);
  auto width = static_cast<uint32_t>(hi - lo + 1);
  auto result = MakeLogic4Vec(arena, width);
  int64_t start = std::max<int64_t>(lo, 0);
  if (start <= hi) {
    auto n = static_cast<uint32_t>(hi - start + 1);
    DepositBitField(
        result, static_cast<uint32_t>(start - lo),
        ExtractBitField(arena, base_val, static_cast<uint32_t>(start), n), n);
  }
  MarkOutOfRangeBitsX(&result, base_val.width, lo, width);
  return result;
}

struct SelectBaseObject {
  const Variable* var = nullptr;
  size_t depth = 0;
};

static const Variable* CompoundSelectVariable(const Expr* select,
                                              SimContext& ctx, Arena& arena) {
  std::string name;
  return BuildCompoundName(select, ctx, arena, name) ? ctx.FindVariable(name)
                                                     : nullptr;
}

static SelectBaseObject FindSelectBaseObject(const Expr* base, SimContext& ctx,
                                             Arena& arena) {
  size_t depth = 0;
  for (const Expr* p = base; p != nullptr; p = p->base, ++depth) {
    if (p->kind == ExprKind::kIdentifier) {
      bool holds_elements =
          depth > 0 && (ctx.FindQueue(p->text) != nullptr ||
                        ctx.FindAssocArray(p->text) != nullptr);
      return {holds_elements ? nullptr : ctx.FindVariable(p->text), depth};
    }
    if (p->kind == ExprKind::kMemberAccess)
      return {FindMemberAccessVariable(p, ctx, arena), depth};
    if (p->kind != ExprKind::kSelect) break;
    if (const Variable* var = CompoundSelectVariable(p, ctx, arena))
      return {var, depth};
  }
  return {};
}

struct SelectRoot {
  const Expr* expr = nullptr;
  size_t depth = 0;
};

static SelectRoot RootOfSelects(const Expr* base) {
  SelectRoot root{base, 0};
  for (; root.expr->kind == ExprKind::kSelect; root.expr = root.expr->base)
    ++root.depth;
  return root;
}

static std::optional<PackedLevel> SelectedClassNameLevel(SelectRoot root,
                                                         uint32_t width,
                                                         SimContext& ctx) {
  FieldTarget target;
  if (root.expr->kind == ExprKind::kMemberAccess) {
    target = ResolveFieldTarget(root.expr, ctx);
  } else if (root.expr->kind == ExprKind::kIdentifier) {
    target = ResolveBarePropertyTarget(root.expr->text, ctx);
  }
  if (target.type == nullptr || (target.kind != FieldTarget::Kind::kProperty &&
                                 target.kind != FieldTarget::Kind::kStatic))
    return std::nullopt;
  return ClassNameLevel(target.type, target.field, root.depth, width, ctx);
}

static std::optional<PackedLevel> InnerMemberLevel(
    const StructFieldInfo& member, size_t depth, uint32_t width,
    SimContext& ctx, Arena& arena) {
  if (member.inner_packed_dims == nullptr ||
      depth > member.inner_packed_dims->size())
    return std::nullopt;
  const auto& [left, right] = (*member.inner_packed_dims)[depth - 1];
  return EvaluatedPackedLevel(left, right, width, ctx, arena);
}

static std::optional<PackedLevel> MemberPackedLevel(SelectRoot root,
                                                    uint32_t width,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  const StructFieldInfo* member = ResolveStructMember(root.expr, ctx);
  if (member == nullptr || member->packed_elem_width == 0) return std::nullopt;
  size_t unpacked =
      member->unpacked_dims != nullptr ? member->unpacked_dims->size() : 0;
  if (root.depth < unpacked) return std::nullopt;
  size_t depth = root.depth - unpacked;
  if (depth == 0) {
    return PackedLevel{{member->packed_left, member->packed_right},
                       member->packed_elem_width};
  }
  return InnerMemberLevel(*member, depth, width, ctx, arena);
}

static std::optional<PackedLevel> SelectBaseLevel(const Expr* base,
                                                  uint32_t width,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  SelectBaseObject obj = FindSelectBaseObject(base, ctx, arena);
  if (obj.var != nullptr) return obj.var->PackedLevelWithin(obj.depth, width);
  if (auto level = CastTypeLevel(base, width, ctx, arena)) return level;
  SelectRoot root = RootOfSelects(base);
  if (auto level = SelectedClassNameLevel(root, width, ctx)) return level;
  return MemberPackedLevel(root, width, ctx, arena);
}

static PackedRange SelectBaseRange(const Expr* base, uint32_t width,
                                   SimContext& ctx, Arena& arena) {
  auto level = SelectBaseLevel(base, width, ctx, arena);
  if (!level) {
    if (auto range = CalledFunctionRange(base, width, ctx, arena))
      return *range;
    return PackedRange::Implicit(width);
  }
  if (level->elem_width > 1) return PackedRange::Implicit(width);
  return level->range;
}

static uint32_t UnknownBoundPartSelectWidth(const PackedRange& range,
                                            int64_t known_bound,
                                            bool unknown_is_more_significant) {
  int64_t known_off = range.OffsetOf(range.Clamp(known_bound));
  int64_t far_off =
      unknown_is_more_significant ? range.OffsetOf(range.left) : 0;
  return static_cast<uint32_t>(std::max(known_off, far_off) -
                               std::min(known_off, far_off) + 1);
}

static Logic4Vec EvalPackedPartSelect(const Expr* expr, const Logic4Vec& base,
                                      int64_t idx, SimContext& ctx,
                                      Arena& arena) {
  auto end = EvalExpr(expr->index_end, ctx, arena);
  auto range = SelectBaseRange(expr->base, base.width, ctx, arena);
  if (HasUnknownBits(end)) {
    return MakeAllX(arena, UnknownBoundPartSelectWidth(range, idx, false));
  }
  auto target = PartSelectTargetIndices(idx, SelectBoundValue(end),
                                        expr->is_part_select_plus,
                                        expr->is_part_select_minus);
  auto level = SelectBaseLevel(expr->base, base.width, ctx, arena);
  if (level && level->elem_width > 1) {
    int64_t w = level->elem_width;
    int64_t first = level->range.OffsetOf(target.first);
    int64_t second = level->range.OffsetOf(target.second);
    return EvalPartSelect(base, std::min(first, second) * w,
                          std::max(first, second) * w + w - 1, arena);
  }
  return EvalPartSelect(base, range.OffsetOf(target.first),
                        range.OffsetOf(target.second), arena);
}

static uint32_t UnknownIndexPartSelectWidth(const Expr* expr, SimContext& ctx,
                                            Arena& arena) {
  int64_t end_val = SelectBoundValue(EvalExpr(expr->index_end, ctx, arena));
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    return end_val > 0 ? static_cast<uint32_t>(end_val) : 1;
  }
  auto range = SelectBaseRange(expr->base, 0, ctx, arena);
  return UnknownBoundPartSelectWidth(range, end_val, true);
}

static Logic4Vec EvalUnknownIndexSelect(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  Logic4Vec elem;
  if (!expr->index_end && TryCompoundDefaultElem(expr, ctx, arena, elem))
    return elem;

  if (expr->index_end) {
    return MakeAllX(arena, UnknownIndexPartSelectWidth(expr, ctx, arena));
  }
  return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                       : MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalStringByteSelect(const Logic4Vec& base_val, uint64_t idx,
                                      Arena& arena) {
  uint32_t nbytes = base_val.width / 8;
  if (idx >= nbytes) return MakeLogic4VecVal(arena, 8, 0);
  uint32_t byte_idx = nbytes - 1 - static_cast<uint32_t>(idx);
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  uint64_t ch =
      (word < base_val.nwords) ? (base_val.words[word].aval >> bit) & 0xFF : 0;
  return MakeLogic4VecVal(arena, 8, ch);
}

static bool SelectsSignedElement(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  SelectBaseObject obj = FindSelectBaseObject(expr->base, ctx, arena);
  return obj.var != nullptr && obj.var->signed_elem_depth == obj.depth;
}

static std::optional<Logic4Vec> TryPackedElementSelect(
    const Expr* expr, int64_t idx, const Logic4Vec& base_val, SimContext& ctx,
    Arena& arena) {
  if (expr->index_end) return std::nullopt;
  auto level = SelectBaseLevel(expr->base, base_val.width, ctx, arena);
  if (!level || level->elem_width <= 1) return std::nullopt;
  uint32_t w = level->elem_width;
  auto range = level->range;
  uint64_t off = range.Contains(idx)
                     ? static_cast<uint64_t>(range.OffsetOf(idx)) * w
                     : base_val.width;
  Logic4Vec elem =
      off < base_val.width
          ? ExtractBitField(arena, base_val, static_cast<uint32_t>(off), w)
      : SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, w)
                                      : MakeLogic4VecVal(arena, w, 0);
  elem.is_signed = SelectsSignedElement(expr, ctx, arena);
  return elem;
}

static Logic4Vec SelectFromPackedValue(const Expr* expr,
                                       const Logic4Vec& base_val,
                                       const Logic4Vec& idx_val,
                                       SimContext& ctx, Arena& arena) {
  uint64_t idx = idx_val.ToUint64();
  if (base_val.is_string && !expr->index_end)
    return EvalStringByteSelect(base_val, idx, arena);
  auto declared_idx = SelectBoundValue(idx_val);
  if (expr->index_end)
    return EvalPackedPartSelect(expr, base_val, declared_idx, ctx, arena);
  if (auto elem =
          TryPackedElementSelect(expr, declared_idx, base_val, ctx, arena))
    return *elem;
  auto range = SelectBaseRange(expr->base, base_val.width, ctx, arena);
  Logic4Vec bit =
      range.Contains(declared_idx)
          ? ExtractBitField(arena, base_val,
                            static_cast<uint32_t>(range.OffsetOf(declared_idx)),
                            1)
      : SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                      : MakeLogic4VecVal(arena, 1, 0);
  bit.is_signed = SelectsSignedElement(expr, ctx, arena);
  return bit;
}

static bool TryStructArrayMemberSelect(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  StructArrayElementRef ref;
  if (!ResolveStructArrayElement(expr, ctx, arena, ref)) return false;
  out = ref.in_range
            ? ExtractBitField(arena, *ref.value, ref.bit_offset, ref.width)
            : MakeAllX(arena, ref.width);
  if (ref.is_string) {
    out = StringMemberText(out, arena);
    return true;
  }
  out.is_signed = ref.is_signed;
  return true;
}

static bool TryPropertyElementOrInstanceSelect(const Expr* expr,
                                               const Logic4Vec& idx_val,
                                               SimContext& ctx, Arena& arena,
                                               Logic4Vec& result) {
  return TryClassArrayElementSelect(expr, SelectBoundValue(idx_val), ctx, arena,
                                    result) ||
         TryInterfaceInstancePathHandle(expr, ctx, arena, result);
}

Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryStructArrayMemberSelect(expr, ctx, arena, result)) return result;
  if (expr->index_end == nullptr && NamesOwnArrayProperty(expr->base, ctx)) {
    auto idx_val = EvalExpr(expr->index, ctx, arena);
    if (!HasUnknownBits(idx_val) &&
        TryClassArrayElementSelect(expr, SelectBoundValue(idx_val), ctx, arena,
                                   result)) {
      return result;
    }
  }
  if (TryQueueSelect(expr, ctx, arena, result)) return result;
  if (TryAssocSelect(expr, ctx, arena, result)) return result;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return EvalUnknownIndexSelect(expr, ctx, arena);
  uint64_t idx = idx_val.ToUint64();
  if (TryArrayElementSelect(expr, idx, ctx, arena, result)) return result;
  if (TryCompoundArraySelect(expr, ctx, arena, result)) return result;
  if (TryArraySliceSelect(expr, ctx, arena, result)) return result;
  if (TryPropertyElementOrInstanceSelect(expr, idx_val, ctx, arena, result))
    return result;
  std::optional<ReturnedAggregate> returned;
  auto base_val = EvalWithReturnedAggregate(expr->base, ctx, arena, returned);
  if (returned && expr->index_end == nullptr)
    return ElementOfReturnedAggregate(*returned, SelectBoundValue(idx_val),
                                      arena);
  return SelectFromPackedValue(expr, base_val, idx_val, ctx, arena);
}

}  // namespace delta
