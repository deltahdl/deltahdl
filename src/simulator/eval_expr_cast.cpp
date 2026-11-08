#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "elaborator/typename_writer.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/dyn_struct_member.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/variable.h"

namespace delta {

static bool IsRealCastTarget(std::string_view name) {
  return name == "real" || name == "realtime" || name == "shortreal";
}

static double ExtractDouble(const Logic4Vec& vec) {
  return RealVecToDouble(vec);
}

struct BitStreamPack {
  std::string_view name;
  const ArrayInfo& info;
  uint32_t elem_count;
  uint32_t total_bits;
  uint64_t elem_mask;
};

struct PackedBits {
  uint64_t aval = 0;
  uint64_t bval = 0;
};

static void PackQueueElements(const BitStreamPack& pack, SimContext& ctx,
                              PackedBits& out) {
  auto* q = ctx.FindQueue(pack.name);
  if (!q) return;
  for (uint32_t i = 0; i < pack.elem_count; ++i) {
    const auto& v = q->elements[i];
    uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
    uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
    uint32_t shift = pack.total_bits - (i + 1) * pack.info.elem_width;
    out.aval |= (aval & pack.elem_mask) << shift;
    out.bval |= (bval & pack.elem_mask) << shift;
  }
}

static void PackFixedArrayElements(const BitStreamPack& pack, SimContext& ctx,
                                   PackedBits& out) {
  for (uint32_t i = 0; i < pack.elem_count; ++i) {
    uint32_t idx = pack.info.lo + i;
    auto elem_name = std::string(pack.name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(elem_name);
    if (!elem) continue;
    uint64_t aval = elem->value.nwords > 0 ? elem->value.words[0].aval : 0;
    uint64_t bval = elem->value.nwords > 0 ? elem->value.words[0].bval : 0;
    uint32_t shift = pack.total_bits - (i + 1) * pack.info.elem_width;
    out.aval |= (aval & pack.elem_mask) << shift;
    out.bval |= (bval & pack.elem_mask) << shift;
  }
}

static Logic4Vec PackArrayBitStream(std::string_view name,
                                    const ArrayInfo& info, SimContext& ctx,
                                    Arena& arena) {
  auto* q = ctx.FindQueue(name);
  uint32_t elem_count = info.size;
  if (q) elem_count = static_cast<uint32_t>(q->elements.size());
  uint32_t total_bits = elem_count * info.elem_width;
  BitStreamPack pack{name, info, elem_count, total_bits,
                     WordMaskWithinWidth(info.elem_width, 0)};
  PackedBits packed;
  if (q) {
    PackQueueElements(pack, ctx, packed);
  } else {
    PackFixedArrayElements(pack, ctx, packed);
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed.aval & width_mask;
    vec.words[0].bval = packed.bval & width_mask;
  }
  return vec;
}

static Logic4Vec PackAssocBitStream(const AssocArrayObject& aa, Arena& arena) {
  uint32_t elem_width = aa.elem_width;
  uint32_t elem_count = aa.Size();
  uint32_t total_bits = elem_count * elem_width;
  uint64_t elem_mask = WordMaskWithinWidth(elem_width, 0);
  PackedBits packed;
  uint32_t i = 0;
  auto pack_one = [&](const Logic4Vec& v) {
    uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
    uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
    uint32_t shift = total_bits - (i + 1) * elem_width;
    packed.aval |= (aval & elem_mask) << shift;
    packed.bval |= (bval & elem_mask) << shift;
    ++i;
  };
  if (aa.is_string_key) {
    for (const auto& entry : aa.str_data) pack_one(entry.second);
  } else {
    for (const auto& entry : aa.int_data) pack_one(entry.second);
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed.aval & width_mask;
    vec.words[0].bval = packed.bval & width_mask;
  }
  return vec;
}

static Logic4Vec CastRealConversion(const Logic4Vec& inner,
                                    std::string_view type_name,
                                    uint32_t target_width, Arena& arena) {
  if (inner.is_real && !IsRealCastTarget(type_name)) {
    auto val = static_cast<uint64_t>(
        static_cast<int64_t>(std::llround(ExtractDouble(inner))));
    if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
    auto result = MakeLogic4VecVal(arena, target_width, val);
    result.is_signed = true;
    return result;
  }
  uint64_t raw = inner.ToUint64();
  auto d = static_cast<double>(raw);
  if (inner.is_signed && inner.width > 0 && inner.width < 64 &&
      ((raw >> (inner.width - 1)) & 1U) != 0U) {
    d = static_cast<double>(
        static_cast<int64_t>(raw | ~((uint64_t{1} << inner.width) - 1)));
  } else if (inner.is_signed && inner.width == 64) {
    d = static_cast<double>(static_cast<int64_t>(raw));
  }
  return MakeRealVec(arena, d, target_width);
}

static std::string ClassScopedTypeKey(const ClassTypeInfo* cls,
                                      std::string_view name, SimContext& ctx) {
  for (; cls != nullptr; cls = cls->enclosing) {
    for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
      std::string key = std::string(c->name) + "::" + std::string(name);
      if (ctx.FindTypeWidth(key) > 0) return key;
    }
  }
  return std::string(name);
}

std::string CastTypeKey(const Expr* expr, SimContext& ctx) {
  const Expr* rhs = expr->rhs;
  if (expr->text.empty()) {
    if (rhs == nullptr || rhs->kind != ExprKind::kMemberAccess ||
        !rhs->is_scope_resolution || rhs->lhs == nullptr ||
        rhs->rhs == nullptr || rhs->lhs->kind != ExprKind::kIdentifier ||
        rhs->rhs->kind != ExprKind::kIdentifier)
      return {};
    if (rhs->lhs->text == "local") {
      const ClassObject* caller = ctx.ConstraintCallerThis();
      return ClassScopedTypeKey(caller != nullptr ? caller->type : nullptr,
                                rhs->rhs->text, ctx);
    }
    return std::string(rhs->lhs->text) + "::" + std::string(rhs->rhs->text);
  }
  return ClassScopedTypeKey(ctx.CurrentMethodClass(), expr->text, ctx);
}

struct CastTarget {
  uint32_t width = 32;
  bool is_4state = true;
  bool is_signed = false;
  bool is_real = false;
};

static bool IsTwoStateKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
      return true;
    default:
      return false;
  }
}

static bool KeywordCastTarget(std::string_view name, CastTarget& out) {
  static constexpr std::string_view kTwoState[] = {"bit", "byte", "shortint",
                                                   "int", "longint"};
  static constexpr std::string_view kFourState[] = {"logic", "reg", "integer",
                                                    "time"};
  static constexpr std::string_view kSigned[] = {"byte", "shortint", "int",
                                                 "longint", "integer"};
  bool two = false;
  bool four = false;
  for (auto k : kTwoState) two = two || name == k;
  for (auto k : kFourState) four = four || name == k;
  if (!two && !four) return false;
  out.width = name == "time" ? 64 : CastTargetWidth(name);
  out.is_4state = four;
  out.is_signed = false;
  for (auto k : kSigned) out.is_signed = out.is_signed || name == k;
  return true;
}

static CastTarget ResolveCastTarget(std::string_view key, SimContext& ctx) {
  CastTarget t;
  if (KeywordCastTarget(key, t)) return t;
  t.width = ResolveCastWidth(key, ctx);
  t.is_signed = ctx.FindTypeSigned(key);
  if (const EnumTypeInfo* e = ctx.FindEnumType(key)) {
    t.is_4state = e->is_4state;
  } else {
    t.is_4state = !IsTwoStateKind(ctx.FindTypeKind(key));
  }
  return t;
}

static bool ExpressionCastTarget(const Expr* e, SimContext& ctx,
                                 CastTarget& out) {
  out.is_real = SimSelfReal(e, ctx);
  out.width = out.is_real ? 64 : SimSelfWidth(e, ctx);
  out.is_4state = SimSelf4State(e, ctx);
  out.is_signed = SimSelfSigned(e, ctx);
  return out.width > 0;
}

static bool NamedCastTarget(std::string_view name, const DataType* written,
                            SimContext& ctx, CastTarget& out) {
  if (const Variable* var = ctx.FindVariable(name)) {
    out.width = var->value.width;
    out.is_4state = var->is_4state;
    out.is_signed = var->is_signed;
    out.is_real = var->is_real;
    return out.width > 0;
  }
  out = ResolveCastTarget(name, ctx);
  out.is_real = written != nullptr && DeclaredTypeIsReal(*written, ctx);
  return true;
}

static bool TypeRefCastTarget(const Expr* ref, SimContext& ctx,
                              CastTarget& out) {
  if (ref == nullptr || ref->kind != ExprKind::kTypeRef) return false;
  const DataType* written = ref->type_value;
  if (written != nullptr && written->kind != DataTypeKind::kNamed) {
    out.width = DeclaredTypeWidth(*written, ctx);
    out.is_4state = !IsTwoStateKind(written->kind);
    out.is_signed = written->is_signed;
    out.is_real = DeclaredTypeIsReal(*written, ctx);
    return out.width > 0;
  }
  if (written != nullptr && written->packed_dim_left != nullptr) {
    out.width = DeclaredTypeWidth(*written, ctx);
    out.is_4state = DeclaredTypeIs4State(*written, ctx);
    out.is_signed = DeclaredTypeIsSigned(*written, ctx);
    return out.width > 0;
  }
  std::string_view name;
  if (written != nullptr && written->scope_name.empty()) {
    name = written->type_name;
  } else if (ref->lhs != nullptr) {
    if (ref->lhs->kind != ExprKind::kIdentifier)
      return ExpressionCastTarget(ref->lhs, ctx, out);
    name = ref->lhs->text;
  }
  if (name.empty()) return false;
  return NamedCastTarget(name, written, ctx, out);
}

SelfType CastSelfType(const Expr* cast, SimContext& ctx) {
  std::string_view name = cast->text;
  if (name == "signed" || name == "unsigned") {
    uint32_t width = SimSelfWidth(cast->lhs, ctx);
    return {width, name == "signed", SimSelf4State(cast->lhs, ctx), width > 0};
  }
  CastTarget target;
  std::string key = CastTypeKey(cast, ctx);
  if (KeywordCastTarget(key, target) || ctx.FindTypeWidth(key) > 0) {
    target = ResolveCastTarget(key, ctx);
  } else if (!name.empty() || cast->rhs == nullptr ||
             cast->rhs->kind == ExprKind::kTypeRef) {
    if (!TypeRefCastTarget(cast->rhs, ctx, target)) return {};
  } else {
    auto width = static_cast<uint32_t>(
        EvalExpr(cast->rhs, ctx, ctx.GetArena()).ToUint64());
    return {width, SimSelfSigned(cast->lhs, ctx), SimSelf4State(cast->lhs, ctx),
            width > 0};
  }
  return {target.width, target.is_signed, target.is_4state, true};
}

uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx) {
  uint32_t w = CastTargetWidth(type_name);
  if (w > 0) return w;

  uint32_t tw = ctx.FindTypeWidth(type_name);
  return tw > 0 ? tw : 32;
}

static bool TryArrayBitStreamCast(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  auto name = expr->lhs->text;
  auto* arr_info = ctx.FindArrayInfo(name);
  ArrayInfo synth;
  if (!arr_info) {
    if (auto* q = ctx.FindQueue(name)) {
      synth.is_queue = true;
      synth.elem_width = q->elem_width;
      synth.size = static_cast<uint32_t>(q->elements.size());
      arr_info = &synth;
    }
  }

  Logic4Vec inner;
  if (arr_info &&
      (arr_info->size > 0 || arr_info->is_queue || arr_info->is_dynamic)) {
    inner = PackArrayBitStream(name, *arr_info, ctx, arena);
  } else if (auto* aa = ctx.FindAssocArray(name)) {
    inner = PackAssocBitStream(*aa, arena);
  } else {
    return false;
  }

  uint32_t target_width = ResolveCastWidth(expr->text, ctx);
  auto result = MakeLogic4Vec(arena, target_width);
  if (result.nwords > 0 && inner.nwords > 0) {
    uint64_t width_mask =
        target_width >= 64 ? ~uint64_t{0} : (uint64_t{1} << target_width) - 1;
    result.words[0].aval = inner.words[0].aval & width_mask;
    result.words[0].bval = inner.words[0].bval & width_mask;
  }
  out = result;
  return true;
}

static void WriteSizeCastWord(const Logic4Vec& inner, uint32_t tw,
                              Logic4Word& out_word) {
  uint64_t mask = tw >= 64 ? ~uint64_t{0} : (uint64_t{1} << tw) - 1;
  uint64_t aval = inner.words[0].aval;
  uint64_t bval = inner.words[0].bval;
  if (inner.is_signed && inner.width > 0 && inner.width < tw &&
      inner.width < 64) {
    uint64_t high_bits = mask & ~((uint64_t{1} << inner.width) - 1);
    if ((aval >> (inner.width - 1)) & 1) aval |= high_bits;
    if ((bval >> (inner.width - 1)) & 1) bval |= high_bits;
  }
  out_word.aval = aval & mask;
  out_word.bval = bval & mask;
}

static bool TrySizeCast(const Expr* expr, SimContext& ctx, Arena& arena,
                        Logic4Vec& out) {
  if (!expr->text.empty() || expr->rhs == nullptr || expr->lhs == nullptr)
    return false;
  if (expr->lhs->kind == ExprKind::kAssignmentPattern ||
      expr->rhs->kind == ExprKind::kTypeRef)
    return false;
  if (std::string key = CastTypeKey(expr, ctx);
      !key.empty() && ctx.FindTypeWidth(key) > 0)
    return false;
  auto width_v = EvalExpr(expr->rhs, ctx, arena);
  if (!width_v.IsKnown()) return false;
  uint64_t w64 = width_v.ToUint64();
  if (w64 == 0 || w64 > 0xFFFF) return false;
  auto tw = static_cast<uint32_t>(w64);

  auto inner = EvalExpr(expr->lhs, ctx, arena, tw);
  auto result = MakeLogic4Vec(arena, tw);
  if (result.nwords > 0 && inner.nwords > 0)
    WriteSizeCastWord(inner, tw, result.words[0]);
  result.is_signed = inner.is_signed;
  out = result;
  return true;
}

static bool TryKeywordCast(std::string_view type_name, Logic4Vec& inner,
                           Arena& arena, Logic4Vec& out) {
  if (type_name == "signed") {
    inner.is_signed = true;
    out = inner;
    return true;
  }
  if (type_name == "unsigned") {
    inner.is_signed = false;
    out = inner;
    return true;
  }
  if (type_name == "const") {
    out = inner;
    return true;
  }
  if (type_name == "void") {
    out = MakeLogic4Vec(arena, 0);
    return true;
  }
  return false;
}

static Logic4Vec EvalCastOperand(const Expr* operand, std::string_view cast,
                                 SimContext& ctx, Arena& arena) {
  if (cast != "const") return EvalExpr(operand, ctx, arena);
  auto& samples = ctx.AssertionSamples();
  bool sampling = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(false);
  auto inner = EvalExpr(operand, ctx, arena);
  samples.SetEvaluatingProperty(sampling);
  return inner;
}

static std::vector<uint32_t> PackedDimSpans(const DataType& dtype,
                                            SimContext& ctx, Arena& arena) {
  std::vector<uint32_t> spans;
  bool vector_kind = dtype.kind == DataTypeKind::kLogic ||
                     dtype.kind == DataTypeKind::kBit ||
                     dtype.kind == DataTypeKind::kReg;
  if (!vector_kind || dtype.packed_dim_left == nullptr) return spans;
  std::vector<std::pair<Expr*, Expr*>> dims{
      {dtype.packed_dim_left, dtype.packed_dim_right}};
  dims.insert(dims.end(), dtype.extra_packed_dims.begin(),
              dtype.extra_packed_dims.end());
  for (const auto& [left, right] : dims) {
    Logic4Vec l = EvalExpr(left, ctx, arena);
    Logic4Vec r = EvalExpr(right, ctx, arena);
    if (!l.IsKnown() || !r.IsKnown()) return {};
    int64_t lo = SelectBoundValue(l);
    int64_t hi = SelectBoundValue(r);
    spans.push_back(static_cast<uint32_t>(std::abs(hi - lo) + 1));
  }
  return spans;
}

static bool TryTypedPatternCast(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kAssignmentPattern)
    return false;
  std::string key = CastTypeKey(expr, ctx);
  if (const StructTypeInfo* layout = ctx.FindStructType(key)) {
    out = EvalStructPatternValue(expr->lhs, layout, ctx, arena);
    return true;
  }
  const DataType* dtype = ctx.FindTypeDeclaration(key);
  if (dtype == nullptr) return false;
  std::vector<uint32_t> spans = PackedDimSpans(*dtype, ctx, arena);
  auto value = EvalPackedArrayPattern(expr->lhs, spans, ctx.FindTypeWidth(key),
                                      ctx, arena);
  if (!value) return false;
  value->is_signed = ctx.FindTypeSigned(key);
  if (dtype->kind == DataTypeKind::kBit) CoerceTo2State(*value);
  out = *value;
  return true;
}

struct StreamedMember {
  uint32_t offset = 0;
  uint32_t width = 0;
  bool is_string = false;
  const StructFieldInfo* dynamic = nullptr;
  bool IsDynamicallySized() const { return is_string || dynamic != nullptr; }
  uint32_t ElementWidth() const {
    if (is_string || dynamic->type_kind == DataTypeKind::kString) return 8;
    return dynamic->dyn_elem_width;
  }
};

static void AppendStreamedMembers(const StructTypeInfo& layout, uint32_t base,
                                  std::vector<StreamedMember>& out) {
  for (const StructFieldInfo& f : layout.fields) {
    uint32_t offset = base + f.bit_offset;
    if (f.nested != nullptr && !f.nested->is_packed && f.elem_count == 0) {
      AppendStreamedMembers(*f.nested, offset, out);
    } else if (f.is_dynamic) {
      out.push_back({offset, f.width, false, &f});
    } else if (f.type_kind == DataTypeKind::kString && f.elem_count > 0) {
      uint32_t elem_width = f.width / f.elem_count;
      for (uint32_t k = f.elem_count; k-- > 0;) {
        out.push_back({offset + (k * elem_width), elem_width, true});
      }
    } else {
      out.push_back({offset, f.width, f.type_kind == DataTypeKind::kString});
    }
  }
}

static std::vector<StreamedMember> DynamicStructMembers(
    const StructTypeInfo* layout) {
  if (layout == nullptr) return {};
  std::vector<StreamedMember> members;
  AppendStreamedMembers(*layout, 0, members);
  for (const StreamedMember& m : members) {
    if (m.IsDynamicallySized()) return members;
  }
  return {};
}

static uint32_t AppendDynamicElements(const QueueObject& q,
                                      const StructFieldInfo& field,
                                      std::vector<Logic4Vec>& parts,
                                      Arena& arena) {
  uint32_t width = 0;
  for (const Logic4Vec& e : q.elements) {
    Logic4Vec bits = ResizeToWidth(e, field.dyn_elem_width, arena);
    if (field.type_kind == DataTypeKind::kString) {
      std::string text = Logic4VecToString(e);
      if (text.empty()) continue;
      bits = StringToLogic4Vec(arena, text);
    }
    width += bits.width;
    parts.push_back(bits);
  }
  return width;
}

static uint32_t AppendStreamedBits(const Logic4Vec& bits,
                                   const StreamedMember& m,
                                   std::vector<Logic4Vec>& parts,
                                   Arena& arena) {
  if (m.dynamic != nullptr) {
    const QueueObject* q = DynMemberQueue(bits);
    return q != nullptr ? AppendDynamicElements(*q, *m.dynamic, parts, arena)
                        : 0;
  }
  if (!m.is_string) {
    parts.push_back(bits);
    return bits.width;
  }
  std::string text = Logic4VecToString(StringMemberText(bits, arena));
  if (text.empty()) return 0;
  parts.push_back(StringToLogic4Vec(arena, text));
  return parts.back().width;
}

static Logic4Vec StreamDynamicStruct(const Logic4Vec& stored,
                                     const std::vector<StreamedMember>& members,
                                     Arena& arena) {
  std::vector<Logic4Vec> parts;
  uint32_t width = 0;
  for (const StreamedMember& m : members) {
    width += AppendStreamedBits(
        ExtractBitField(arena, stored, m.offset, m.width), m, parts, arena);
  }
  return AssembleConcatParts(parts, width, arena);
}

static Logic4Vec DynMemberOfStream(const Logic4Vec& bits,
                                   const StructFieldInfo& field, Arena& arena) {
  Logic4Vec handle;
  QueueObject* q = NewDynMember(field, handle, arena);
  if (field.type_kind == DataTypeKind::kString) {
    Logic4Vec text = StringToLogic4Vec(arena, Logic4VecToString(bits));
    text.is_string = true;
    q->elements.push_back(text);
    q->AssignFreshIds();
    return handle;
  }
  uint32_t elem_width = field.dyn_elem_width;
  for (uint32_t at = bits.width; at > 0; at -= elem_width) {
    q->elements.push_back(
        ExtractBitField(arena, bits, at - elem_width, elem_width));
  }
  q->AssignFreshIds();
  return handle;
}

static Logic4Vec UnstreamDynamicStruct(
    const Logic4Vec& stream, const std::vector<StreamedMember>& members,
    uint32_t stored_width, uint32_t remainder, Arena& arena) {
  Logic4Vec result = MakeLogic4Vec(arena, stored_width);
  uint32_t pos = stream.width;
  for (const StreamedMember& m : members) {
    uint32_t width = m.IsDynamicallySized() ? remainder : m.width;
    if (m.IsDynamicallySized()) remainder = 0;
    if (width == 0) continue;
    pos -= width;
    Logic4Vec bits = ExtractBitField(arena, stream, pos, width);
    if (m.is_string) bits = StringMemberHandle(bits, arena);
    if (m.dynamic != nullptr) bits = DynMemberOfStream(bits, *m.dynamic, arena);
    DepositBitField(result, m.offset, bits, m.width);
  }
  return result;
}

static bool TryCastIntoDynamicStruct(const Expr* expr, const Logic4Vec& stream,
                                     SimContext& ctx, Arena& arena,
                                     Logic4Vec& out) {
  std::string key = CastTypeKey(expr, ctx);
  const StructTypeInfo* layout = ctx.FindStructType(key);
  std::vector<StreamedMember> members = DynamicStructMembers(layout);
  if (members.empty()) return false;
  uint32_t fixed = 0;
  uint32_t elem_width = 0;
  for (const StreamedMember& m : members) {
    if (!m.IsDynamicallySized()) {
      fixed += m.width;
    } else if (elem_width == 0) {
      elem_width = m.ElementWidth();
    }
  }
  out = MakeLogic4Vec(arena, layout->total_width);
  if (stream.width < fixed) {
    ctx.GetDiag().Error(
        expr->range.start,
        std::format("bit-stream cast to '{}': the {}-bit source is narrower "
                    "than the {} bits of its fixed-size members",
                    key, stream.width, fixed),
        Subclause("6.24.3"));
    return true;
  }
  uint32_t remainder = stream.width - fixed;
  if (remainder % elem_width != 0) {
    ctx.GetDiag().Error(
        expr->range.start,
        std::format("bit-stream cast to '{}': the {}-bit source leaves its "
                    "first dynamically sized member {} bits, which are no "
                    "whole number of its {}-bit elements",
                    key, stream.width, remainder, elem_width),
        Subclause("6.24.3"));
    return true;
  }
  out = UnstreamDynamicStruct(stream, members, layout->total_width, remainder,
                              arena);
  return true;
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (IsSelfDeterminedCast(expr)) return EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec stream_out;
  if (TryArrayBitStreamCast(expr, ctx, arena, stream_out)) return stream_out;
  Logic4Vec pattern_out;
  if (TryTypedPatternCast(expr, ctx, arena, pattern_out)) return pattern_out;

  Logic4Vec size_out;
  if (TrySizeCast(expr, ctx, arena, size_out)) return size_out;

  std::string_view type_name = expr->text;
  auto inner = EvalCastOperand(expr->lhs, type_name, ctx, arena);

  Logic4Vec kw_out;
  if (TryKeywordCast(type_name, inner, arena, kw_out)) return kw_out;
  std::vector<StreamedMember> streamed =
      DynamicStructMembers(StructLayoutOfOperand(expr->lhs, ctx));
  if (!streamed.empty()) inner = StreamDynamicStruct(inner, streamed, arena);
  Logic4Vec struct_out;
  if (TryCastIntoDynamicStruct(expr, inner, ctx, arena, struct_out))
    return struct_out;

  CastTarget target;
  if (!TypeRefCastTarget(expr->rhs, ctx, target))
    target = ResolveCastTarget(CastTypeKey(expr, ctx), ctx);
  uint32_t target_width = target.width;
  if (!streamed.empty() && inner.width != target_width) {
    ctx.GetDiag().Error(
        expr->range.start,
        std::format("bit-stream cast to '{}': the source streams {} bits, "
                    "where the type holds {}",
                    CastTypeKey(expr, ctx), inner.width, target_width),
        Subclause("6.24.3"));
  }

  if (inner.is_real != (target.is_real || IsRealCastTarget(type_name))) {
    return CastRealConversion(inner, type_name, target_width, arena);
  }
  if (inner.is_real) {
    return ConvertRealForKnownLhs(inner, true, target_width, arena);
  }
  Logic4Vec result =
      OwnRhsWords(ResizeToWidth(inner, target_width, arena), arena);
  if (!target.is_4state) CoerceTo2State(result);
  result.is_signed = target.is_signed;
  return result;
}

}  // namespace delta
