#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  out.var_name = access->lhs->text;
  out.method_name = access->rhs->text;
  return true;
}

struct ReplicateInner {
  uint64_t aval = 0;
  uint64_t bval = 0;
  uint32_t width = 0;
  bool is_string = false;
};

static ReplicateInner EvalReplicateInner(const Expr* expr, SimContext& ctx,
                                         Arena& arena) {
  ReplicateInner inner;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    auto vec = EvalExpr(elem, ctx, arena);
    // The inner expression of a replication is a self-determined
    // context, so an unbased unsized literal contributes one bit
    // (per §5.7.1) rather than its default wide carrier.
    if (elem && elem->kind == ExprKind::kUnbasedUnsizedLiteral &&
        vec.width > 1) {
      auto bit = MakeLogic4Vec(arena, 1);
      if (vec.nwords > 0) {
        bit.words[0].aval = vec.words[0].aval & 1;
        bit.words[0].bval = vec.words[0].bval & 1;
      }
      vec = bit;
    }
    parts.push_back(vec);
    if (parts.back().is_string) inner.is_string = true;
    inner.width += parts.back().width;
  }
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    inner.aval |= it->ToUint64() << bit_pos;
    uint64_t bv = (it->nwords > 0) ? it->words[0].bval : 0;
    inner.bval |= bv << bit_pos;
    bit_pos += it->width;
  }
  return inner;
}

Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, arena).ToUint64());
  if (count == 0) {
    EvalReplicateInner(expr, ctx, arena);
    return MakeLogic4Vec(arena, 0);
  }
  if (expr->elements.empty()) return MakeLogic4Vec(arena, 0);

  auto inner = EvalReplicateInner(expr, ctx, arena);
  uint32_t total_width = inner.width * count;
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  uint32_t ew = (inner.width > 64) ? 64 : inner.width;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= inner.aval << bit;
      result.words[word].bval |= inner.bval << bit;
      if (bit + ew > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= inner.aval >> (64 - bit);
        result.words[word + 1].bval |= inner.bval >> (64 - bit);
      }
    }
    bit_pos += inner.width;
  }
  result.is_string = inner.is_string;
  return result;
}

// Applies a real-valued unary increment/decrement by unpacking the IEEE-754
// bits of old_val, adding delta (+1.0 for ++, -1.0 for --), and repacking.
static Logic4Vec ApplyRealUnaryOp(const Logic4Vec& old_val, double delta,
                                  Arena& arena) {
  double d = 0.0;
  uint64_t bits = old_val.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  d += delta;
  std::memcpy(&bits, &d, sizeof(double));
  Logic4Vec new_val = MakeLogic4VecVal(arena, 64, bits);
  new_val.is_real = true;
  return new_val;
}

// Shared by the prefix and postfix ++/-- operators: evaluates the operand,
// computes the incremented/decremented value, writes it back to the target,
// and returns the {old, new} pair so each caller can return its own side.
struct IncDecResult {
  Logic4Vec old_val;
  Logic4Vec new_val;
};

static IncDecResult EvalIncDec(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    new_val = ApplyRealUnaryOp(
        old_val, (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0, arena);
  } else {
    uint64_t v = old_val.ToUint64();
    uint64_t nv = (expr->op == TokenKind::kPlusPlus) ? v + 1 : v - 1;
    new_val = MakeLogic4VecVal(arena, old_val.width, nv);
  }
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = new_val;
  } else if (expr->lhs->kind == ExprKind::kSelect) {
    TryAssocIndexedWrite(expr->lhs, new_val, ctx, arena);
  }
  return {old_val, new_val};
}

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).new_val;
}

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).old_val;
}

static void BuildMemberName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildMemberName(expr->lhs, out);
    out += ".";
    BuildMemberName(expr->rhs, out);
  }
}

std::string StripRootPrefix(const std::string& name) {
  constexpr std::string_view kPrefix = "$root.";
  if (name.size() > kPrefix.size() &&
      std::string_view(name).substr(0, kPrefix.size()) == kPrefix) {
    auto rest = std::string_view(name).substr(kPrefix.size());
    auto dot = rest.find('.');
    if (dot != std::string_view::npos) return std::string(rest.substr(dot + 1));
    return std::string(rest);
  }
  return name;
}

static Logic4Vec ExtractStructField(Variable* base_var,
                                    const StructTypeInfo* info,
                                    std::string_view field, Arena& arena) {
  for (const auto& f : info->fields) {
    if (f.name != field) continue;
    uint64_t val = base_var->value.ToUint64() >> f.bit_offset;
    uint64_t mask =
        (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
    return MakeLogic4VecVal(arena, f.width, val & mask);
  }
  return MakeLogic4Vec(arena, 1);
}

static bool TryCollectionAccess(std::string_view base, std::string_view field,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalArrayProperty(base, field, ctx, arena, out)) return true;
  if (TryExecArrayPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalQueueProperty(base, field, ctx, arena, out)) return true;
  if (TryExecQueuePropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalAssocProperty(base, field, ctx, arena, out)) return true;
  if (TryExecAssocPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalStringProperty(base, field, ctx, arena, out)) return true;
  return false;
}

// Bundles the subject of a member access (`base_name.field_name`) together with
// the resolved base variable (when one exists) and the evaluation context. A
// single instance is built once in ResolveMemberByType and shared across the
// per-feature member-access helpers below.
struct MemberAccess {
  std::string_view base_name;
  std::string_view field_name;
  Variable* base_var;
  SimContext& ctx;
  Arena& arena;
};

static bool TryClassPropertyAccess(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  if (!base_var) return false;
  SimContext& ctx = ma.ctx;
  Arena& arena = ma.arena;
  std::string_view field_name = ma.field_name;
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj) return false;
  auto declared = ctx.GetVariableClassType(ma.base_name);
  if (!declared.empty()) {
    auto* declared_type = ctx.FindClassType(declared);
    if (declared_type) {
      out = obj->GetPropertyForType(field_name, declared_type, arena);
      return true;
    }
  }
  out = obj->GetProperty(field_name, arena);
  return true;
}

static bool TryClassEnumAccess(Variable* base_var, std::string_view field_name,
                               SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (!base_var) return false;
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return false;
  auto it = obj->type->enum_members.find(std::string(field_name));
  if (it == obj->type->enum_members.end()) return false;
  out = MakeLogic4VecVal(arena, 32, it->second);
  return true;
}

// Looks up a static property or enum member named `field_name` directly on
// `cls_type` (no inheritance walk). Returns true and fills `out` on a hit.
static bool TryLocalStaticMember(const ClassTypeInfo* cls_type,
                                 std::string_view field_name, Arena& arena,
                                 Logic4Vec& out) {
  auto it = cls_type->static_properties.find(std::string(field_name));
  if (it != cls_type->static_properties.end()) {
    out = it->second;
    return true;
  }
  auto eit = cls_type->enum_members.find(std::string(field_name));
  if (eit != cls_type->enum_members.end()) {
    out = MakeLogic4VecVal(arena, 32, eit->second);
    return true;
  }
  return false;
}

// Walks the interface-class inheritance graph rooted at `cls_type` (parent
// interface plus all extended interfaces) searching for a static property or
// enum member named `field_name`. Returns true and fills `out` on a hit.
static bool TryInterfaceStaticMember(const ClassTypeInfo* cls_type,
                                     std::string_view field_name, Arena& arena,
                                     Logic4Vec& out) {
  std::vector<const ClassTypeInfo*> stack;
  if (cls_type->parent && cls_type->parent->is_interface)
    stack.push_back(cls_type->parent);
  for (const auto* ei : cls_type->extended_interfaces) stack.push_back(ei);
  while (!stack.empty()) {
    const auto* cur = stack.back();
    stack.pop_back();
    if (TryLocalStaticMember(cur, field_name, arena, out)) return true;
    if (cur->parent && cur->parent->is_interface) stack.push_back(cur->parent);
    for (const auto* ei : cur->extended_interfaces) stack.push_back(ei);
  }
  return false;
}

static bool TryStaticMemberAccess(std::string_view base_name,
                                  std::string_view field_name, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
  if (TryLocalStaticMember(cls_type, field_name, arena, out)) return true;
  if (cls_type->is_interface &&
      TryInterfaceStaticMember(cls_type, field_name, arena, out)) {
    return true;
  }
  return false;
}

// Resolves member access on the implicit `this`/`super` object. `is_super`
// selects the parent-type property view used by super. Returns true and fills
// `out` when `base_name` named one of those keywords.
static bool TryThisSuperMember(std::string_view base_name,
                               std::string_view field_name, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  if (base_name == "this") {
    auto* self = ctx.CurrentThis();
    out = self ? self->GetProperty(field_name, arena) : MakeLogic4Vec(arena, 1);
    return true;
  }
  if (base_name == "super") {
    auto* self = ctx.CurrentThis();
    // §8.15: super resolves against the parent of the lexically enclosing class
    // (tracked during method execution); fall back to the dynamic type's parent
    // when no enclosing-class context is active.
    const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
    const ClassTypeInfo* super_type =
        enclosing ? enclosing->parent
                  : (self && self->type ? self->type->parent : nullptr);
    if (self && super_type) {
      out = self->GetPropertyForType(field_name, super_type, arena);
    } else {
      out = MakeLogic4Vec(arena, 1);
    }
    return true;
  }
  return false;
}

// §11.4.13 union access: if `sinfo` describes a tagged union with an active
// tag that does not match the (top-level) field being read, reports the
// runtime error and fills `out` with all-X. Returns true when the mismatch
// fired and `out` was set.
static bool TryUnionTagMismatch(const MemberAccess& ma,
                                const StructTypeInfo* sinfo, Logic4Vec& out) {
  if (!sinfo->is_union) return false;
  auto tag = ma.ctx.GetVariableTag(ma.base_name);
  if (tag.empty()) return false;
  auto top = ma.field_name;
  auto subdot = top.find('.');
  if (subdot != std::string_view::npos) top = top.substr(0, subdot);
  if (tag == top) return false;
  ma.ctx.GetDiag().Error(
      {}, "run-time error: accessing member '" + std::string(ma.field_name) +
              "' of tagged union '" + std::string(ma.base_name) +
              "' which currently has tag '" + std::string(tag) + "'");
  out = MakeAllX(ma.arena, sinfo->total_width);
  return true;
}

// Handles the named-event `.triggered` and named-sequence `.triggered`/`.ended`
// pseudo-methods. Returns true and fills `out` when `field_name` named one of
// these and the base referred to a matching event/sequence.
static bool TryEventSequenceMethod(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  SimContext& ctx = ma.ctx;
  Arena& arena = ma.arena;
  std::string_view base_name = ma.base_name;
  std::string_view field_name = ma.field_name;
  if (base_var && base_var->is_event && field_name == "triggered") {
    // §15.5.3: the triggered method of a null named event evaluates to false,
    // independent of any triggered state recorded for the current time step.
    out = base_var->is_null_event
              ? MakeLogic4VecVal(arena, 1, 0u)
              : MakeLogic4VecVal(arena, 1,
                                 ctx.IsEventTriggered(base_name) ? 1u : 0u);
    return true;
  }
  if (!base_var && field_name == "triggered" &&
      ctx.FindSequenceDecl(base_name)) {
    std::string ep_name = std::string("__seq_") + std::string(base_name);
    out = MakeLogic4VecVal(arena, 1, ctx.IsEventTriggered(ep_name) ? 1u : 0u);
    return true;
  }
  if (!base_var && field_name == "ended" && ctx.FindSequenceDecl(base_name)) {
    // Annex C.2.3: IEEE 1800-2005 supplied the ended sequence method to detect
    // a sequence end point inside a sequence expression, while triggered served
    // the same role in other contexts. The two had identical meaning but
    // mutually exclusive uses, so this version retires ended and lets triggered
    // cover both. A reference to ended on a named sequence therefore names a
    // removed method and is reported rather than silently evaluated.
    ctx.GetDiag().Error(
        {},
        "the ended sequence method has been removed; use the triggered "
        "method to detect the end point of sequence '" +
            std::string(base_name) + "'");
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  return false;
}

static Logic4Vec ResolveMemberByType(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  if (TryThisSuperMember(base_name, field_name, ctx, arena, out)) return out;

  auto* base_var = ctx.FindVariable(base_name);
  auto* sinfo = ctx.GetVariableStructType(base_name);

  MemberAccess ma{base_name, field_name, base_var, ctx, arena};

  if (base_var && sinfo) {
    if (TryUnionTagMismatch(ma, sinfo, out)) {
      return out;
    }
    return ExtractStructField(base_var, sinfo, field_name, arena);
  }

  if (TryEventSequenceMethod(ma, out)) {
    return out;
  }

  if (TryClassPropertyAccess(ma, out)) return out;
  if (TryClassEnumAccess(base_var, field_name, ctx, arena, out)) return out;
  if (TryCollectionAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryEvalEnumProperty(base_name, field_name, ctx, arena, out)) return out;
  if (TryStaticMemberAccess(base_name, field_name, ctx, arena, out)) return out;
  return MakeLogic4Vec(arena, 1);
}

// §25.9: a component referenced through a virtual interface redirects to the
// bound interface instance. Referencing a component of an unbound (null or
// uninitialized) virtual interface is a fatal runtime error. Returns true and
// fills `out` when `expr` accessed a member through a virtual interface var.
static bool TryVirtualInterfaceMember(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  auto* base = ctx.FindVariable(expr->lhs->text);
  if (!ctx.IsVirtualInterfaceVar(base)) return false;
  if (!ctx.VirtualInterfaceIsBound(base)) {
    ctx.GetDiag().Error({}, "reference through a null virtual interface");
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  std::string_view field =
      (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
          ? expr->rhs->text
          : std::string_view(expr->text);
  std::string target =
      std::string(ctx.VirtualInterfaceBinding(base)) + "." + std::string(field);
  auto* tv = ctx.FindVariable(target);
  out = tv ? tv->value : MakeLogic4Vec(arena, 1);
  return true;
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec vif_out;
  if (TryVirtualInterfaceMember(expr, ctx, arena, vif_out)) return vif_out;

  std::string name;
  BuildMemberName(expr, name);
  auto resolved = StripRootPrefix(name);
  auto* var = ctx.FindVariable(resolved);
  if (var) return var->value;

  auto dot = resolved.find('.');
  if (dot == std::string::npos) return MakeLogic4Vec(arena, 1);
  auto base_name = std::string_view(resolved).substr(0, dot);
  auto field_name = std::string_view(resolved).substr(dot + 1);
  return ResolveMemberByType(base_name, field_name, ctx, arena);
}

static bool IsRealCastTarget(std::string_view name) {
  return name == "real" || name == "realtime" || name == "shortreal";
}

static double ExtractDouble(const Logic4Vec& vec) {
  double d = 0.0;
  uint64_t bits = vec.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// §6.24.3: packs the elements of a bit-stream source into a single packed
// value. The first element (index 0 of a fixed unpacked, dynamic, or queue
// array) takes the most significant bit positions of the result. The aval
// and bval (4-state mask) are propagated independently so a source carrying
// any X or Z bit yields a 4-state packed value.
//
// BitStreamPack bundles the packing layout for one unpacked array: the source
// array's name and shape (`info`) plus the element count, total packed width,
// and the per-element bit mask derived from the element width.
struct BitStreamPack {
  std::string_view name;
  const ArrayInfo& info;
  uint32_t elem_count;
  uint32_t total_bits;
  uint32_t elem_mask;
};

// Accumulated packed result: the aval/bval mask pair of the packed value.
struct PackedBits {
  uint64_t aval = 0;
  uint64_t bval = 0;
};

// Packs the low word of each queue element into the accumulated result using
// the element-major shift expected by PackArrayBitStream (element 0 most
// significant).
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

// Packs the low word of each fixed-unpacked-array element into `out` using the
// same element-major shift.
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
  uint32_t elem_count = info.size;
  if (info.is_queue) {
    if (auto* q = ctx.FindQueue(name)) {
      elem_count = static_cast<uint32_t>(q->elements.size());
    }
  }
  uint32_t total_bits = elem_count * info.elem_width;
  uint32_t elem_mask = info.elem_width >= 64
                           ? ~uint32_t{0}
                           : (uint32_t{1} << info.elem_width) - 1;
  BitStreamPack pack{name, info, elem_count, total_bits, elem_mask};
  PackedBits packed;
  if (info.is_queue) {
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
  auto d = static_cast<double>(inner.ToUint64());
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, target_width, bits);
  result.is_real = true;
  return result;
}

uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx) {
  uint32_t w = CastTargetWidth(type_name);
  if (w > 0) return w;

  uint32_t tw = ctx.FindTypeWidth(type_name);
  return tw > 0 ? tw : 32;
}

// §6.24.3 bit-stream cast: when the cast source names an unpacked/dynamic/queue
// array, packs it and width-masks into the destination, carrying both halves of
// the 4-state encoding so any X/Z in the source propagates. Returns true and
// fills `out` when `expr` named such an array source.
static bool TryArrayBitStreamCast(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  auto* arr_info = ctx.FindArrayInfo(expr->lhs->text);
  bool source_present = arr_info && (arr_info->size > 0 || arr_info->is_queue ||
                                     arr_info->is_dynamic);
  if (!source_present) return false;
  auto inner = PackArrayBitStream(expr->lhs->text, *arr_info, ctx, arena);
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

// Handles the signedness/const/void cast keywords that simply re-tag or empty
// the inner value. Returns true and fills `out` when `type_name` was one of
// those keywords. `inner` may be mutated in place for the signedness cases.
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

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec stream_out;
  if (TryArrayBitStreamCast(expr, ctx, arena, stream_out)) return stream_out;

  auto inner = EvalExpr(expr->lhs, ctx, arena);
  std::string_view type_name = expr->text;

  Logic4Vec kw_out;
  if (TryKeywordCast(type_name, inner, arena, kw_out)) return kw_out;

  uint32_t target_width = ResolveCastWidth(type_name, ctx);

  if (inner.is_real != IsRealCastTarget(type_name)) {
    return CastRealConversion(inner, type_name, target_width, arena);
  }
  uint64_t val = inner.ToUint64();
  if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
  return MakeLogic4VecVal(arena, target_width, val);
}

static uint64_t ResolveDollarBound(uint32_t width, bool lower) {
  if (lower) return 0;
  if (width >= 64) return ~uint64_t{0};
  return (uint64_t{1} << width) - 1;
}

static void ComputeToleranceBounds(uint64_t a, uint64_t b, TokenKind op,
                                   uint64_t& lo, uint64_t& hi) {
  uint64_t tol = b;
  if (op == TokenKind::kPlusPercentMinus) tol = a * b / 100;
  lo = (a >= tol) ? a - tol : 0;
  hi = a + tol;
  if (lo > hi) std::swap(lo, hi);
}

static int InsideMatchTolerance(uint64_t lv, const Expr* elem, SimContext& ctx,
                                Arena& arena) {
  auto a_v = EvalExpr(elem->index, ctx, arena);
  auto b_v = EvalExpr(elem->index_end, ctx, arena);
  if (!a_v.IsKnown() || !b_v.IsKnown()) return 2;
  uint64_t lo = 0;
  uint64_t hi = 0;
  ComputeToleranceBounds(a_v.ToUint64(), b_v.ToUint64(), elem->op, lo, hi);
  return (lv >= lo && lv <= hi) ? 1 : 0;
}

static bool IsDollarExpr(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

static int InsideMatchRange(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  if (!lhs.IsKnown()) return 2;
  uint64_t lv = lhs.ToUint64();

  if (elem->op == TokenKind::kPlusSlashMinus ||
      elem->op == TokenKind::kPlusPercentMinus) {
    return InsideMatchTolerance(lv, elem, ctx, arena);
  }

  uint64_t lo = IsDollarExpr(elem->index)
                    ? ResolveDollarBound(lhs.width, true)
                    : EvalExpr(elem->index, ctx, arena).ToUint64();
  uint64_t hi = IsDollarExpr(elem->index_end)
                    ? ResolveDollarBound(lhs.width, false)
                    : EvalExpr(elem->index_end, ctx, arena).ToUint64();
  if (lo > hi) return 0;
  return (lv >= lo && lv <= hi) ? 1 : 0;
}

// Compares the left-hand expression against one singular set member, returning
// 1 for a match, 0 for a mismatch, and 2 when the comparison is ambiguous (x).
// Integral members use wildcard equality so an x or z bit on the member side is
// a do-not-care, while an x or z bit that survives on the left-hand side leaves
// the comparison ambiguous (§11.4.13, §11.4.6).
static int CompareInsideValue(const Logic4Vec& lhs, const Logic4Vec& ev) {
  uint64_t rhs_dc = ev.nwords > 0 ? ev.words[0].bval : 0;
  uint64_t lhs_x = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  if (lhs_x & ~rhs_dc) return 2;
  if (rhs_dc || lhs_x) {
    return (((lhs.ToUint64() ^ ev.ToUint64()) & ~rhs_dc) == 0) ? 1 : 0;
  }
  return (lhs.ToUint64() == ev.ToUint64()) ? 1 : 0;
}

static int InsideMatchValue(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  return CompareInsideValue(lhs, EvalExpr(elem, ctx, arena));
}

// §11.4.13: a set member that names an unpacked array is not compared as an
// aggregate. Instead its elements are traversed down to singular values, so the
// membership test sees each element as if it had been listed individually.
// Returns true (filling `out`) when `elem` named an unpacked array, covering
// both queues/dynamic arrays and fixed-size unpacked arrays.
static bool CollectUnpackedSetMembers(const Expr* elem, SimContext& ctx,
                                      std::vector<Logic4Vec>& out) {
  if (elem->kind != ExprKind::kIdentifier) return false;
  if (auto* q = ctx.FindQueue(elem->text)) {
    for (auto& e : q->elements) out.push_back(e);
    return true;
  }
  if (auto* info = ctx.FindArrayInfo(elem->text)) {
    for (uint32_t i = 0; i < info->size; ++i) {
      std::string elem_name =
          std::string(elem->text) + "[" + std::to_string(info->lo + i) + "]";
      auto* var = ctx.FindVariable(elem_name);
      out.push_back(var ? var->value
                        : MakeLogic4Vec(ctx.GetArena(), info->elem_width));
    }
    return true;
  }
  return false;
}

// Tests `lhs` against each singular value collected from an unpacked-array set
// member. Returns 1 on the first match, 2 if any comparison was ambiguous (and
// none matched), and 0 otherwise.
static int MatchUnpackedSetMembers(const Logic4Vec& lhs,
                                   const std::vector<Logic4Vec>& members) {
  int result = 0;
  for (const auto& member : members) {
    int mr = CompareInsideValue(lhs, member);
    if (mr == 1) return 1;
    if (mr == 2) result = 2;
  }
  return result;
}

// When `elem` (in a non-range position) names an unpacked array, traverses it
// to singular values per §11.4.13 and reports the membership result through
// `out`/the return value. Returns true when `elem` was such an array.
static bool TryMatchUnpackedSetMember(const Logic4Vec& lhs, const Expr* elem,
                                      SimContext& ctx, int& out) {
  std::vector<Logic4Vec> members;
  if (!CollectUnpackedSetMembers(elem, ctx, members)) return false;
  out = MatchUnpackedSetMembers(lhs, members);
  return true;
}

// Evaluates `lhs inside { elem }` for one set member. Returns 1 on a match, 0
// on a definite mismatch, and 2 when the comparison was ambiguous (x). Handles
// ranges, unpacked-array members (traversed to singular values per §11.4.13),
// and plain singular values.
static int EvalInsideElement(const Logic4Vec& lhs, const Expr* elem,
                             SimContext& ctx, Arena& arena) {
  bool is_range =
      elem->kind == ExprKind::kSelect && elem->index && elem->index_end;
  if (!is_range) {
    int unpacked_result = 0;
    if (TryMatchUnpackedSetMember(lhs, elem, ctx, unpacked_result)) {
      return unpacked_result;
    }
  }
  return is_range ? InsideMatchRange(lhs, elem, ctx, arena)
                  : InsideMatchValue(lhs, elem, ctx, arena);
}

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs = EvalExpr(expr->lhs, ctx, arena);
  bool ambiguous = false;
  for (auto* elem : expr->elements) {
    int r = EvalInsideElement(lhs, elem, ctx, arena);
    if (r == 1) return MakeLogic4VecVal(arena, 1, 1);
    if (r == 2) ambiguous = true;
  }
  if (ambiguous) {
    auto x = MakeLogic4Vec(arena, 1);
    // x is aval=0/bval=1 (z is aval=1/bval=1).
    x.words[0] = {0, 1};
    return x;
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

TokenKind CompoundAssignBaseOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
      return TokenKind::kPlus;
    case TokenKind::kMinusEq:
      return TokenKind::kMinus;
    case TokenKind::kStarEq:
      return TokenKind::kStar;
    case TokenKind::kSlashEq:
      return TokenKind::kSlash;
    case TokenKind::kPercentEq:
      return TokenKind::kPercent;
    case TokenKind::kAmpEq:
      return TokenKind::kAmp;
    case TokenKind::kPipeEq:
      return TokenKind::kPipe;
    case TokenKind::kCaretEq:
      return TokenKind::kCaret;
    case TokenKind::kLtLtEq:
      return TokenKind::kLtLt;
    case TokenKind::kGtGtEq:
      return TokenKind::kGtGt;
    case TokenKind::kLtLtLtEq:
      return TokenKind::kLtLtLt;
    case TokenKind::kGtGtGtEq:
      return TokenKind::kGtGtGt;
    default:
      return TokenKind::kEof;
  }
}

bool IsCompoundAssignOp(TokenKind op) {
  return CompoundAssignBaseOp(op) != TokenKind::kEof;
}

Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  auto base_op = CompoundAssignBaseOp(expr->op);
  auto result = EvalBinaryOp(base_op, lhs_val, rhs_val, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = result;
  } else if (expr->lhs->kind == ExprKind::kSelect) {
    TryAssocIndexedWrite(expr->lhs, result, ctx, arena);
  }
  return result;
}

}  // namespace delta
