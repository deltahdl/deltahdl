#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
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

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    double d = 0.0;
    uint64_t bits = old_val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    d += (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0;
    std::memcpy(&bits, &d, sizeof(double));
    new_val = MakeLogic4VecVal(arena, 64, bits);
    new_val.is_real = true;
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
  return new_val;
}

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    double d = 0.0;
    uint64_t bits = old_val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    d += (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0;
    std::memcpy(&bits, &d, sizeof(double));
    new_val = MakeLogic4VecVal(arena, 64, bits);
    new_val.is_real = true;
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
  return old_val;
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

static std::string StripRootPrefix(const std::string& name) {
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

static bool TryClassPropertyAccess(Variable* base_var,
                                   std::string_view field_name,
                                   std::string_view var_name, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!base_var) return false;
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj) return false;
  auto declared = ctx.GetVariableClassType(var_name);
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

static bool TryStaticMemberAccess(std::string_view base_name,
                                  std::string_view field_name, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
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

  if (cls_type->is_interface) {
    std::vector<const ClassTypeInfo*> stack;
    if (cls_type->parent && cls_type->parent->is_interface)
      stack.push_back(cls_type->parent);
    for (const auto* ei : cls_type->extended_interfaces) stack.push_back(ei);
    while (!stack.empty()) {
      const auto* cur = stack.back();
      stack.pop_back();
      auto sit = cur->static_properties.find(std::string(field_name));
      if (sit != cur->static_properties.end()) {
        out = sit->second;
        return true;
      }
      auto seit = cur->enum_members.find(std::string(field_name));
      if (seit != cur->enum_members.end()) {
        out = MakeLogic4VecVal(arena, 32, seit->second);
        return true;
      }
      if (cur->parent && cur->parent->is_interface)
        stack.push_back(cur->parent);
      for (const auto* ei : cur->extended_interfaces) stack.push_back(ei);
    }
  }
  return false;
}

static Logic4Vec ResolveMemberByType(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, Arena& arena) {
  if (base_name == "this") {
    auto* self = ctx.CurrentThis();
    if (self) return self->GetProperty(field_name, arena);
    return MakeLogic4Vec(arena, 1);
  }

  if (base_name == "super") {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      return self->GetPropertyForType(field_name, self->type->parent, arena);
    }
    return MakeLogic4Vec(arena, 1);
  }
  auto* base_var = ctx.FindVariable(base_name);
  auto* sinfo = ctx.GetVariableStructType(base_name);
  Logic4Vec out;

  if (base_var && sinfo) {
    if (sinfo->is_union) {
      auto tag = ctx.GetVariableTag(base_name);
      if (!tag.empty()) {
        auto top = field_name;
        auto subdot = top.find('.');
        if (subdot != std::string_view::npos) top = top.substr(0, subdot);
        if (tag != top) {
          ctx.GetDiag().Error(
              {}, "run-time error: accessing member '" +
                      std::string(field_name) + "' of tagged union '" +
                      std::string(base_name) + "' which currently has tag '" +
                      std::string(tag) + "'");
          return MakeAllX(arena, sinfo->total_width);
        }
      }
    }
    return ExtractStructField(base_var, sinfo, field_name, arena);
  }

  if (base_var && base_var->is_event && field_name == "triggered") {
    // §15.5.3: the triggered method of a null named event evaluates to false,
    // independent of any triggered state recorded for the current time step.
    if (base_var->is_null_event) return MakeLogic4VecVal(arena, 1, 0u);
    return MakeLogic4VecVal(arena, 1,
                            ctx.IsEventTriggered(base_name) ? 1u : 0u);
  }

  if (!base_var && field_name == "triggered" &&
      ctx.FindSequenceDecl(base_name)) {
    std::string ep_name = std::string("__seq_") + std::string(base_name);
    return MakeLogic4VecVal(arena, 1, ctx.IsEventTriggered(ep_name) ? 1u : 0u);
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
    return MakeLogic4Vec(arena, 1);
  }
  if (TryClassPropertyAccess(base_var, field_name, base_name, ctx, arena, out))
    return out;
  if (TryClassEnumAccess(base_var, field_name, ctx, arena, out)) return out;
  if (TryCollectionAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryEvalEnumProperty(base_name, field_name, ctx, arena, out)) return out;
  if (TryStaticMemberAccess(base_name, field_name, ctx, arena, out)) return out;
  return MakeLogic4Vec(arena, 1);
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  // §25.9: a component referenced through a virtual interface redirects to the
  // bound interface instance. Referencing a component of an unbound (null or
  // uninitialized) virtual interface is a fatal runtime error.
  if (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier) {
    auto* base = ctx.FindVariable(expr->lhs->text);
    if (ctx.IsVirtualInterfaceVar(base)) {
      if (!ctx.VirtualInterfaceIsBound(base)) {
        ctx.GetDiag().Error({}, "reference through a null virtual interface");
        return MakeLogic4Vec(arena, 1);
      }
      std::string_view field =
          (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
              ? expr->rhs->text
              : std::string_view(expr->text);
      std::string target = std::string(ctx.VirtualInterfaceBinding(base)) +
                           "." + std::string(field);
      if (auto* tv = ctx.FindVariable(target)) return tv->value;
      return MakeLogic4Vec(arena, 1);
    }
  }

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

static uint32_t CastWidth(std::string_view type_name) {
  if (type_name == "byte") return 8;
  if (type_name == "shortint") return 16;
  if (type_name == "int") return 32;
  if (type_name == "longint") return 64;
  if (type_name == "integer") return 32;
  if (type_name == "real" || type_name == "realtime") return 64;
  if (type_name == "shortreal") return 32;
  if (type_name == "bit") return 1;
  if (type_name == "logic") return 1;
  if (type_name == "reg") return 1;
  if (type_name == "string") return 0;

  if (!type_name.empty() && type_name[0] >= '0' && type_name[0] <= '9') {
    uint32_t w = 0;
    for (char c : type_name) {
      if (c >= '0' && c <= '9')
        w = w * 10 + (c - '0');
      else
        break;
    }
    if (w > 0) return w;
  }
  return 0;
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
  uint64_t packed_a = 0;
  uint64_t packed_b = 0;
  uint32_t elem_mask = info.elem_width >= 64
                           ? ~uint32_t{0}
                           : (uint32_t{1} << info.elem_width) - 1;
  auto append_elem = [&](uint64_t aval, uint64_t bval, uint32_t i) {
    uint32_t shift = total_bits - (i + 1) * info.elem_width;
    packed_a |= (aval & elem_mask) << shift;
    packed_b |= (bval & elem_mask) << shift;
  };
  if (info.is_queue) {
    auto* q = ctx.FindQueue(name);
    if (q) {
      for (uint32_t i = 0; i < elem_count; ++i) {
        const auto& v = q->elements[i];
        uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
        uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
        append_elem(aval, bval, i);
      }
    }
  } else {
    for (uint32_t i = 0; i < elem_count; ++i) {
      uint32_t idx = info.lo + i;
      auto elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
      auto* elem = ctx.FindVariable(elem_name);
      if (!elem) continue;
      uint64_t aval = elem->value.nwords > 0 ? elem->value.words[0].aval : 0;
      uint64_t bval = elem->value.nwords > 0 ? elem->value.words[0].bval : 0;
      append_elem(aval, bval, i);
    }
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed_a & width_mask;
    vec.words[0].bval = packed_b & width_mask;
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

static uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx) {
  uint32_t w = CastWidth(type_name);
  if (w > 0) return w;

  uint32_t tw = ctx.FindTypeWidth(type_name);
  return tw > 0 ? tw : 32;
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier) {
    auto* arr_info = ctx.FindArrayInfo(expr->lhs->text);
    bool source_present =
        arr_info &&
        (arr_info->size > 0 || arr_info->is_queue || arr_info->is_dynamic);
    if (source_present) {
      auto inner = PackArrayBitStream(expr->lhs->text, *arr_info, ctx, arena);
      uint32_t target_width = ResolveCastWidth(expr->text, ctx);
      // §6.24.3: width-mask the packed bit-stream into the destination, but
      // carry forward both halves of the 4-state encoding so any X/Z in the
      // source propagates into the result.
      auto result = MakeLogic4Vec(arena, target_width);
      if (result.nwords > 0 && inner.nwords > 0) {
        uint64_t width_mask = target_width >= 64
                                  ? ~uint64_t{0}
                                  : (uint64_t{1} << target_width) - 1;
        result.words[0].aval = inner.words[0].aval & width_mask;
        result.words[0].bval = inner.words[0].bval & width_mask;
      }
      return result;
    }
  }
  auto inner = EvalExpr(expr->lhs, ctx, arena);
  std::string_view type_name = expr->text;

  if (type_name == "signed") {
    inner.is_signed = true;
    return inner;
  }
  if (type_name == "unsigned") {
    inner.is_signed = false;
    return inner;
  }
  if (type_name == "const") {
    return inner;
  }
  if (type_name == "void") {
    return MakeLogic4Vec(arena, 0);
  }
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

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs = EvalExpr(expr->lhs, ctx, arena);
  bool ambiguous = false;
  for (auto* elem : expr->elements) {
    bool is_range =
        elem->kind == ExprKind::kSelect && elem->index && elem->index_end;
    if (!is_range) {
      std::vector<Logic4Vec> members;
      if (CollectUnpackedSetMembers(elem, ctx, members)) {
        for (const auto& member : members) {
          int mr = CompareInsideValue(lhs, member);
          if (mr == 1) return MakeLogic4VecVal(arena, 1, 1);
          if (mr == 2) ambiguous = true;
        }
        continue;
      }
    }
    int r = is_range ? InsideMatchRange(lhs, elem, ctx, arena)
                     : InsideMatchValue(lhs, elem, ctx, arena);
    if (r == 1) return MakeLogic4VecVal(arena, 1, 1);
    if (r == 2) ambiguous = true;
  }
  if (ambiguous) {
    auto x = MakeLogic4Vec(arena, 1);
    x.words[0] = {~uint64_t{0}, ~uint64_t{0}};
    return x;
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

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

static bool ResolveWithRange(const Expr* with_expr, SimContext& ctx,
                             Arena& arena, uint32_t array_size,
                             uint32_t array_lo, uint32_t& out_start,
                             uint32_t& out_count) {
  if (!with_expr || with_expr->kind != ExprKind::kSelect) {
    out_start = 0;
    out_count = array_size;
    return true;
  }
  int64_t idx =
      static_cast<int64_t>(EvalExpr(with_expr->index, ctx, arena).ToUint64());
  if (!with_expr->index_end) {
    int64_t rel = idx - static_cast<int64_t>(array_lo);
    if (rel < 0 || static_cast<uint32_t>(rel) >= array_size) {
      out_start = 0;
      out_count = 0;
      return false;
    }
    out_start = static_cast<uint32_t>(rel);
    out_count = 1;
    return true;
  }
  int64_t idx2 = static_cast<int64_t>(
      EvalExpr(with_expr->index_end, ctx, arena).ToUint64());
  if (with_expr->is_part_select_plus) {
    int64_t rel = idx - static_cast<int64_t>(array_lo);
    out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
    out_count = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
  } else if (with_expr->is_part_select_minus) {
    uint32_t width = (idx2 < 0) ? 0 : static_cast<uint32_t>(idx2);
    int64_t lo_idx = idx - static_cast<int64_t>(width) + 1;
    int64_t rel = lo_idx - static_cast<int64_t>(array_lo);
    out_start = (rel < 0) ? 0 : static_cast<uint32_t>(rel);
    out_count = width;
  } else {
    int64_t lo = idx, hi = idx2;
    if (lo > hi) std::swap(lo, hi);
    int64_t rel_lo = lo - static_cast<int64_t>(array_lo);
    out_start = (rel_lo < 0) ? 0 : static_cast<uint32_t>(rel_lo);
    out_count = static_cast<uint32_t>(hi - lo + 1);
  }
  return true;
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

static void ExpandArrayElementsSliced(std::string_view name, SimContext& ctx,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width, uint32_t start,
                                      uint32_t count) {
  auto* info = ctx.FindArrayInfo(name);
  if (!info) return;
  for (uint32_t i = 0; i < count; ++i) {
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
                                uint32_t& total_width, Arena& arena) {
  for (const auto& elem : queue->elements) {
    parts.push_back(elem);
    total_width += elem.width;
  }
}

static void ExpandQueueElementsSliced(QueueObject* queue,
                                      std::vector<Logic4Vec>& parts,
                                      uint32_t& total_width, Arena& arena,
                                      uint32_t start, uint32_t count) {
  for (uint32_t i = 0; i < count; ++i) {
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

Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    if (elem->kind == ExprKind::kIdentifier) {
      if (auto* ainfo = ctx.FindArrayInfo(elem->text)) {
        if (elem->with_expr) {
          uint32_t start = 0, count = 0;
          ResolveWithRange(elem->with_expr, ctx, arena, ainfo->size, ainfo->lo,
                           start, count);
          ExpandArrayElementsSliced(elem->text, ctx, parts, total_width, start,
                                    count);
        } else {
          ExpandArrayElements(elem->text, ctx, parts, total_width);
        }
        continue;
      }

      if (auto* queue = ctx.FindQueue(elem->text)) {
        if (elem->with_expr) {
          uint32_t start = 0, count = 0;
          ResolveWithRange(elem->with_expr, ctx, arena,
                           static_cast<uint32_t>(queue->elements.size()), 0,
                           start, count);
          ExpandQueueElementsSliced(queue, parts, total_width, arena, start,
                                    count);
        } else {
          ExpandQueueElements(queue, parts, total_width, arena);
        }
        continue;
      }

      if (auto* aa = ctx.FindAssocArray(elem->text)) {
        ExpandAssocArrayElements(aa, parts, total_width);
        continue;
      }

      if (auto* sinfo = ctx.GetVariableStructType(elem->text)) {
        auto* var = ctx.FindVariable(elem->text);
        if (var) {
          if (sinfo->is_union) {
            ExpandUnionFirstMember(var, sinfo, parts, total_width, arena);
          } else {
            ExpandStructFields(var, sinfo, parts, total_width, arena);
          }
          continue;
        }
      }

      if (auto class_type = ctx.GetVariableClassType(elem->text);
          !class_type.empty()) {
        auto* var = ctx.FindVariable(elem->text);
        if (var) {
          uint64_t handle = var->value.ToUint64();
          if (handle == kNullClassHandle) {
            continue;
          }

          auto* obj = ctx.GetClassObject(handle);
          if (obj) {
            ExpandClassProperties(obj, parts, total_width, arena);
            continue;
          }
        }
      }
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
  uint32_t nslices = (total_width + ss - 1) / ss;
  auto result = MakeLogic4Vec(arena, total_width);
  for (uint32_t i = 0; i < nslices; ++i) {
    uint32_t src_start = i * ss;
    uint32_t dst_start =
        total_width > (i + 1) * ss ? total_width - (i + 1) * ss : 0;
    uint64_t slice = ExtractSlice(concat, src_start, ss);
    PlaceSlice(result, dst_start, slice, ss);
  }
  return result;
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
  return val.ToUint64();
}

static bool TryQueueSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;

  bool idx_xz = false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz) {
    out = MakeAllX(arena, q->elem_width);
    return true;
  }
  out = (idx < q->elements.size()) ? q->elements[idx]
                                   : MakeAllX(arena, q->elem_width);
  return true;
}

static const ArrayInfo* FindRootArrayInfo(const Expr* expr, SimContext& ctx) {
  const Expr* root = expr->base;
  while (root && root->kind == ExprKind::kSelect) root = root->base;
  return (root && root->kind == ExprKind::kIdentifier)
             ? ctx.FindArrayInfo(root->text)
             : nullptr;
}

// Reports whether the object a select reads from is four-state. An invalid
// bit-select address yields x on a four-state object but 0 on a two-state one,
// so the read result for an out-of-bounds or unknown index depends on this.
static bool SelectBaseIs4State(const Expr* expr, SimContext& ctx) {
  const Expr* root = expr->base;
  while (root && root->kind == ExprKind::kSelect) root = root->base;
  if (!root || root->kind != ExprKind::kIdentifier) return true;
  if (auto* info = ctx.FindArrayInfo(root->text)) return info->is_4state;
  if (auto* var = ctx.FindVariable(root->text)) return var->is_4state;
  return true;
}

static bool TryArrayElementSelect(const Expr* expr, uint64_t idx,
                                  SimContext& ctx, Arena& arena,
                                  Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* info = ctx.FindArrayInfo(expr->base->text);
  if (!info) return false;
  auto elem_name =
      std::string(expr->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(elem_name);
  if (!elem) {
    out = info->is_4state ? MakeAllX(arena, info->elem_width)
                          : MakeLogic4VecVal(arena, info->elem_width, 0);
    return true;
  }
  out = elem->value;
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

static bool TryCompoundArraySelect(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kSelect) return false;
  if (expr->index_end) return false;
  std::string compound;
  bool xz = false;
  if (!BuildCompoundName(expr, ctx, arena, compound, &xz)) {
    if (!xz) return false;

    if (auto* info = FindRootArrayInfo(expr, ctx)) {
      out = info->is_4state ? MakeAllX(arena, info->elem_width)
                            : MakeLogic4VecVal(arena, info->elem_width, 0);
      return true;
    }
    return false;
  }
  auto* elem = ctx.FindVariable(compound);
  if (!elem) {
    if (auto* info = FindRootArrayInfo(expr, ctx)) {
      out = info->is_4state ? MakeAllX(arena, info->elem_width)
                            : MakeLogic4VecVal(arena, info->elem_width, 0);
      return true;
    }
    return false;
  }
  out = elem->value;
  return true;
}

static bool TryArraySliceSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (!expr->index_end || !expr->base) return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* info = ctx.FindArrayInfo(expr->base->text);
  if (!info) return false;
  auto hi_val = EvalExpr(expr->index, ctx, arena).ToUint64();
  auto lo_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
  auto lo = std::min(hi_val, lo_val);
  auto hi = std::max(hi_val, lo_val);
  auto count = static_cast<uint32_t>(hi - lo + 1);
  uint32_t ew = info->elem_width;
  out = MakeLogic4Vec(arena, count * ew);
  for (uint32_t i = 0; i < count; ++i) {
    auto n = std::string(expr->base->text) + "[" + std::to_string(lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    auto val = v ? v->value.ToUint64() : 0;
    uint32_t bit_off = i * ew;
    out.words[bit_off / 64].aval |= (val & ((1ULL << ew) - 1))
                                    << (bit_off % 64);
  }
  return true;
}

static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, uint64_t idx,
                                uint64_t end_idx, Arena& arena) {
  auto lo = static_cast<uint32_t>(std::min(idx, end_idx));
  auto hi = static_cast<uint32_t>(std::max(idx, end_idx));
  uint32_t width = hi - lo + 1;
  uint64_t val = base_val.ToUint64() >> lo;
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  auto result = MakeLogic4VecVal(arena, width, val & mask);

  if (hi >= base_val.width && result.nwords > 0) {
    uint32_t first_oob = (base_val.width > lo) ? base_val.width - lo : 0;
    for (uint32_t b = first_oob; b < width && b < 64; ++b) {
      result.words[0].aval |= uint64_t{1} << b;
      result.words[0].bval |= uint64_t{1} << b;
    }
  }
  return result;
}

static Logic4Vec AssocDefault(const AssocArrayObject* aa, Arena& arena) {
  if (aa->has_default) return aa->default_value;
  return aa->is_4state ? MakeAllX(arena, aa->elem_width)
                       : MakeLogic4VecVal(arena, aa->elem_width, 0);
}

static std::string ExtractStringKey(const Logic4Vec& key) {
  uint32_t nb = key.width / 8;
  std::string s;
  s.reserve(nb);
  for (uint32_t i = nb; i > 0; --i) {
    uint32_t bi = i - 1;
    auto ch = static_cast<char>(
        (key.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
    if (ch != 0) s.push_back(ch);
  }
  return s;
}

static void WarnAssocMiss(const AssocArrayObject* aa, std::string_view name,
                          SimContext& ctx) {
  if (!aa->has_default)
    ctx.GetDiag().Warning({}, "associative array '" + std::string(name) +
                                  "': read of non-existent index");
}

static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto s = ExtractStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  if (it != aa->str_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx);
  return AssocDefault(aa, arena);
}

static Logic4Vec AssocReadInt(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto val = EvalExpr(idx_expr, ctx, arena);
  if (HasUnknownBits(val)) {
    // §7.8.6: an x/z index is an invalid read. A configured user default
    // suppresses the diagnostic and supplies the returned value (see §7.9.11),
    // matching the nonexistent-entry path in WarnAssocMiss.
    if (!aa->has_default)
      ctx.GetDiag().Warning({}, "associative array '" + std::string(name) +
                                    "': index contains x/z");
    return AssocDefault(aa, arena);
  }
  auto key =
      AssocIntKey(val, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  auto it = aa->int_data.find(key);
  if (it != aa->int_data.end()) return it->second;
  WarnAssocMiss(aa, name, ctx);
  return AssocDefault(aa, arena);
}

static bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* aa = ctx.FindAssocArray(expr->base->text);
  if (!aa) return false;
  out = aa->is_string_key
            ? AssocReadStr(aa, expr->index, expr->base->text, ctx, arena)
            : AssocReadInt(aa, expr->index, expr->base->text, ctx, arena);
  return true;
}

static Logic4Vec EvalPackedPartSelect(const Expr* expr, const Logic4Vec& base,
                                      uint64_t idx, SimContext& ctx,
                                      Arena& arena) {
  auto end_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
  if (expr->is_part_select_plus) {
    auto w = static_cast<uint32_t>(end_val);
    return EvalPartSelect(base, idx, idx + w - 1, arena);
  }
  if (expr->is_part_select_minus) {
    auto w = static_cast<uint32_t>(end_val);
    uint64_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
    return EvalPartSelect(base, lo, idx, arena);
  }
  return EvalPartSelect(base, idx, end_val, arena);
}

Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryQueueSelect(expr, ctx, arena, result)) return result;
  if (TryAssocSelect(expr, ctx, arena, result)) return result;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  if (HasUnknownBits(idx_val)) {
    if (!expr->index_end) {
      if (auto* info = FindRootArrayInfo(expr, ctx)) {
        return info->is_4state ? MakeAllX(arena, info->elem_width)
                               : MakeLogic4VecVal(arena, info->elem_width, 0);
      }
    }

    if (expr->index_end) {
      auto w = static_cast<uint32_t>(
          EvalExpr(expr->index_end, ctx, arena).ToUint64());
      return MakeAllX(arena, w > 0 ? w : 1);
    }
    return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                         : MakeLogic4VecVal(arena, 1, 0);
  }
  uint64_t idx = idx_val.ToUint64();
  if (TryArrayElementSelect(expr, idx, ctx, arena, result)) return result;
  if (TryCompoundArraySelect(expr, ctx, arena, result)) return result;
  if (TryArraySliceSelect(expr, ctx, arena, result)) return result;
  auto base_val = EvalExpr(expr->base, ctx, arena);

  if (base_val.is_string && !expr->index_end) {
    uint32_t nbytes = base_val.width / 8;
    if (idx >= nbytes) return MakeLogic4VecVal(arena, 8, 0);
    uint32_t byte_idx = nbytes - 1 - static_cast<uint32_t>(idx);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    uint64_t ch = (word < base_val.nwords)
                      ? (base_val.words[word].aval >> bit) & 0xFF
                      : 0;
    return MakeLogic4VecVal(arena, 8, ch);
  }
  if (expr->index_end)
    return EvalPackedPartSelect(expr, base_val, idx, ctx, arena);
  if (idx >= base_val.width)
    return SelectBaseIs4State(expr, ctx) ? MakeAllX(arena, 1)
                                         : MakeLogic4VecVal(arena, 1, 0);
  return MakeLogic4VecVal(arena, 1, (base_val.ToUint64() >> idx) & 1);
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
