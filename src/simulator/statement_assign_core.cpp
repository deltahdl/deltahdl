#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

static std::string_view LhsIdentName(const Expr* lhs) {
  while (lhs) {
    if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
    if (lhs->kind == ExprKind::kSelect && lhs->base) {
      lhs = lhs->base;
      continue;
    }
    break;
  }
  return {};
}

void CoerceTo2State(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

static void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena) {
  var->value = ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

static bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                                    SimContext& ctx, Arena& arena) {
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) {
    WriteVar(elem, rhs_val, arena);
    return true;
  }
  if (TryQueueIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (TryAssocIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (auto* compound = TryResolveCompoundElement(lhs, ctx, arena)) {
    WriteVar(compound, rhs_val, arena);
    return true;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);

  if (var && lhs->kind == ExprKind::kSelect && lhs->base && !lhs->index_end) {
    auto base_name = LhsIdentName(lhs->base);
    if (!base_name.empty() && ctx.IsStringVariable(base_name)) {
      auto idx_val = EvalExpr(lhs->index, ctx, arena);
      if (!HasUnknownBits(idx_val)) {
        StringWriteByte(var, static_cast<uint32_t>(idx_val.ToUint64()),
                        static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF), arena);
        var->NotifyWatchers();
      }
      return true;
    }
  }
  if (var) {
    WriteBitSelect(var, lhs, rhs_val, ctx, arena);
    var->NotifyWatchers();
  }
  return true;
}

static bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (stmt->rhs->kind != ExprKind::kIdentifier) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  auto* src = ctx.FindAssocArray(stmt->rhs->text);
  if (!dst || !src) return false;
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  return true;
}

// §7.12.5 — assigning the result of `src.map() with (...)` to an
// associative-array target, where the source is itself an associative array.
// map() returns an array whose set of index values matches the source, with
// each stored value replaced by the value of the with expression; copy those
// key/value pairs into the destination, replacing its previous contents. This
// is the associative analogue of the indexed-array map (whose result flows
// through the queue/dynamic-array element-collection path); without it a bare
// `dst = src.map() with (...)` between two associative arrays would leave the
// destination empty.
static bool TryAssocMapAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  if (!dst) return false;
  AssocArrayObject mapped;
  if (!TryCollectAssocMapResult(stmt->rhs, ctx, arena, mapped)) return false;
  dst->int_data = mapped.int_data;
  dst->str_data = mapped.str_data;
  return true;
}

static std::string StripAssocKeyQuotes(std::string_view key) {
  if (key.size() >= 2 && key.front() == '"' && key.back() == '"')
    return std::string(key.substr(1, key.size() - 2));
  return std::string(key);
}

// §7.9.11: besides writing an associative array one entry at a time, the whole
// array contents can be replaced by assigning an '{index:value} array literal.
// Discard the existing entries and repopulate keyed entries and the optional
// default from the pattern, mirroring the declaration-time initialization.
static bool TryAssocLiteralAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kAssignmentPattern)
    return false;
  if (stmt->rhs->pattern_keys.empty()) return false;
  auto* aa = ctx.FindAssocArray(stmt->lhs->text);
  if (!aa) return false;
  aa->int_data.clear();
  aa->str_data.clear();
  const Expr* rhs = stmt->rhs;
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    const auto& key = rhs->pattern_keys[i];
    auto val = EvalExpr(rhs->elements[i], ctx, arena);
    if (key == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripAssocKeyQuotes(key)] = val;
    } else {
      aa->int_data[static_cast<int64_t>(std::stoll(std::string(key)))] = val;
    }
  }
  return true;
}

// `new src_obj` shallow-copy form: returns true (and writes the copy handle to
// the target) when the rhs argument resolves to an existing class object.
static bool TryClassCopyNewAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto src_val = EvalExpr(stmt->rhs->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, 64, copy_handle);
    var->NotifyWatchers();
  }
  return true;
}

// `new (referent)` for a weak_reference-typed target: allocate the weak
// reference wrapper and write its handle to the target.
static void AssignWeakReferenceNew(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  uint64_t referent = kNullClassHandle;
  if (!stmt->rhs->args.empty()) {
    auto val = EvalExpr(stmt->rhs->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, 64, wr_handle);
    var->NotifyWatchers();
  }
}

static bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto type_name = ctx.GetVariableClassType(stmt->lhs->text);
  if (type_name.empty()) return false;

  if (TryClassCopyNewAssign(stmt, ctx, arena)) return true;

  if (type_name == "weak_reference") {
    AssignWeakReferenceNew(stmt, ctx, arena);
    return true;
  }

  auto handle = EvalClassNew(type_name, stmt->rhs, ctx, arena);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  ApplyClassParamOverrides(stmt->lhs->text, handle.ToUint64(), ctx, arena);
  return true;
}

static bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->rhs->rhs || stmt->rhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  if (stmt->rhs->rhs->text != "new") return false;
  auto* cls = ctx.FindClassType(stmt->rhs->lhs->text);
  if (!cls) return false;
  // §8.25: a parameterized class scope (E#(.N(77))::new) carries its
  // specialization overrides in the base identifier's elements. Bind them as
  // locals in a fresh scope before constructing so the constructor body reads
  // the overridden parameter values, mirroring the class-scope method path.
  bool parameterized = !stmt->rhs->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, stmt->rhs->lhs, ctx, arena);
  }
  auto handle = EvalClassNew(stmt->rhs->lhs->text, nullptr, ctx, arena);
  if (parameterized) ctx.PopScope();
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  return true;
}

// §8.12: the declared class-type name of property `field` on `type`, searching
// base classes along the parent chain. Empty when no such property exists or it
// is not class-typed.
static std::string_view MemberClassTypeName(const ClassTypeInfo* type,
                                            std::string_view field) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == field)
        return m->data_type.type_name;
    }
  }
  return {};
}

// §8.4 / §8.12: `obj.field = new` where field is a class handle. The bare `new`
// carries no type context, so resolve field's declared class type from the AST,
// construct the object, and store the resulting handle through the member chain
// (WriteStructField reaches the real nested handle, so a later shallow copy
// shares it rather than falling back to a flat "field.x" key).
static bool TryMemberClassNewAssign(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs->lhs || stmt->lhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->lhs->rhs || stmt->lhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  auto base_type = ctx.GetVariableClassType(stmt->lhs->lhs->text);
  if (base_type.empty()) return false;
  const auto* cls = ctx.FindClassType(base_type);
  if (cls == nullptr) return false;
  auto field_type = MemberClassTypeName(cls, stmt->lhs->rhs->text);
  if (field_type.empty() || ctx.FindClassType(field_type) == nullptr)
    return false;
  auto handle = EvalClassNew(field_type, stmt->rhs, ctx, arena);
  WriteStructField(stmt->lhs, handle, ctx);
  return true;
}

static const Expr* UnwrapTypedPattern(const Expr* expr) {
  if (expr->kind == ExprKind::kCast && expr->lhs &&
      expr->lhs->kind == ExprKind::kAssignmentPattern)
    return expr->lhs;
  return expr;
}

static uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx) {
  if (!lhs) return 0;
  // 11.3.6 / 11.6.1: a concatenation target's width is the sum of its operand
  // widths, and that width is the assignment context the right-hand side is
  // evaluated in (so `{carry, acc} = rega + regb` adds at the full LHS width
  // and keeps the carry-out bit).
  if (lhs->kind == ExprKind::kConcatenation) {
    uint32_t total = 0;
    for (auto* elem : lhs->elements) total += LhsContextWidth(elem, ctx);
    return total;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  return var ? var->value.width : 0;
}

Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  uint32_t ctx_width = LhsContextWidth(stmt->lhs, ctx);
  if (!stmt->rhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  }
  // §11.9: the member value of a tagged expression may be a §10.9.2 structure
  // assignment pattern (e.g. `i1 = tagged Add '{e1, 4, ed}`). Pack that pattern
  // against the union member's own struct layout, not the union as a whole, so
  // each field expression is coerced to its member's width instead of being
  // concatenated at its self-determined width.
  if (stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs &&
      stmt->rhs->lhs && stmt->rhs->lhs->kind == ExprKind::kAssignmentPattern) {
    if (const auto* sinfo = ctx.GetVariableStructType(stmt->lhs->text)) {
      for (const auto& field : sinfo->fields) {
        if (field.name == stmt->rhs->rhs->text && field.nested)
          return EvalStructPatternValue(stmt->rhs->lhs, field.nested, ctx,
                                        arena);
      }
    }
  }
  auto* inner = UnwrapTypedPattern(stmt->rhs);
  // §10.9.2: both keyed and positional structure patterns are evaluated against
  // the target's member layout so each member expression is coerced to its
  // member's type; only route when the target is actually a struct.
  if (inner->kind != ExprKind::kAssignmentPattern)
    return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  auto* sinfo = ctx.GetVariableStructType(stmt->lhs->text);
  if (!sinfo) return EvalExpr(stmt->rhs, ctx, arena, ctx_width);
  return EvalStructPatternValue(inner, sinfo, ctx, arena);
}

static std::pair<uint32_t, uint32_t> ComputeSliceRange(const Expr* expr,
                                                       SimContext& ctx,
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

static void CollectSliceSourceElements(const Expr* rhs, SimContext& ctx,
                                       Arena& arena,
                                       std::vector<Logic4Vec>& out) {
  if (rhs->kind != ExprKind::kSelect || !rhs->index_end) return;
  if (!rhs->base || rhs->base->kind != ExprKind::kIdentifier) return;
  auto* info = ctx.FindArrayInfo(rhs->base->text);
  if (!info) return;
  auto [lo, count] = ComputeSliceRange(rhs, ctx, arena);
  for (uint32_t i = 0; i < count; ++i) {
    auto n = std::string(rhs->base->text) + "[" + std::to_string(lo + i) + "]";
    auto* v = ctx.FindVariable(n);
    out.push_back(v ? v->value : MakeLogic4VecVal(arena, info->elem_width, 0));
  }
}

// §7.4.6: destination window of an unpacked-array slice assignment, i.e. the
// elements `base[dst_lo .. dst_lo+dst_count)` each `elem_width` bits wide.
struct UnpackedSliceTarget {
  std::string_view base;
  uint32_t dst_lo;
  uint32_t dst_count;
  uint32_t elem_width;
};

// When no element-wise source was collected, evaluate the rhs as a single
// packed value and split it into `dst.dst_count` element-width slices.
static void FillSliceSourceFromPacked(const Stmt* stmt,
                                      const UnpackedSliceTarget& dst,
                                      SimContext& ctx, Arena& arena,
                                      std::vector<Logic4Vec>& src) {
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  uint32_t elem_width = dst.elem_width;
  uint64_t mask =
      (elem_width >= 64) ? ~uint64_t{0} : (uint64_t{1} << elem_width) - 1;
  for (uint32_t i = 0; i < dst.dst_count; ++i)
    src.push_back(MakeLogic4VecVal(
        arena, elem_width, (val.ToUint64() >> (i * elem_width)) & mask));
}

// Write the collected source elements into the destination slice elements
// `dst.base[dst.dst_lo .. dst.dst_lo+dst.dst_count)`, resizing/coercing as for
// a scalar write.
static void WriteUnpackedSliceElements(const UnpackedSliceTarget& dst,
                                       const std::vector<Logic4Vec>& src,
                                       SimContext& ctx, Arena& arena) {
  for (uint32_t i = 0; i < dst.dst_count && i < src.size(); ++i) {
    auto n = std::string(dst.base) + "[" + std::to_string(dst.dst_lo + i) + "]";
    auto* var = ctx.FindVariable(n);
    if (!var) continue;
    var->value = ResizeToWidth(src[i], var->value.width, arena);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  }
}

static bool TryUnpackedSliceAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* lhs = stmt->lhs;
  if (lhs->kind != ExprKind::kSelect || !lhs->index_end) return false;
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* dst_info = ctx.FindArrayInfo(lhs->base->text);
  if (!dst_info) return false;
  auto [dst_lo, dst_count] = ComputeSliceRange(lhs, ctx, arena);
  UnpackedSliceTarget dst{lhs->base->text, dst_lo, dst_count,
                          dst_info->elem_width};
  std::vector<Logic4Vec> src;
  CollectSliceSourceElements(stmt->rhs, ctx, arena, src);
  if (src.empty()) {
    FillSliceSourceFromPacked(stmt, dst, ctx, arena, src);
  }
  WriteUnpackedSliceElements(dst, src, ctx, arena);
  return true;
}

static Variable* FindOrCreateElement(const std::string& name, uint32_t width,
                                     SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(name);
  if (var) return var;
  return ctx.CreateVariable(*arena.Create<std::string>(name), width);
}

static bool IsCompoundSelect(const Expr* expr) {
  return expr && expr->kind == ExprKind::kSelect && expr->base &&
         expr->base->kind == ExprKind::kSelect && !expr->index_end;
}

static bool TrySubarrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!IsCompoundSelect(stmt->lhs) || !IsCompoundSelect(stmt->rhs))
    return false;
  std::string dst_prefix, src_prefix;
  if (!BuildCompoundLhsName(stmt->lhs, ctx, arena, dst_prefix)) return false;
  if (!BuildCompoundLhsName(stmt->rhs, ctx, arena, src_prefix)) return false;
  std::string match = src_prefix + "[";
  std::vector<std::pair<std::string, Logic4Vec>> elems;
  for (const auto& [vname, vptr] : ctx.GetVariables()) {
    if (vname.starts_with(match))
      elems.emplace_back(std::string(vname.substr(src_prefix.size())),
                         vptr->value);
  }
  if (elems.empty()) return false;
  for (const auto& [suffix, val] : elems) {
    auto* dst = FindOrCreateElement(dst_prefix + suffix, val.width, ctx, arena);
    dst->value = val;
    dst->NotifyWatchers();
  }
  return true;
}

// §11.4.1/§11.5.1: width of a concatenation lvalue element -- a nested
// concatenation/assignment pattern sums its own elements; any other form
// reduces to the width of the resolved target variable (0 when unresolved).
static uint32_t ConcatLhsElemWidth(const Expr* e, SimContext& ctx) {
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kAssignmentPattern) {
    uint32_t total = 0;
    for (const auto* sub : e->elements) total += ConcatLhsElemWidth(sub, ctx);
    return total;
  }
  auto* var = ResolveLhsVariable(e, ctx);
  return var ? var->value.width : 0;
}

static void UnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                            SimContext& ctx, Arena& arena) {
  uint64_t rhs_raw = rhs_val.ToUint64();
  uint32_t bit_offset = 0;
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    const Expr* el = *it;
    uint32_t w = ConcatLhsElemWidth(el, ctx);
    if (w == 0) continue;
    uint64_t mask = (w >= 64) ? ~uint64_t{0} : (uint64_t{1} << w) - 1;
    uint64_t slice = (rhs_raw >> bit_offset) & mask;
    bit_offset += w;
    // §11.4.1: a nested concatenation lvalue distributes its slice recursively.
    if (el->kind == ExprKind::kConcatenation ||
        el->kind == ExprKind::kAssignmentPattern) {
      UnpackConcatLhs(el, MakeLogic4VecVal(arena, w, slice), ctx, arena);
      continue;
    }
    auto* var = ResolveLhsVariable(el, ctx);
    if (!var) continue;
    var->value = MakeLogic4VecVal(arena, w, slice);
    var->NotifyWatchers();
  }
}

static double RealVecToDouble(const Logic4Vec& v) {
  if (v.width == 32) {
    float f = 0.0f;
    auto bits = static_cast<uint32_t>(v.ToUint64());
    std::memcpy(&f, &bits, sizeof(float));
    return static_cast<double>(f);
  }
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

static Logic4Vec ConvertToRealIfNeeded(double d, uint32_t target_width,
                                       Arena& arena) {
  if (target_width == 32) {
    auto f = static_cast<float>(d);
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    auto result = MakeLogic4VecVal(arena, 32, fbits);
    result.is_real = true;
    return result;
  }
  uint64_t dbits = 0;
  std::memcpy(&dbits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, 64, dbits);
  result.is_real = true;
  return result;
}

Logic4Vec ConvertRealForKnownLhs(Logic4Vec rhs_val, bool lhs_is_real,
                                 uint32_t target_width, Arena& arena) {
  // §6.12.1: a real assigned to an integer converts by rounding to the nearest
  // integer with ties away from zero (std::llround), never a raw bit copy.
  if (rhs_val.is_real && !lhs_is_real) {
    double d = RealVecToDouble(rhs_val);
    auto ival = static_cast<uint64_t>(static_cast<int64_t>(std::llround(d)));
    auto result = MakeLogic4VecVal(arena, target_width, ival);
    result.is_signed = true;
    return result;
  }
  // §6.12.1: an expression assigned to a real converts numerically; x/z bits of
  // the source read as zero (ToUint64's aval & ~bval projection).
  if (!rhs_val.is_real && lhs_is_real) {
    uint64_t raw = rhs_val.nwords > 0
                       ? (rhs_val.words[0].aval & ~rhs_val.words[0].bval)
                       : 0;
    auto d = static_cast<double>(raw);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  if (rhs_val.is_real && lhs_is_real && rhs_val.width != target_width) {
    double d = RealVecToDouble(rhs_val);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  return ResizeToWidth(rhs_val, target_width, arena);
}

Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              uint32_t target_width, SimContext& ctx,
                              Arena& arena) {
  auto name = LhsIdentName(lhs);
  if (name.empty()) return ResizeToWidth(rhs_val, target_width, arena);
  bool lhs_is_real = ctx.IsRealVariable(name);
  return ConvertRealForKnownLhs(rhs_val, lhs_is_real, target_width, arena);
}

static void AssignToScalarLhs(const Stmt* stmt, Logic4Vec rhs_val,
                              SimContext& ctx, Arena& arena) {
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (var) {
    if (var->is_forced) return;

    auto lhs_name = LhsIdentName(stmt->lhs);
    if (!lhs_name.empty() && ctx.IsStringVariable(lhs_name)) {
      var->value = StripStringZeros(rhs_val, arena);
      var->NotifyWatchers();
      return;
    }
    rhs_val =
        ConvertRealOnAssign(rhs_val, stmt->lhs, var->value.width, ctx, arena);
    var->value = rhs_val;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();

    if (stmt->rhs && stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs)
      ctx.SetVariableTag(stmt->lhs->text, stmt->rhs->rhs->text);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(stmt->lhs, rhs_val, ctx);
  }
}

// §11.4.14: extract a slice of `total_w` bits from `src` starting at bit
// `start`, returning a `width`-bit Logic4Vec. Helper shared by the
// pack-to-queue path below.
static Logic4Vec ExtractWidenedSlice(const Logic4Vec& src, uint32_t start,
                                     uint32_t width, Arena& arena) {
  auto out = MakeLogic4Vec(arena, width);
  for (uint32_t b = 0; b < width; ++b) {
    uint32_t sbit = start + b;
    uint32_t sw = sbit / 64, sb = sbit % 64;
    uint32_t dw = b / 64, db = b % 64;
    if (sw < src.nwords) {
      if ((src.words[sw].aval >> sb) & 1ull)
        out.words[dw].aval |= uint64_t{1} << db;
      if ((src.words[sw].bval >> sb) & 1ull)
        out.words[dw].bval |= uint64_t{1} << db;
    }
  }
  return out;
}

// §11.4.14: handle a streaming_concatenation feeding a dynamically sized
// target. Resize the target to the smallest number of elements that is at
// least as wide as the stream; if the resized total exceeds the stream width,
// pad the stream with zero bits on the right before unpacking.
// Left-shift `stream` (stream_w bits) into a `total_w`-bit vector, padding the
// LSB side with zero bits. When no padding is needed the input is returned.
static Logic4Vec RightPadStreamToWidth(const Logic4Vec& stream,
                                       uint32_t stream_w, uint32_t total_w,
                                       Arena& arena) {
  if (total_w <= stream_w) return stream;
  auto widened = MakeLogic4Vec(arena, total_w);
  uint32_t shift = total_w - stream_w;
  for (uint32_t b = 0; b < stream_w; ++b) {
    uint32_t sw = b / 64, sb = b % 64;
    uint32_t dst_bit = shift + b;
    uint32_t dw = dst_bit / 64, db = dst_bit % 64;
    if (sw < stream.nwords) {
      if ((stream.words[sw].aval >> sb) & 1ull)
        widened.words[dw].aval |= uint64_t{1} << db;
      if ((stream.words[sw].bval >> sb) & 1ull)
        widened.words[dw].bval |= uint64_t{1} << db;
    }
  }
  return widened;
}

// §11.4.14: geometry of a widened bit-stream that is unpacked MSB-first into a
// queue: the padded stream bits plus the element count, total width, and
// element width describing how to carve it into successive elements.
struct WidenedStreamLayout {
  const Logic4Vec& widened;
  uint32_t n_elems;
  uint32_t total_w;
  uint32_t elem_w;
};

// Repopulate `queue` from the widened stream described by `layout`, carving out
// `n_elems` element-width slices (MSB-first into successive elements).
static void PopulateQueueFromWidenedStream(QueueObject* queue,
                                           const WidenedStreamLayout& layout,
                                           Arena& arena) {
  queue->elements.clear();
  queue->elements.reserve(layout.n_elems);
  for (uint32_t i = 0; i < layout.n_elems; ++i) {
    uint32_t src_start = layout.total_w - (i + 1) * layout.elem_w;
    queue->elements.push_back(
        ExtractWidenedSlice(layout.widened, src_start, layout.elem_w, arena));
  }
  queue->AssignFreshIds();
  ++queue->generation;
}

static bool TryStreamingConcatToQueueTarget(const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kStreamingConcat) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* queue = ctx.FindQueue(stmt->lhs->text);
  if (!queue) return false;

  auto stream = EvalExpr(stmt->rhs, ctx, arena);
  uint32_t stream_w = stream.width;
  uint32_t elem_w = queue->elem_width;
  if (elem_w == 0) return false;

  if (stream_w == 0) {
    queue->elements.clear();
    queue->element_ids.clear();
    ++queue->generation;
    return true;
  }

  uint32_t n_elems = (stream_w + elem_w - 1) / elem_w;
  uint32_t total_w = n_elems * elem_w;

  Logic4Vec widened = RightPadStreamToWidth(stream, stream_w, total_w, arena);
  PopulateQueueFromWidenedStream(
      queue, WidenedStreamLayout{widened, n_elems, total_w, elem_w}, arena);
  return true;
}

// §11.4.14: when a streaming_concatenation is the source of an assignment and
// the target is a data object of bit-stream type, the stream is left-aligned
// in the target. A fixed-size target wider than the stream is filled with
// zero bits on the right (LSB side); a fixed-size target narrower than the
// stream is an error.
Logic4Vec ApplyStreamPackToTargetWidening(const Stmt* stmt, Logic4Vec rhs_val,
                                          SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kStreamingConcat) {
    return rhs_val;
  }
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return rhs_val;
  }
  if (ctx.FindArrayInfo(stmt->lhs->text) || ctx.FindQueue(stmt->lhs->text) ||
      ctx.FindAssocArray(stmt->lhs->text)) {
    return rhs_val;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var || var->value.width == 0) return rhs_val;
  uint32_t target_width = var->value.width;
  uint32_t stream_width = rhs_val.width;
  if (target_width == stream_width) return rhs_val;
  if (target_width < stream_width) {
    ctx.GetDiag().Error(
        {},
        "streaming concatenation source is wider than the fixed-size target");
    return rhs_val;
  }

  return RightPadStreamToWidth(rhs_val, stream_width, target_width, arena);
}

// §25.9: assignment to a virtual interface variable. The right-hand side is
// another virtual interface, an interface instance, or null; bind, copy, or
// clear the target's interface-instance binding accordingly.
static bool TryVirtualInterfaceAssign(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
  if (!ctx.IsVirtualInterfaceVar(lhs_var)) return false;
  const Expr* rhs = stmt->rhs;
  if (!rhs || rhs->kind != ExprKind::kIdentifier) return false;

  if (rhs->text == "null") {
    ctx.UnbindVirtualInterface(lhs_var);
    return true;
  }
  auto* rhs_var = ctx.FindVariable(rhs->text);
  if (ctx.IsVirtualInterfaceVar(rhs_var)) {
    if (ctx.VirtualInterfaceIsBound(rhs_var)) {
      std::string src(ctx.VirtualInterfaceBinding(rhs_var));
      ctx.BindVirtualInterface(lhs_var, src);
    } else {
      ctx.UnbindVirtualInterface(lhs_var);
    }
    return true;
  }
  std::string scope = ctx.ResolveInstanceScope(rhs->text);
  if (!scope.empty()) {
    ctx.BindVirtualInterface(lhs_var, scope);
    return true;
  }
  return false;
}

// §6.18: assignment between named event variables. `e = null` nullifies the
// event; `e1 = e2` (both events) aliases the lhs to the rhs trigger.
static bool TryEventVarAssign(const Stmt* stmt, SimContext& ctx) {
  if (stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs ||
      stmt->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
  if (!lhs_var || !lhs_var->is_event) return false;

  if (stmt->rhs->text == "null") {
    ctx.NullifyEventVariable(stmt->lhs->text);
    return true;
  }
  auto* rhs_var = ctx.FindVariable(stmt->rhs->text);
  if (rhs_var && rhs_var->is_event) {
    ctx.AliasVariable(stmt->lhs->text, stmt->rhs->text);
    return true;
  }
  return false;
}

// §11.4.1: a compound assignment evaluates any left-hand index expression only
// once. The resolve/read/write helpers below each re-derive the target from
// lhs->index (and index_end) by calling EvalExpr on those nodes, which would
// invoke a side-effecting index (e.g. `data[f()] += 1`) several times. Evaluate
// each index expression a single time up front and stash the result as a
// per-expression snapshot; EvalExpr returns a stored snapshot ahead of any real
// evaluation, so every later read of the same index node reuses this value.
static void SnapshotSelectIndices(const Expr* lhs, SimContext& ctx,
                                  Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  SnapshotSelectIndices(lhs->base, ctx, arena);
  if (lhs->index != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index, EvalExpr(lhs->index, ctx, arena));
  if (lhs->index_end != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index_end,
                               EvalExpr(lhs->index_end, ctx, arena));
}

// Undoes SnapshotSelectIndices once the compound assignment has finished so the
// snapshots do not leak into later statements that reuse the same index nodes.
static void ClearSelectIndices(const Expr* lhs, SimContext& ctx) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  ClearSelectIndices(lhs->base, ctx);
  if (lhs->index != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index);
  if (lhs->index_end != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index_end);
}

// §11.4.1 compound assignment operators (`+=`, `<<=`, etc.): read-modify-write
// the lhs through the appropriate target kind.
static void ApplyCompoundAssignOp(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  auto base_op = CompoundAssignBaseOp(stmt->rhs->op);
  auto actual_rhs = EvalExpr(stmt->rhs->rhs, ctx, arena);

  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ResolveLhsVariable(stmt->lhs, ctx);
    if (var) {
      auto result = EvalBinaryOp(base_op, var->value, actual_rhs, arena);
      WriteVar(var, result, arena);
    }
  } else if (stmt->lhs->kind == ExprKind::kSelect) {
    SnapshotSelectIndices(stmt->lhs, ctx, arena);
    if (auto* elem = TryResolveArrayElement(stmt->lhs, ctx)) {
      auto result = EvalBinaryOp(base_op, elem->value, actual_rhs, arena);
      WriteVar(elem, result, arena);
    } else {
      auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
      auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
      TrySelectBlockingAssign(stmt->lhs, result, ctx, arena);
    }
    ClearSelectIndices(stmt->lhs, ctx);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
    auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
    WriteStructField(stmt->lhs, result, ctx);
  } else {
    auto result = EvalExpr(stmt->rhs, ctx, arena);
    AssignToScalarLhs(stmt, result, ctx, arena);
  }
}

// Run the chain of special-case blocking-assignment handlers that do not need
// the generic rhs value (virtual interfaces, class `new`, associative-array
// copy/literal, streaming-to-queue, queue/event/slice/subarray, and compound
// operators). Returns true when one of them fully handled the assignment.
static bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                             Arena& arena) {
  if (TryVirtualInterfaceAssign(stmt, ctx)) return true;
  if (TryClassNewAssign(stmt, ctx, arena)) return true;
  if (TryTypedClassNewAssign(stmt, ctx, arena)) return true;
  if (TryMemberClassNewAssign(stmt, ctx, arena)) return true;
  if (TryAssocMapAssign(stmt, ctx, arena)) return true;
  if (TryAssocCopyAssign(stmt, ctx)) return true;
  if (TryAssocLiteralAssign(stmt, ctx, arena)) return true;
  if (TryStreamingConcatToQueueTarget(stmt, ctx, arena)) return true;
  if (TryQueueBlockingAssign(stmt, ctx, arena)) return true;
  if (TryEventVarAssign(stmt, ctx)) return true;
  if (TryUnpackedSliceAssign(stmt, ctx, arena)) return true;
  if (TrySubarrayAssign(stmt, ctx, arena)) return true;
  // A bare `lhs op= rhs` statement carries the compound operator as its own rhs
  // node. A parenthesized compound assign is instead an embedded assignment
  // expression (11.4.1 primary `( operator_assignment )`), e.g. `x = (y += 2)`,
  // whose target is its own lhs (y), not the statement lhs (x); let it fall
  // through to the generic path so EvalExpr routes it to EvalCompoundAssign.
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(stmt->rhs->op) && !stmt->rhs->is_parenthesized) {
    ApplyCompoundAssignOp(stmt, ctx, arena);
    return true;
  }
  return false;
}

// Apply the generic blocking assignment of `rhs_val` once the special-case
// handlers have declined. Covers concatenation/pattern unpack, streaming
// unpack, bit/part-select writes, array writes, and the scalar fallback.
static void ApplyGenericBlockingAssign(const Stmt* stmt, Logic4Vec rhs_val,
                                       SimContext& ctx, Arena& arena) {
  // §10.9: a typed assignment pattern expression (type'{...}) is also a valid
  // left-hand target. Strip the type prefix so its members unpack the RHS
  // exactly as a bare positional pattern does.
  const Expr* lhs_pat = UnwrapTypedPattern(stmt->lhs);
  if (lhs_pat->kind == ExprKind::kConcatenation ||
      lhs_pat->kind == ExprKind::kAssignmentPattern) {
    UnpackConcatLhs(lhs_pat, rhs_val, ctx, arena);
    return;
  }
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  rhs_val = ApplyStreamPackToTargetWidening(stmt, rhs_val, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  if (TryArrayBlockingAssign(stmt, ctx, arena)) return;
  AssignToScalarLhs(stmt, rhs_val, ctx, arena);
}

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  if (TryDispatchSpecialBlockingAssign(stmt, ctx, arena))
    return StmtResult::kDone;
  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);
  ApplyGenericBlockingAssign(stmt, rhs_val, ctx, arena);
  return StmtResult::kDone;
}

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena) {
  if (!lhs) return;
  // §10.9: a typed assignment pattern expression on the left unpacks like the
  // bare pattern it wraps.
  const Expr* lhs_pat = UnwrapTypedPattern(lhs);
  if (lhs_pat->kind == ExprKind::kConcatenation ||
      lhs_pat->kind == ExprKind::kAssignmentPattern) {
    UnpackConcatLhs(lhs_pat, rhs_val, ctx, arena);
    return;
  }

  if (lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(lhs, rhs_val, ctx, arena);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) {
    Logic4Vec mutable_val = rhs_val;
    TrySelectBlockingAssign(lhs, mutable_val, ctx, arena);
    return;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (var) {
    if (var->is_forced) return;
    auto converted =
        ConvertRealOnAssign(rhs_val, lhs, var->value.width, ctx, arena);
    var->value = converted;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  } else if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, rhs_val, ctx);
  }
}

}  // namespace delta
