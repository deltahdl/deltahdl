#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// Builds the layout of a struct/union DataType: each field's bit offset (within
// its own width frame) and width, recursing into aggregate members so a nested
// member is reachable by its dotted path (§7.2.1). The result is arena-owned so
// the registered top-level copy's nested pointers stay valid.
static StructTypeInfo* BuildStructTypeInfo(const DataType* dtype,
                                           uint32_t total_width,
                                           std::string_view type_name,
                                           Arena& arena) {
  auto* info = arena.Create<StructTypeInfo>();
  info->type_name = type_name;
  info->is_packed = dtype->is_packed;
  info->is_union = (dtype->kind == DataTypeKind::kUnion);
  info->is_soft = dtype->is_soft;
  info->total_width = total_width;

  uint32_t offset = total_width;
  for (const auto& m : dtype->struct_members) {
    uint32_t fw = EvalStructMemberWidth(m);
    uint32_t field_off = 0;
    if (!info->is_union) {
      offset -= fw;
      field_off = offset;
    }
    StructFieldInfo fi{m.name, field_off, fw, m.type_kind};
    if (m.nested_type && !m.nested_type->struct_members.empty()) {
      fi.nested = BuildStructTypeInfo(m.nested_type, fw, m.type_name, arena);
    }
    info->fields.push_back(fi);
  }
  return info;
}

static void RegisterStructInfo(const RtlirVariable& var, SimContext& ctx,
                               Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  auto* info = BuildStructTypeInfo(var.dtype, var.width, var.name, arena);
  ctx.RegisterStructType(var.name, *info);
  ctx.SetVariableStructType(var.name, var.name);
}

static uint8_t StringLiteralByteAt(const Logic4Vec& packed, uint32_t i) {
  uint32_t nbytes = packed.width / 8;
  if (i >= nbytes) return 0;
  uint32_t byte_idx = nbytes - 1 - i;
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  if (word >= packed.nwords) return 0;
  return static_cast<uint8_t>((packed.words[word].aval >> bit) & 0xFF);
}

static void InitArrayElement(const RtlirVariable& var, uint32_t elem_idx,
                             Variable* elem, SimContext& ctx, Arena& arena) {
  if (!var.init_expr) {
    elem->value = MakeLogic4VecVal(arena, var.width, 0);
    return;
  }

  if (var.init_expr->kind == ExprKind::kStringLiteral) {
    auto packed = EvalExpr(var.init_expr, ctx, arena);
    auto b = StringLiteralByteAt(packed, elem_idx);
    elem->value = MakeLogic4VecVal(arena, var.width, b);
    return;
  }
  auto& elements = var.init_expr->elements;
  if (elem_idx < elements.size()) {
    // §10.9.1: each pattern item is evaluated in the assignment context of its
    // element, so a value whose self-width differs is coerced to the element
    // width (no-op when they already match).
    elem->value = ResizeToWidth(EvalExpr(elements[elem_idx], ctx, arena),
                                var.width, arena);
    return;
  }
  elem->value = MakeLogic4VecVal(arena, var.width, 0);
}

static void InitArrayFromReplicate(const RtlirVariable& var, uint32_t elem_idx,
                                   Variable* elem, SimContext& ctx,
                                   Arena& arena) {
  auto* rep = var.init_expr->elements[0];
  auto inner_count = static_cast<uint32_t>(rep->elements.size());
  if (inner_count == 0) {
    elem->value = MakeLogic4VecVal(arena, var.width, 0);
    return;
  }
  // §10.9.1: a replicated item is likewise evaluated in its element's
  // assignment context.
  elem->value =
      ResizeToWidth(EvalExpr(rep->elements[elem_idx % inner_count], ctx, arena),
                    var.width, arena);
}

static bool InitArrayFromIndexKey(const Expr* init, uint32_t idx,
                                  Variable* elem, SimContext& ctx,
                                  Arena& arena) {
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto& key = init->pattern_keys[i];
    if (key == "default" || IsTypeKeyword(key)) continue;
    auto key_idx = static_cast<uint32_t>(std::stoul(std::string(key)));
    if (key_idx == idx) {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return true;
    }
  }
  return false;
}

static bool InitArrayFromTypeKey(const Expr* init, DataTypeKind elem_type_kind,
                                 Variable* elem, SimContext& ctx,
                                 Arena& arena) {
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto& key = init->pattern_keys[i];
    if (IsTypeKeyword(key) && TypeKeyMatchesKind(key, elem_type_kind)) {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return true;
    }
  }
  return false;
}

static bool InitArrayFromDefaultKey(const Expr* init, Variable* elem,
                                    SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    if (init->pattern_keys[i] == "default") {
      elem->value = EvalExpr(init->elements[i], ctx, arena);
      return true;
    }
  }
  return false;
}

static void InitArrayFromNamed(const RtlirVariable& var, uint32_t idx,
                               Variable* elem, SimContext& ctx, Arena& arena) {
  auto* init = var.init_expr;

  // §10.9.1: index, type, and default keys resolve a value that is then
  // evaluated in the assignment context of the element, so coerce the chosen
  // value to the element width (no-op when it already matches). An element
  // covered by none of the keys keeps the zero default at the element width.
  if (InitArrayFromIndexKey(init, idx, elem, ctx, arena) ||
      InitArrayFromTypeKey(init, var.elem_type_kind, elem, ctx, arena) ||
      InitArrayFromDefaultKey(init, elem, ctx, arena)) {
    elem->value = ResizeToWidth(elem->value, var.width, arena);
    return;
  }
  elem->value = MakeLogic4VecVal(arena, var.width, 0);
}

namespace {
// §7.4.2: bundle for materializing the leaves of a fixed multidimensional
// unpacked array, keeping the recursive walk within the parameter-count limit.
struct MultiDimArray {
  const RtlirVariable& var;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

// §7.4.2: recursively create one leaf variable per element of a fixed
// multidimensional unpacked array, named arr[i0][i1]... in row-major order so a
// compound select (eval_select.cpp) and a nested assignment pattern resolve to
// it. An untouched 2-state leaf defaults to 0; a 4-state leaf keeps the x that
// CreateVariable seeds (§6.4).
static void CreateMultiDimLeaves(const MultiDimArray& m,
                                 const std::string& prefix, size_t d) {
  const auto& sizes = m.var.unpacked_dim_sizes;
  if (d == sizes.size()) {
    auto* stored = m.arena.Create<std::string>(prefix);
    auto* elem = m.ctx.CreateVariable(*stored, m.var.width);
    elem->is_4state = m.var.is_4state;
    elem->is_signed = m.var.is_signed;
    if (!m.var.is_4state)
      elem->value = MakeLogic4VecVal(m.arena, m.var.width, 0);
    return;
  }
  uint32_t lo = m.var.unpacked_dim_los[d];
  for (uint32_t i = 0; i < sizes[d]; ++i) {
    CreateMultiDimLeaves(m, prefix + "[" + std::to_string(lo + i) + "]", d + 1);
  }
}

// §7.4.2: register a fixed multidimensional unpacked array and create its
// leaves. The single-dimension lo/size keep describing the outermost dimension
// (so existing whole-array and outer-index paths still work), while dim_los /
// dim_sizes carry every dimension. Returns false for a single-dimension array.
static bool TryCreateMultiDimArray(const RtlirVariable& var, SimContext& ctx,
                                   Arena& arena) {
  if (var.unpacked_dim_sizes.size() < 2) return false;
  ArrayInfo info;
  info.lo = var.unpacked_lo;
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  info.is_4state = var.is_4state;
  info.elem_type_kind = var.elem_type_kind;
  info.dim_los = var.unpacked_dim_los;
  info.dim_sizes = var.unpacked_dim_sizes;
  ctx.RegisterArray(var.name, info);
  CreateMultiDimLeaves(MultiDimArray{var, ctx, arena}, std::string(var.name),
                       0);
  return true;
}

static void CreateArrayElements(const RtlirVariable& var, SimContext& ctx,
                                Arena& arena) {
  if (var.unpacked_size == 0) return;
  if (TryCreateMultiDimArray(var, ctx, arena)) return;
  ArrayInfo info;
  info.lo = var.unpacked_lo;
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  info.is_4state = var.is_4state;
  info.elem_type_kind = var.elem_type_kind;
  ctx.RegisterArray(var.name, info);

  bool named = var.init_expr && !var.init_expr->pattern_keys.empty();
  bool replicate = var.init_expr && var.init_expr->elements.size() == 1 &&
                   var.init_expr->elements[0]->kind == ExprKind::kReplicate;
  for (uint32_t i = 0; i < var.unpacked_size; ++i) {
    uint32_t idx = var.unpacked_lo + i;
    auto elem_name = std::string(var.name) + "[" + std::to_string(idx) + "]";
    auto* stored = arena.Create<std::string>(std::move(elem_name));
    auto* elem = ctx.CreateVariable(*stored, var.width);
    uint32_t pat_idx = var.is_descending ? (var.unpacked_size - 1 - i) : i;
    if (named) {
      InitArrayFromNamed(var, idx, elem, ctx, arena);
    } else if (replicate) {
      InitArrayFromReplicate(var, pat_idx, elem, ctx, arena);
    } else {
      InitArrayElement(var, pat_idx, elem, ctx, arena);
    }
  }
}

static std::string StripQuotes(std::string_view s) {
  if (s.size() >= 2 && s.front() == '"' && s.back() == '"')
    return std::string(s.substr(1, s.size() - 2));
  return std::string(s);
}

// §7.5.1: a dynamic array declaration may use the new[] constructor as its
// declaration-assignment right-hand side. Size the array, default-initialize
// its elements, then copy from the optional initialization array. Returns true
// when the init_expr was a new[] constructor (handled here).
static bool LowerDynArrayNewInit(const Expr* init_expr, QueueObject* q,
                                 SimContext& ctx, Arena& arena) {
  if (init_expr->kind != ExprKind::kCall || init_expr->text != "new" ||
      init_expr->args.empty())
    return false;

  auto sz_val = EvalExpr(init_expr->args[0], ctx, arena);
  int64_t sz = SignExtend(sz_val.ToUint64(), sz_val.width);
  if (sz < 0) {
    ctx.GetDiag().Error({}, "dynamic array new[] size is negative");
    return true;
  }
  q->elements.assign(static_cast<size_t>(sz),
                     MakeLogic4VecVal(arena, q->elem_width, 0));
  if (init_expr->args.size() >= 2) {
    auto* src_expr = init_expr->args[1];
    if (src_expr && src_expr->kind == ExprKind::kIdentifier) {
      if (auto* src = ctx.FindQueue(src_expr->text)) {
        size_t copy_len = std::min(q->elements.size(), src->elements.size());
        for (size_t i = 0; i < copy_len; ++i) q->elements[i] = src->elements[i];
      }
    }
  }
  q->AssignFreshIds();
  return true;
}

void Lowerer::LowerDynArrayInit(const RtlirVariable& var) {
  if (!var.init_expr) return;
  auto* q = ctx_.FindQueue(var.name);
  if (!q) return;

  if (LowerDynArrayNewInit(var.init_expr, q, ctx_, arena_)) return;

  if (var.init_expr->kind != ExprKind::kAssignmentPattern &&
      var.init_expr->kind != ExprKind::kConcatenation)
    return;
  for (auto* elem : var.init_expr->elements) {
    q->elements.push_back(EvalExpr(elem, ctx_, arena_));
  }
}

void Lowerer::InitAssocDefault(const Expr* init, AssocArrayObject* aa) {
  if (!init || init->kind != ExprKind::kAssignmentPattern) return;
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    auto key = init->pattern_keys[i];
    auto val = EvalExpr(init->elements[i], ctx_, arena_);
    if (key == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripQuotes(key)] = val;
    } else {
      auto ikey = static_cast<int64_t>(std::stoll(std::string(key)));
      aa->int_data[ikey] = val;
    }
  }
}

static void ApplyStructMemberDefaults(const RtlirVariable& var, Variable* v,
                                      SimContext& ctx, Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  if (var.dtype->kind == DataTypeKind::kUnion) return;
  auto* sinfo = ctx.GetVariableStructType(var.name);
  if (!sinfo) return;
  for (const auto& f : sinfo->fields) {
    for (const auto& m : var.dtype->struct_members) {
      if (m.name != f.name || !m.init_expr) continue;
      // Multi-word safe: a field at bit offset >= 64 cannot be reached through
      // ToUint64() (which keeps only the low 64 bits).
      Logic4Vec val = EvalExpr(m.init_expr, ctx, arena);
      DepositBitField(v->value, f.bit_offset, val, f.width);
      break;
    }
  }
}

void Lowerer::LowerVarAggregate(const RtlirVariable& var) {
  if (var.is_queue) {
    ctx_.CreateQueue(var.name, var.width, var.queue_max_size, var.is_4state);
    // §7.10.1: a queue may be initialized from an assignment-pattern literal
    // (e.g. int q[$] = '{10, 20, 30}). Populate its elements like a dynamic
    // array; LowerDynArrayInit is a no-op when there is no initializer.
    LowerDynArrayInit(var);
  } else if (var.is_dynamic) {
    ctx_.CreateQueue(var.name, var.width);
    LowerDynArrayInit(var);

    ArrayInfo info;
    info.is_dynamic = true;
    info.elem_width = var.width;
    ctx_.RegisterArray(var.name, info);
  } else if (var.is_assoc) {
    auto* aa = ctx_.CreateAssocArray(
        var.name, var.width, var.is_string_index,
        AssocArraySpec{var.assoc_index_width, var.is_wildcard_index,
                       var.is_4state, var.is_index_signed});
    InitAssocDefault(var.init_expr, aa);
  } else {
    CreateArrayElements(var, ctx_, arena_);
  }
}

// §7.4.1: when a variable is a packed multidimensional array (more than one
// packed dimension, stored as a single flat vector), record the outermost
// element width and low bound so a single-index select `x[i]` slices that many
// bits rather than one bit. No-op for ordinary vectors and packed structs.
void Lowerer::RecordPackedArrayStride(const RtlirVariable& var, Variable* v) {
  const DataType* dt = var.dtype;
  if (!dt || dt->extra_packed_dims.empty() || !dt->packed_dim_left ||
      !dt->packed_dim_right)
    return;
  auto span = [&](const Expr* l, const Expr* r) -> uint32_t {
    int64_t lv = static_cast<int64_t>(EvalExpr(l, ctx_, arena_).ToUint64());
    int64_t rv = static_cast<int64_t>(EvalExpr(r, ctx_, arena_).ToUint64());
    return static_cast<uint32_t>((lv >= rv ? lv - rv : rv - lv) + 1);
  };
  uint32_t stride = 1;
  for (const auto& [l, r] : dt->extra_packed_dims) stride *= span(l, r);
  if (stride <= 1) return;
  int64_t lv = static_cast<int64_t>(
      EvalExpr(dt->packed_dim_left, ctx_, arena_).ToUint64());
  int64_t rv = static_cast<int64_t>(
      EvalExpr(dt->packed_dim_right, ctx_, arena_).ToUint64());
  v->packed_elem_width = stride;
  v->packed_outer_lo = static_cast<uint32_t>(std::min(lv, rv));
}

void Lowerer::LowerVar(const RtlirVariable& var) {
  uint32_t width = var.class_type_name.empty() ? var.width : 64;
  auto* v = ctx_.CreateVariable(var.name, width);
  RecordPackedArrayStride(var, v);

  // §25.9: track virtual interface variables so assignments bind them to an
  // interface instance and component access redirects through that binding.
  if (var.elem_type_kind == DataTypeKind::kVirtualInterface) {
    ctx_.RegisterVirtualInterfaceVar(v);
  }

  if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle) {
    v->value = MakeLogic4VecVal(arena_, width, 0);
  }

  if (var.is_chandle) v->value = MakeLogic4VecVal(arena_, width, 0);
  v->is_4state = var.is_4state;
  if (var.is_event) v->is_event = true;
  if (var.is_signed) v->is_signed = true;
  if (var.is_string) ctx_.RegisterStringVariable(var.name);
  if (var.is_real) ctx_.RegisterRealVariable(var.name);
  // §21.2.1.6: the %p renderer prints a null chandle as "null", so it needs to
  // know which variables are chandles.
  if (var.is_chandle) ctx_.RegisterChandleVariable(var.name);
  RegisterStructInfo(var, ctx_, arena_);
  if (var.init_expr) {
    LowerVarInit(var, v, width);
  }
  if (!var.init_expr) ApplyStructMemberDefaults(var, v, ctx_, arena_);
  if (!var.class_type_name.empty())
    ctx_.SetVariableClassType(var.name, var.class_type_name);

  if (!var.enum_type_name.empty() && var.dtype) {
    RegisterEnumForCast(var);
  }
  LowerVarAggregate(var);
}

// §8.7/§6.8: a class-handle declaration initialized with `new` constructs the
// object as part of static initialization (before any initial/always block),
// the same as a runtime `handle = new(args)` assignment. Generic EvalExpr
// cannot do this because a bare `new` call carries no target class type; the
// declared handle type supplies it. Returns true when it handled a class-new
// initializer.
static bool TryLowerClassNewVarInit(const RtlirVariable& var, Variable* v,
                                    SimContext& ctx, Arena& arena) {
  if (var.class_type_name.empty() || var.init_expr->kind != ExprKind::kCall ||
      var.init_expr->text != "new")
    return false;
  v->value = EvalClassNew(var.class_type_name, var.init_expr, ctx, arena);
  return true;
}

// §6.17/§15: an event variable initialized to `null` is a null event; one
// initialized to another event identifier aliases that event. Returns true when
// it handled an event initializer.
static bool TryLowerEventVarInit(const RtlirVariable& var, Variable* v,
                                 SimContext& ctx) {
  if (!var.is_event || var.init_expr->kind != ExprKind::kIdentifier)
    return false;
  if (var.init_expr->text == "null") {
    v->is_null_event = true;
    return true;
  }
  auto* target = ctx.FindVariable(var.init_expr->text);
  if (target && target->is_event) {
    ctx.AliasVariable(var.name, var.init_expr->text);
    return true;
  }
  return false;
}

void Lowerer::LowerVarInit(const RtlirVariable& var, Variable* v,
                           uint32_t width) {
  if (TryLowerEventVarInit(var, v, ctx_)) return;
  if (TryLowerClassNewVarInit(var, v, ctx_, arena_)) return;
  // §8.8: `C c = D::new;` at module scope constructs the specified type during
  // static initialization. The argument-less typed constructor is a bare
  // scope-resolved member access, not a `new` call, so route it to the typed
  // construction path before the generic initializer lowering below.
  {
    Logic4Vec typed;
    if (var.init_expr &&
        TryEvalTypedConstructorNew(var.init_expr, ctx_, arena_, typed)) {
      v->value = typed;
      return;
    }
  }

  auto* sinfo = ctx_.GetVariableStructType(var.name);

  auto* init = var.init_expr;
  if (init->kind == ExprKind::kCast && init->lhs &&
      init->lhs->kind == ExprKind::kAssignmentPattern)
    init = init->lhs;
  // §10.9.2: a struct-typed declaration initializer that is an assignment
  // pattern (keyed or positional) is evaluated against the member layout, so
  // each member expression is coerced to its member's type.
  if (init->kind == ExprKind::kAssignmentPattern && sinfo) {
    v->value = EvalStructPatternValue(init, sinfo, ctx_, arena_);
    return;
  }
  // §11.6: a declaration initializer is an assignment, so its target width is
  // the context the initializer expression is evaluated in, exactly as for a
  // procedural assign. For a plain integral scalar target this lets an
  // arithmetic initializer such as `logic [16:0] s = a + b;` keep the carry-out
  // that a self-determined evaluation at the operands' own width would drop.
  // Aggregate, real, string, event, and chandle initializers keep their
  // dedicated sizing and stay self-determined.
  uint32_t init_ctx = 0;
  if (!sinfo && !var.is_real && !var.is_string && !var.is_event &&
      !var.is_chandle && init->kind != ExprKind::kAssignmentPattern)
    init_ctx = width;
  auto val = EvalExpr(var.init_expr, ctx_, arena_, init_ctx);
  // §6.12.1: a declaration initializer is an assignment, so an initializer that
  // crosses the real/integer boundary undergoes the same implicit conversion as
  // a procedural assign (round-to-nearest ties-away one way; x/z->0 numeric
  // conversion the other), never a raw bit reinterpretation of the operand.
  if (val.is_real != var.is_real && !var.is_string && !val.is_string &&
      !var.is_event && !var.is_chandle)
    val = ConvertRealForKnownLhs(val, var.is_real, width, arena_);
  if (val.width != width && !var.is_real && !var.is_string)
    val = MakeLogic4VecVal(arena_, width, val.ToUint64());

  if (var.is_string) val = StripStringZeros(val, arena_);
  // §6.11.2: assigning a 4-state initializer to a 2-state variable is an
  // automatic conversion, so unknown/high-impedance bits become zero. The
  // width-mismatch branch above already drops them via the numeric
  // projection; this also covers the matching-width case.
  if (!var.is_4state && !var.is_string && !var.is_real && !var.is_event &&
      !var.is_chandle)
    CoerceTo2State(val);
  v->value = val;

  // §11.9: initializing a tagged-union variable with a tagged expression
  // establishes the variable's active tag, exactly as the procedural
  // `u = tagged Member value` assignment does. Without this the tag would stay
  // undefined and a later member access would not be checked against the tag
  // set by the initializer.
  if (var.init_expr->kind == ExprKind::kTagged && var.init_expr->rhs)
    ctx_.SetVariableTag(var.name, var.init_expr->rhs->text);
}

void Lowerer::RegisterEnumForCast(const RtlirVariable& var) {
  ctx_.SetVariableEnumType(var.name, var.enum_type_name);
}

void Lowerer::RegisterEnumTypes(const RtlirModule* mod) {
  for (const auto& [name, members] : mod->enum_types) {
    if (ctx_.FindEnumType(name)) continue;
    EnumTypeInfo info;
    info.type_name = name;
    for (const auto& m : members) {
      info.members.push_back({m.name, static_cast<uint64_t>(m.value)});
    }
    ctx_.RegisterEnumType(name, info);
  }
}

}  // namespace delta
