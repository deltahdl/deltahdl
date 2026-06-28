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
#include "simulator/statement_assign_internal.h"

namespace delta {

static void RegisterStructInfo(const RtlirVariable& var, SimContext& ctx) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  StructTypeInfo info;
  info.type_name = var.name;
  info.is_packed = var.dtype->is_packed;
  info.is_union = (var.dtype->kind == DataTypeKind::kUnion);
  info.is_soft = var.dtype->is_soft;
  info.total_width = var.width;

  uint32_t offset = var.width;
  for (const auto& m : var.dtype->struct_members) {
    uint32_t fw = EvalStructMemberWidth(m);
    if (info.is_union) {
      info.fields.push_back({m.name, 0, fw, m.type_kind});
    } else {
      offset -= fw;
      info.fields.push_back({m.name, offset, fw, m.type_kind});
    }
  }
  ctx.RegisterStructType(var.name, info);
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
    elem->value = EvalExpr(elements[elem_idx], ctx, arena);
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
  elem->value = EvalExpr(rep->elements[elem_idx % inner_count], ctx, arena);
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

  if (InitArrayFromIndexKey(init, idx, elem, ctx, arena)) return;
  if (InitArrayFromTypeKey(init, var.elem_type_kind, elem, ctx, arena)) return;
  if (InitArrayFromDefaultKey(init, elem, ctx, arena)) return;
  elem->value = MakeLogic4VecVal(arena, var.width, 0);
}

static void CreateArrayElements(const RtlirVariable& var, SimContext& ctx,
                                Arena& arena) {
  if (var.unpacked_size == 0) return;
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
      auto val = EvalExpr(m.init_expr, ctx, arena).ToUint64();
      uint64_t mask =
          (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
      uint64_t old_val = v->value.ToUint64();
      old_val |= (val & mask) << f.bit_offset;
      v->value = MakeLogic4VecVal(arena, v->value.width, old_val);
      break;
    }
  }
}

void Lowerer::LowerVarAggregate(const RtlirVariable& var) {
  if (var.is_queue) {
    ctx_.CreateQueue(var.name, var.width, var.queue_max_size, var.is_4state);
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

void Lowerer::LowerVar(const RtlirVariable& var) {
  uint32_t width = var.class_type_name.empty() ? var.width : 64;
  auto* v = ctx_.CreateVariable(var.name, width);

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
  RegisterStructInfo(var, ctx_);
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

void Lowerer::LowerVarInit(const RtlirVariable& var, Variable* v,
                           uint32_t width) {
  if (var.is_event && var.init_expr->kind == ExprKind::kIdentifier &&
      var.init_expr->text == "null") {
    v->is_null_event = true;
    return;
  }

  if (var.is_event && var.init_expr->kind == ExprKind::kIdentifier) {
    auto* target = ctx_.FindVariable(var.init_expr->text);
    if (target && target->is_event) {
      ctx_.AliasVariable(var.name, var.init_expr->text);
      return;
    }
  }
  if (TryLowerClassNewVarInit(var, v, ctx_, arena_)) return;

  auto* sinfo = ctx_.GetVariableStructType(var.name);

  auto* init = var.init_expr;
  if (init->kind == ExprKind::kCast && init->lhs &&
      init->lhs->kind == ExprKind::kAssignmentPattern)
    init = init->lhs;
  bool named =
      init->kind == ExprKind::kAssignmentPattern && !init->pattern_keys.empty();
  if (named && sinfo) {
    v->value = EvalStructPattern(init, sinfo, ctx_, arena_);
    return;
  }
  auto val = EvalExpr(var.init_expr, ctx_, arena_);
  if (val.width != width && !var.is_real && !var.is_string)
    val = MakeLogic4VecVal(arena_, width, val.ToUint64());

  if (var.is_string) val = StripStringZeros(val, arena_);
  v->value = val;
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
