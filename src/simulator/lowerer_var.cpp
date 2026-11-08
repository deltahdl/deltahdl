#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/typename_writer.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/gen_block_const_frame.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/pattern_type_key.h"
#include "simulator/queue_bound.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sync_variable.h"

namespace delta {

static void RegisterStructInfo(std::string_view name, const RtlirVariable& var,
                               Variable* v, SimContext& ctx, Arena& arena) {
  RegisterAggregateLayout(name, var.dtype, var.width, ctx, arena);
  MarkUnpackedStructStorage(name, v, var.init_expr == nullptr, ctx);
}

uint8_t StringLiteralByteAt(const Logic4Vec& packed, uint32_t i) {
  uint32_t nbytes = packed.width / 8;
  if (i >= nbytes) return 0;
  uint32_t byte_idx = nbytes - 1 - i;
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  if (word >= packed.nwords) return 0;
  return static_cast<uint8_t>((packed.words[word].aval >> bit) & 0xFF);
}

const Expr* StringLiteralSource(const Expr* expr) {
  if (expr->kind == ExprKind::kCast) expr = expr->lhs;
  return expr->kind == ExprKind::kStringLiteral ? expr : nullptr;
}

static Logic4Vec ElementDefaultInitialValue(const RtlirVariable& var,
                                            Arena& arena) {
  return var.is_4state ? MakeAllX(arena, var.width)
                       : MakeLogic4VecVal(arena, var.width, 0);
}

static Logic4Vec CoerceArrayInitItem(const RtlirVariable& var, Logic4Vec val,
                                     Arena& arena) {
  val = ArrayItemForElement(var, val, arena);
  if (!var.is_4state && !var.is_string && !var.is_real) CoerceTo2State(val);
  if (!var.is_real) val.is_signed = var.is_signed;
  return val;
}

struct ElementTarget {
  Variable* elem = nullptr;
  const StructTypeInfo* layout = nullptr;
};

static void InitArrayElement(const RtlirVariable& var, uint32_t elem_idx,
                             const ElementTarget& target, SimContext& ctx,
                             Arena& arena) {
  Variable* elem = target.elem;
  const StructTypeInfo* layout = target.layout;
  if (!var.init_expr) {
    elem->value = ElementDefaultInitialValue(var, arena);
    return;
  }

  if (const Expr* str = StringLiteralSource(var.init_expr)) {
    auto packed = EvalExpr(str, ctx, arena);
    auto b = StringLiteralByteAt(packed, elem_idx);
    elem->value = MakeLogic4VecVal(arena, var.width, b);
    return;
  }
  auto& elements = var.init_expr->elements;
  if (elem_idx < elements.size()) {
    elem->value = CoerceArrayInitItem(
        var, EvalItemForLayout(elements[elem_idx], layout, ctx, arena), arena);
    return;
  }
  elem->value = ElementDefaultInitialValue(var, arena);
}

static void InitArrayFromReplicate(const RtlirVariable& var, uint32_t elem_idx,
                                   const ElementTarget& target, SimContext& ctx,
                                   Arena& arena) {
  Variable* elem = target.elem;
  auto* rep = var.init_expr->elements[0];
  auto inner_count = static_cast<uint32_t>(rep->elements.size());
  if (inner_count == 0) {
    elem->value = MakeLogic4VecVal(arena, var.width, 0);
    return;
  }
  elem->value = CoerceArrayInitItem(
      var,
      EvalItemForLayout(rep->elements[elem_idx % inner_count], target.layout,
                        ctx, arena),
      arena);
}

static void InitArrayFromNamed(const RtlirVariable& var, uint32_t idx,
                               const ElementTarget& target, SimContext& ctx,
                               Arena& arena) {
  const Expr* pat = var.init_expr;
  const Expr* item = IndexKeyedItem(pat, idx, ctx, arena);
  if (item == nullptr)
    item = TypeKeyedItem(pat, SubjectOfVariableElement(var, ctx, arena), ctx);
  if (item == nullptr && target.layout != nullptr &&
      PatternHasTypeKey(pat, ctx)) {
    target.elem->value = CoerceArrayInitItem(
        var, EvalStructPatternValue(pat, target.layout, ctx, arena), arena);
    return;
  }
  const Expr* fallback = DefaultKeyedItem(pat);
  if (item == nullptr) item = fallback;
  if (item == nullptr) {
    target.elem->value = ElementDefaultInitialValue(var, arena);
    return;
  }
  Logic4Vec val = item == fallback
                      ? EvalDefaultForElement(item, target.layout, ctx, arena)
                      : EvalExpr(item, ctx, arena);
  target.elem->value = CoerceArrayInitItem(var, val, arena);
}

static bool IsMultiDimArray(const RtlirVariable& var) {
  return var.unpacked_dim_sizes.size() >= 2 &&
         var.unpacked_dims.size() == var.unpacked_dim_sizes.size();
}

static bool TryCreateMultiDimArray(std::string_view name,
                                   const RtlirVariable& var, SimContext& ctx,
                                   Arena& arena) {
  if (!IsMultiDimArray(var)) return false;
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(var.unpacked_lo);
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  info.is_4state = var.is_4state;
  RecordElementType(info, var, ctx, arena);
  info.elem_type_is_unpacked_array = var.element.type_is_unpacked_array;
  info.dim_los.reserve(var.unpacked_dims.size());
  info.dim_descending.reserve(var.unpacked_dims.size());
  for (const auto& dim : var.unpacked_dims) {
    info.dim_los.push_back(static_cast<uint32_t>(dim.Low()));
    info.dim_descending.push_back(dim.left > dim.right);
  }
  info.dim_sizes = var.unpacked_dim_sizes;
  ctx.RegisterArray(name, info);
  FillMultiDimLeaves(name, var, ctx, arena, false);
  return true;
}

static std::string ArrayElementKey(std::string_view name,
                                   const RtlirVariable& var, uint32_t i) {
  uint32_t idx = static_cast<uint32_t>(var.unpacked_lo) + i;
  return std::string(name) + "[" + std::to_string(idx) + "]";
}

static void FillArrayElement(const RtlirVariable& var, uint32_t i,
                             const ElementTarget& target, SimContext& ctx,
                             Arena& arena) {
  bool named = var.init_expr && !var.init_expr->pattern_keys.empty();
  bool replicate = var.init_expr && var.init_expr->elements.size() == 1 &&
                   var.init_expr->elements[0]->is_pattern_replication;
  uint32_t idx = static_cast<uint32_t>(var.unpacked_lo) + i;
  uint32_t pat_idx = var.is_descending ? (var.unpacked_size - 1 - i) : i;
  if (named) {
    InitArrayFromNamed(var, idx, target, ctx, arena);
  } else if (replicate) {
    InitArrayFromReplicate(var, pat_idx, target, ctx, arena);
  } else {
    InitArrayElement(var, pat_idx, target, ctx, arena);
  }
}

void CreateArrayElements(std::string_view name, const RtlirVariable& var,
                         SimContext& ctx, Arena& arena) {
  if (var.unpacked_size == 0) return;
  if (TryCreateMultiDimArray(name, var, ctx, arena)) return;
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(var.unpacked_lo);
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  info.is_4state = var.is_4state;
  RecordElementType(info, var, ctx, arena);
  info.elem_type_is_unpacked_array = var.element.type_is_unpacked_array;
  ctx.RegisterArray(name, info);

  for (uint32_t i = 0; i < var.unpacked_size; ++i) {
    auto* stored = arena.Create<std::string>(ArrayElementKey(name, var, i));
    auto* elem = ctx.CreateVariable(*stored, var.width);
    RecordPackedRange(var.dtype, elem, ctx, arena);
    elem->is_4state = var.is_4state;
    elem->is_signed = var.is_signed;
    elem->is_string = var.is_string;
    elem->is_event = var.is_event;
    FillArrayElement(var, i, {elem, ctx.GetVariableStructType(name)}, ctx,
                     arena);
  }
}

void InitArrayElements(std::string_view name, const RtlirVariable& var,
                       SimContext& ctx, Arena& arena) {
  if (var.unpacked_size == 0) return;
  if (IsMultiDimArray(var)) {
    FillMultiDimLeaves(name, var, ctx, arena, true);
    return;
  }
  for (uint32_t i = 0; i < var.unpacked_size; ++i) {
    Variable* elem = ExistingArrayElement(ctx, ArrayElementKey(name, var, i));
    if (elem != nullptr)
      FillArrayElement(var, i, {elem, ctx.GetVariableStructType(name)}, ctx,
                       arena);
  }
}

static std::string StripQuotes(std::string_view s) {
  if (s.size() >= 2 && s.front() == '"' && s.back() == '"')
    return std::string(s.substr(1, s.size() - 2));
  return std::string(s);
}

static bool LowerDynArrayNewInit(const Expr* init_expr, QueueObject* q,
                                 SimContext& ctx, Arena& arena) {
  if (init_expr->kind != ExprKind::kCall || init_expr->text != "new" ||
      init_expr->args.empty())
    return false;

  auto sz_val = EvalExpr(init_expr->args[0], ctx, arena);
  int64_t sz = LongintValue(sz_val);
  if (sz < 0) {
    ctx.GetDiag().Error(init_expr->args[0]->range.start,
                        "dynamic array new[] size is negative",
                        Subclause("7.5.1"));
    return true;
  }
  q->elements.clear();
  q->elements.reserve(static_cast<size_t>(sz));
  for (int64_t i = 0; i < sz; ++i)
    q->elements.push_back(MakeLogic4VecVal(arena, q->elem_width, 0));
  if (init_expr->args.size() >= 2) {
    auto* src_expr = init_expr->args[1];
    if (src_expr && src_expr->kind == ExprKind::kIdentifier) {
      if (auto* src = ctx.FindQueue(src_expr->text)) {
        size_t copy_len = std::min(q->elements.size(), src->elements.size());
        for (size_t i = 0; i < copy_len; ++i)
          q->elements[i] = OwnRhsWords(src->elements[i], arena);
      }
    }
  }
  EnforceQueueBound(q, "new[]", init_expr->range.start, ctx);
  q->AssignFreshIds();
  return true;
}

void InitQueueFromDeclInit(QueueObject* q, const Expr* init, SimContext& ctx,
                           Arena& arena) {
  if (!q || !init) return;
  if (LowerDynArrayNewInit(init, q, ctx, arena)) return;
  if (FillQueueOfQueues(q, init, ctx, arena)) {
    EnforceQueueBound(q, "declaration initializer", init->range.start, ctx);
    return;
  }
  std::vector<Logic4Vec> items;
  if (init->kind == ExprKind::kConcatenation) {
    CollectQueueElements(init, ctx, arena, items);
  } else if (init->kind == ExprKind::kAssignmentPattern) {
    for (auto* elem : init->elements)
      items.push_back(EvalExpr(elem, ctx, arena));
  } else {
    return;
  }
  for (const auto& item : items)
    q->elements.push_back(SizedForQueueElement(*q, item, arena));
  EnforceQueueBound(q, "declaration initializer", init->range.start, ctx);
  q->AssignFreshIds();
}

void Lowerer::LowerDynArrayInit(QueueObject* q, const RtlirVariable& var) {
  InitQueueFromDeclInit(q, var.init_expr, ctx_, arena_);
}

void InitAssocFromDeclInit(const Expr* init, AssocArrayObject* aa,
                           SimContext& ctx, Arena& arena) {
  if (!init || init->kind != ExprKind::kAssignmentPattern) return;
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    const auto* key = init->pattern_keys[i];
    auto val = OwnRhsWords(EvalExpr(init->elements[i], ctx, arena), arena);
    if (key->text == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripQuotes(key->text)] = val;
    } else {
      auto key_val = EvalExpr(key, ctx, arena);
      aa->int_data[AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                               aa->is_index_signed)] = val;
    }
  }
}

void Lowerer::InitAssocDefault(const Expr* init, AssocArrayObject* aa) {
  InitAssocFromDeclInit(init, aa, ctx_, arena_);
}

static void ApplyStructMemberDefaults(std::string_view name,
                                      const RtlirVariable& var, Variable* v,
                                      SimContext& ctx, Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  if (var.dtype->kind == DataTypeKind::kUnion) return;
  auto* sinfo = ctx.GetVariableStructType(name);
  if (!sinfo) return;
  ApplyLayoutDefaults(v->value, *sinfo, 0, ctx, arena);
}

static DataTypeKind VcdEffectiveDeclKind(const RtlirVariable& var) {
  DataTypeKind kind = var.elem_type_kind;
  if (kind == DataTypeKind::kNamed && var.dtype != nullptr)
    kind = var.dtype->kind;
  if (kind == DataTypeKind::kEnum && var.dtype != nullptr &&
      var.dtype->enum_base_kind != DataTypeKind::kImplicit)
    return var.dtype->enum_base_kind;
  if (kind == DataTypeKind::kStruct && var.dtype != nullptr &&
      var.dtype->is_packed)
    return DataTypeKind::kBit;
  return kind;
}

static bool IsVirtualInterfaceDecl(const RtlirVariable& var) {
  return var.elem_type_kind == DataTypeKind::kVirtualInterface;
}

static uint32_t StorageWidth(const RtlirVariable& var) {
  if (!var.class_type_name.empty() || IsVirtualInterfaceDecl(var) ||
      var.covergroup != nullptr) {
    return 64;
  }
  return var.width;
}

static void MarkVirtualInterfaceVar(const RtlirVariable& var, Variable* v,
                                    uint32_t width, SimContext& ctx,
                                    Arena& arena) {
  if (!IsVirtualInterfaceDecl(var)) return;
  ctx.RegisterVirtualInterfaceVar(v);
  v->value = MakeLogic4VecVal(arena, width, 0);
}

static void RecordClassSpecialization(std::string_view name,
                                      const RtlirVariable& var,
                                      SimContext& ctx) {
  if (var.class_data_type == nullptr) return;
  RecordClassParamActuals(name, var.class_type_name,
                          var.class_data_type->type_params, ctx);
}

static void RecordVcdDeclaration(std::string_view name,
                                 const RtlirVariable& var, SimContext& ctx) {
  ctx.Vcd().SetVcdVarKind(name, VcdEffectiveDeclKind(var));
  if (var.is_enum_constant) ctx.Vcd().MarkVcdEnumConstant(name);
}

void Lowerer::LowerVar(std::string_view name, const RtlirVariable& var) {
  uint32_t width = StorageWidth(var);
  auto* v = ctx_.CreateVariable(name, width);
  RecordPackedRange(var.dtype, v, ctx_, arena_);
  MarkVirtualInterfaceVar(var, v, width, ctx_, arena_);
  RecordClassSpecialization(name, var, ctx_);

  if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle) {
    v->value = MakeLogic4VecVal(arena_, width, 0);
  }

  if (var.is_chandle) v->value = MakeLogic4VecVal(arena_, width, 0);
  v->is_4state = var.is_4state;
  v->declared_type = var.written_type != nullptr ? var.written_type : var.dtype;
  v->declared_unpacked = *arena_.Create<std::string>(UnpackedDimsText(var));
  if (var.is_event) v->is_event = true;
  if (var.is_signed) v->is_signed = true;
  if (var.is_string) ctx_.RegisterStringVariable(name);
  v->is_real = var.is_real;
  if (var.is_real) ctx_.RegisterRealVariable(name);
  RecordVcdDeclaration(name, var, ctx_);
  if (var.is_chandle) ctx_.RegisterChandleVariable(name);
  RegisterStructInfo(name, var, v, ctx_, arena_);
  if (!var.enum_type_name.empty() && var.dtype) {
    RegisterEnumForCast(name, var);
    ctx_.SetStorageEnumType(v, var.enum_type_name);
  }
  GenBlockConstFrame loop_consts(var.gen_block_consts, ctx_, arena_);
  if (var.init_expr) {
    ctx_.SetLoweringGenBlockPrefix(var.gen_block_prefix);
    LowerVarInit(name, var, v, width);
    ctx_.SetLoweringGenBlockPrefix({});
  }
  if (!var.init_expr) ApplyStructMemberDefaults(name, var, v, ctx_, arena_);
  if (!var.class_type_name.empty() && ctx_.GetVariableClassType(name).empty())
    ctx_.SetVariableClassType(name, var.class_type_name);
  CreateSyncObjectForVar(name, var, v, ctx_, arena_);
  LowerVarAggregate(name, var);
}

static bool TryLowerClassNewVarInit(std::string_view name,
                                    const RtlirVariable& var, Variable* v,
                                    SimContext& ctx, Arena& arena) {
  if (var.class_type_name.empty() || var.init_expr->kind != ExprKind::kCall ||
      var.init_expr->text != "new")
    return false;
  if (var.class_type_name == "weak_reference") {
    v->value = EvalWeakReferenceNew(var.init_expr, ctx, arena);
    return true;
  }
  std::string_view cls = ctx.GetVariableClassType(name);
  if (cls.empty()) cls = var.class_type_name;
  v->value =
      EvalClassNew(cls, var.init_expr, ctx, arena, var.init_expr->range.start);
  ApplyClassParamOverrides(name, v->value.ToUint64(), ctx, arena);
  return true;
}

static bool TryLowerEventVarInit(std::string_view name,
                                 const RtlirVariable& var, Variable* v,
                                 SimContext& ctx) {
  if (!var.is_event || var.init_expr->kind != ExprKind::kIdentifier)
    return false;
  if (var.init_expr->text == "null") {
    v->is_null_event = true;
    return true;
  }
  auto* target = ctx.FindVariable(var.init_expr->text);
  if (target && target->is_event) {
    ctx.AliasVariable(name, var.init_expr->text);
    return true;
  }
  return false;
}

Logic4Vec Lowerer::CoerceVarInitValue(const RtlirVariable& var, Logic4Vec val,
                                      uint32_t width) {
  if (val.is_real != var.is_real && !var.is_string && !val.is_string &&
      !var.is_event && !var.is_chandle)
    val = ConvertRealForKnownLhs(val, var.is_real, width, arena_);
  if (val.width != width && !var.is_real && !var.is_string)
    val = ResizeToWidth(val, width, arena_);
  if (var.is_string) val = StripStringZeros(val, arena_);
  if (!var.is_string && !var.is_real && !var.is_event && !var.is_chandle) {
    val.is_signed = var.is_signed;
    if (!var.is_4state) CoerceTo2State(val);
  }
  return val;
}

void Lowerer::LowerVarInit(std::string_view name, const RtlirVariable& var,
                           Variable* v, uint32_t width) {
  if (TryLowerEventVarInit(name, var, v, ctx_)) return;
  if (TryLowerClassNewVarInit(name, var, v, ctx_, arena_)) return;
  {
    Logic4Vec typed;
    if (var.init_expr &&
        TryEvalTypedConstructorNew(var.init_expr, ctx_, arena_, typed)) {
      v->value = typed;
      return;
    }
  }

  auto* sinfo = ctx_.GetVariableStructType(name);

  auto* init = var.init_expr;
  if (init->kind == ExprKind::kCast && init->lhs &&
      init->lhs->kind == ExprKind::kAssignmentPattern)
    init = init->lhs;
  if (init->kind == ExprKind::kAssignmentPattern && sinfo) {
    v->value = EvalStructPatternValue(init, sinfo, ctx_, arena_);
    return;
  }
  bool is_stream = init->kind == ExprKind::kStreamingConcat && !var.is_string;
  bool self_determined = sinfo != nullptr || var.is_real || var.is_string ||
                         var.is_event || var.is_chandle || is_stream ||
                         init->kind == ExprKind::kAssignmentPattern;
  auto val = EvalTaggedOrPlain(var.init_expr, sinfo, ctx_, arena_,
                               self_determined ? 0 : width);
  if (is_stream && width > 0) {
    val = WidenStreamPackToFixedTarget(val, width, init->range.start, ctx_,
                                       arena_);
  }
  v->value = CoerceVarInitValue(var, val, width);

  if (var.init_expr->kind == ExprKind::kTagged && var.init_expr->rhs)
    ctx_.SetVariableTag(name, var.init_expr->rhs->text);
}

}  // namespace delta
