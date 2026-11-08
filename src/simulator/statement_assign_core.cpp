#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/modport_expression.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/struct_string_member.h"
#include "simulator/variable.h"

namespace delta {

std::string LhsIdentName(const Expr* lhs) {
  while (lhs && lhs->kind == ExprKind::kSelect) lhs = lhs->base;
  if (lhs && lhs->kind == ExprKind::kIdentifier) return DeclaredKindsKey(lhs);
  return {};
}

void CoerceTo2State(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

Logic4Vec OwnRhsWords(const Logic4Vec& val, Arena& arena) {
  Logic4Vec copy = ExtractBitField(arena, val, 0, val.width);
  copy.is_real = val.is_real;
  copy.is_signed = val.is_signed;
  copy.is_string = val.is_string;
  copy.fills_width = val.fills_width;
  return copy;
}

void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena) {
  if (var->is_forced) return;
  var->value = var->is_string ? StripStringZeros(val, arena)
                              : ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

static Variable* DeepestElementPrefix(const Expr* lhs, SimContext& ctx,
                                      Arena& arena) {
  for (const Expr* p = lhs->base; p != nullptr && p->kind == ExprKind::kSelect;
       p = p->base) {
    std::string name;
    if (!BuildCompoundLhsName(p, ctx, arena, name)) continue;
    if (auto* var = ctx.FindVariable(name)) return var;
  }
  return nullptr;
}

static Variable* PackedRootVariable(std::string_view root, SimContext& ctx) {
  if (ctx.FindQueue(root) != nullptr || ctx.FindAssocArray(root) != nullptr)
    return nullptr;
  auto* var = ctx.FindVariable(root);
  return (var != nullptr && var->packed_elem_width > 1) ? var : nullptr;
}

Variable* TryResolveCompoundElementBase(const Expr* lhs, SimContext& ctx,
                                        Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  std::string compound;
  if (BuildCompoundLhsName(lhs, ctx, arena, compound) &&
      ctx.FindVariable(compound) != nullptr) {
    return nullptr;
  }
  std::string_view root = CompoundRootName(lhs);
  const ArrayInfo* info = ctx.FindArrayInfo(root);
  if (info == nullptr) return PackedRootVariable(root, ctx);
  if (info->elem_type_is_unpacked_array) return nullptr;
  return DeepestElementPrefix(lhs, ctx, arena);
}

static bool TryCompoundElementWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                                    SimContext& ctx, Arena& arena) {
  if (auto* elem = TryResolveCompoundElementBase(lhs, ctx, arena)) {
    WriteBitSelect(elem, lhs, rhs_val, ctx, arena);
    return true;
  }
  bool absent_element = false;
  if (auto* compound =
          TryResolveCompoundElement(lhs, ctx, arena, &absent_element)) {
    WriteVar(compound, rhs_val, arena);
    return true;
  }
  return absent_element;
}

static bool TryWriteClassPropertyPart(const Expr* lhs, Logic4Vec& rhs_val,
                                      SimContext& ctx, Arena& arena) {
  return TryWriteClassArrayElementChar(lhs, rhs_val, ctx, arena) ||
         TryWriteClassArrayElementBits(lhs, rhs_val, ctx, arena) ||
         TryWriteClassArrayElement(lhs, rhs_val, ctx, arena) ||
         TryWriteClassPropertyBits(lhs, rhs_val, ctx, arena);
}

static bool TryWriteStringVariableChar(Variable* var, const Expr* lhs,
                                       const Logic4Vec& rhs_val,
                                       SimContext& ctx, Arena& arena) {
  if (!var || lhs->kind != ExprKind::kSelect || !lhs->base || lhs->index_end)
    return false;
  auto base_name = LhsIdentName(lhs->base);
  if (base_name.empty() || !ctx.IsStringVariable(base_name)) return false;
  auto idx_val = EvalExpr(lhs->index, ctx, arena);
  if (!HasUnknownBits(idx_val)) {
    StringWriteByte(var, static_cast<uint32_t>(idx_val.ToUint64()),
                    static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF), arena);
    var->NotifyWatchers();
  }
  return true;
}

static bool DeclaredArrayOfStrings(const Expr* sel, SimContext& ctx) {
  const Expr* root = sel;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  if (root == nullptr || root->kind != ExprKind::kIdentifier) return false;
  const ArrayInfo* info = ctx.FindArrayInfo(root->text);
  if (info == nullptr) return false;
  if (info->elem_type_kind == DataTypeKind::kString) return true;
  std::string first(root->text);
  if (info->dim_los.empty()) {
    first += "[" + std::to_string(info->lo) + "]";
  } else {
    for (uint32_t lo : info->dim_los) first += "[" + std::to_string(lo) + "]";
  }
  return ctx.IsStringVariable(first);
}

static bool TryWriteStringElementChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                      SimContext& ctx, Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr ||
      lhs->index_end != nullptr || lhs->base->kind != ExprKind::kSelect ||
      !DeclaredArrayOfStrings(lhs->base, ctx))
    return false;
  Variable* element = TryResolveArrayElement(lhs->base, ctx);
  if (element == nullptr)
    element = TryResolveCompoundElement(lhs->base, ctx, arena, nullptr);
  if (element == nullptr || !element->is_string) return false;
  Logic4Vec idx_val = EvalExpr(lhs->index, ctx, arena);
  if (!HasUnknownBits(idx_val)) {
    StringWriteByte(element, static_cast<uint32_t>(idx_val.ToUint64()),
                    static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF), arena);
    element->NotifyWatchers();
  }
  return true;
}

static bool TryStructArrayMemberWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                                      SimContext& ctx, Arena& arena) {
  StructArrayElementRef ref;
  if (!ResolveStructArrayElement(lhs, ctx, arena, ref)) return false;
  if (!ref.in_range || (ref.var != nullptr && ref.var->is_forced)) return true;
  Logic4Vec bits = ref.is_string ? StringMemberHandle(rhs_val, arena)
                                 : ResizeToWidth(rhs_val, ref.width, arena);
  DepositBitField(*ref.value, ref.bit_offset, bits, ref.width);
  if (ref.var != nullptr) ref.var->NotifyWatchers();
  return true;
}

static Logic4Vec ElementBeforeMemberWrite(const Expr* select,
                                          uint32_t layout_width,
                                          SimContext& ctx, Arena& arena) {
  const AssocArrayObject* aa = FindAssocArrayOfBase(select->base, ctx, arena);
  if (aa != nullptr) {
    Logic4Vec key = EvalExpr(select->index, ctx, arena);
    bool held =
        aa->is_string_key
            ? aa->str_data.count(AssocStringKey(key)) != 0
            : !HasUnknownBits(key) && aa->int_data.count(AssocIntKey(
                                          key, aa->is_wildcard, aa->index_width,
                                          aa->is_index_signed)) != 0;
    if (!held)
      return OwnRhsWords(
          ResizeToWidth(AssocAllocValue(aa, arena), layout_width, arena),
          arena);
  }
  return OwnRhsWords(
      ResizeToWidth(EvalExpr(select, ctx, arena), layout_width, arena), arena);
}

SelectedElementMember ResolveSelectedElementMember(const Expr* lhs,
                                                   SimContext& ctx) {
  SelectedElementMember m;
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr ||
      lhs->lhs->kind != ExprKind::kSelect || lhs->lhs->index_end != nullptr ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier)
    return m;
  m.layout = ContainerElementLayout(lhs->lhs->base, ctx);
  if (m.layout != nullptr)
    m.field = ResolveStructField(m.layout, lhs->rhs->text, &m.offset);
  return m;
}

static bool TryContainerElementMemberWrite(const Expr* lhs,
                                           const Logic4Vec& rhs_val,
                                           SimContext& ctx, Arena& arena) {
  SelectedElementMember m = ResolveSelectedElementMember(lhs, ctx);
  if (m.field == nullptr) return false;
  const Expr* select = lhs->lhs;
  Logic4Vec element =
      ElementBeforeMemberWrite(select, m.layout->total_width, ctx, arena);
  DepositBitField(
      element, m.offset,
      ResizeToWidth(MemberBitsOf(rhs_val, m.field->type_kind, arena),
                    m.field->width, arena),
      m.field->width);
  PerformBlockingAssign(select, element, ctx, arena);
  return true;
}

static Logic4Vec ElementStoreValue(const Logic4Vec& rhs_val, const Expr* lhs,
                                   const Variable& elem, SimContext& ctx,
                                   Arena& arena) {
  if (!rhs_val.is_real && !elem.is_real &&
      !ctx.IsRealVariable(LhsIdentName(lhs)))
    return rhs_val;
  return ConvertRealOnAssign(rhs_val, lhs, elem, ctx, arena);
}

bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena) {
  if (TryStructArrayMemberWrite(lhs, rhs_val, ctx, arena)) return true;
  if (NamesOwnArrayProperty(lhs->base, ctx) &&
      TryWriteClassArrayElement(lhs, rhs_val, ctx, arena))
    return true;
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) {
    WriteVar(elem, ElementStoreValue(rhs_val, lhs, *elem, ctx, arena), arena);
    return true;
  }
  if (TryQueueIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (TryAssocIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (TryWriteAssocElementBits(lhs, rhs_val, ctx, arena)) return true;
  if (TryWriteStringPropertyChar(lhs, rhs_val, ctx, arena)) return true;
  if (TryWriteClassPropertyPart(lhs, rhs_val, ctx, arena)) return true;
  if (TryWriteStringElementChar(lhs, rhs_val, ctx, arena)) return true;
  if (TryCompoundElementWrite(lhs, rhs_val, ctx, arena)) return true;
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (TryWriteStringVariableChar(var, lhs, rhs_val, ctx, arena)) return true;
  if (var) {
    WriteBitSelect(var, lhs, rhs_val, ctx, arena);
  }
  return true;
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
  if (rhs_val.is_real && !lhs_is_real) {
    double d = RealVecToDouble(rhs_val);
    auto ival = static_cast<uint64_t>(static_cast<int64_t>(std::llround(d)));
    auto result = MakeLogic4VecVal(arena, target_width, ival);
    result.is_signed = true;
    return result;
  }
  if (!rhs_val.is_real && lhs_is_real) {
    uint64_t raw = rhs_val.nwords > 0
                       ? (rhs_val.words[0].aval & ~rhs_val.words[0].bval)
                       : 0;
    auto d = rhs_val.is_signed
                 ? static_cast<double>(SignExtend(raw, rhs_val.width))
                 : static_cast<double>(raw);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  if (rhs_val.is_real && lhs_is_real && rhs_val.width != target_width) {
    double d = RealVecToDouble(rhs_val);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  return ResizeToWidth(rhs_val, target_width, arena);
}

Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              const Variable& var, SimContext& ctx,
                              Arena& arena) {
  uint32_t target_width = var.value.width;
  auto name = LhsIdentName(lhs);
  if (name.empty()) return ResizeToWidth(rhs_val, target_width, arena);
  bool lhs_is_real = var.is_real || ctx.IsRealVariable(name);
  return ConvertRealForKnownLhs(rhs_val, lhs_is_real, target_width, arena);
}

static bool IsStringTarget(const Expr* lhs, SimContext& ctx) {
  auto name = LhsIdentName(lhs);
  if (!name.empty()) return ctx.IsStringVariable(name);
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->is_scope_resolution ||
      lhs->lhs == nullptr || lhs->rhs == nullptr ||
      lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  return ctx.IsStringVariable(std::string(lhs->lhs->text) + "." +
                              std::string(lhs->rhs->text));
}

static void RecordTaggedValueTags(const Expr* rhs, std::string key,
                                  const StructTypeInfo* layout, SimContext& ctx,
                                  Arena& arena) {
  while (rhs != nullptr && rhs->kind == ExprKind::kTagged &&
         rhs->rhs != nullptr) {
    ctx.SetVariableTag(*arena.Create<std::string>(key), rhs->rhs->text);
    layout = layout != nullptr ? TaggedMemberLayout(*layout, rhs->rhs->text)
                               : nullptr;
    if (layout == nullptr || !layout->is_union) return;
    key += '.';
    key += rhs->rhs->text;
    rhs = rhs->lhs;
  }
}

void RecordPropertyTags(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->rhs == nullptr || stmt->rhs->kind != ExprKind::kTagged ||
      stmt->rhs->rhs == nullptr)
    return;
  std::string name;
  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    name = std::string(stmt->lhs->text);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    BuildLhsName(stmt->lhs, name);
  } else {
    return;
  }
  std::string key;
  const StructTypeInfo* layout = PropertyAggregateLayout(name, ctx, key);
  if (layout == nullptr || !layout->is_union) return;
  RecordTaggedValueTags(stmt->rhs, std::move(key), layout, ctx, arena);
}

void CopyTagChain(std::string src, std::string dst,
                  const StructTypeInfo* layout, SimContext& ctx, Arena& arena) {
  while (layout != nullptr && layout->is_union) {
    const std::string_view kTag = ctx.GetVariableTag(src);
    if (kTag.empty()) return;
    const std::string kOwnedTag(kTag);
    ctx.SetVariableTag(*arena.Create<std::string>(dst), kOwnedTag);
    layout = TaggedMemberLayout(*layout, kOwnedTag);
    src += '.';
    src += kOwnedTag;
    dst += '.';
    dst += kOwnedTag;
  }
}

static void RecordAssignedTag(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const StructTypeInfo* layout = StructLayoutOfName(stmt->lhs->text, ctx);
  const std::string kKey = TagKeyOfName(stmt->lhs->text, ctx);
  const Expr* source = stmt->rhs;
  if (source != nullptr && source->kind == ExprKind::kTagged) {
    RecordTaggedValueTags(source, kKey, layout, ctx, arena);
    return;
  }
  if (layout == nullptr || !layout->is_union) return;
  while (source != nullptr && source->kind == ExprKind::kTernary) {
    const Truth kChoice = TruthOf(EvalExpr(source->condition, ctx, arena));
    if (kChoice == Truth::kAmbiguous) return;
    source = kChoice == Truth::kTrue ? source->true_expr : source->false_expr;
  }
  if (source == nullptr) return;
  if (source->kind == ExprKind::kTagged) {
    RecordTaggedValueTags(source, kKey, layout, ctx, arena);
    return;
  }
  if (source->kind != ExprKind::kIdentifier) return;
  CopyTagChain(TagKeyOfName(source->text, ctx), kKey, layout, ctx, arena);
}

void AssignToScalarLhs(const Stmt* stmt, Logic4Vec rhs_val, SimContext& ctx,
                       Arena& arena) {
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (var) {
    if (var->is_forced) return;

    if (IsStringTarget(stmt->lhs, ctx)) {
      var->value = StripStringZeros(rhs_val, arena);
      var->NotifyWatchers();
      return;
    }
    rhs_val = ConvertRealOnAssign(rhs_val, stmt->lhs, *var, ctx, arena);
    var->value = rhs_val;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();

    RecordAssignedTag(stmt, ctx, arena);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    if (WriteStructField(stmt->lhs, rhs_val, ctx))
      RecordPropertyTags(stmt, ctx, arena);
  }
}

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
    if (ctx.FindLocalVariable(stmt->lhs->text) != nullptr) {
      ctx.AliasLocalVariable(stmt->lhs->text, rhs_var);
    } else {
      ctx.AliasVariable(stmt->lhs->text, stmt->rhs->text);
    }
    return true;
  }
  return false;
}

static bool TryArrayObjectAssign(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  return TryClassArrayWholeAssign(stmt, ctx, arena) ||
         TryClassArrayElementNewAssign(stmt, ctx, arena) ||
         TryAssocElementNewAssign(stmt, ctx, arena) ||
         TryQueueBlockingAssign(stmt, ctx, arena);
}

static bool TryDispatchSyncAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  return TrySemaphoreNewAssign(stmt, ctx, arena) ||
         TryMailboxNewAssign(stmt, ctx, arena) ||
         TrySyncHandleAssign(stmt, ctx, arena);
}

static bool TryDispatchNewAssign(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  return TryCovergroupOptionAssign(stmt, ctx, arena) ||
         TryCovergroupNewAssign(stmt, ctx, arena) ||
         TryClassArrayNewAssign(stmt, ctx, arena) ||
         TryClassNewAssign(stmt, ctx, arena) ||
         TryTypedClassNewAssign(stmt, ctx, arena) ||
         TryMemberClassNewAssign(stmt, ctx, arena) ||
         TryStructMemberClassNewAssign(stmt, ctx, arena);
}

static std::optional<std::vector<Logic4Vec>> DeconstructedElements(
    const Expr* rhs, SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> elems;
  if (rhs->kind == ExprKind::kIdentifier) {
    if (const ArrayInfo* ai = ctx.FindArrayInfo(rhs->text);
        ai != nullptr && !ai->is_dynamic && !ai->is_queue) {
      CollectFixedArrayElements(rhs->text, *ai, ctx, elems);
    } else if (const QueueObject* q = ctx.FindQueue(rhs->text)) {
      elems = q->elements;
    } else {
      return std::nullopt;
    }
  } else {
    const Expr* pattern = UnwrapTypedPattern(rhs);
    if (pattern->kind != ExprKind::kAssignmentPattern ||
        !pattern->pattern_keys.empty() || pattern->repeat_count != nullptr)
      return std::nullopt;
    for (const Expr* item : pattern->elements)
      elems.push_back(EvalExpr(item, ctx, arena));
  }
  for (Logic4Vec& elem : elems) elem = OwnRhsWords(elem, arena);
  return elems;
}

static bool TryDeconstructingPatternAssign(const Stmt* stmt, SimContext& ctx,
                                           Arena& arena) {
  if (stmt->rhs == nullptr) return false;
  const Expr* target = UnwrapTypedPattern(stmt->lhs);
  if (target->kind != ExprKind::kAssignmentPattern ||
      !target->pattern_keys.empty())
    return false;
  auto elems = DeconstructedElements(stmt->rhs, ctx, arena);
  if (!elems || elems->size() != target->elements.size()) return false;
  for (size_t i = 0; i < elems->size(); ++i)
    PerformBlockingAssign(target->elements[i], (*elems)[i], ctx, arena);
  return true;
}

static bool TryAssocAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  return TryAssocMapAssign(stmt, ctx, arena) || TryAssocCopyAssign(stmt, ctx) ||
         TryAssocLiteralAssign(stmt, ctx, arena);
}

static bool TryConditionalAssign(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  return TryConditionalArrayAssign(stmt, ctx, arena) ||
         TryConditionalCollectionAssign(stmt, ctx, arena);
}

bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  if (TryDeconstructingPatternAssign(stmt, ctx, arena)) return true;
  if (TryConditionalAssign(stmt, ctx, arena)) return true;
  if (TryCallResultArrayAssign(stmt, ctx, arena)) return true;
  if (TryDispatchSyncAssign(stmt, ctx, arena)) return true;
  if (TryDispatchNewAssign(stmt, ctx, arena)) return true;
  if (TryAssocAssign(stmt, ctx, arena)) return true;
  if (TryModportExpressionAssign(stmt, ctx, arena)) return true;
  if (TryStreamingConcatToQueueTarget(stmt, ctx, arena)) return true;
  if (TryArrayObjectAssign(stmt, ctx, arena)) return true;
  if (TryEventVarAssign(stmt, ctx)) return true;
  if (TryUnpackedSliceAssign(stmt, ctx, arena)) return true;
  if (TrySubarrayAssign(stmt, ctx, arena)) return true;
  if (TryArrayAggregateAssign(stmt, ctx, arena)) return true;
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(stmt->rhs->op) && !stmt->rhs->is_parenthesized) {
    ApplyCompoundAssignOp(stmt, ctx, arena);
    return true;
  }
  return false;
}

void ApplyGenericBlockingAssign(const Stmt* stmt, Logic4Vec rhs_val,
                                SimContext& ctx, Arena& arena) {
  LhsIndexPin pin(stmt->lhs, ctx, arena);
  if (TryUnpackConcatLhs(stmt->lhs, rhs_val, ctx, arena)) return;
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  rhs_val = ApplyStreamPackToTargetWidening(stmt, rhs_val, ctx, arena);
  if (TryContainerElementMemberWrite(stmt->lhs, rhs_val, ctx, arena)) return;
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
  LhsIndexPin pin(TaggedElementTarget(stmt), ctx, arena);
  auto rhs_val = EvalRhsCarryingReturnedTag(stmt, ctx, arena);
  rhs_val = OwnRhsWords(rhs_val, arena);
  ApplyGenericBlockingAssign(stmt, rhs_val, ctx, arena);
  return StmtResult::kDone;
}

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena) {
  if (!lhs) return;
  LhsIndexPin pin(lhs, ctx, arena);
  Logic4Vec owned = OwnRhsWords(rhs_val, arena);
  if (TryUnpackConcatLhs(lhs, owned, ctx, arena)) return;
  if (TryModportExpressionWrite(lhs, owned, ctx, arena)) return;

  if (lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(lhs, owned, ctx, arena);
    return;
  }
  if (TryContainerElementMemberWrite(lhs, owned, ctx, arena)) return;
  if (lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(lhs, owned, ctx, arena);
    return;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (var) {
    if (var->is_forced) return;
    if (IsStringTarget(lhs, ctx)) {
      var->value = StripStringZeros(owned, arena);
      var->NotifyWatchers();
      return;
    }
    auto converted = ConvertRealOnAssign(owned, lhs, *var, ctx, arena);
    var->value = converted;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  } else if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, owned, ctx);
  } else if (lhs->kind == ExprKind::kIdentifier) {
    TryFuncClassPropertyWrite(lhs, owned, ctx, arena);
  }
}

}  // namespace delta
