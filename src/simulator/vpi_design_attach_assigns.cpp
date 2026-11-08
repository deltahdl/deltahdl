#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/pattern_type_key.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_assigns_internal.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_prefixed_refs.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_expr_decompile.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_select_indexes.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

VpiHandle DeclaredIn(const VpiObject* scope, std::string_view name) {
  for (VpiObject* var : scope->loop_vars) {
    if (var != nullptr && var->name == name) return var;
  }
  for (VpiObject* child : scope->children) {
    const bool kDeclares =
        VpiIsVariablesType(child->type) || child->type == vpiNamedEvent ||
        child->type == vpiNamedEventArray || child->type == vpiRefObj;
    if (kDeclares && child->name == name) return child;
  }
  return nullptr;
}

VpiHandle BlockDeclaration(const VpiObject* scope, std::string_view name,
                           bool gen) {
  for (; scope != nullptr && !VpiIsInstanceType(scope->type);
       scope = scope->parent) {
    if ((scope->type == vpiGenScope) != gen) continue;
    VpiHandle declared = DeclaredIn(scope, name);
    if (declared != nullptr) return declared;
  }
  return nullptr;
}

VpiHandle ImportedObject(const AssignNames& names, std::string_view name) {
  for (const RtlirImport& entry : names.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    VpiHandle item = FindObjectForFlatName(
        names.objects, VpiFlatName(std::string(entry.package_name), name));
    if (item == nullptr) continue;
    const VpiObject* at = names.scope != nullptr ? names.scope : names.instance;
    while (!VpiIsInstanceType(at->type)) at = at->parent;
    std::vector<VpiObject*>& imported = at->instance_facts.imported;
    if (std::ranges::find(imported, item) == imported.end()) {
      imported.push_back(item);
    }
    return item;
  }
  return nullptr;
}

}  // namespace

VpiHandle Resolve(const AssignNames& names, std::string_view name) {
  VpiHandle declared = BlockDeclaration(names.scope, name, false);
  if (declared != nullptr) return declared;
  for (auto it = names.gen.rbegin(); it != names.gen.rend(); ++it) {
    VpiHandle obj = FindObjectForFlatName(
        names.objects,
        VpiFlatName(names.prefix, std::string(*it) + std::string(name)));
    if (obj != nullptr) return obj;
  }
  declared = BlockDeclaration(names.scope, name, true);
  if (declared != nullptr) return declared;
  VpiHandle own =
      FindObjectForFlatName(names.objects, VpiFlatName(names.prefix, name));
  return own != nullptr ? own : ImportedObject(names, name);
}

namespace {

VpiObject* OperationObject(int op_type,
                           const std::vector<const Expr*>& operands,
                           const AssignBuild& build) {
  if (op_type == 0) return nullptr;
  VpiObject* op = build.alloc();
  op->type = vpiOperation;
  op->op_type = op_type;
  for (const Expr* operand : operands) {
    VpiObject* obj = ExpressionObject(operand, build);
    if (obj != nullptr) op->children.push_back(obj);
  }
  return op;
}

VpiObject* ConstantObject(const Expr* expr, const AssignBuild& build) {
  if (build.sim == nullptr) return nullptr;
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = expr->kind == ExprKind::kRealLiteral   ? vpiRealConst
                         : expr->kind == ExprKind::kTimeLiteral ? vpiTimeConst
                         : expr->kind == ExprKind::kStringLiteral
                             ? vpiStringConst
                             : vpiIntConst;
  Arena& arena = build.sim->GetArena();
  auto* storage = arena.Create<Variable>();
  storage->value = EvalExpr(expr, *build.sim, arena);
  constant->var = storage;
  constant->size = static_cast<int>(storage->value.width);
  return constant;
}

std::optional<int64_t> GenvarValue(std::string_view name,
                                   const AssignBuild& build) {
  const auto kGenvar = std::ranges::find_if(
      build.names.genvars,
      [name](const auto& genvar) { return genvar.first == name; });
  if (kGenvar == build.names.genvars.end()) return std::nullopt;
  return kGenvar->second;
}

VpiObject* GenvarParameter(std::string_view name, const AssignBuild& build) {
  const std::optional<int64_t> kValue = GenvarValue(name, build);
  if (!kValue) return nullptr;
  Arena& arena = build.sim->GetArena();
  auto* storage = arena.Create<Variable>();
  storage->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(*kValue));
  storage->value.is_signed = true;
  VpiObject* param = build.alloc();
  param->type = vpiParameter;
  param->name = build.keep(std::string(name));
  param->local_param = true;
  param->var = storage;
  param->size = 32;
  return param;
}

}  // namespace

std::optional<int64_t> ElaborationConstant(const Expr* expr,
                                           const AssignBuild& build) {
  std::vector<std::string_view> names;
  CollectReads(expr, names);
  ScopeMap scope;
  for (std::string_view name : names) {
    const VpiObject* named = Resolve(build.names, name);
    const std::optional<int64_t> kValue = named != nullptr
                                              ? VpiElaborationValue(named)
                                              : GenvarValue(name, build);
    if (!kValue) return std::nullopt;
    scope[name] = *kValue;
  }
  return ConstEvalInt(expr, scope);
}

namespace {

std::vector<const Expr*> Operands(const Expr* first,
                                  const std::vector<Expr*>& rest) {
  std::vector<const Expr*> operands{first};
  operands.insert(operands.end(), rest.begin(), rest.end());
  return operands;
}

int ElementSize(const VpiObject& array) {
  for (const VpiObject* child : array.children) {
    if (!child->array_member) continue;
    return VpiIsArrayVarType(child->type) ? ElementSize(*child) : child->size;
  }
  return 0;
}

void NameSelect(VpiObject* select, const VpiObject& base, const Expr* index,
                const AssignBuild& build) {
  const std::string kSuffix = "[" + VpiExprDecompile(index) + "]";
  select->name = build.keep(std::string(base.name) + kSuffix);
  select->full_name =
      (base.full_name.empty() ? std::string(base.name) : base.full_name) +
      kSuffix;
}

VpiObject* VarSelectObject(VpiObject* base, const Expr* index,
                           const AssignBuild& build) {
  VpiObject* select = build.alloc();
  select->type = vpiVarSelect;
  select->parent = base;
  NameSelect(select, *base, index, build);
  select->index_expr = ExpressionObject(index, build);
  if (select->index_expr != nullptr) {
    select->children.push_back(select->index_expr);
  }
  const VpiObject* array = base;
  std::size_t depth = 1;
  for (; array->type == vpiVarSelect; array = array->parent) ++depth;
  if (base->type == vpiVarSelect) {
    select->children.insert(select->children.end(), base->children.begin(),
                            base->children.end());
  } else {
    base->children.push_back(select);
  }
  if (depth == array->array_dim_indices.size()) {
    select->size = ElementSize(*array);
  }
  return select;
}

VpiObject* SelectThroughVarSelect(VpiObject* outer, const Expr* index,
                                  const AssignBuild& build) {
  const VpiObject* array = outer;
  std::size_t depth = 0;
  for (; array->type == vpiVarSelect; array = array->parent) ++depth;
  if (depth < array->array_dim_indices.size()) {
    return VarSelectObject(outer, index, build);
  }
  VpiObject* select = build.alloc();
  select->type = vpiBitSelect;
  select->parent = outer;
  select->index_expr = ExpressionObject(index, build);
  select->size = 1;
  for (const VpiObject* element : array->children) {
    if (!element->array_member) continue;
    if (element->var != nullptr && element->var->packed_elem_width != 0) {
      select->size = static_cast<int>(element->var->packed_elem_width);
    }
    break;
  }
  return select;
}

int SliceKind(const VpiObject& root) {
  if (root.net != nullptr || VpiIsNetsType(root.type)) return root.type;
  return root.var != nullptr && !root.var->is_4state ? vpiBitVar : kVpiReg;
}

VpiObject* SliceObject(VpiObject* root, std::vector<PackedRange> rest,
                       int64_t width, const AssignBuild& build) {
  VpiObject* slice = build.alloc();
  slice->type = rest.empty()
                    ? (VpiIsNetsType(root->type) ? vpiNetBit : vpiRegBit)
                    : SliceKind(*root);
  slice->parent = root;
  slice->var = root->var;
  slice->net = root->net;
  slice->size = static_cast<int>(width);
  slice->packed_dims = std::move(rest);
  return slice;
}

VpiObject* PackedSelectObject(VpiObject* base, const Expr* index,
                              const AssignBuild& build) {
  if (base->select_dim || index == nullptr) return nullptr;
  VpiObject* root = base->bit_offset >= 0 ? base->parent : base;
  const int64_t kBaseOffset = base->bit_offset >= 0 ? base->bit_offset : 0;
  const PackedRange kDim = base->packed_dims.front();
  std::vector<PackedRange> rest(base->packed_dims.begin() + 1,
                                base->packed_dims.end());
  const int64_t kWidth = PackedDimsWidth(rest);
  const std::optional<int64_t> kConstant = ElaborationConstant(index, build);
  if (!kConstant) {
    VpiObject* select = SliceObject(root, std::move(rest), kWidth, build);
    select->select_dim = kDim;
    select->select_base_offset = static_cast<int>(kBaseOffset);
    select->index_expr = ExpressionObject(index, build);
    if (select->type == vpiRegBit && select->index_expr != nullptr) {
      select->children.push_back(select->index_expr);
    }
    return select;
  }
  const int64_t kIndex = *kConstant;
  if (!kDim.Contains(kIndex)) return nullptr;
  const int64_t kOffset = kBaseOffset + (kDim.OffsetOf(kIndex) * kWidth);
  if (rest.empty()) return VpiBitAtOffset(*root, kOffset);
  VpiObject* slice = SliceObject(root, std::move(rest), kWidth, build);
  slice->bit_offset = static_cast<int>(kOffset);
  const std::string kSuffix = "[" + std::to_string(kIndex) + "]";
  slice->name = build.keep(std::string(base->name) + kSuffix);
  slice->full_name = base->full_name + kSuffix;
  return slice;
}

VpiObject* BitSelectObject(const Expr* expr, const AssignBuild& build) {
  VpiObject* base = ExpressionObject(expr->base, build);
  if (base == nullptr) return nullptr;
  if (base->type == vpiIntegerVar || base->type == vpiTimeVar ||
      base->type == vpiParameter || base->type == vpiSpecParam) {
    VpiObject* select = build.alloc();
    select->type = vpiBitSelect;
    select->parent = base;
    select->size = 1;
    select->index_expr = ExpressionObject(expr->index, build);
    NameSelect(select, *base, expr->index, build);
    return select;
  }
  if (!base->packed_dims.empty() || base->select_dim) {
    return PackedSelectObject(base, expr->index, build);
  }
  if (expr->index == nullptr) return nullptr;
  if (base->type == vpiVarSelect) {
    return SelectThroughVarSelect(base, expr->index, build);
  }
  const std::optional<int64_t> kConstant =
      ElaborationConstant(expr->index, build);
  if (!kConstant) {
    return base->type == vpiArrayVar ? VarSelectObject(base, expr->index, build)
                                     : nullptr;
  }
  const auto kIndex = static_cast<int>(*kConstant);
  for (VpiObject* child : base->children) {
    if (VpiIndexSelects(*base, *child, kIndex)) return child;
  }
  return nullptr;
}

VpiObject* SelectObject(const Expr* expr, const AssignBuild& build) {
  if (expr->index_end == nullptr) return BitSelectObject(expr, build);
  VpiObject* select = build.alloc();
  select->parent = ExpressionObject(expr->base, build);
  VpiObject* first = ExpressionObject(expr->index, build);
  VpiObject* second = ExpressionObject(expr->index_end, build);
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    select->type = vpiIndexedPartSelect;
    select->indexed_part_select_type =
        expr->is_part_select_plus ? vpiPosIndexed : vpiNegIndexed;
    select->base_expr = first;
    select->width_expr = second;
  } else {
    select->type = vpiPartSelect;
    select->left_range = first;
    select->right_range = second;
  }
  return select;
}

VpiObject* CallObject(const Expr* expr, const AssignBuild& build) {
  VpiObject* call = build.alloc();
  call->type =
      expr->kind == ExprKind::kSystemCall ? vpiSysFuncCall : vpiFuncCall;
  if (build.shape_call && build.shape_call(*expr, call)) return call;
  if (call->type == vpiFuncCall && expr->lhs != nullptr && build.callees) {
    call->tf_decl = build.callees(*expr->lhs);
  }
  for (const Expr* arg : expr->args) {
    VpiObject* obj = ExpressionObject(arg, build);
    if (obj != nullptr) call->arguments.push_back(obj);
  }
  return call;
}

VpiObject* ListOperationObject(const Expr* expr, const AssignBuild& build) {
  switch (expr->kind) {
    case ExprKind::kReplicate:
      return OperationObject(vpiMultiConcatOp,
                             Operands(expr->repeat_count, expr->elements),
                             build);
    case ExprKind::kInside:
      if (expr->dist_items != nullptr) {
        return VpiMakeDistribution(ExpressionObject(expr->lhs, build),
                                   *expr->dist_items, build.alloc,
                                   [&build](const Expr* item) {
                                     return ExpressionObject(item, build);
                                   });
      }
      return OperationObject(vpiInsideOp, Operands(expr->lhs, expr->elements),
                             build);
    default:
      return OperationObject(
          expr->op == TokenKind::kLtLt ? vpiStreamRLOp : vpiStreamLROp,
          std::vector<const Expr*>(expr->elements.begin(),
                                   expr->elements.end()),
          build);
  }
}

VpiObject* PatternObject(const Expr* expr, const AssignBuild& build) {
  if (!expr->pattern_keys.empty()) return nullptr;
  const Expr* first = expr->elements.front();
  if (expr->elements.size() == 1 && first->is_pattern_replication) {
    return OperationObject(vpiMultiAssignmentPatternOp,
                           Operands(first->repeat_count, first->elements),
                           build);
  }
  return OperationObject(
      vpiAssignmentPatternOp,
      std::vector<const Expr*>(expr->elements.begin(), expr->elements.end()),
      build);
}

bool KeyNames(Expr* key, const VpiObject* slot, const AssignBuild& build) {
  if (!slot->array_member) return key->text == slot->name;
  return VpiEvaluatedRange(key, key, *build.sim).left == slot->index;
}

const Expr* KeyedValue(const Expr* pattern, const VpiObject* slot,
                       const AssignBuild& build) {
  const Expr* typed = nullptr;
  const Expr* fallback = nullptr;
  for (std::size_t i = 0; i < pattern->pattern_keys.size(); ++i) {
    Expr* key = pattern->pattern_keys[i];
    const Expr* value = pattern->elements[i];
    const DataTypeKind kType = PatternKeyKeywordKind(key->text);
    if (key->text == "default") {
      fallback = value;
    } else if (kType != DataTypeKind::kImplicit) {
      if (VpiDataTypeVariableKind(kType) == slot->type) typed = value;
    } else if (KeyNames(key, slot, build)) {
      return value;
    }
  }
  return typed != nullptr ? typed : fallback;
}

const VpiObject* PatternLayout(const VpiObject* target) {
  if (target->type != vpiTypespecMember) return target;
  for (const VpiObject* child : target->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return target;
}

bool IsPatternSlot(const VpiObject& child, const VpiObject& layout) {
  return child.member_of == &layout || child.array_member ||
         child.type == vpiTypespecMember;
}

VpiObject* KeyedPatternObject(const Expr* pattern, const VpiObject* target,
                              const AssignBuild& build) {
  const VpiObject* laid_out = PatternLayout(target);
  VpiObject* op = nullptr;
  for (const VpiObject* child : laid_out->children) {
    if (!IsPatternSlot(*child, *laid_out)) continue;
    if (op == nullptr) {
      op = build.alloc();
      op->type = vpiOperation;
      op->op_type = vpiAssignmentPatternOp;
    }
    const Expr* value = KeyedValue(pattern, child, build);
    VpiObject* placed = value != nullptr
                            ? AssignedExpressionObject(value, child, build)
                            : nullptr;
    if (placed != nullptr) op->children.push_back(placed);
  }
  return op;
}

}  // namespace

VpiObject* AssignedExpressionObject(const Expr* expr, const VpiObject* target,
                                    const AssignBuild& build) {
  VpiObject* made = ExpressionObject(expr, build);
  if (made != nullptr || expr->kind != ExprKind::kAssignmentPattern) {
    return made;
  }
  return KeyedPatternObject(expr, target, build);
}

namespace {

bool DottedName(const Expr* expr, std::string& out) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return expr->scope_prefix.empty();
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier || !DottedName(expr->lhs, out)) {
    return false;
  }
  out += ".";
  out += expr->rhs->text;
  return true;
}

VpiObject* HierarchicalObject(const Expr* expr, const AssignBuild& build) {
  std::string dotted;
  if (!DottedName(expr, dotted)) return nullptr;
  const std::string_view kFirst =
      std::string_view(dotted).substr(0, dotted.find('.'));
  if (VpiObject* holder = Resolve(build.names, kFirst)) {
    if (VpiObject* block = VpiVirtualInterfaceClockingBlock(
            holder, dotted, build.alloc, build.keep)) {
      return block;
    }
    if (VpiIsDynamicPrefixHolderType(holder->type)) {
      return VpiPrefixedReference(holder, dotted, build.alloc, build.keep);
    }
    VpiObject* member =
        FindObjectForFlatName(VpiObjectMap{{kFirst, holder}}, dotted);
    if (member != nullptr) return member;
  }
  if (VpiObject* block = VpiClockingBlockAround(InnermostScope(build.names),
                                                build.names.objects,
                                                build.names.prefix, kFirst)) {
    return VpiPrefixedReference(block, dotted, build.alloc, build.keep);
  }
  VpiObject* below = FindObjectForFlatName(
      build.names.objects, VpiFlatName(build.names.prefix, dotted));
  return below != nullptr ? below
                          : FindObjectForFlatName(build.names.objects, dotted);
}

VpiObject* CastObject(const Expr* expr, const AssignBuild& build) {
  return VpiTypedCast(OperationObject(vpiCastOp, {expr->lhs}, build), *expr,
                      build);
}

VpiObject* UnaryObject(const Expr* expr, const AssignBuild& build) {
  const int kStep =
      VpiIncDecOpType(expr->op, expr->kind == ExprKind::kPostfixUnary);
  return OperationObject(kStep != 0 ? kStep : VpiUnaryOpType(expr->op),
                         {expr->lhs}, build);
}

VpiObject* LetDeclIn(const VpiObject* scope, std::string_view name) {
  if (scope == nullptr) return nullptr;
  for (VpiObject* child : scope->children) {
    if (child->type == vpiLetDecl && child->name == name) return child;
  }
  return nullptr;
}

VpiObject* LetDeclNamed(const AssignNames& names, std::string_view name) {
  for (const VpiObject* at = VpiScopeOrInstance(
           names.scope != nullptr ? names.scope : names.instance, names.objects,
           names.prefix);
       at != nullptr; at = VpiIsInstanceType(at->type) ? nullptr : at->parent) {
    if (VpiObject* let = LetDeclIn(at, name)) return let;
  }
  for (const RtlirImport& entry : names.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    VpiObject* let = LetDeclIn(
        FindObjectForFlatName(names.objects, entry.package_name), name);
    if (let != nullptr) return let;
  }
  return LetDeclIn(
      FindObjectForFlatName(names.objects, UnitScopes::ScopeName(names.unit)),
      name);
}

VpiObject* CalledLetDecl(const Expr& call, const AssignNames& names) {
  if (!call.callee.empty()) return LetDeclNamed(names, call.callee);
  if (call.lhs == nullptr || !VpiIsPackageScopedName(*call.lhs)) {
    return nullptr;
  }
  return LetDeclIn(FindObjectForFlatName(names.objects, call.lhs->lhs->text),
                   call.lhs->rhs->text);
}

VpiObject* LetExprObject(const Expr* expr, VpiObject* decl,
                         const AssignBuild& build) {
  if (decl == nullptr) return nullptr;
  VpiObject* let = build.alloc();
  let->type = vpiLetExpr;
  let->name = decl->name;
  let->children.push_back(decl);
  for (const Expr* arg : expr->args) {
    VpiObject* actual = ExpressionObject(arg, build);
    if (actual == nullptr) {
      actual = build.alloc();
      VpiMakeEmptyArgument(actual);
    }
    let->children.push_back(actual);
  }
  return let;
}

VpiObject* NamedObject(const Expr* expr, const AssignBuild& build) {
  VpiObject* named = Resolve(build.names, expr->text);
  if (named != nullptr) return named;
  VpiObject* let =
      LetExprObject(expr, LetDeclNamed(build.names, expr->text), build);
  if (let != nullptr) return let;
  VpiObject* genvar = GenvarParameter(expr->text, build);
  return genvar != nullptr
             ? genvar
             : VpiClockingBlockAround(InnermostScope(build.names),
                                      build.names.objects, build.names.prefix,
                                      expr->text);
}

VpiObject* ModelledExpression(const Expr* expr, const AssignBuild& build) {
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return NamedObject(expr, build);
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
      return ConstantObject(expr, build);
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      return UnaryObject(expr, build);
    case ExprKind::kBinary:
      return OperationObject(VpiBinaryOpType(expr->op), {expr->lhs, expr->rhs},
                             build);
    case ExprKind::kTernary:
      return OperationObject(
          vpiConditionOp, {expr->condition, expr->true_expr, expr->false_expr},
          build);
    case ExprKind::kConcatenation:
      return OperationObject(vpiConcatOp,
                             std::vector<const Expr*>(expr->elements.begin(),
                                                      expr->elements.end()),
                             build);
    case ExprKind::kReplicate:
    case ExprKind::kInside:
    case ExprKind::kStreamingConcat:
      return ListOperationObject(expr, build);
    case ExprKind::kAssignmentPattern:
      return PatternObject(expr, build);
    case ExprKind::kCast:
      return CastObject(expr, build);
    case ExprKind::kMinTypMax:
      return OperationObject(vpiMinTypMaxOp,
                             {expr->lhs, expr->condition, expr->rhs}, build);
    case ExprKind::kSelect:
      return SelectObject(expr, build);
    case ExprKind::kCall:
      if (VpiObject* let =
              LetExprObject(expr, CalledLetDecl(*expr, build.names), build)) {
        return let;
      }
      return CallObject(expr, build);
    case ExprKind::kSystemCall:
      return CallObject(expr, build);
    default:
      return HierarchicalObject(expr, build);
  }
}

}  // namespace

VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build) {
  if (expr == nullptr) return nullptr;
  VpiObject* obj = ModelledExpression(expr, build);
  VpiSizeExpression(obj, *expr, build);
  if (obj != nullptr &&
      (obj->type == vpiOperation || obj->type == vpiFuncCall ||
       obj->type == vpiMethodFuncCall || obj->type == vpiSysFuncCall ||
       obj->type == vpiBitSelect || obj->type == vpiPartSelect ||
       obj->type == vpiIndexedPartSelect)) {
    obj->expr_scope = std::make_shared<const VpiExprScope>(
        VpiExprScope{expr, VpiFlatName(build.names.prefix, ""),
                     std::vector<std::string>(build.names.gen.begin(),
                                              build.names.gen.end())});
  }
  if (obj != nullptr && expr->kind == ExprKind::kSelect) {
    VpiNoteSelectIndexes(obj, expr, build.alloc);
  }
  if (obj != nullptr && expr->kind != ExprKind::kIdentifier &&
      expr->kind != ExprKind::kMemberAccess && VpiIsExprType(obj->type)) {
    obj->decompile = VpiExprDecompile(expr);
  }
  if (obj != nullptr && obj->type == vpiOperation && build.sim != nullptr) {
    VpiAttachAttributes(obj, VpiNodeAttributes(build.attrs, expr), false,
                        *build.sim,
                        {build.alloc, build.keep, build.sim->GetArena()});
  }
  return obj;
}

VpiObject* VpiInstanceExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const std::string& prefix, SimContext& ctx,
                                 const VpiAttachBuild& build) {
  static const GenBlockPrefixes kNoGenBlocks;
  return VpiGenBlockExpression(expr, {objects, prefix, kNoGenBlocks}, ctx,
                               build);
}

VpiObject* VpiGenBlockExpression(const Expr* expr, const VpiExprNames& names,
                                 SimContext& ctx, const VpiAttachBuild& build) {
  std::function<bool(const Expr&, VpiObject*)> defer = nullptr;
  if (names.stand != nullptr && build.deferred_calls != nullptr) {
    defer = [&names, &build](const Expr& call, VpiObject* made) {
      build.deferred_calls->push_back(
          {&call, made, *names.stand, names.prefix, names.gen_prefixes});
      return true;
    };
  }
  return ExpressionObject(
      expr,
      AssignBuild{
          build.alloc,
          &ctx,
          AssignNames{names.objects, names.prefix, names.gen_prefixes,
                      names.scope, AssignNames::NoGenvars(), names.instance,
                      names.mod != nullptr ? names.mod->imports
                                           : AssignNames::NoImports(),
                      names.mod != nullptr ? names.mod->unit_index : -1,
                      build.unit_typespecs},
          {},
          build.keep,
          defer,
          names.attrs});
}

namespace {

AssignBuild CallSiteBuild(const VpiObjectMap& objects, const VpiCallSite& site,
                          SimContext& ctx, const VpiAttachBuild& build) {
  static const GenBlockPrefixes kNoGenBlocks;
  const GenBlockPrefixes& gen =
      site.gen_prefixes != nullptr ? *site.gen_prefixes : kNoGenBlocks;
  return AssignBuild{
      build.alloc,
      &ctx,
      AssignNames{objects, site.prefix, gen,
                  site.formals != nullptr ? site.formals : site.scope,
                  AssignNames::NoGenvars(), nullptr, site.mod.imports,
                  site.mod.unit_index, build.unit_typespecs},
      VpiCalleesAt(site),
      build.keep,
      site.shape_call,
      &site.mod.node_attrs};
}

}  // namespace

VpiObject* VpiCallSiteExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const VpiCallSite& site, SimContext& ctx,
                                 const VpiAttachBuild& build) {
  return ExpressionObject(expr, CallSiteBuild(objects, site, ctx, build));
}

VpiObject* VpiCallSiteAssignedExpression(const VpiAssignedSide& side,
                                         const VpiObjectMap& objects,
                                         const VpiCallSite& site,
                                         SimContext& ctx,
                                         const VpiAttachBuild& build) {
  return AssignedExpressionObject(side.expr, side.target,
                                  CallSiteBuild(objects, site, ctx, build));
}

}  // namespace delta
