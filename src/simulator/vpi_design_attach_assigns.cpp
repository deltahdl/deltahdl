#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
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

// §23.9, §12.7.3 and §16.8: the variable, named event or formal's ref obj
// (VpiFormalNames) `scope` declares under `name`, or the index variable of the
// foreach loop `scope` is; null where neither is.
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

// §23.9: the variable or named event a block around `scope`, or `scope`
// itself, declares under `name`, the innermost first, or the index variable
// a foreach loop around it declares (§12.7.3); null where none does, the
// instance's own declarations being looked up after. A block's declarations
// hang beneath it (§37.12), and the walk stops at the instance. `gen` picks
// the generate block instances around `scope` (§27.4) rather than the blocks.
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

// §26.3 with §37.12 detail 4: the item of a package an import of the module
// makes visible under `name`, by its name or with a wildcard, recorded among
// the objects imported into the instance the expression stands in, which it
// references; null where no import makes one visible. An expression of a
// module, which alone carries imports, stands in a scope of the module's
// instance or in the instance itself.
VpiHandle ImportedObject(const AssignNames& names, std::string_view name) {
  for (const RtlirImport& entry : names.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    VpiHandle item = FindObjectForFlatName(
        names.objects, VpiFlatName(std::string(entry.package_name), name));
    if (item == nullptr) continue;
    const VpiObject* at = names.scope;
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
  // §27.4: a generate block's declarations, through the flattened key the run
  // stores each under, whose object AttachGenBlockStorage makes the block's.
  for (auto it = names.gen.rbegin(); it != names.gen.rend(); ++it) {
    VpiHandle obj = FindObjectForFlatName(
        names.objects,
        VpiFlatName(names.prefix, std::string(*it) + std::string(name)));
    if (obj != nullptr) return obj;
  }
  // What a generate block instance holds under no such key, a loop's genvar.
  declared = BlockDeclaration(names.scope, name, true);
  if (declared != nullptr) return declared;
  VpiHandle own =
      FindObjectForFlatName(names.objects, VpiFlatName(names.prefix, name));
  return own != nullptr ? own : ImportedObject(names, name);
}

namespace {

// §37.59: an operation with its operands in the order the source wrote them.
// An operator the tables above do not hold is not modelled.
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

// §37.58: a literal as a constant carrying the value it evaluates to, a time
// literal (§5.8) one of type vpiTimeConst.
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

// §27.4 with §37.85 detail 3: a loop generate block's genvar named in a
// continuous assignment the block holds, as the local parameter §27.4 declares
// in the block instance under the genvar's name, holding the value it holds
// there; no name the run keys resolves to it. Null where `name` is no such
// genvar.
VpiObject* GenvarParameter(std::string_view name, const AssignBuild& build) {
  const auto kGenvar = std::ranges::find_if(
      build.names.genvars,
      [name](const auto& genvar) { return genvar.first == name; });
  if (kGenvar == build.names.genvars.end()) return nullptr;
  Arena& arena = build.sim->GetArena();
  auto* storage = arena.Create<Variable>();
  storage->value =
      MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(kGenvar->second));
  storage->value.is_signed = true;
  VpiObject* param = build.alloc();
  param->type = vpiParameter;
  param->name = build.keep(std::string(name));
  param->local_param = true;
  param->var = storage;
  param->size = 32;
  return param;
}

// `first` followed by `rest`, as the operands of an operation.
std::vector<const Expr*> Operands(const Expr* first,
                                  const std::vector<Expr*>& rest) {
  std::vector<const Expr*> operands{first};
  operands.insert(operands.end(), rest.begin(), rest.end());
  return operands;
}

// The width in bits of an element of the array var `array`, read off the
// first element it holds, through its subarrays; 0 where it holds none.
int ElementSize(const VpiObject& array) {
  for (const VpiObject* child : array.children) {
    if (!child->array_member) continue;
    return VpiIsArrayVarType(child->type) ? ElementSize(*child) : child->size;
  }
  return 0;
}

// §37.58 and §37.19: name the select `select` after its parent `base` and the
// index `index` it was written with, `a[i]`, and full-name it through `base`.
void NameSelect(VpiObject* select, const VpiObject& base, const Expr* index,
                const AssignBuild& build) {
  const std::string kSuffix = "[" + VpiExprDecompile(index) + "]";
  select->name = build.keep(std::string(base.name) + kSuffix);
  select->full_name =
      (base.full_name.empty() ? std::string(base.name) : base.full_name) +
      kSuffix;
}

// §37.19: a select of an element of the array var `base` whose index is not a
// constant: a var select reaching the array through vpiParent and the
// expression the source wrote through vpiIndex. Which element it stands for is
// not fixed before the run, so it holds none, and its value is the one of the
// element its index selects when the value is read or written (vpi_value.cpp).
// §37.17 with §37.19 (printed pages 1025 and 1030): an array var reaches the
// var selects of it, so a select of the array itself, rather than one through
// another var select, is among the array's children. §37.17 detail 5: a
// select through another reaches the indices of both, its own first and then
// outward, and detail 10: one that selects an element is as many bits wide as
// the element is.
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

// §37.19: a select through the var select `outer`: a var select of its own
// where `outer` selects a subarray -- the chain of var selects down from the
// array var indexes fewer of its unpacked dimensions than it has -- and where
// `outer` selects an element, a bit select of it (§37.58), whose vpiParent is
// `outer`, as Table 37-1 has a part select into it reach (§37.59 detail 10).
// It is one element of the element's outermost packed dimension wide.
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
    // §7.4.1: the run's storage for the element keeps the width an index of
    // its outermost packed dimension selects; the model's objects do not.
    if (element->var != nullptr && element->var->packed_elem_width != 0) {
      select->size = static_cast<int>(element->var->packed_elem_width);
    }
    break;
  }
  return select;
}

// §37.16 detail 31, §37.17 detail 26: the kind a select out of `root` that
// leaves packed dimensions unindexed is, a vector of the kind `root` is: a
// logic var or a bit var as the variable is four- or two-state, or the net
// kind of a net.
int SliceKind(const VpiObject& root) {
  if (root.net != nullptr || VpiIsNetsType(root.type)) return root.type;
  return root.var != nullptr && !root.var->is_4state ? vpiBitVar : kVpiReg;
}

// A select the run builds an object of its own for out of the vector `root`,
// `width` bits wide, the packed dimensions it leaves unindexed `rest`: a bit
// of `root` where it leaves none, and otherwise a vector of `root`'s kind.
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

// §37.16 detail 31, §37.17 detail 26: a select of `base`, a vector or a slice
// of one, by `index` along its outermost packed dimension. Where the select
// leaves dimensions unindexed it is a vector of `base`'s root's kind, sized
// by those dimensions, and where it indexes the last it is one of the root's
// bits; either way its vpiParent is the root, the largest packed array
// containing it. A constant index fixes the bits now and names the select by
// it; any other fixes them when its value is read, as a varying bit's does.
// Null for an index out of range and for a select of a varying slice.
VpiObject* PackedSelectObject(VpiObject* base, const Expr* index,
                              const AssignBuild& build) {
  if (base->select_dim || index == nullptr) return nullptr;
  VpiObject* root = base->bit_offset >= 0 ? base->parent : base;
  const int64_t kBaseOffset = base->bit_offset >= 0 ? base->bit_offset : 0;
  const PackedRange kDim = base->packed_dims.front();
  std::vector<PackedRange> rest(base->packed_dims.begin() + 1,
                                base->packed_dims.end());
  const int64_t kWidth = PackedDimsWidth(rest);
  if (index->kind != ExprKind::kIntegerLiteral) {
    VpiObject* select = SliceObject(root, std::move(rest), kWidth, build);
    select->select_dim = kDim;
    select->select_base_offset = static_cast<int>(kBaseOffset);
    select->index_expr = ExpressionObject(index, build);
    if (select->type == vpiRegBit && select->index_expr != nullptr) {
      select->children.push_back(select->index_expr);
    }
    return select;
  }
  const auto kIndex = static_cast<int64_t>(index->int_val);
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

// §37.58: a select of one bit. Of an integer var, a time var or a parameter it
// is a bit select reaching the object through vpiParent and its index through
// vpiIndex; of a vector net or a logic or bit variable it is that object's own
// bit (§37.16, §37.17), the one a constant index names, or one standing for
// whichever bit a varying index selects. Of an unpacked array it is the
// element or subarray a constant index names (§37.17 details 2 and 18), the
// child vpi_handle_by_index reaches (§38.19), and of an array var a varying
// index makes it a var select (§37.19).
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
  // A varying bit of a vector was made above (PackedSelectObject), so what a
  // varying index selects from here is an element, a var select of an array
  // var's (§37.19). An array net's has no object.
  if (expr->index->kind != ExprKind::kIntegerLiteral) {
    return base->type == vpiArrayVar ? VarSelectObject(base, expr->index, build)
                                     : nullptr;
  }
  const auto kIndex = static_cast<int>(expr->index->int_val);
  for (VpiObject* child : base->children) {
    if (VpiIndexSelects(*base, *child, kIndex)) return child;
  }
  return nullptr;
}

// §37.59: a part select or an indexed part select, which reaches the object it
// selects into through vpiParent and the bounds, or the base and width, it
// was written with.
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

// §37.42 with §37.59: a call of a function or system function, carrying its
// arguments in order, which vpiArgument reaches, and a function call reaching
// the function it calls.
VpiObject* CallObject(const Expr* expr, const AssignBuild& build) {
  VpiObject* call = build.alloc();
  call->type =
      expr->kind == ExprKind::kSystemCall ? vpiSysFuncCall : vpiFuncCall;
  // A call is the tf call its statement would be: a method func call of a
  // method, named, with its prefix (details 2 and 11), and a system function
  // call named, reaching the systf of its registration, wherever the
  // expression stands, a procedure or a continuous assignment.
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

// §37.59: the operations whose operands the source writes as a list -- a
// replication, its multiplier first (detail 1); an inside expression, its
// value first; and a streaming concatenation, whose direction is its operator.
VpiObject* ListOperationObject(const Expr* expr, const AssignBuild& build) {
  switch (expr->kind) {
    case ExprKind::kReplicate:
      return OperationObject(vpiMultiConcatOp,
                             Operands(expr->repeat_count, expr->elements),
                             build);
    case ExprKind::kInside:
      // §37.34 with §16.14.2: an assertion's dist is a distribution, though
      // the run evaluates it as the inside expression it was read into.
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

// §37.59 details 6 and 7: a positional assignment pattern is an assignment
// pattern operation over its expressions, and a replicated one a multi
// assignment pattern operation over its multiplier and its expressions. The
// parser holds the replication as the pattern's one element, marked
// is_pattern_replication, which tells it from a replicate written as the
// pattern's one expression. A keyed pattern, whose positional order its
// target's type decides, is not modelled.
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

// §10.9.1 and §10.9.2: whether the key `key` of a pattern names the position
// `slot` takes: a structure member by its name, an array element by the
// index the key evaluates to.
bool KeyNames(Expr* key, const VpiObject* slot, const AssignBuild& build) {
  if (!slot->array_member) return key->text == slot->name;
  return VpiEvaluatedRange(key, key, *build.sim).left == slot->index;
}

// §10.9.2: the expression the keys of `pattern` put in the place of `slot`:
// the one its own key names, else the last a type key naming its type gives,
// else the default's; null where none does.
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

// What a keyed pattern assigned to `target` is laid out by: `target` itself,
// or a typespec member's typespec.
const VpiObject* PatternLayout(const VpiObject* target) {
  if (target->type != vpiTypespecMember) return target;
  for (const VpiObject* child : target->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return target;
}

// Whether `child` of `layout` takes a place in a pattern laid out by it: a
// member, an element, or a typespec member.
bool IsPatternSlot(const VpiObject& child, const VpiObject& layout) {
  return child.member_of == &layout || child.array_member ||
         child.type == vpiTypespecMember;
}

// §37.59 detail 6: the keyed assignment pattern `pattern` assigned to
// `target` as an assignment pattern operation over its expressions in the
// positional order of `target`'s members or elements, left first (§37.17
// details 3 and 18), or of a struct typespec's typespec members (§37.26),
// each in the place its keys give it and built against that place, so a
// pattern nested in it is laid out by the member or element it fills. A
// typespec member is laid out by its typespec's members. Null where `target`
// has none.
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

// The expression object `expr` stands for, assigned to `target`, whose
// members or elements order a keyed pattern's expressions (§37.59 detail 6).
VpiObject* AssignedExpressionObject(const Expr* expr, const VpiObject* target,
                                    const AssignBuild& build) {
  VpiObject* made = ExpressionObject(expr, build);
  if (made != nullptr || expr->kind != ExprKind::kAssignmentPattern) {
    return made;
  }
  return KeyedPatternObject(expr, target, build);
}

namespace {

// §23.6: `expr` as the dotted name it writes, `u1.clk`, onto `out`, a
// package's name before `::` (§26.3) joined as a scope like any other,
// `p::obj` as `p.obj`, which is the flat name the package's objects are found
// under; false where it is not identifiers joined so alone.
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

// §23.6: the net or variable a hierarchical name reaches, whose first name
// is no declaration the scope sees, an instance's: below the instance writing
// it first, and then from the top of the design. A first name the scope does
// declare is a structure variable, and the name selects its members (§37.17
// details 3 and 26), each a child of the one before it, as a flat name's
// components are. Null where it names nothing.
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
  if (VpiObject* block = VpiClockingBlockAround(
          build.names.scope, build.names.objects, build.names.prefix, kFirst)) {
    return VpiPrefixedReference(block, dotted, build.alloc, build.keep);
  }
  VpiObject* below = FindObjectForFlatName(
      build.names.objects, VpiFlatName(build.names.prefix, dotted));
  return below != nullptr ? below
                          : FindObjectForFlatName(build.names.objects, dotted);
}

// §37.59 details 3 and 5: a cast, an operation related to the typespec of the
// type it casts its operand to. Where the cast names no type, the expression
// it was written with is a size cast's width (§6.24.1), whose value it has
// where the source wrote it.
VpiObject* CastObject(const Expr* expr, const AssignBuild& build) {
  const VpiObject* width = expr->text.empty() && expr->rhs != nullptr
                               ? ExpressionObject(expr->rhs, build)
                               : nullptr;
  return VpiTypedCast(
      OperationObject(vpiCastOp, {expr->lhs}, build), *expr,
      VpiScopeOrInstance(build.names.scope != nullptr ? build.names.scope
                                                      : build.names.instance,
                         build.names.objects, build.names.prefix),
      width, build.alloc);
}

// §37.59 with §11.4.2: a unary operation over the one operand it is written
// with, an increment or decrement within an expression among them, whose
// operand is the variable it steps.
VpiObject* UnaryObject(const Expr* expr, const AssignBuild& build) {
  const int kStep =
      VpiIncDecOpType(expr->op, expr->kind == ExprKind::kPostfixUnary);
  return OperationObject(kStep != 0 ? kStep : VpiUnaryOpType(expr->op),
                         {expr->lhs}, build);
}

// §11.12 with §37.57: the let decl `scope` declares under `name`; null where
// it declares none or there is no scope.
VpiObject* LetDeclIn(const VpiObject* scope, std::string_view name) {
  if (scope == nullptr) return nullptr;
  for (VpiObject* child : scope->children) {
    if (child->type == vpiLetDecl && child->name == name) return child;
  }
  return nullptr;
}

// §11.12 with §37.57: the let decl `name` names where `names` places it: one a
// scope around the expression, or its instance, declares, the innermost
// first; else one a package declares that an import of the module makes
// visible, by its name or with a wildcard (§26.3); else one the compilation
// unit the module belongs to declares (§3.12.1). Null where none is.
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

// §11.12 with §26.3: the let decl the call `call` names: its callee's name,
// where it is written plain, or the let of the package a package path names,
// `pk::f`; null where it names no let, a call written with no callee of its
// own, a constructor's among them, naming none.
VpiObject* CalledLetDecl(const Expr& call, const AssignNames& names) {
  if (!call.callee.empty()) return LetDeclNamed(names, call.callee);
  if (call.lhs == nullptr || !VpiIsPackageScopedName(*call.lhs)) {
    return nullptr;
  }
  return LetDeclIn(FindObjectForFlatName(names.objects, call.lhs->lhs->text),
                   call.lhs->rhs->text);
}

// §11.12 with §37.57: the let expr `expr` stands for where it calls or is
// the let `decl` declares: reaching that let decl and an argument per actual
// written, one written as nothing, or as an expression not modelled, an empty
// argument (§37.42 detail 8), which detail 1 has stand for its formal's
// default; null where `decl` is none.
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

// The net, variable or parameter the simple name `expr` resolves to, the use
// of a let it names (§11.12), or the parameter a genvar it names stands as.
VpiObject* NamedObject(const Expr* expr, const AssignBuild& build) {
  VpiObject* named = Resolve(build.names, expr->text);
  if (named != nullptr) return named;
  VpiObject* let =
      LetExprObject(expr, LetDeclNamed(build.names, expr->text), build);
  return let != nullptr ? let : GenvarParameter(expr->text, build);
}

// The object standing for one side of an assignment: the net or variable a
// name stands for, a constant, a select, a call, or an operation over these.
// A member access is left to the default, HierarchicalObject, which gives
// null for any other kind the switch does not name, as no dotted name: such a
// kind is not modelled.
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
      // §11.12: a call naming a let is a use of it rather than a call.
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
  VpiSizeExpression(obj);
  // §37.3.5 with §38.15: an operation, a function, method function or system
  // function call, and a bit select, part select or indexed part select
  // (§37.59) hold no storage, so the value of each is its expression evaluated
  // where the source wrote it, in the instance and the generate blocks the
  // expression stands in.
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
  // §37.3.5: a select whose index has side effects is written through by no
  // vpi_put_value().
  if (obj != nullptr && expr->kind == ExprKind::kSelect) {
    VpiNoteSelectIndexes(obj, expr, build.alloc);
  }
  // §37.59 detail 2: an expression object made for what the source wrote
  // decompiles to it. A name stands for the net or variable it resolves to,
  // which is no object of this expression's own.
  if (obj != nullptr && expr->kind != ExprKind::kIdentifier &&
      expr->kind != ExprKind::kMemberAccess && VpiIsExprType(obj->type)) {
    obj->decompile = VpiExprDecompile(expr);
  }
  // §37.83: an operation carries the attributes its operator is written with.
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
  // An expression an instance writes outside every generate block resolves
  // its names in the instance itself.
  static const GenBlockPrefixes kNoGenBlocks;
  return VpiGenBlockExpression(expr, {objects, prefix, kNoGenBlocks}, ctx,
                               build);
}

VpiObject* VpiGenBlockExpression(const Expr* expr, const VpiExprNames& names,
                                 SimContext& ctx, const VpiAttachBuild& build) {
  // §37.42: a call made where the names stand is held, unshaped and without
  // its arguments, until VpiShapeDeferredCalls makes it the tf call it is.
  std::function<bool(const Expr&, VpiObject*)> defer = nullptr;
  if (names.stand != nullptr && build.deferred_calls != nullptr) {
    defer = [&names, &build](const Expr& call, VpiObject* made) {
      build.deferred_calls->push_back(
          {&call, made, *names.stand, names.prefix, names.gen_prefixes});
      return true;
    };
  }
  return ExpressionObject(
      expr, AssignBuild{build.alloc,
                        &ctx,
                        AssignNames{names.objects, names.prefix,
                                    names.gen_prefixes, names.scope},
                        {},
                        build.keep,
                        defer,
                        names.attrs});
}

namespace {

// What building an expression written at `site` needs: its names resolve in
// the blocks around the site, then in the generate blocks it stands in and in
// the instance, as VpiInstanceExpression's do, and its callees at the site.
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
                  site.mod.unit_index},
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
