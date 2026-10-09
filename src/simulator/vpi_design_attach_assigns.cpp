#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <initializer_list>
#include <memory>
#include <set>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_expr_decompile.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.59: the vpiOpType of a binary operator, and 0 for one this table does
// not hold.
int BinaryOpType(TokenKind op) {
  switch (op) {
    case TokenKind::kPlus:
      return vpiAddOp;
    case TokenKind::kMinus:
      return vpiSubOp;
    case TokenKind::kStar:
      return vpiMultOp;
    case TokenKind::kSlash:
      return vpiDivOp;
    case TokenKind::kPercent:
      return vpiModOp;
    case TokenKind::kPower:
      return vpiPowerOp;
    case TokenKind::kAmp:
      return vpiBitAndOp;
    case TokenKind::kPipe:
      return vpiBitOrOp;
    case TokenKind::kCaret:
      return vpiBitXorOp;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return vpiBitXnorOp;
    case TokenKind::kAmpAmp:
      return vpiLogAndOp;
    case TokenKind::kPipePipe:
      return vpiLogOrOp;
    case TokenKind::kEqEq:
      return vpiEqOp;
    case TokenKind::kBangEq:
      return vpiNeqOp;
    case TokenKind::kEqEqEq:
      return vpiCaseEqOp;
    case TokenKind::kBangEqEq:
      return vpiCaseNeqOp;
    case TokenKind::kEqEqQuestion:
      return vpiWildEqOp;
    case TokenKind::kBangEqQuestion:
      return vpiWildNeqOp;
    case TokenKind::kLt:
      return vpiLtOp;
    case TokenKind::kGt:
      return vpiGtOp;
    case TokenKind::kLtEq:
      return vpiLeOp;
    case TokenKind::kGtEq:
      return vpiGeOp;
    case TokenKind::kLtLt:
      return vpiLShiftOp;
    case TokenKind::kGtGt:
      return vpiRShiftOp;
    case TokenKind::kLtLtLt:
      return vpiArithLShiftOp;
    case TokenKind::kGtGtGt:
      return vpiArithRShiftOp;
    case TokenKind::kArrow:
      return vpiImplyOp;
    default:
      return 0;
  }
}

// §37.59: the vpiOpType of a prefix unary operator, and 0 for one this table
// does not hold.
int UnaryOpType(TokenKind op) {
  switch (op) {
    case TokenKind::kMinus:
      return vpiMinusOp;
    case TokenKind::kPlus:
      return vpiPlusOp;
    case TokenKind::kBang:
      return vpiNotOp;
    case TokenKind::kTilde:
      return vpiBitNegOp;
    case TokenKind::kAmp:
      return vpiUnaryAndOp;
    case TokenKind::kTildeAmp:
      return vpiUnaryNandOp;
    case TokenKind::kPipe:
      return vpiUnaryOrOp;
    case TokenKind::kTildePipe:
      return vpiUnaryNorOp;
    case TokenKind::kCaret:
      return vpiUnaryXorOp;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return vpiUnaryXNorOp;
    default:
      return 0;
  }
}

// Where the names of one assignment resolve: the instance it was elaborated
// in, keyed as the simulator keys it; the generate blocks it stands in,
// innermost last, whose declarations a name finds first; and, for an
// expression a procedure's statement writes, the block or statement it stands
// in, whose blocks' declarations a name finds ahead of all of those.
struct AssignNames {
  const std::unordered_map<std::string_view, VpiObject*>& objects;
  const std::string& prefix;
  const GenBlockPrefixes& gen;
  const VpiObject* scope = nullptr;
  // §27.4: the genvars of the loop generate blocks a continuous assignment
  // stands in, each with the value it holds in the block instance; none for
  // any other expression.
  const GenBlockConsts& genvars = NoGenvars();

  static const GenBlockConsts& NoGenvars() {
    static const GenBlockConsts kNone;
    return kNone;
  }
};

// §23.9 and §12.7.3: the variable or named event `scope` itself declares
// under `name`, or the index variable of the foreach loop `scope` is; null
// where neither is.
VpiHandle DeclaredIn(const VpiObject* scope, std::string_view name) {
  for (VpiObject* var : scope->loop_vars) {
    if (var != nullptr && var->name == name) return var;
  }
  for (VpiObject* child : scope->children) {
    const bool kDeclares = VpiIsVariablesType(child->type) ||
                           child->type == vpiNamedEvent ||
                           child->type == vpiNamedEventArray;
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
  return FindObjectForFlatName(names.objects, VpiFlatName(names.prefix, name));
}

// What building one assignment's expressions needs: somewhere to allocate an
// object, the run a constant's value is evaluated in, the names, and the
// functions the calls in them resolve to.
struct AssignBuild {
  std::function<VpiObject*()> alloc;
  SimContext* sim;
  AssignNames names;
  VpiCalleeResolver callees;
  std::function<std::string_view(std::string)> keep;
};

VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build);

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

// §27.4: a loop generate block's genvar named in a continuous assignment the
// block holds, as a constant of the value it holds in the block instance; the
// run holds no storage for a genvar, so no name resolves to one. Null where
// `name` is no such genvar.
VpiObject* GenvarConstant(std::string_view name, const AssignBuild& build) {
  const auto kGenvar = std::ranges::find_if(
      build.names.genvars,
      [name](const auto& genvar) { return genvar.first == name; });
  if (kGenvar == build.names.genvars.end()) return nullptr;
  Arena& arena = build.sim->GetArena();
  auto* storage = arena.Create<Variable>();
  storage->value =
      MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(kGenvar->second));
  storage->value.is_signed = true;
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = vpiIntConst;
  constant->var = storage;
  constant->size = 32;
  return constant;
}

// `first` followed by `rest`, as the operands of an operation.
std::vector<const Expr*> Operands(const Expr* first,
                                  const std::vector<Expr*>& rest) {
  std::vector<const Expr*> operands{first};
  operands.insert(operands.end(), rest.begin(), rest.end());
  return operands;
}

// §37.19: a select of an element of the array var `base` whose index is not a
// constant: a var select reaching the array through vpiParent and the
// expression the source wrote through vpiIndex. Which element it stands for is
// not fixed before the run, so it holds none, and its value is the one of the
// element its index selects when the value is read or written (vpi_value.cpp).
VpiObject* VarSelectObject(VpiObject* base, const Expr* index,
                           const AssignBuild& build) {
  VpiObject* select = build.alloc();
  select->type = vpiVarSelect;
  select->parent = base;
  select->index_expr = ExpressionObject(index, build);
  if (select->index_expr != nullptr) {
    select->children.push_back(select->index_expr);
  }
  return select;
}

// §37.19: a select through the var select `outer`: a var select of its own
// where `outer` selects a subarray -- the chain of var selects down from the
// array var indexes fewer of its unpacked dimensions than it has -- and null
// where `outer` selects an element, whose bits a further index selects.
VpiObject* SelectThroughVarSelect(VpiObject* outer, const Expr* index,
                                  const AssignBuild& build) {
  const VpiObject* array = outer;
  std::size_t depth = 0;
  for (; array->type == vpiVarSelect; array = array->parent) ++depth;
  if (depth < array->array_dim_indices.size()) {
    return VarSelectObject(outer, index, build);
  }
  return nullptr;
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
    if (select->index_expr != nullptr) {
      select->index_expressions.push_back(select->index_expr);
    }
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
    if (VpiIndexSelects(*child, kIndex)) return child;
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
// parser holds the replication as the pattern's one element, a replicate
// starting where the pattern does, which tells it from a replicate written as
// the pattern's one expression. A keyed pattern, whose positional order its
// target's type decides, is not modelled.
VpiObject* PatternObject(const Expr* expr, const AssignBuild& build) {
  if (!expr->pattern_keys.empty()) return nullptr;
  const Expr* first = expr->elements.front();
  if (expr->elements.size() == 1 && first->kind == ExprKind::kReplicate &&
      first->range.start.line == expr->range.start.line &&
      first->range.start.column == expr->range.start.column) {
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
    const DataTypeKind kType = PatternTypeKeyKind(key->text);
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

// §37.59 detail 6: the keyed assignment pattern `pattern` assigned to
// `target` as an assignment pattern operation over its expressions in the
// positional order of `target`'s members or elements, left first (§37.17
// details 3 and 18), each in the place its keys give it. Null where `target`
// has neither.
VpiObject* KeyedPatternObject(const Expr* pattern, const VpiObject* target,
                              const AssignBuild& build) {
  std::vector<const Expr*> placed;
  for (const VpiObject* child : target->children) {
    if (child->member_of == target || child->array_member) {
      placed.push_back(KeyedValue(pattern, child, build));
    }
  }
  if (placed.empty()) return nullptr;
  return OperationObject(vpiAssignmentPatternOp, placed, build);
}

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

// §23.6: `expr` as the dotted name it writes, `u1.clk`, onto `out`; false
// where it is not identifiers joined by dots alone.
bool DottedName(const Expr* expr, std::string& out) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return expr->scope_prefix.empty();
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->is_scope_resolution ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier ||
      !DottedName(expr->lhs, out)) {
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
    return FindObjectForFlatName(VpiObjectMap{{kFirst, holder}}, dotted);
  }
  VpiObject* below = FindObjectForFlatName(
      build.names.objects, VpiFlatName(build.names.prefix, dotted));
  return below != nullptr ? below
                          : FindObjectForFlatName(build.names.objects, dotted);
}

// The object standing for one side of an assignment: the net or variable a
// name stands for, a constant, a select, a call, or an operation over these.
// The kinds of expression the switch does not name are not modelled and give
// null.
VpiObject* ModelledExpression(const Expr* expr, const AssignBuild& build) {
  switch (expr->kind) {
    case ExprKind::kIdentifier: {
      VpiObject* named = Resolve(build.names, expr->text);
      return named != nullptr ? named : GenvarConstant(expr->text, build);
    }
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
      return ConstantObject(expr, build);
    case ExprKind::kUnary:
      return OperationObject(UnaryOpType(expr->op), {expr->lhs}, build);
    case ExprKind::kBinary:
      return OperationObject(BinaryOpType(expr->op), {expr->lhs, expr->rhs},
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
      return OperationObject(vpiCastOp, {expr->lhs}, build);
    case ExprKind::kMinTypMax:
      return OperationObject(vpiMinTypMaxOp,
                             {expr->lhs, expr->condition, expr->rhs}, build);
    case ExprKind::kSelect:
      return SelectObject(expr, build);
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
      return CallObject(expr, build);
    case ExprKind::kMemberAccess:
      return HierarchicalObject(expr, build);
    default:
      return nullptr;
  }
}

VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build) {
  if (expr == nullptr) return nullptr;
  VpiObject* obj = ModelledExpression(expr, build);
  // §37.3.5 with §38.15: an operation and a function or system function call
  // hold no storage, so the value of each is its expression evaluated where
  // the source wrote it, in the instance and the generate blocks the
  // expression stands in.
  if (obj != nullptr &&
      (obj->type == vpiOperation || obj->type == vpiFuncCall ||
       obj->type == vpiSysFuncCall)) {
    obj->expr_scope = std::make_shared<const VpiExprScope>(
        VpiExprScope{expr, VpiFlatName(build.names.prefix, ""),
                     std::vector<std::string>(build.names.gen.begin(),
                                              build.names.gen.end())});
  }
  // §37.59 detail 2: an expression object made for what the source wrote
  // decompiles to it. A name stands for the net or variable it resolves to,
  // which is no object of this expression's own.
  if (obj != nullptr && expr->kind != ExprKind::kIdentifier &&
      expr->kind != ExprKind::kMemberAccess && VpiIsExprType(obj->type)) {
    obj->decompile = VpiExprDecompile(expr);
  }
  return obj;
}

// §37.46: the names an assignment's left side drives -- a net written whole,
// through a select, or as an element of a concatenation.
void CollectTargets(const Expr* expr, std::vector<std::string_view>& out) {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back(expr->text);
  } else if (expr->kind == ExprKind::kSelect) {
    CollectTargets(expr->base, out);
  } else if (expr->kind == ExprKind::kConcatenation) {
    for (const Expr* element : expr->elements) CollectTargets(element, out);
  }
}

// §37.46: the names an assignment's right side reads, wherever they stand in
// it. A member access reads its prefix; the member is no name of the scope.
void CollectReads(const Expr* expr, std::vector<std::string_view>& out) {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back(expr->text);
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    CollectReads(expr->lhs, out);
    return;
  }
  for (const Expr* sub : {expr->lhs, expr->rhs, expr->condition,
                          expr->true_expr, expr->false_expr, expr->base,
                          expr->index, expr->index_end, expr->repeat_count}) {
    CollectReads(sub, out);
  }
  for (const Expr* arg : expr->args) CollectReads(arg, out);
  for (const Expr* element : expr->elements) CollectReads(element, out);
}

// Hangs `assign` among the children of each object `names` resolve to once,
// which is where §37.46's driver and load iterations look for it.
void HangOn(VpiObject* assign, const std::vector<std::string_view>& found,
            const AssignNames& names) {
  for (std::string_view name : found) {
    VpiHandle net = Resolve(names, name);
    if (net == nullptr) continue;
    bool present = false;
    for (const VpiObject* child : net->children) present |= child == assign;
    if (!present) net->children.push_back(assign);
  }
}

// §37.47: the continuous assignment `ca` stands for, in `scope`, with its two
// sides; and §37.46: a driver of what it writes and a load of what it reads.
// §37.47 with §37.3.4 and §10.3.3: the delays the assignment `ca` was
// written with, in ticks, as vpi_get_delays reads them off `obj`: a rise, a
// fall that is the rise where none was written, and a turn-off that is the
// smaller of the two where none was.
void FillContAssignDelays(VpiObject* obj, const RtlirContAssign& ca,
                          SimContext& sim) {
  Arena& arena = sim.GetArena();
  const auto kTicks = [&sim, &arena](const Expr* delay) {
    return static_cast<double>(
        DelayValueToTicks(EvalExpr(delay, sim, arena), sim));
  };
  const double kRise = kTicks(ca.delay);
  const double kFall = ca.delay_fall != nullptr ? kTicks(ca.delay_fall) : kRise;
  const double kOff = ca.delay_decay != nullptr ? kTicks(ca.delay_decay)
                                                : std::min(kRise, kFall);
  for (const double kDelay : {kRise, kFall, kOff}) {
    VpiDelayInfo info;
    info.delay = kDelay;
    obj->delays.push_back(info);
  }
}

void MakeContinuousAssignment(const RtlirContAssign& ca, VpiObject* scope,
                              const AssignBuild& build) {
  const ModuleItem* item = ca.source_item;
  const bool kDecl = item->kind == ModuleItemKind::kNetDecl;
  // A net declaration's assignment has no left side written in the source; the
  // elaborator names the net in one of its own.
  const Expr* lhs = kDecl ? ca.lhs : item->assign_lhs;
  const Expr* rhs = kDecl ? item->init_expr : item->assign_rhs;

  VpiObject* obj = build.alloc();
  obj->type = vpiContAssign;
  // It hangs among a net's children as a driver or a load, where an index
  // selects a bit (§38.19); it is no bit, so it answers no index.
  obj->index = -1;
  obj->net_decl_assign = kDecl;
  obj->parent = scope;
  scope->children.push_back(obj);
  obj->lhs = ExpressionObject(lhs, build);
  obj->rhs = AssignedExpressionObject(rhs, obj->lhs, build);

  if (ca.delay != nullptr && build.sim != nullptr) {
    FillContAssignDelays(obj, ca, *build.sim);
  }

  std::vector<std::string_view> names;
  CollectTargets(lhs, names);
  // §38.32: what the run keys the assignment's delays under, the instance and
  // the net it drives, which a vpi_put_delays gives it new ones under.
  if (!names.empty()) {
    const std::string& prefix = build.names.prefix;
    obj->run_key = (prefix.empty() ? "" : prefix + ".") + std::string(names[0]);
  }
  HangOn(obj, names, build.names);
  names.clear();
  CollectReads(rhs, names);
  HangOn(obj, names, build.names);
}

// §37.42 with §23.9: the scope a func call an assignment makes, written in
// the generate block instances `prefixes` names, resolves its callee from
// first: the innermost of them declaring a task or function, whose gen scope
// is found through the path one of those declarations records, and the
// instance `instance` where none does.
const VpiObject* CalleeScope(const RtlirModule& mod,
                             const GenBlockPrefixes& prefixes,
                             VpiHandle instance) {
  for (auto it = prefixes.rbegin(); it != prefixes.rend(); ++it) {
    const std::string_view kBlock = *it;
    const auto kDeclared =
        std::ranges::find_if(mod.gen_block_subroutines,
                             [kBlock](const RtlirGenBlockSubroutine& sub) {
                               return !sub.gen_block_prefixes.empty() &&
                                      sub.gen_block_prefixes.back() == kBlock;
                             });
    if (kDeclared == mod.gen_block_subroutines.end()) continue;
    VpiHandle block = VpiGenScopeOf(instance, kDeclared->gen_block_path);
    return block != nullptr ? block : instance;
  }
  return instance;
}

}  // namespace

VpiObject* VpiBitAtOffset(const VpiObject& root, int64_t offset) {
  for (VpiObject* child : root.children) {
    if ((child->type == vpiNetBit || child->type == vpiRegBit) &&
        child->bit_offset == offset) {
      return child;
    }
  }
  return nullptr;
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
  return ExpressionObject(
      expr,
      AssignBuild{build.alloc,
                  &ctx,
                  AssignNames{names.objects, names.prefix, names.gen_prefixes},
                  {},
                  build.keep});
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
  return AssignBuild{build.alloc, &ctx,
                     AssignNames{objects, site.prefix, gen, site.scope},
                     VpiCalleesAt(site), build.keep};
}

}  // namespace

VpiObject* VpiCallSiteExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const VpiCallSite& site, SimContext& ctx,
                                 const VpiAttachBuild& build) {
  return ExpressionObject(expr, CallSiteBuild(objects, site, ctx, build));
}

VpiObject* VpiCallSiteAssignedExpression(
    const Expr* expr, const VpiObject* target, const VpiObjectMap& objects,
    const VpiCallSite& site, SimContext& ctx, const VpiAttachBuild& build) {
  return AssignedExpressionObject(expr, target,
                                  CallSiteBuild(objects, site, ctx, build));
}

void VpiContext::AttachContinuousAssignments(
    const RtlirDesign* design, const VpiSubroutineObjects& subroutines) {
  // §37.47: a module reaches the continuous assignments it holds. Nothing made
  // one, so the relation reached none and no net had a driver or a load
  // (§37.46).
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  const std::string kFirstTop(design->top_modules.front()->name);
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiHandle scope = FindObjectForFlatName(
            object_map_, prefix.empty() ? kFirstTop : prefix);
        if (scope == nullptr) return;
        // The elaborator splits one statement into an assignment per element of
        // a concatenation it writes, and each instance of a loop generate
        // block holds its own instance of the statement (§27.4): the statement
        // is one object per generate block instance it stands in.
        std::set<std::pair<const ModuleItem*, GenBlockPrefixes>> made;
        for (const RtlirContAssign& ca : mod->assigns) {
          if (ca.source_item == nullptr ||
              !made.emplace(ca.source_item, ca.gen_block_prefixes).second) {
            continue;
          }
          AssignBuild build{
              [this] { return AllocObject(); }, sim_ctx_,
              AssignNames{object_map_, prefix, ca.gen_block_prefixes, nullptr,
                          ca.gen_block_consts},
              VpiCalleesAt({*design, *mod, prefix,
                            CalleeScope(*mod, ca.gen_block_prefixes, scope),
                            subroutines}),
              [this](std::string name) {
                name_pool_.push_back(std::move(name));
                return std::string_view(name_pool_.back());
              }};
          MakeContinuousAssignment(ca, scope, build);
        }
      });
}

}  // namespace delta
