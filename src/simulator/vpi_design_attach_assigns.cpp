#include <functional>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
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

// Where the names of one continuous assignment resolve: the instance it was
// elaborated in, keyed as the simulator keys it, and the generate blocks it
// stands in, innermost last, whose declarations a name finds first.
struct AssignNames {
  const std::unordered_map<std::string_view, VpiObject*>& objects;
  const std::string& prefix;
  const GenBlockPrefixes& gen;
};

VpiHandle Resolve(const AssignNames& names, std::string_view name) {
  for (auto it = names.gen.rbegin(); it != names.gen.rend(); ++it) {
    VpiHandle obj = FindObjectForFlatName(
        names.objects,
        VpiFlatName(names.prefix, std::string(*it) + std::string(name)));
    if (obj != nullptr) return obj;
  }
  return FindObjectForFlatName(names.objects, VpiFlatName(names.prefix, name));
}

// What building one assignment's expressions needs: somewhere to allocate an
// object, the run a constant's value is evaluated in, and the names.
struct AssignBuild {
  std::function<VpiObject*()> alloc;
  SimContext* sim;
  AssignNames names;
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

// §37.58: a literal as a constant carrying the value it evaluates to.
VpiObject* ConstantObject(const Expr* expr, const AssignBuild& build) {
  if (build.sim == nullptr) return nullptr;
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = expr->kind == ExprKind::kRealLiteral ? vpiRealConst
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

// `first` followed by `rest`, as the operands of an operation.
std::vector<const Expr*> Operands(const Expr* first,
                                  const std::vector<Expr*>& rest) {
  std::vector<const Expr*> operands{first};
  operands.insert(operands.end(), rest.begin(), rest.end());
  return operands;
}

// §37.16, §37.17 details 12 and 13: a bit of a vector net or packed variable
// whose index is not a constant. It is a bit of the kind the vector's own bits
// are, reaching the vector through vpiParent and the expression the source
// wrote through vpiIndex; which of the vector's bits it stands for is not fixed
// before the run, so it holds none of them, and its value is the one of the bit
// its index selects when the value is read or written (vpi_value.cpp). Null
// for a vector with no bits.
VpiObject* VaryingBitObject(VpiObject* base, const Expr* index,
                            const AssignBuild& build) {
  int bit_type = 0;
  for (const VpiObject* child : base->children) {
    if (child->type == vpiNetBit || child->type == vpiRegBit) {
      bit_type = child->type;
      break;
    }
  }
  if (bit_type == 0) return nullptr;
  VpiObject* bit = build.alloc();
  bit->type = bit_type;
  bit->parent = base;
  bit->size = 1;
  bit->index_expr = ExpressionObject(index, build);
  if (bit_type == vpiRegBit && bit->index_expr != nullptr) {
    bit->children.push_back(bit->index_expr);
  }
  return bit;
}

// §37.58: a select of one bit. Of an integer var, a time var or a parameter it
// is a bit select reaching the object through vpiParent and its index through
// vpiIndex; of a vector net or a logic or bit variable it is that object's own
// bit (§37.16, §37.17), the one a constant index names, or one standing for
// whichever bit a varying index selects.
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
  if (expr->index == nullptr) return nullptr;
  if (expr->index->kind != ExprKind::kIntegerLiteral) {
    return VaryingBitObject(base, expr->index, build);
  }
  const auto kIndex = static_cast<int>(expr->index->int_val);
  for (VpiObject* child : base->children) {
    if ((child->type == vpiNetBit || child->type == vpiRegBit) &&
        child->index == kIndex) {
      return child;
    }
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
// arguments in order, which vpiArgument reaches.
VpiObject* CallObject(const Expr* expr, const AssignBuild& build) {
  VpiObject* call = build.alloc();
  call->type =
      expr->kind == ExprKind::kSystemCall ? vpiSysFuncCall : vpiFuncCall;
  for (const Expr* arg : expr->args) {
    VpiObject* obj = ExpressionObject(arg, build);
    if (obj != nullptr) call->children.push_back(obj);
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

// The object standing for one side of an assignment: the net or variable a
// name stands for, a constant, a select, a call, or an operation over these.
// The kinds of expression the switch does not name are not modelled and give
// null.
VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build) {
  if (expr == nullptr) return nullptr;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return Resolve(build.names, expr->text);
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
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
    default:
      return nullptr;
  }
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
  obj->rhs = ExpressionObject(rhs, build);

  std::vector<std::string_view> names;
  CollectTargets(lhs, names);
  HangOn(obj, names, build.names);
  names.clear();
  CollectReads(rhs, names);
  HangOn(obj, names, build.names);
}

}  // namespace

VpiObject* VpiInstanceExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const std::string& prefix, SimContext& ctx,
                                 const VpiAttachBuild& build) {
  // An expression an instance writes outside every generate block, whose
  // names resolve in the instance itself.
  static const GenBlockPrefixes kNoGenBlocks;
  return ExpressionObject(
      expr, AssignBuild{build.alloc, &ctx,
                        AssignNames{objects, prefix, kNoGenBlocks}});
}

void VpiContext::AttachContinuousAssignments(const RtlirDesign* design) {
  // §37.47: a module reaches the continuous assignments it holds. Nothing made
  // one, so the relation reached none and no net had a driver or a load
  // (§37.46).
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  const std::string kFirstTop(design->top_modules.front()->name);
  WalkInstancePaths(design, [&](const RtlirModule* mod,
                                const std::string& prefix) {
    VpiHandle scope =
        FindObjectForFlatName(object_map_, prefix.empty() ? kFirstTop : prefix);
    if (scope == nullptr) return;
    // The elaborator splits one statement into an assignment per element of
    // a concatenation it writes; the statement is one object.
    std::unordered_set<const ModuleItem*> made;
    for (const RtlirContAssign& ca : mod->assigns) {
      if (ca.source_item == nullptr || !made.insert(ca.source_item).second) {
        continue;
      }
      AssignBuild build{
          [this] { return AllocObject(); }, sim_ctx_,
          AssignNames{object_map_, prefix, ca.gen_block_prefixes}};
      MakeContinuousAssignment(ca, scope, build);
    }
  });
}

}  // namespace delta
