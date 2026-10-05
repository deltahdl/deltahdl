#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.50: the object kind of the concurrent assertion `item` writes, by its
// keyword.
int ConcurrentKindOf(const ModuleItem& item) {
  switch (item.kind) {
    case ModuleItemKind::kAssumeProperty:
      return vpiAssume;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      return vpiCover;
    case ModuleItemKind::kRestrictProperty:
      return vpiRestrict;
    default:
      return vpiAssert;
  }
}

// §37.50: the object the concurrent assertion `item` stands as in `scope`,
// named by its label, reporting where it stands and, for a cover, whether it
// covers a sequence.
VpiObject* MakeConcurrentAssertion(const ModuleItem& item, VpiObject* scope,
                                   SimContext& ctx,
                                   const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = ConcurrentKindOf(item);
  obj->parent = scope;
  if (!item.name.empty()) {
    obj->name = build.keep(std::string(item.name));
    obj->full_name = VpiScopedFullName(scope, item.name);
  }
  obj->cover_sequence = item.kind == ModuleItemKind::kCoverSequence;
  VpiRecordAssertionLocation(obj, SourceRange{item.loc, item.end}, ctx);
  scope->children.push_back(obj);
  return obj;
}

// §6.11, §6.12 and §6.17: the data type a type keyword names alone.
struct KeywordType {
  TokenKind keyword;
  DataTypeKind type;
};
constexpr KeywordType kKeywordTypes[] = {
    {TokenKind::kKwLogic, DataTypeKind::kLogic},
    {TokenKind::kKwReg, DataTypeKind::kReg},
    {TokenKind::kKwBit, DataTypeKind::kBit},
    {TokenKind::kKwByte, DataTypeKind::kByte},
    {TokenKind::kKwShortint, DataTypeKind::kShortint},
    {TokenKind::kKwInt, DataTypeKind::kInt},
    {TokenKind::kKwLongint, DataTypeKind::kLongint},
    {TokenKind::kKwInteger, DataTypeKind::kInteger},
    {TokenKind::kKwTime, DataTypeKind::kTime},
    {TokenKind::kKwReal, DataTypeKind::kReal},
    {TokenKind::kKwShortreal, DataTypeKind::kShortreal},
    {TokenKind::kKwRealtime, DataTypeKind::kRealtime},
    {TokenKind::kKwString, DataTypeKind::kString},
    {TokenKind::kKwEvent, DataTypeKind::kEvent},
};

// The data type `keyword` names alone; kImplicit where it names none.
DataTypeKind KeywordDataType(TokenKind keyword) {
  for (const KeywordType& entry : kKeywordTypes) {
    if (entry.keyword == keyword) return entry.type;
  }
  return DataTypeKind::kImplicit;
}

// §37.51 detail 3 with §37.25: the kind of typespec a property formal declared
// with the type keyword `keyword` reaches, 0 for an untyped formal, which
// reaches none. §16.12 adds sequence and property to the data types a formal
// may be declared with; §6.12 makes realtime a synonym for real.
int FormalTypespecKind(TokenKind keyword) {
  switch (keyword) {
    case TokenKind::kKwSequence:
      return vpiSequenceTypespec;
    case TokenKind::kKwProperty:
      return vpiPropertyTypespec;
    case TokenKind::kKwEvent:
      return vpiEventTypespec;
    case TokenKind::kKwRealtime:
      return vpiRealTypespec;
    default: {
      const DataTypeKind kType = KeywordDataType(keyword);
      return kType == DataTypeKind::kImplicit ? 0 : VpiTypespecKind(kType);
    }
  }
}

// §37.25: the typespec the typedef `name` declares in the scopes from
// `holder` out to the instance, or else among the compilation unit's,
// `unit`; null where none of them declares one.
VpiObject* TypedefTypespec(const VpiObject* holder, std::string_view name,
                           const VpiObjectMap& unit) {
  for (const VpiObject* scope = holder; scope != nullptr;
       scope = scope->parent) {
    for (VpiObject* child : scope->children) {
      if (VpiIsTypespecType(child->type) && child->name == name) return child;
    }
    if (VpiIsInstanceType(scope->type)) break;
  }
  auto it = unit.find(name);
  return it == unit.end() ? nullptr : it->second;
}

// §37.51 detail 3 with §37.25: the typespec the formal `index` of `decl` is
// declared with, hung from `formal`: the one the typedef it names declares,
// which other objects of that type share (§37.17), or one of the type's own,
// reaching a range per packed dimension it was written with (§37.22); none
// for an untyped formal.
void MakeFormalTypespec(const ModuleItem& decl, size_t index, VpiObject* formal,
                        const VpiPropertyDeclSite& at,
                        const VpiAttachBuild& build) {
  const DataType* type = index < decl.prop_formal_types.size()
                             ? decl.prop_formal_types[index]
                             : nullptr;
  if (type != nullptr && type->kind == DataTypeKind::kNamed) {
    VpiObject* named =
        TypedefTypespec(formal->parent, type->type_name, at.unit_typespecs);
    if (named != nullptr) formal->children.push_back(named);
    return;
  }
  const TokenKind kKeyword = index < decl.prop_formal_type_kw.size()
                                 ? decl.prop_formal_type_kw[index]
                                 : TokenKind::kEof;
  int kind = 0;
  if (kKeyword != TokenKind::kEof) {
    kind = FormalTypespecKind(kKeyword);
  } else if (type != nullptr) {
    kind = VpiTypespecKind(type->kind);
  }
  if (kind == 0) return;
  VpiObject* typespec = build.alloc();
  typespec->type = kind;
  typespec->parent = formal;
  formal->children.push_back(typespec);
  for (const PackedRange& dim : WrittenPackedDims(type, at.ctx)) {
    typespec->children.push_back(VpiRangeObject(typespec, dim, build));
  }
}

// §37.51: the prop formal decl the formal `index` of `decl` stands as, hung
// from `property`: named, of no direction unless it is a local variable
// argument (detail 5), reaching the typespec of the type it is declared with
// (detail 3) and the default value it declares, where it declares one,
// through vpiExpr (detail 4).
void MakePropFormal(const ModuleItem& decl, size_t index, VpiObject* property,
                    const VpiPropertyDeclSite& at, const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiPropFormalDecl;
  formal->parent = property;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction =
      VpiPropFormalDirection(index < decl.prop_formal_is_local.size() &&
                             decl.prop_formal_is_local[index]);
  MakeFormalTypespec(decl, index, formal, at, with.build);
  if (index < decl.prop_formal_defaults.size()) {
    VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
    if (value != nullptr) formal->children.push_back(value);
  }
  property->children.push_back(formal);
}

// §37.51 with §16.10: the variable the local variable `local` a property
// declares stands as, hung from the property decl `property` and named in
// it, of the kind its type is (§37.17). §37.52 detail 1 gives its value no
// access, so it holds none.
void MakePropertyVariable(const SeqLocalDecl& local, VpiObject* property,
                          const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = VpiDataTypeVariableKind(KeywordDataType(local.type_kw));
  var->parent = property;
  var->name = build.keep(std::string(local.name));
  var->full_name = VpiScopedFullName(property, local.name);
  property->children.push_back(var);
}

// The child of `scope` of `type` named `name`; null where none is.
VpiObject* ChildOfType(const VpiObject* scope, int type,
                       std::string_view name) {
  for (VpiObject* child : scope->children) {
    if (child->type == type && child->name == name) return child;
  }
  return nullptr;
}

// §37.51: the property decl named `name` the scope standing around `holder`
// declares, the nearest from a generate block instance out to the instance;
// null where none was built. §16.16 (b): a name written through a clocking
// block, `cb.p`, is the property that block declares.
VpiObject* PropertyDeclAround(const VpiObject* holder, std::string_view name) {
  const size_t kDot = name.find('.');
  for (VpiObject* scope = holder->parent; scope != nullptr;
       scope = scope->parent) {
    VpiObject* found =
        kDot == std::string_view::npos
            ? ChildOfType(scope, vpiPropertyDecl, name)
            : ChildOfType(scope, vpiClockingBlock, name.substr(0, kDot));
    if (found != nullptr && kDot != std::string_view::npos) {
      return ChildOfType(found, vpiPropertyDecl, name.substr(kDot + 1));
    }
    if (found != nullptr) return found;
    if (VpiIsInstanceType(scope->type)) break;
  }
  return nullptr;
}

// §37.52 detail 2: the operation of `op_type` over `operands`, in the order
// given, strong where `strong` is (detail 3); null where an operand is.
VpiObject* PropertyOperation(int op_type,
                             const std::vector<VpiObject*>& operands,
                             bool strong, const VpiAttachBuild& build) {
  for (const VpiObject* operand : operands) {
    if (operand == nullptr) return nullptr;
  }
  VpiObject* op = build.alloc();
  op->type = vpiOperation;
  op->op_type = op_type;
  op->op_strong = strong;
  op->children = operands;
  return op;
}

// §37.54 detail 3: the bound `value` of a range or a repetition, `$` the
// unbounded constant.
VpiObject* BoundConstant(uint32_t value, const VpiAttachBuild& build) {
  if (value != SeqCycleDelay::kUnbounded) return VpiIntConstant(value, build);
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = vpiUnboundedConst;
  return constant;
}

// §37.54 detail 3: the left bound `min` onto `operands`, and the right bound
// `max` where it differs from the left.
void AppendBounds(std::vector<VpiObject*>& operands, uint32_t min, uint32_t max,
                  const VpiAttachBuild& build) {
  operands.push_back(BoundConstant(min, build));
  if (max != min) operands.push_back(BoundConstant(max, build));
}

// §16.9.2: the operand `index` of the chain `body` under the repetition it
// carries, the sequence repeated first and then its bounds (detail 3).
VpiObject* RepeatedOperand(const SeqLinearBody& body, size_t index,
                           const VpiStmtBuild& with) {
  VpiObject* operand = with.expression(body.operands[index]);
  if (index >= body.repetitions.size()) return operand;
  const SeqRepetition& repetition = body.repetitions[index];
  int op = vpiRepeatOp;
  switch (repetition.kind) {
    case SeqRepetition::Kind::kNone:
      return operand;
    case SeqRepetition::Kind::kConsecutive:
      op = vpiConsecutiveRepeatOp;
      break;
    case SeqRepetition::Kind::kGoto:
      op = vpiGotoRepeatOp;
      break;
    default:
      break;
  }
  std::vector<VpiObject*> operands{operand};
  AppendBounds(operands, repetition.min, repetition.max, with.build);
  return PropertyOperation(op, operands, false, with.build);
}

// §16.9.1 and §16.9.2: the operands of the chain `body` joined left to right
// by the cycle delays between them, each with its two sequences and its
// range, and a delay before the first a unary cycle delay over it (detail 3).
VpiObject* ChainExpr(const SeqLinearBody& body, const VpiStmtBuild& with) {
  if (body.operands.empty()) return nullptr;
  VpiObject* chain = RepeatedOperand(body, 0, with);
  if (!body.delays.empty() &&
      (body.delays[0].min != 0 || body.delays[0].max != 0)) {
    std::vector<VpiObject*> operands{chain};
    AppendBounds(operands, body.delays[0].min, body.delays[0].max, with.build);
    chain =
        PropertyOperation(vpiUnaryCycleDelayOp, operands, false, with.build);
  }
  for (size_t i = 1; i < body.operands.size(); ++i) {
    std::vector<VpiObject*> operands{chain, RepeatedOperand(body, i, with)};
    if (i < body.delays.size()) {
      AppendBounds(operands, body.delays[i].min, body.delays[i].max,
                   with.build);
    }
    chain = PropertyOperation(vpiCycleDelayOp, operands, false, with.build);
  }
  return chain;
}

// §16.9.5 and §16.9.6: the chain `body` intersected with each chain of its
// intersect, the whole and-ed with each of its conjuncts, left to right.
VpiObject* ConjunctionExpr(const SeqLinearBody& body,
                           const VpiStmtBuild& with) {
  VpiObject* joined = ChainExpr(body, with);
  for (const SeqLinearBody& other : body.intersects) {
    joined = PropertyOperation(vpiIntersectOp, {joined, ChainExpr(other, with)},
                               false, with.build);
  }
  for (const SeqLinearBody& other : body.conjuncts) {
    joined =
        PropertyOperation(vpiCompAndOp, {joined, ConjunctionExpr(other, with)},
                          false, with.build);
  }
  return joined;
}

// Whether every part of `body` is one the sequence exprs below are built of:
// no operand with a clocking event of its own (§37.56), no match item and no
// throughout.
bool IsModelledSequence(const SeqLinearBody& body) {
  const auto kUnclocked = [](const std::vector<EventExpr>& clock) {
    return clock.empty();
  };
  const auto kNoItems = [](const std::vector<SeqMatchAssign>& items) {
    return items.empty();
  };
  if (!body.throughouts.empty() || !body.first_match_items.empty() ||
      !std::ranges::all_of(body.clocks, kUnclocked) ||
      !std::ranges::all_of(body.match_items, kNoItems)) {
    return false;
  }
  for (const auto* parts :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    if (!std::ranges::all_of(*parts, IsModelledSequence)) return false;
  }
  return true;
}

// §37.52 with §37.54: the sequence `sequence` as a property expr or as an
// operand of a property operator; null for one holding a part not built.
VpiObject* SequenceOperand(const ModuleItem* sequence,
                           const VpiStmtBuild& with) {
  if (sequence == nullptr) return nullptr;
  return VpiSequenceExprObject(sequence->seq_linear, with);
}

// The property expr of the operand `index` of `node`; null where it has none.
VpiObject* OperandOf(const PropertyExprNode& node, size_t index,
                     const VpiStmtBuild& with) {
  return index < node.operands.size()
             ? VpiPropertyExprObject(node.operands[index], with)
             : nullptr;
}

// §16.12.5: an and or an or over every operand of `node`, joined left to
// right as the grammar's binary operator joins them.
VpiObject* JoinedOperation(int op_type, const PropertyExprNode& node,
                           const VpiStmtBuild& with) {
  VpiObject* joined = OperandOf(node, 0, with);
  for (size_t i = 1; i < node.operands.size(); ++i) {
    joined = PropertyOperation(op_type, {joined, OperandOf(node, i, with)},
                               false, with.build);
  }
  return joined;
}

// §16.12.9: the followed-by `node`, the not standing for it, as the operator
// written: the implication's antecedent, then the property its negated
// consequent negates.
VpiObject* FollowedByOperation(const PropertyExprNode& node,
                               const VpiStmtBuild& with) {
  const PropertyExprNode* implication =
      node.operands.empty() ? nullptr : node.operands.front();
  if (implication == nullptr || implication->operands.empty() ||
      implication->operands.front()->operands.empty()) {
    return nullptr;
  }
  const int kOp =
      implication->strong ? vpiNonOverlapFollowedByOp : vpiOverlapFollowedByOp;
  return PropertyOperation(kOp,
                           {SequenceOperand(implication->sequence, with),
                            OperandOf(*implication->operands.front(), 0, with)},
                           false, with.build);
}

// §16.12.10: an if, or an if-else where an else is written, its condition
// first.
VpiObject* ConditionalOperation(const PropertyExprNode& node,
                                const VpiStmtBuild& with) {
  std::vector<VpiObject*> operands{with.expression(node.boolean),
                                   OperandOf(node, 0, with)};
  if (node.operands.size() > 1) operands.push_back(OperandOf(node, 1, with));
  return PropertyOperation(node.operands.size() > 1 ? vpiIfElseOp : vpiIfOp,
                           operands, false, with.build);
}

// §16.12.11 and §16.12.13 with detail 2: a nexttime takes its property and
// its constant, the constant only where it is other than 1; an always and an
// eventually their property and the bounds of their range.
VpiObject* CountedOperation(int op_type, const PropertyExprNode& node,
                            const VpiStmtBuild& with) {
  VpiObject* property = OperandOf(node, 0, with);
  if (op_type == vpiNexttimeOp) {
    const Expr* count = node.boolean;
    const bool kOne = count != nullptr &&
                      count->kind == ExprKind::kIntegerLiteral &&
                      count->int_val == 1;
    return PropertyOperation(
        op_type, VpiNexttimeOperands(property, with.expression(count), !kOne),
        node.strong, with.build);
  }
  return PropertyOperation(
      op_type,
      VpiAlwaysEventuallyOperands(property, with.expression(node.range_min),
                                  with.expression(node.range_max)),
      node.strong, with.build);
}

// §16.12.3 and §16.12.9: a not over its operand, or the followed-by it
// stands for.
VpiObject* NotOperation(const PropertyExprNode& node,
                        const VpiStmtBuild& with) {
  if (node.followed_by) return FollowedByOperation(node, with);
  return PropertyOperation(vpiNotOp, {OperandOf(node, 0, with)}, false,
                           with.build);
}

// §16.12.7: an implication, overlapping or not, its antecedent first.
VpiObject* ImplicationOperation(const PropertyExprNode& node,
                                const VpiStmtBuild& with) {
  const int kOp = node.strong ? vpiNonOverlapImplyOp : vpiOverlapImplyOp;
  return PropertyOperation(
      kOp, {SequenceOperand(node.sequence, with), OperandOf(node, 0, with)},
      false, with.build);
}

// §16.12.8 and §16.12.12: the operator of an implies, an iff or an until,
// the untils told apart by whether they overlap.
int BinaryOp(const PropertyExprNode& node) {
  switch (node.kind) {
    case PropertyExprNode::Kind::kImplies:
      return vpiImpliesOp;
    case PropertyExprNode::Kind::kIff:
      return vpiIffOp;
    default:
      return node.range_unbounded ? vpiUntilWithOp : vpiUntilOp;
  }
}

// §16.12.8 and §16.12.12: an implies, an iff or an until over its two
// operands, an until strong where it was written so.
VpiObject* BinaryOperation(const PropertyExprNode& node,
                           const VpiStmtBuild& with) {
  return PropertyOperation(BinaryOp(node),
                           {OperandOf(node, 0, with), OperandOf(node, 1, with)},
                           node.strong, with.build);
}

// §16.12.14: the abort operator `node` was written with.
int AbortOp(const PropertyExprNode& node) {
  if (node.accept) return node.synchronous ? vpiSyncAcceptOnOp : vpiAcceptOnOp;
  return node.synchronous ? vpiSyncRejectOnOp : vpiRejectOnOp;
}

// §37.52 with §16.12.16: the case property `node`, reaching its case
// expression through vpiCondition and an item per property it branches to,
// each grouping the expressions written before that property (detail 4),
// the default's none (detail 5).
VpiObject* CaseProperty(const PropertyExprNode& node,
                        const VpiStmtBuild& with) {
  VpiObject* obj = with.build.alloc();
  obj->type = vpiCaseProperty;
  VpiObject* condition = with.expression(node.boolean);
  if (condition != nullptr) obj->children.push_back(condition);
  for (size_t i = 0; i < node.operands.size(); ++i) {
    VpiObject* item = with.build.alloc();
    item->type = vpiCasePropertyItem;
    item->parent = obj;
    if (i < node.case_values.size()) {
      for (const Expr* value : node.case_values[i]) {
        VpiObject* expression = with.expression(value);
        if (expression != nullptr) item->children.push_back(expression);
      }
    }
    item->body = OperandOf(node, i, with);
    obj->children.push_back(item);
  }
  return obj;
}

// §37.52: the property expr `node` stands for, its own clock aside.
VpiObject* UnclockedPropertyExpr(const PropertyExprNode* node,
                                 const VpiStmtBuild& with) {
  using Kind = PropertyExprNode::Kind;
  switch (node->kind) {
    case Kind::kBoolean:
      return with.expression(node->boolean);
    case Kind::kSequence:
      return SequenceOperand(node->sequence, with);
    case Kind::kNot:
      return NotOperation(*node, with);
    case Kind::kOr:
      return JoinedOperation(vpiCompOrOp, *node, with);
    case Kind::kAnd:
      return JoinedOperation(vpiCompAndOp, *node, with);
    case Kind::kIfElse:
      return ConditionalOperation(*node, with);
    case Kind::kImplication:
      return ImplicationOperation(*node, with);
    case Kind::kImplies:
    case Kind::kIff:
    case Kind::kUntil:
      return BinaryOperation(*node, with);
    case Kind::kNexttime:
      return CountedOperation(vpiNexttimeOp, *node, with);
    case Kind::kAlways:
      return CountedOperation(vpiAlwaysOp, *node, with);
    case Kind::kEventually:
      return CountedOperation(vpiEventuallyOp, *node, with);
    case Kind::kAbort:
      return PropertyOperation(
          AbortOp(*node),
          {with.expression(node->boolean), OperandOf(*node, 0, with)}, false,
          with.build);
    case Kind::kCase:
      return CaseProperty(*node, with);
    default:
      return nullptr;
  }
}

}  // namespace

VpiObject* VpiSequenceExprObject(const SeqLinearBody& body,
                                 const VpiStmtBuild& with) {
  if (!IsModelledSequence(body)) return nullptr;
  // §16.9.7 and §16.9.8: the alternatives of an or, left to right, and the
  // whole under the first_match it is the operand of.
  VpiObject* whole = ConjunctionExpr(body, with);
  for (const SeqLinearBody& other : body.alternatives) {
    whole = PropertyOperation(
        vpiCompOrOp, {whole, ConjunctionExpr(other, with)}, false, with.build);
  }
  if (body.first_match) {
    whole = PropertyOperation(vpiFirstMatchOp, {whole}, false, with.build);
  }
  return whole;
}

VpiObject* VpiPropertyExprObject(const PropertyExprNode* node,
                                 const VpiStmtBuild& with) {
  if (node == nullptr) return nullptr;
  VpiObject* property = UnclockedPropertyExpr(node, with);
  if (property == nullptr || node->clock.empty()) return property;
  // §37.52 with §16.13.2: a property written under a clocking event of its
  // own is a clocked property, reaching that event and the property.
  VpiObject* clocked = with.build.alloc();
  clocked->type = vpiClockedProp;
  clocked->clocking_event = VpiEventCondition(node->clock, with);
  clocked->children.push_back(property);
  return clocked;
}

VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiPropertyInst;
  inst->parent = holder;
  const std::string_view kName =
      instance.kind == ExprKind::kCall ? instance.callee : instance.text;
  inst->property_decl = PropertyDeclAround(holder, kName);
  // §37.51 detail 2: an argument per formal, in the order declared, the
  // formal's default standing for an actual the instance leaves out; with no
  // declaration built, the actuals as written.
  std::vector<VpiHandle> provided;
  provided.reserve(instance.args.size());
  for (const Expr* actual : instance.args) {
    provided.push_back(with.expression(actual));
  }
  std::vector<VpiPropertyFormal> formals;
  for (VpiHandle formal : VpiPropFormals(inst->property_decl)) {
    formals.push_back(VpiPropertyFormal{VpiPropFormalInitExpr(formal)});
  }
  for (VpiHandle argument : formals.empty()
                                ? provided
                                : VpiPropertyInstArguments(formals, provided)) {
    if (argument != nullptr) inst->arguments.push_back(argument);
  }
  holder->children.push_back(inst);
  return inst;
}

VpiObject* VpiMakePropertyDecl(const RtlirPropertyDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with) {
  VpiObject* scope = at.scope;
  // §37.12 with §14.3: a property a clocking block declares is of that block.
  if (declared.clocking_block != nullptr) {
    scope = ChildOfType(scope, vpiClockingBlock, declared.clocking_block->name);
    if (scope == nullptr) return nullptr;
  }
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = with.build.alloc();
  obj->type = vpiPropertyDecl;
  obj->parent = scope;
  // §16.16 (b): the run keys a clocking block's property under the block's
  // name and its own, `cb.p`, the block being its scope here.
  const std::string_view kName =
      declared.clocking_block == nullptr
          ? decl.name
          : decl.name.substr(decl.name.rfind('.') + 1);
  obj->name = with.build.keep(std::string(kName));
  obj->full_name = VpiScopedFullName(scope, kName);
  scope->children.push_back(obj);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakePropFormal(decl, i, obj, at, with);
  }
  for (const SeqLocalDecl& local : decl.prop_locals) {
    MakePropertyVariable(local, obj, with.build);
  }
  // §37.52: the body the parser read, its clock, its disable condition and,
  // for a Boolean property, its expression; a body of another shape was not
  // read and stands for no spec.
  const PropertyExprNode* tree = decl.prop_body_tree;
  if (tree == nullptr) return obj;
  VpiMakePropertySpecOf(
      obj, VpiPropertySpecParts{decl.prop_clock, decl.prop_disable_iff, tree},
      with);
  return obj;
}

void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx) {
  // §37.49: where the assertion stands - its file, the line and column it
  // starts at and those it ends at - read where the text was written (§22.12).
  // A position the parser did not record leaves its pair as it was.
  const SourceManager& sources = ctx.GetDiag().Sources();
  if (range.start.IsValid()) {
    const SourceLoc kStart = sources.ResolveToOrigin(range.start);
    obj->file = std::string(sources.FilePath(kStart.file_id));
    obj->start_line = static_cast<int>(kStart.line);
    obj->column = static_cast<int>(kStart.column);
  }
  if (range.end.IsValid()) {
    const SourceLoc kEnd = sources.ResolveToOrigin(range.end);
    obj->end_line = static_cast<int>(kEnd.line);
    obj->end_column = static_cast<int>(kEnd.column);
  }
}

void VpiMakeItemAssertion(const RtlirAssertion& assertion, VpiObject* scope,
                          SimContext& ctx, const VpiStmtBuild& with) {
  const ModuleItem& item = *assertion.item;
  // §37.49 with §39.3.1 step b: an assertion written as an item is an
  // assertion of the scope writing it. A deferred immediate one runs as a
  // process the elaborator makes of it, whose walk builds it as the statement
  // it is, with its parts (§37.55).
  if (item.body != nullptr && item.body->is_deferred) return;
  VpiObject* obj = MakeConcurrentAssertion(item, scope, ctx, with.build);
  // §37.50: the clock the elaborator resolved onto the statement it carries,
  // where it carries one, and the property: a property inst where the spec
  // instantiates a declared property, a property spec otherwise.
  if (item.body != nullptr) {
    VpiFillAssertionClock(obj, *item.body, with);
    // §16.5.2: a clock of $global_clock is the event this instance's global
    // clocking declaration names (§14.14).
    if (assertion.leading_clock != nullptr) {
      obj->clocking_event = VpiEventCondition(*assertion.leading_clock, with);
    }
  }
  if (!item.prop_instance_name.empty() && item.assert_expr != nullptr) {
    VpiMakePropertyInst(obj, *item.assert_expr, with);
  } else if (item.body != nullptr) {
    VpiMakePropertySpec(obj, *item.body, with);
  }
  // §37.50 detail 2: a restrict writes no action; §16.14.3 gives a cover a
  // pass action alone.
  with.statement(item.assert_pass_stmt, obj);
  obj->else_stmt = with.statement(item.assert_fail_stmt, obj);
}

}  // namespace delta
