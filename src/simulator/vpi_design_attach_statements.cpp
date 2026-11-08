#include <algorithm>
#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

bool IsOperatorAssignment(const Stmt& stmt) {
  return stmt.rhs != nullptr && stmt.rhs->kind == ExprKind::kBinary &&
         stmt.lhs != nullptr && stmt.rhs->lhs == stmt.lhs;
}

std::string_view OperatorSpelling(TokenKind op) {
  const std::string_view kName = TokenKindName(op);
  return kName.substr(1, kName.size() - 2);
}

VpiObject* MakeOperation(int op_type,
                         std::initializer_list<VpiObject*> operands,
                         const VpiAttachBuild& build) {
  for (const VpiObject* operand : operands) {
    if (operand == nullptr) return nullptr;
  }
  VpiObject* op = build.alloc();
  op->type = vpiOperation;
  op->op_type = op_type;
  op->children.assign(operands.begin(), operands.end());
  return op;
}

VpiObject* EventItem(const EventExpr& event, const VpiStmtBuild& with) {
  if (event.is_sequence_event) {
    return VpiSequenceOperandObject(*event.signal, with);
  }
  VpiObject* item = with.expression(event.signal);
  if (event.edge == Edge::kEdge) {
    item = MakeOperation(
        vpiEventOrOp,
        {MakeOperation(vpiPosedgeOp, {item}, with.build),
         MakeOperation(vpiNegedgeOp, {with.expression(event.signal)},
                       with.build)},
        with.build);
  } else if (event.edge != Edge::kNone) {
    item = MakeOperation(
        event.edge == Edge::kPosedge ? vpiPosedgeOp : vpiNegedgeOp, {item},
        with.build);
  }
  if (event.iff_condition != nullptr) {
    item = MakeOperation(vpiIffOp, {item, with.expression(event.iff_condition)},
                         with.build);
  }
  return item;
}

VpiObject* EventCondition(const std::vector<EventExpr>& events,
                          const VpiStmtBuild& with) {
  VpiObject* condition = nullptr;
  for (const EventExpr& event : events) {
    VpiObject* item = EventItem(event, with);
    if (item == nullptr) return nullptr;
    condition =
        condition == nullptr
            ? item
            : MakeOperation(vpiEventOrOp, {condition, item}, with.build);
  }
  return condition;
}

VpiObject* MakeControl(int type, VpiObject* holder, VpiObject* operand,
                       const VpiAttachBuild& build) {
  VpiObject* control = build.alloc();
  control->type = type;
  control->parent = holder;
  if (operand != nullptr) control->children.push_back(operand);
  holder->children.push_back(control);
  return control;
}

void MakeIntraAssignmentControl(VpiObject* obj, const Stmt& stmt,
                                const VpiStmtBuild& with) {
  if (stmt.delay != nullptr) {
    MakeControl(vpiDelayControl, obj, with.expression(stmt.delay), with.build);
  } else if (stmt.repeat_event_count != nullptr) {
    VpiObject* repeat =
        MakeControl(vpiRepeatControl, obj,
                    with.expression(stmt.repeat_event_count), with.build);
    MakeControl(vpiEventControl, repeat, EventCondition(stmt.events, with),
                with.build);
  } else if (!stmt.events.empty()) {
    MakeControl(vpiEventControl, obj, EventCondition(stmt.events, with),
                with.build);
  }
}

void FillAssignment(VpiObject* obj, const Stmt& stmt,
                    const VpiStmtBuild& with) {
  const bool kOperator = IsOperatorAssignment(stmt);
  obj->lhs = with.expression(stmt.lhs);
  obj->rhs = kOperator             ? with.expression(stmt.rhs->rhs)
             : obj->lhs != nullptr ? with.assigned(stmt.rhs, obj->lhs)
                                   : with.expression(stmt.rhs);
  obj->op_type = kOperator ? VpiAssignmentOpType(OperatorSpelling(stmt.rhs->op))
                           : vpiAssignmentOp;
  obj->blocking = stmt.kind == StmtKind::kBlockingAssign;
  MakeIntraAssignmentControl(obj, stmt, with);
}

void HangOnObjectsRead(VpiObject* holder, VpiObject* expr) {
  if (expr == nullptr) return;
  if (expr->type == vpiOperation || VpiIsTfCallType(expr->type)) {
    for (VpiObject* sub : VpiSubexpressions(*expr)) {
      HangOnObjectsRead(holder, sub);
    }
    return;
  }
  for (const VpiObject* select = expr; select != nullptr;
       select = VpiIsVariableSelectType(select->type) ||
                        select->type == vpiVarSelect
                    ? select->parent
                    : nullptr) {
    for (VpiObject* part :
         {select->index_expr, select->base_expr, select->width_expr,
          select->left_range, select->right_range}) {
      HangOnObjectsRead(holder, part);
    }
  }
  VpiHangOnNetsNamed(holder, expr);
  VpiHangOnVariablesNamed(holder, expr);
}

void FillProceduralAssignment(VpiObject* obj, const Stmt& stmt,
                              const VpiStmtBuild& with) {
  obj->lhs = with.expression(stmt.lhs);
  obj->rhs = with.expression(stmt.rhs);
  if (stmt.kind != StmtKind::kAssign && stmt.kind != StmtKind::kForce) return;
  if (stmt.kind == StmtKind::kForce) VpiHangOnNetsNamed(obj, obj->lhs);
  VpiHangOnVariablesNamed(obj, obj->lhs);
  HangOnObjectsRead(obj, obj->rhs);
}

void AddChild(VpiObject* obj, VpiObject* child) {
  if (child != nullptr) obj->children.push_back(child);
}

int QualifierOf(const Stmt& stmt) {
  int qualifier = vpiNoQualifier;
  if (stmt.qualifier == CaseQualifier::kUnique ||
      stmt.qualifier == CaseQualifier::kUnique0) {
    qualifier |= vpiUniqueQualifier;
  } else if (stmt.qualifier == CaseQualifier::kPriority) {
    qualifier |= vpiPriorityQualifier;
  }
  if (stmt.case_inside) qualifier |= vpiInsideQualifier;
  if (stmt.case_matches) qualifier |= vpiTaggedQualifier;
  return qualifier;
}

VpiObject* TypespecOf(const VpiObject* obj) {
  if (obj == nullptr) return nullptr;
  for (VpiObject* child : obj->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

const std::vector<VpiObject*>& MembersOf(const VpiObject* typespec) {
  static const std::vector<VpiObject*> kNone;
  return typespec != nullptr ? typespec->children : kNone;
}

const Expr* KeyedMemberPattern(const Expr& keyed, std::string_view name) {
  for (std::size_t i = 0; i < keyed.pattern_keys.size(); ++i) {
    if (keyed.pattern_keys[i]->text == name) return keyed.elements[i];
  }
  return nullptr;
}

VpiObject* PatternObject(const Expr* pattern, VpiObject* parent,
                         const VpiObject* typespec, const VpiStmtBuild& with);

VpiObject* AnyPattern(std::string_view binds, VpiObject* parent,
                      const VpiStmtBuild& with) {
  VpiObject* any = with.build.alloc();
  any->type = vpiAnyPattern;
  any->parent = parent;
  if (!binds.empty()) any->name = with.build.keep(std::string(binds));
  return any;
}

VpiObject* StructurePattern(const Expr& pattern, VpiObject* parent,
                            const VpiObject* typespec,
                            const VpiStmtBuild& with) {
  VpiObject* op = with.build.alloc();
  op->type = vpiOperation;
  op->op_type = vpiAssignmentPatternOp;
  op->parent = parent;
  const std::vector<VpiObject*>& members = MembersOf(typespec);
  if (pattern.pattern_keys.empty()) {
    for (std::size_t i = 0; i < pattern.elements.size(); ++i) {
      AddChild(
          op, PatternObject(
                  pattern.elements[i], op,
                  TypespecOf(i < members.size() ? members[i] : nullptr), with));
    }
    return op;
  }
  for (const VpiObject* member : members) {
    VpiObject* struct_pattern = with.build.alloc();
    struct_pattern->type = vpiStructPattern;
    struct_pattern->parent = op;
    struct_pattern->name = member->name;
    const Expr* written = KeyedMemberPattern(pattern, member->name);
    struct_pattern->children.push_back(
        written != nullptr
            ? PatternObject(written, struct_pattern, TypespecOf(member), with)
            : AnyPattern({}, struct_pattern, with));
    op->children.push_back(struct_pattern);
  }
  return op;
}

VpiObject* MemberTypespec(const VpiObject* typespec, std::string_view name) {
  const std::vector<VpiObject*>& members = MembersOf(typespec);
  const auto kMember = std::ranges::find_if(
      members, [name](const VpiObject* m) { return m->name == name; });
  return kMember != members.end() ? TypespecOf(*kMember) : nullptr;
}

VpiObject* PatternObject(const Expr* pattern, VpiObject* parent,
                         const VpiObject* typespec, const VpiStmtBuild& with) {
  if (pattern == nullptr) return nullptr;
  const bool kWildcard =
      pattern->kind == ExprKind::kIdentifier && pattern->text == ".*";
  if (kWildcard || pattern->is_pattern_binding) {
    return AnyPattern(kWildcard ? std::string_view{} : pattern->text, parent,
                      with);
  }
  if (pattern->kind == ExprKind::kTagged) {
    VpiObject* tagged = with.build.alloc();
    tagged->type = vpiTaggedPattern;
    tagged->parent = parent;
    tagged->name = with.build.keep(std::string(pattern->rhs->text));
    VpiObject* member = MemberTypespec(typespec, pattern->rhs->text);
    AddChild(tagged, member);
    AddChild(tagged, PatternObject(pattern->lhs, tagged, member, with));
    return tagged;
  }
  if (pattern->kind == ExprKind::kAssignmentPattern) {
    return StructurePattern(*pattern, parent, typespec, with);
  }
  return with.expression(pattern);
}

void FillCase(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->case_type = stmt.case_kind == TokenKind::kKwCasex   ? vpiCaseX
                   : stmt.case_kind == TokenKind::kKwCasez ? vpiCaseZ
                                                           : vpiCaseExact;
  obj->qualifier = QualifierOf(stmt);
  VpiObject* condition = with.expression(stmt.condition);
  AddChild(obj, condition);
  const VpiObject* case_typespec = TypespecOf(condition);
  for (const CaseItem& item : stmt.case_items) {
    VpiObject* made = with.build.alloc();
    made->type = vpiCaseItem;
    made->parent = obj;
    made->process = obj->process;
    made->default_case_item = item.is_default;
    obj->children.push_back(made);
    for (const Expr* pattern : item.patterns) {
      AddChild(made, stmt.case_matches
                         ? PatternObject(pattern, made, case_typespec, with)
                         : with.expression(pattern));
    }
    with.statement(item.body, made);
  }
}

std::vector<VpiObject*> HeaderStmts(VpiObject* obj,
                                    const std::vector<Stmt*>& stmts,
                                    const VpiStmtBuild& with) {
  const std::size_t kBefore = obj->children.size();
  for (const Stmt* header : stmts) with.statement(header, obj);
  const auto kFirst =
      obj->children.begin() + static_cast<std::ptrdiff_t>(kBefore);
  std::vector<VpiObject*> made(kFirst, obj->children.end());
  obj->children.erase(kFirst, obj->children.end());
  return made;
}

void FillFor(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->local_var_decls =
      !stmt.for_init_types.empty() &&
      stmt.for_init_types.front().kind != DataTypeKind::kImplicit;
  AddChild(obj, with.expression(stmt.for_cond));
  obj->for_init_stmts = HeaderStmts(obj, stmt.for_inits, with);
  obj->for_inc_stmts = HeaderStmts(obj, stmt.for_steps, with);
  obj->body = with.statement(stmt.for_body, obj);
}

void FillForeach(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->foreach_array = with.expression(stmt.expr);
  for (std::string_view name : stmt.foreach_vars) {
    VpiObject* var = nullptr;
    if (!name.empty()) {
      var = with.build.alloc();
      var->type =
          obj->loop_vars.empty() ? with.index_kind(stmt.expr) : vpiIntVar;
      var->name = with.build.keep(std::string(name));
      var->parent = obj;
    }
    obj->loop_vars.push_back(var);
  }
  obj->body = with.statement(stmt.body, obj);
}

void FillOrderedWait(VpiObject* obj, const Stmt& stmt,
                     const VpiStmtBuild& with) {
  for (const Expr* event : stmt.wait_order_events) {
    AddChild(obj, with.expression(event));
  }
  with.statement(stmt.then_branch, obj);
  obj->else_stmt = with.statement(stmt.else_branch, obj);
}

void FillConditional(VpiObject* obj, const Stmt& stmt,
                     const VpiStmtBuild& with) {
  if (stmt.kind == StmtKind::kIf) obj->qualifier = QualifierOf(stmt);
  AddChild(obj, with.expression(stmt.condition));
  if (stmt.kind == StmtKind::kIf) {
    obj->body = with.statement(stmt.then_branch, obj);
    obj->else_stmt = with.statement(stmt.else_branch, obj);
    return;
  }
  obj->body = with.statement(stmt.body, obj);
}

bool NameParts(const Expr* expr, std::vector<std::string_view>& parts) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    parts.push_back(expr->text);
    return true;
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->rhs == nullptr ||
      !NameParts(expr->lhs, parts)) {
    return false;
  }
  parts.push_back(expr->rhs->text);
  return true;
}

VpiObject* DisableTarget(VpiObject* from, const Expr* name) {
  std::vector<std::string_view> parts;
  if (!NameParts(name, parts)) return nullptr;
  for (VpiObject* scope = from; scope != nullptr; scope = scope->parent) {
    VpiObject* found =
        scope->name == parts.front() ? scope : ChildNamed(scope, parts.front());
    for (std::size_t i = 1; found != nullptr && i < parts.size(); ++i) {
      found = ChildNamed(found, parts[i]);
    }
    if (found != nullptr && VpiIsDisableTargetType(found->type)) return found;
  }
  return nullptr;
}

int AssertionStmtKind(const Stmt& stmt) {
  const bool kConcurrent = stmt.is_procedural_concurrent;
  switch (stmt.kind) {
    case StmtKind::kAssumeImmediate:
      return kConcurrent ? vpiAssume : vpiImmediateAssume;
    case StmtKind::kCoverImmediate:
      return kConcurrent ? vpiCover : vpiImmediateCover;
    default:
      return kConcurrent ? vpiAssert : vpiImmediateAssert;
  }
}

void FillAssertion(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->cover_sequence = stmt.cover_sequence;
  if (!stmt.is_procedural_concurrent) {
    obj->is_deferred = stmt.is_deferred;
    obj->is_final = stmt.is_final_deferred;
    AddChild(obj, with.expression(stmt.assert_expr));
  } else {
    if (stmt.kind != StmtKind::kExpect) VpiFillAssertionClock(obj, stmt, with);
    if (stmt.assert_instance != nullptr && stmt.kind == StmtKind::kExpect) {
      VpiObject* spec = with.build.alloc();
      spec->type = vpiPropertySpec;
      spec->parent = obj;
      spec->clocking_event = EventCondition(stmt.assert_clock, with);
      spec->disable_condition = with.expression(stmt.assert_disable_iff);
      obj->children.push_back(spec);
      VpiMakePropertyInst(spec, *stmt.assert_instance, stmt.assert_disable_iff,
                          with);
    } else if (stmt.assert_instance != nullptr) {
      VpiMakePropertyInst(obj, *stmt.assert_instance, stmt.assert_disable_iff,
                          with);
    } else {
      VpiMakePropertySpec(obj, stmt, with);
    }
  }
  with.statement(stmt.assert_pass_stmt, obj);
  obj->else_stmt = with.statement(stmt.assert_fail_stmt, obj);
}

bool NamesClockingBlock(const std::vector<EventExpr>& clock,
                        std::string_view name) {
  return clock.size() == 1 && clock[0].edge == Edge::kNone &&
         clock[0].signal->kind == ExprKind::kIdentifier &&
         clock[0].signal->text == name;
}

VpiObject* ClockingBlockClocking(const VpiObject* obj, const Stmt& property) {
  const bool kFromDefault = property.assert_clock_from_default_clocking;
  for (const VpiObject* at = obj->parent; at != nullptr; at = at->parent) {
    for (VpiObject* child : at->children) {
      if (child->type != vpiClockingBlock) continue;
      if (kFromDefault
              ? child->default_clocking
              : NamesClockingBlock(property.assert_clock, child->name)) {
        return child;
      }
    }
  }
  return nullptr;
}

}  // namespace

void VpiFillAssertionClock(VpiObject* obj, const Stmt& property,
                           const VpiStmtBuild& with) {
  obj->clocking_event = EventCondition(property.assert_clock, with);
  obj->clock_inferred = property.assert_clock_inferred;
  AddChild(obj, ClockingBlockClocking(obj, property));
}

VpiObject* VpiMakePropertySpec(VpiObject* holder, const Stmt& property,
                               const VpiStmtBuild& with) {
  if (property.assert_expr == nullptr && property.assert_sequence == nullptr &&
      property.assert_property == nullptr) {
    return nullptr;
  }
  PropertyExprNode boolean;
  boolean.boolean = property.assert_expr;
  PropertyExprNode negated;
  negated.kind = PropertyExprNode::Kind::kNot;
  negated.operands.push_back(&boolean);
  PropertyExprNode sequence;
  sequence.kind = PropertyExprNode::Kind::kSequence;
  sequence.sequence = property.assert_sequence;
  sequence.strong = property.assert_strong;
  const PropertyExprNode* tree = property.assert_property;
  if (tree == nullptr && property.assert_sequence != nullptr) {
    tree = &sequence;
  } else if (tree == nullptr) {
    tree = property.assert_negated ? &negated : &boolean;
  }
  return VpiMakePropertySpecOf(
      holder,
      VpiPropertySpecParts{property.assert_clock, property.assert_disable_iff,
                           tree},
      with);
}

VpiObject* VpiMakePropertySpecOf(VpiObject* holder,
                                 const VpiPropertySpecParts& parts,
                                 const VpiStmtBuild& with) {
  VpiObject* spec = with.build.alloc();
  spec->type = vpiPropertySpec;
  spec->parent = holder;
  spec->clocking_event = EventCondition(parts.clock, with);
  spec->disable_condition = with.expression(parts.disable);
  AddChild(spec,
           VpiPropertyExprObject(parts.property, with,
                                 parts.clock.empty() ? nullptr : &parts.clock));
  holder->children.push_back(spec);
  return spec;
}

VpiObject* VpiEventCondition(const std::vector<EventExpr>& events,
                             const VpiStmtBuild& with) {
  return EventCondition(events, with);
}

int VpiBuiltStmtKind(const Stmt& stmt) {
  switch (stmt.kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      return vpiAssignment;
    case StmtKind::kEventControl:
      return vpiEventControl;
    case StmtKind::kDelay:
      return vpiDelayControl;
    case StmtKind::kAssign:
      return vpiAssignStmt;
    case StmtKind::kDeassign:
      return vpiDeassign;
    case StmtKind::kForce:
      return vpiForce;
    case StmtKind::kRelease:
      return vpiRelease;
    case StmtKind::kIf:
      return stmt.else_branch != nullptr ? vpiIfElse : vpiIf;
    case StmtKind::kCase:
      return vpiCase;
    case StmtKind::kForever:
      return vpiForever;
    case StmtKind::kWhile:
      return vpiWhile;
    case StmtKind::kRepeat:
      return vpiRepeat;
    case StmtKind::kDoWhile:
      return vpiDoWhile;
    case StmtKind::kFor:
      return vpiFor;
    case StmtKind::kForeach:
      return vpiForeachStmt;
    case StmtKind::kWait:
      return vpiWait;
    case StmtKind::kWaitFork:
      return vpiWaitFork;
    case StmtKind::kWaitOrder:
      return vpiOrderedWait;
    case StmtKind::kDisable:
      return vpiDisable;
    case StmtKind::kDisableFork:
      return vpiDisableFork;
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      return AssertionStmtKind(stmt);
    case StmtKind::kExpect:
      return vpiExpectStmt;
    case StmtKind::kReturn:
      return vpiReturnStmt;
    default:
      return 0;
  }
}

int VpiBareAtomicKind(StmtKind kind) {
  switch (kind) {
    case StmtKind::kBreak:
      return vpiBreak;
    case StmtKind::kContinue:
      return vpiContinue;
    case StmtKind::kNull:
      return vpiNullStmt;
    default:
      return 0;
  }
}

void VpiFillStmt(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  switch (stmt.kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      FillAssignment(obj, stmt, with);
      return;
    case StmtKind::kEventControl:
      AddChild(obj, stmt.is_star_event ? nullptr
                                       : EventCondition(stmt.events, with));
      obj->body = with.statement(stmt.body, obj);
      return;
    case StmtKind::kDelay:
      AddChild(obj, with.expression(stmt.delay));
      obj->body = with.statement(stmt.body, obj);
      return;
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
      FillProceduralAssignment(obj, stmt, with);
      return;
    case StmtKind::kCase:
      FillCase(obj, stmt, with);
      return;
    case StmtKind::kFor:
      FillFor(obj, stmt, with);
      return;
    case StmtKind::kForeach:
      FillForeach(obj, stmt, with);
      return;
    case StmtKind::kWaitOrder:
      FillOrderedWait(obj, stmt, with);
      return;
    case StmtKind::kWaitFork:
    case StmtKind::kDisableFork:
    case StmtKind::kDisable:
      return;
    case StmtKind::kReturn:
      AddChild(obj, with.expression(stmt.expr));
      return;
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
    case StmtKind::kExpect:
      FillAssertion(obj, stmt, with);
      return;
    default:
      FillConditional(obj, stmt, with);
      return;
  }
}

void VpiResolveDisableTargets(const VpiStmtObjects& stmts) {
  for (const auto& [key, obj] : stmts) {
    if (key.first->kind == StmtKind::kDisable) {
      obj->disable_target = DisableTarget(obj->parent, key.first->expr);
    }
  }
}

}  // namespace delta
