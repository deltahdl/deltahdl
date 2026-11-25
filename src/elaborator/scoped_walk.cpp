#include "elaborator/scoped_walk.h"

#include <cstddef>
#include <initializer_list>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/value_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

DataType MemberType(const StructMember& member) {
  if (member.nested_type != nullptr) return *member.nested_type;
  DataType type;
  type.kind = member.type_kind;
  type.type_name = member.type_name;
  type.scope_name = member.scope_name;
  type.type_params = member.type_params;
  type.packed_dim_left = member.packed_dim_left;
  type.packed_dim_right = member.packed_dim_right;
  type.extra_packed_dims = member.extra_packed_dims;
  return type;
}

}  // namespace

void ScopedWalk::WalkUnit(const CompilationUnit& unit) {
  for (const PackageDecl* package : unit.packages) {
    WalkItems(package->items, scopes_.PackageScope(package->name));
  }
  WalkItems(unit.cu_items, scopes_.Unit());
  for (const ClassDecl* cls : unit.classes) WalkClass(*cls);
  for (const auto* decls :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *decls) WalkModule(*decl);
  }
  for (const BindDirective* bind : unit.bind_directives) WalkBind(*bind);
}

void ScopedWalk::WalkExprs(const std::vector<Expr*>& exprs,
                           const NameScope& scope) {
  for (const Expr* e : exprs) WalkExpr(e, scope);
}

void ScopedWalk::WalkEach(std::initializer_list<const Expr*> exprs,
                          const NameScope& scope) {
  for (const Expr* e : exprs) WalkExpr(e, scope);
}

void ScopedWalk::WalkWith(const Expr& call, const NameScope& scope) {
  NameScope with{&scope};
  scopes_.DeclareIterator(call, scope, with);
  WalkExpr(call.with_expr, with);
}

void ScopedWalk::WalkInlineConstraint(const Expr& call,
                                      const NameScope& scope) {
  NameScope object{&scope};
  if (call.lhs->kind == ExprKind::kMemberAccess &&
      !call.lhs->is_scope_resolution)
    object.cls = scopes_.ValueOf(*call.lhs->lhs, scope).cls;
  WalkConstraints(call.inline_constraint->constraint_items, object);
}

void ScopedWalk::WalkExpr(const Expr* e, const NameScope& scope) {
  if (e == nullptr) return;
  VisitExpr(*e, scope);
  if (e->type_value != nullptr) {
    WalkType(*e->type_value, e->range.start, scope);
  }
  if (e->with_expr != nullptr) WalkWith(*e, scope);
  if (e->inline_constraint != nullptr) WalkInlineConstraint(*e, scope);
  WalkTree(e->property_actual, scope);
  ForEachExprChild(e, [&](const Expr* child) {
    if (child != e->with_expr) WalkExpr(child, scope);
  });
}

void ScopedWalk::WalkDist(const std::vector<ConstraintDistItem>& items,
                          const NameScope& scope) {
  for (const ConstraintDistItem& item : items) {
    WalkEach({item.value, item.lo, item.hi, item.tolerance, item.weight},
             scope);
  }
}

void ScopedWalk::WalkConstraints(const std::vector<ConstraintItem*>& items,
                                 const NameScope& scope) {
  for (const ConstraintItem* item : items) {
    NameScope loop{&scope};
    for (const std::string_view kVar : item->loop_vars) {
      DeclareOther(kVar, loop);
    }
    WalkExpr(item->expr, scope);
    WalkDist(item->dist, loop);
    WalkExprs(item->exprs, loop);
    WalkExprs(item->after, loop);
    WalkConstraints(item->body, loop);
    WalkConstraints(item->else_body, loop);
  }
}

void ScopedWalk::WalkEvents(const std::vector<EventExpr>& events,
                            const NameScope& scope) {
  for (const EventExpr& event : events) {
    WalkEach({event.signal, event.iff_condition}, scope);
  }
}

void ScopedWalk::WalkSequence(const SeqLinearBody& body,
                              const NameScope& scope) {
  ForEachBody(body, [&](const SeqLinearBody& nested) {
    for (const auto& clock : nested.clocks) WalkEvents(clock, scope);
    WalkEvents(nested.clock_out, scope);
  });
  ForEachBodyExpr(body, [&](const Expr* e) { WalkExpr(e, scope); });
}

void ScopedWalk::WalkTree(const PropertyExprNode* tree,
                          const NameScope& scope) {
  ForEachTreeNode(tree, [&](const PropertyExprNode& node) {
    WalkExpr(node.boolean, scope);
    WalkEvents(node.clock, scope);
    for (const auto& values : node.case_values) WalkExprs(values, scope);
    if (node.sequence == nullptr) return;
    WalkEvents(node.sequence->seq_clock, scope);
    WalkSequence(node.sequence->seq_linear, scope);
  });
}

void ScopedWalk::WalkTypes(const std::vector<DataType>& types, SourceLoc loc,
                           const NameScope& scope) {
  for (const DataType& type : types) WalkType(type, loc, scope);
}

void ScopedWalk::WalkType(const DataType& type, SourceLoc loc,
                          const NameScope& scope) {
  VisitType(type, loc, scope);
  WalkExpr(type.type_ref_expr, scope);
  WalkEach({type.packed_dim_left, type.packed_dim_right}, scope);
  for (const auto& [left, right] : type.extra_packed_dims) {
    WalkEach({left, right}, scope);
  }
  for (const DataType& specialized : type.specialized_scopes) {
    WalkTypes(specialized.type_params, loc, scope);
  }
  WalkTypes(type.type_params, loc, scope);
  for (const StructMember& member : type.struct_members) {
    WalkType(MemberType(member), loc, scope);
    WalkExprs(member.unpacked_dims, scope);
    WalkExpr(member.init_expr, scope);
  }
}

void ScopedWalk::DeclareLoopNames(const Stmt& stmt, NameScope& scope) {
  for (const std::string_view kVar : stmt.foreach_vars) {
    DeclareOther(kVar, scope);
  }
  for (std::size_t i = 0; i < stmt.for_init_types.size(); ++i) {
    if (stmt.for_init_types[i].kind == DataTypeKind::kImplicit) continue;
    DeclareData(stmt.for_inits[i]->lhs->text, stmt.for_init_types[i], 0, scope);
  }
}

void ScopedWalk::WalkStmt(const Stmt* stmt, const NameScope& outer) {
  if (stmt == nullptr) return;
  NameScope scope{&outer};
  scopes_.DeclareStmts(stmt->stmts, scope);
  scopes_.DeclareStmts(stmt->fork_stmts, scope);
  DeclareLoopNames(*stmt, scope);
  if (stmt->kind == StmtKind::kVarDecl) {
    WalkType(stmt->var_decl_type, stmt->range.start, scope);
  }
  WalkTypes(stmt->for_init_types, stmt->range.start, scope);
  ForEachChildExpr(stmt, [&](const Expr* e) { WalkExpr(e, scope); });
  WalkExpr(stmt->assert_disable_iff, scope);
  WalkEvents(stmt->assert_clock, scope);
  WalkTree(stmt->assert_property, scope);
  if (stmt->assert_sequence != nullptr) {
    WalkSequence(stmt->assert_sequence->seq_linear, scope);
  }
  if (stmt->decl_item != nullptr) WalkItem(*stmt->decl_item, scope);
  ForEachChildStmt(stmt, [&](Stmt* const& sub) { WalkStmt(sub, scope); });
}

void ScopedWalk::WalkFormals(const std::vector<FunctionArg>& formals,
                             SourceLoc loc, const NameScope& scope) {
  for (const FunctionArg& formal : formals) {
    WalkType(formal.data_type, loc, scope);
    WalkExpr(formal.default_value, scope);
    WalkExprs(formal.unpacked_dims, scope);
  }
}

void ScopedWalk::WalkBody(const ModuleItem& item, const NameScope& outer) {
  WalkType(item.return_type, item.loc, outer);
  WalkFormals(item.func_args, item.loc, outer);
  NameScope scope{&outer};
  DeclareResult(item, scope);
  DeclareFormals(item.func_args, scope);
  scopes_.DeclareStmts(item.func_body_stmts, scope);
  for (const Stmt* stmt : item.func_body_stmts) WalkStmt(stmt, scope);
  if (item.kind == ModuleItemKind::kLetDecl) WalkExpr(item.init_expr, scope);
}

void ScopedWalk::WalkSubroutine(const ModuleItem& item,
                                const NameScope& scope) {
  const ClassDecl* cls = item.method_class.empty()
                             ? nullptr
                             : scopes_.ClassNamed(item.method_class, scope);
  WalkBody(item, cls == nullptr ? scope : scopes_.ClassScope(*cls));
}

void ScopedWalk::WalkPropertyOrSequence(const ModuleItem& item,
                                        const NameScope& outer) {
  NameScope scope{&outer};
  for (std::size_t i = 0; i < item.prop_formals.size(); ++i) {
    if (item.prop_formal_types[i] != nullptr) {
      DeclareData(item.prop_formals[i], *item.prop_formal_types[i],
                  item.prop_formal_unpacked_dims[i].size(), scope);
    } else {
      DeclareOther(item.prop_formals[i], scope);
    }
  }
  for (const DataType* type : item.prop_formal_types) {
    if (type != nullptr) WalkType(*type, item.loc, outer);
  }
  for (const SeqLocalDecl& local : item.prop_locals) {
    DeclareOther(local.name, scope);
    WalkExpr(local.init, scope);
  }
  WalkExprs(item.prop_formal_defaults, outer);
  WalkEvents(item.prop_clock, scope);
  WalkEvents(item.seq_clock, scope);
  WalkEach({item.prop_body_expr, item.prop_disable_iff}, scope);
  WalkTree(item.prop_body_tree, scope);
  WalkSequence(item.seq_linear, scope);
}

void ScopedWalk::WalkRanges(const std::vector<CovergroupValueRange>& ranges,
                            const NameScope& scope) {
  for (const CovergroupValueRange& range : ranges) {
    WalkEach({range.lo, range.hi}, scope);
  }
}

void ScopedWalk::WalkBins(const BinsOrOptions& bins, const NameScope& scope) {
  WalkEach({bins.option.value, bins.array_size, bins.with_expr, bins.set_expr,
            bins.iff},
           scope);
  WalkRanges(bins.ranges, scope);
  for (const TransSet& set : bins.transitions) {
    for (const TransRangeList& step : set.steps) {
      WalkRanges(step.items, scope);
      WalkEach({step.repeat_lo, step.repeat_hi}, scope);
    }
  }
}

void ScopedWalk::WalkBinsSelection(const SelectExpression* select,
                                   const NameScope& scope) {
  if (select == nullptr) return;
  WalkRanges(select->intersect, scope);
  WalkEach({select->expr, select->matches}, scope);
  WalkBinsSelection(select->lhs, scope);
  WalkBinsSelection(select->rhs, scope);
}

void ScopedWalk::WalkCross(const CoverCrossDecl& cross,
                           const NameScope& scope) {
  WalkExpr(cross.iff, scope);
  for (const CrossBodyItem& item : cross.body) {
    if (item.function != nullptr) WalkBody(*item.function, scope);
    WalkEach({item.option.value, item.bins.iff}, scope);
    WalkBinsSelection(item.bins.select, scope);
  }
}

void ScopedWalk::WalkCovergroup(const CovergroupDecl& group, SourceLoc loc,
                                const NameScope& outer) {
  WalkFormals(group.formals, loc, outer);
  NameScope scope{&outer};
  DeclareFormals(group.formals, scope);
  DeclareFormals(group.event.sample_formals, scope);
  WalkEvents(group.event.clocking, scope);
  for (const CoverageSpecOrOption& item : group.items) {
    WalkExpr(item.option.value, scope);
    if (item.cover_point != nullptr) {
      WalkEach({item.cover_point->expr, item.cover_point->iff}, scope);
      for (const BinsOrOptions& bins : item.cover_point->bins) {
        WalkBins(bins, scope);
      }
    }
    if (item.cover_cross != nullptr) WalkCross(*item.cover_cross, scope);
  }
}

void ScopedWalk::WalkHeader(const ClassDecl& cls, const NameScope& scope) {
  VisitClass(cls, scope);
  WalkTypes(cls.base_class_type_params, cls.range.start, scope);
  for (const auto* refs : {&cls.extends_interfaces, &cls.implements_types}) {
    for (const InterfaceRef& ref : *refs) {
      WalkTypes(ref.type_params, cls.range.start, scope);
    }
  }
  WalkTypes(cls.param_types, cls.range.start, scope);
  for (const auto& [name, value] : cls.params) WalkExpr(value, scope);
  WalkExprs(cls.extends_args, scope);
}

void ScopedWalk::WalkClass(const ClassDecl& cls) {
  const NameScope& scope = scopes_.ClassScope(cls);
  WalkHeader(cls, scope);
  for (const ClassMember* member : cls.members) {
    WalkType(member->data_type, member->loc, scope);
    if (member->typedef_item != nullptr) WalkItem(*member->typedef_item, scope);
    WalkExprs(member->unpacked_dims, scope);
    WalkExpr(member->init_expr, scope);
    WalkConstraints(member->constraint_items, scope);
    if (member->method != nullptr) WalkBody(*member->method, scope);
    if (member->nested_class != nullptr) WalkClass(*member->nested_class);
    if (member->covergroup != nullptr) {
      WalkCovergroup(*member->covergroup, member->loc, scope);
    }
  }
}

void ScopedWalk::WalkGenerate(const ModuleItem& item, const NameScope& outer) {
  WalkExpr(item.gen_cond, outer);
  for (const GenerateCaseItem& arm : item.gen_case_items) {
    WalkExprs(arm.patterns, outer);
    WalkGenerateBlock(arm.body, outer);
  }
  WalkGenerateBlock(item.gen_body, outer);
  if (item.gen_else != nullptr) WalkGenerate(*item.gen_else, outer);
}

void ScopedWalk::WalkGenerateBlock(const std::vector<ModuleItem*>& items,
                                   const NameScope& outer) {
  NameScope scope{&outer};
  scopes_.DeclareItems(items, scope);
  WalkItems(items, scope);
}

void ScopedWalk::WalkInstance(const ModuleItem& item, const NameScope& scope) {
  for (const auto& [name, value] : item.inst_params) WalkExpr(value, scope);
  for (const auto& [name, value] : item.inst_ports) WalkExpr(value, scope);
  for (const auto& [left, right] : item.inst_dims) {
    WalkEach({left, right}, scope);
  }
  for (const auto& [target, value] : item.defparam_assigns) {
    WalkExpr(value, scope);
  }
  WalkExprs(item.gate_terminals, scope);
}

void ScopedWalk::WalkBind(const BindDirective& bind) {
  const NameScope* target = scopes_.ModuleNamed(bind.target.path);
  if (target != nullptr) {
    WalkInstance(*bind.instantiation, *target);
  }
}

void ScopedWalk::WalkClocking(const ModuleItem& item, const NameScope& scope) {
  WalkEvents(item.clocking_event, scope);
  for (const ClockingSignalDecl& signal : item.clocking_signals) {
    WalkExpr(signal.hier_expr, scope);
  }
}

void ScopedWalk::WalkItem(const ModuleItem& item, const NameScope& scope) {
  WalkType(item.data_type, item.loc, scope);
  WalkType(item.typedef_type, item.loc, scope);
  WalkExprs(item.unpacked_dims, scope);
  WalkEach({item.assign_lhs, item.assign_rhs, item.assign_delay,
            item.assign_delay_fall, item.assign_delay_decay, item.net_delay,
            item.net_delay_fall, item.net_delay_decay, item.gate_delay,
            item.gate_delay_fall, item.gate_delay_decay, item.assert_expr},
           scope);
  if (item.kind != ModuleItemKind::kLetDecl) WalkExpr(item.init_expr, scope);
  WalkInstance(item, scope);
  WalkStmt(item.body, scope);
  WalkEvents(item.sensitivity, scope);
  WalkSubroutine(item, scope);
  WalkPropertyOrSequence(item, scope);
  WalkClocking(item, scope);
  WalkGenerate(item, scope);
  if (item.class_decl != nullptr) WalkClass(*item.class_decl);
  if (item.covergroup != nullptr)
    WalkCovergroup(*item.covergroup, item.loc, scope);
  if (item.nested_module_decl != nullptr) {
    WalkModule(*item.nested_module_decl);
  }
}

void ScopedWalk::WalkItems(const std::vector<ModuleItem*>& items,
                           const NameScope& scope) {
  for (const ModuleItem* item : items) WalkItem(*item, scope);
}

void ScopedWalk::WalkModule(const ModuleDecl& decl) {
  const NameScope& scope = scopes_.ModuleScope(decl);
  WalkTypes(decl.param_types, decl.range.start, scope);
  for (const auto& [name, value] : decl.params) WalkExpr(value, scope);
  for (const PortDecl& port : decl.ports) {
    WalkType(port.data_type, port.loc, scope);
    WalkEach({port.default_value, port.port_expr}, scope);
    WalkExprs(port.unpacked_dims, scope);
  }
  for (const ModportDecl* modport : decl.modports) {
    for (const ModportPort& port : modport->ports) {
      WalkExpr(port.expr, scope);
    }
  }
  for (const BindDirective* bind : decl.bind_directives) WalkBind(*bind);
  WalkItems(decl.items, scope);
}

}  // namespace delta
