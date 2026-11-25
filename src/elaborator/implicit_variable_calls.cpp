#include "elaborator/implicit_variable_calls.h"

#include <cstddef>
#include <initializer_list>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
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

class ImplicitVariableWalk {
 public:
  ImplicitVariableWalk(const CompilationUnit& unit, DiagEngine& diag)
      : scopes_(unit), diag_(diag) {}

  void WalkUnit(const CompilationUnit& unit) {
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

 private:
  void Judge(const Expr& e, const ValueScope& scope) {
    if (e.kind != ExprKind::kMemberAccess || e.is_scope_resolution ||
        !IsBuiltinMethodNameWithoutArguments(e.rhs->text)) {
      return;
    }
    const ScopedValue kReceiver = scopes_.ValueOf(*e.lhs, scope);
    if (!scopes_.MethodOn(kReceiver, e.rhs->text, false).is_method ||
        !reported_.insert(&e).second) {
      return;
    }
    diag_.Error(e.rhs->range.start,
                "a built-in method call used as an implicit variable shall "
                "include its parentheses",
                Subclause("5.13"));
  }

  void WalkExprs(const std::vector<Expr*>& exprs, const ValueScope& scope) {
    for (const Expr* e : exprs) WalkExpr(e, scope);
  }

  void WalkEach(std::initializer_list<const Expr*> exprs,
                const ValueScope& scope) {
    for (const Expr* e : exprs) WalkExpr(e, scope);
  }

  void WalkWith(const Expr& call, const ValueScope& scope) {
    ValueScope with{&scope};
    scopes_.DeclareIterator(call, scope, with);
    WalkExpr(call.with_expr, with);
  }

  void WalkInlineConstraint(const Expr& call, const ValueScope& scope) {
    ValueScope object{&scope};
    if (call.lhs->kind == ExprKind::kMemberAccess &&
        !call.lhs->is_scope_resolution)
      object.cls = scopes_.ValueOf(*call.lhs->lhs, scope).cls;
    WalkConstraints(call.inline_constraint->constraint_items, object);
  }

  void WalkExpr(const Expr* e, const ValueScope& scope) {
    if (e == nullptr) return;
    if (e->kind == ExprKind::kSelect && e->base != nullptr) {
      Judge(*e->base, scope);
    }
    if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      Judge(*e->lhs, scope);
    }
    if (e->with_expr != nullptr) WalkWith(*e, scope);
    if (e->inline_constraint != nullptr) WalkInlineConstraint(*e, scope);
    WalkTree(e->property_actual, scope);
    ForEachExprChild(e, [&](const Expr* child) {
      if (child != e->with_expr) WalkExpr(child, scope);
    });
  }

  void WalkDist(const std::vector<ConstraintDistItem>& items,
                const ValueScope& scope) {
    for (const ConstraintDistItem& item : items) {
      WalkEach({item.value, item.lo, item.hi, item.tolerance, item.weight},
               scope);
    }
  }

  void WalkConstraints(const std::vector<ConstraintItem*>& items,
                       const ValueScope& scope) {
    for (const ConstraintItem* item : items) {
      ValueScope loop{&scope};
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

  void WalkEvents(const std::vector<EventExpr>& events,
                  const ValueScope& scope) {
    for (const EventExpr& event : events) {
      WalkEach({event.signal, event.iff_condition}, scope);
    }
  }

  void WalkSequence(const SeqLinearBody& body, const ValueScope& scope) {
    ForEachBody(body, [&](const SeqLinearBody& nested) {
      for (const auto& clock : nested.clocks) WalkEvents(clock, scope);
      WalkEvents(nested.clock_out, scope);
    });
    ForEachBodyExpr(body, [&](const Expr* e) { WalkExpr(e, scope); });
  }

  void WalkTree(const PropertyExprNode* tree, const ValueScope& scope) {
    ForEachTreeNode(tree, [&](const PropertyExprNode& node) {
      WalkExpr(node.boolean, scope);
      WalkEvents(node.clock, scope);
      for (const auto& values : node.case_values) WalkExprs(values, scope);
      if (node.sequence == nullptr) return;
      WalkEvents(node.sequence->seq_clock, scope);
      WalkSequence(node.sequence->seq_linear, scope);
    });
  }

  void WalkType(const DataType& type, const ValueScope& scope) {
    WalkEach({type.packed_dim_left, type.packed_dim_right}, scope);
    for (const auto& [left, right] : type.extra_packed_dims) {
      WalkEach({left, right}, scope);
    }
  }

  void DeclareLoopNames(const Stmt& stmt, ValueScope& scope) {
    for (const std::string_view kVar : stmt.foreach_vars) {
      DeclareOther(kVar, scope);
    }
    for (std::size_t i = 0; i < stmt.for_init_types.size(); ++i) {
      if (stmt.for_init_types[i].kind == DataTypeKind::kImplicit) continue;
      DeclareData(stmt.for_inits[i]->lhs->text, stmt.for_init_types[i], 0,
                  scope);
    }
  }

  void WalkStmt(const Stmt* stmt, const ValueScope& outer) {
    if (stmt == nullptr) return;
    ValueScope scope{&outer};
    scopes_.DeclareStmts(stmt->stmts, scope);
    scopes_.DeclareStmts(stmt->fork_stmts, scope);
    DeclareLoopNames(*stmt, scope);
    if (stmt->kind == StmtKind::kVarDecl) WalkType(stmt->var_decl_type, scope);
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

  void WalkFormals(const std::vector<FunctionArg>& formals,
                   const ValueScope& scope) {
    for (const FunctionArg& formal : formals) {
      WalkType(formal.data_type, scope);
      WalkExpr(formal.default_value, scope);
      WalkExprs(formal.unpacked_dims, scope);
    }
  }

  void WalkBody(const ModuleItem& item, const ValueScope& outer) {
    WalkFormals(item.func_args, outer);
    ValueScope scope{&outer};
    DeclareResult(item, scope);
    DeclareFormals(item.func_args, scope);
    scopes_.DeclareStmts(item.func_body_stmts, scope);
    for (const Stmt* stmt : item.func_body_stmts) WalkStmt(stmt, scope);
    if (item.kind == ModuleItemKind::kLetDecl) WalkExpr(item.init_expr, scope);
  }

  void WalkSubroutine(const ModuleItem& item, const ValueScope& scope) {
    const ClassDecl* cls = item.method_class.empty()
                               ? nullptr
                               : scopes_.ClassNamed(item.method_class, scope);
    WalkBody(item, cls == nullptr ? scope : scopes_.ClassScope(*cls));
  }

  void WalkPropertyOrSequence(const ModuleItem& item, const ValueScope& outer) {
    ValueScope scope{&outer};
    for (std::size_t i = 0; i < item.prop_formals.size(); ++i) {
      if (item.prop_formal_types[i] != nullptr) {
        DeclareData(item.prop_formals[i], *item.prop_formal_types[i],
                    item.prop_formal_unpacked_dims[i].size(), scope);
      } else {
        DeclareOther(item.prop_formals[i], scope);
      }
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

  void WalkRanges(const std::vector<CovergroupValueRange>& ranges,
                  const ValueScope& scope) {
    for (const CovergroupValueRange& range : ranges) {
      WalkEach({range.lo, range.hi}, scope);
    }
  }

  void WalkBins(const BinsOrOptions& bins, const ValueScope& scope) {
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

  void WalkBinsSelection(const SelectExpression* select,
                         const ValueScope& scope) {
    if (select == nullptr) return;
    WalkRanges(select->intersect, scope);
    WalkEach({select->expr, select->matches}, scope);
    WalkBinsSelection(select->lhs, scope);
    WalkBinsSelection(select->rhs, scope);
  }

  void WalkCross(const CoverCrossDecl& cross, const ValueScope& scope) {
    WalkExpr(cross.iff, scope);
    for (const CrossBodyItem& item : cross.body) {
      if (item.function != nullptr) WalkBody(*item.function, scope);
      WalkEach({item.option.value, item.bins.iff}, scope);
      WalkBinsSelection(item.bins.select, scope);
    }
  }

  void WalkCovergroup(const CovergroupDecl& group, const ValueScope& outer) {
    WalkFormals(group.formals, outer);
    ValueScope scope{&outer};
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

  void WalkClass(const ClassDecl& cls) {
    const ValueScope& scope = scopes_.ClassScope(cls);
    for (const auto& [name, value] : cls.params) WalkExpr(value, scope);
    WalkExprs(cls.extends_args, scope);
    for (const ClassMember* member : cls.members) {
      WalkType(member->data_type, scope);
      WalkExprs(member->unpacked_dims, scope);
      WalkExpr(member->init_expr, scope);
      WalkConstraints(member->constraint_items, scope);
      if (member->method != nullptr) WalkBody(*member->method, scope);
      if (member->nested_class != nullptr) WalkClass(*member->nested_class);
      if (member->covergroup != nullptr) {
        WalkCovergroup(*member->covergroup, scope);
      }
    }
  }

  void WalkGenerate(const ModuleItem& item, const ValueScope& outer) {
    WalkExpr(item.gen_cond, outer);
    for (const GenerateCaseItem& arm : item.gen_case_items) {
      WalkExprs(arm.patterns, outer);
      WalkGenerateBlock(arm.body, outer);
    }
    WalkGenerateBlock(item.gen_body, outer);
    if (item.gen_else != nullptr) WalkGenerate(*item.gen_else, outer);
  }

  void WalkGenerateBlock(const std::vector<ModuleItem*>& items,
                         const ValueScope& outer) {
    ValueScope scope{&outer};
    scopes_.DeclareItems(items, scope);
    WalkItems(items, scope);
  }

  void WalkInstance(const ModuleItem& item, const ValueScope& scope) {
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

  void WalkBind(const BindDirective& bind) {
    const ValueScope* target = scopes_.ModuleNamed(bind.target.path);
    if (target != nullptr) {
      WalkInstance(*bind.instantiation, *target);
    }
  }

  void WalkClocking(const ModuleItem& item, const ValueScope& scope) {
    WalkEvents(item.clocking_event, scope);
    for (const ClockingSignalDecl& signal : item.clocking_signals) {
      WalkExpr(signal.hier_expr, scope);
    }
  }

  void WalkItem(const ModuleItem& item, const ValueScope& scope) {
    WalkType(item.data_type, scope);
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
    if (item.covergroup != nullptr) WalkCovergroup(*item.covergroup, scope);
    if (item.nested_module_decl != nullptr) {
      WalkModule(*item.nested_module_decl);
    }
  }

  void WalkItems(const std::vector<ModuleItem*>& items,
                 const ValueScope& scope) {
    for (const ModuleItem* item : items) WalkItem(*item, scope);
  }

  void WalkModule(const ModuleDecl& decl) {
    const ValueScope& scope = scopes_.ModuleScope(decl);
    for (const auto& [name, value] : decl.params) WalkExpr(value, scope);
    for (const PortDecl& port : decl.ports) {
      WalkType(port.data_type, scope);
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

  ValueScopes scopes_;
  DiagEngine& diag_;
  std::unordered_set<const Expr*> reported_;
};

}  // namespace

void ReportBareCallsAsImplicitVariables(const CompilationUnit& unit,
                                        DiagEngine& diag) {
  ImplicitVariableWalk(unit, diag).WalkUnit(unit);
}

}  // namespace delta
