#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/checker_instance_assertion.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/multiclock_sequence_rules.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/semantic_leading_clocks.h"
#include "elaborator/sequence_match_class.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

void CheckConcurrentAssertionNoChandle(const ModuleItem* item,
                                       const RtlirModule* mod,
                                       DiagEngine& diag) {
  const Expr* bodies[] = {item->assert_expr, item->body != nullptr
                                                 ? item->body->assert_expr
                                                 : nullptr};
  for (const Expr* b : bodies) {
    std::string_view ch = ConcurrentAssertionExprReferencedChandle(b, mod);
    if (!ch.empty()) {
      diag.Error(item->loc,
                 "concurrent assertion expression references chandle "
                 "variable \"" +
                     std::string(ch) + "\"",
                 Subclause("16.6"));
      return;
    }
  }
}

void CheckConcurrentAssertionNoNonStaticMember(const ModuleItem* item,
                                               const RtlirModule* mod,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag) {
  const Expr* bodies[] = {item->assert_expr, item->body != nullptr
                                                 ? item->body->assert_expr
                                                 : nullptr};
  for (const Expr* b : bodies) {
    std::string ref =
        ConcurrentAssertionExprReferencedNonStaticMember(b, mod, unit);
    if (!ref.empty()) {
      diag.Error(item->loc,
                 "concurrent assertion expression references non-static "
                 "class member \"" +
                     ref + "\"",
                 Subclause("16.6"));
      return;
    }
  }
}

bool IsStaticDeferredAssertion(const ModuleItem* item) {
  return item->body != nullptr && item->body->is_deferred;
}

void AppendClockOnce(std::vector<EventExpr>& clock, const EventExpr& ev) {
  if (ev.signal == nullptr) return;
  for (const EventExpr& have : clock) {
    if (have.edge == ev.edge && SamePath(have.signal, ev.signal)) return;
  }
  clock.push_back(ev);
}

void CollectBodyClocks(const SeqLinearBody& body,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth);

void AppendInstanceClockEvents(EventExpr ev, const ActualsByFormal& actuals,
                               std::vector<EventExpr>& out);

void CollectInstanceSequenceClocks(const Expr* operand,
                                   const PropertyRegistry& registry,
                                   std::vector<EventExpr>& out, int depth) {
  const ModuleItem* decl =
      InstantiatedDecl(operand, ModuleItemKind::kSequenceDecl, registry);
  if (decl == nullptr) return;
  ActualsByFormal actuals = BindActualsWithDefaults(
      decl->prop_formals, decl->prop_formal_defaults, operand);
  for (const EventExpr& ev : decl->seq_clock) {
    AppendInstanceClockEvents(ev, actuals, out);
  }
  CollectBodyClocks(decl->seq_linear, registry, out, depth + 1);
}

void CollectBodiesClocks(const std::vector<SeqLinearBody>& bodies,
                         const PropertyRegistry& registry,
                         std::vector<EventExpr>& out, int depth) {
  for (const SeqLinearBody& inner : bodies) {
    CollectBodyClocks(inner, registry, out, depth);
  }
}

void CollectBodyClocks(const SeqLinearBody& body,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth) {
  for (const auto& clock : body.clocks) {
    for (const EventExpr& ev : clock) AppendClockOnce(out, ev);
  }
  if (depth < 4) {
    for (const Expr* operand : body.operands) {
      CollectInstanceSequenceClocks(operand, registry, out, depth);
    }
  }
  CollectBodiesClocks(body.intersects, registry, out, depth);
  CollectBodiesClocks(body.conjuncts, registry, out, depth);
  CollectBodiesClocks(body.alternatives, registry, out, depth);
}

void CollectTreeClocks(const PropertyExprNode* node,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth);

void AppendInstanceClockEvents(EventExpr ev, const ActualsByFormal& actuals,
                               std::vector<EventExpr>& out) {
  if (ev.signal != nullptr && ev.signal->kind == ExprKind::kIdentifier) {
    auto it = actuals.find(ev.signal->text);
    if (it != actuals.end() && IsEventActual(it->second)) {
      for (const EventExpr& event : EventsOfActual(it->second)) {
        AppendClockOnce(out, event);
      }
      return;
    }
    if (it != actuals.end() && it->second != nullptr) ev.signal = it->second;
  }
  AppendClockOnce(out, ev);
}

void CollectInstanceClocks(const Expr* instance,
                           const PropertyRegistry& registry,
                           std::vector<EventExpr>& out, int depth) {
  if (instance == nullptr || depth >= 4) return;
  const ModuleItem* decl =
      InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry);
  if (decl != nullptr) {
    ActualsByFormal actuals = BindActualsWithDefaults(
        decl->prop_formals, decl->prop_formal_defaults, instance);
    for (const EventExpr& ev : decl->prop_clock) {
      AppendInstanceClockEvents(ev, actuals, out);
    }
    CollectTreeClocks(decl->prop_body_tree, registry, out, depth + 1);
  }
  if (instance->kind != ExprKind::kCall) return;
  for (const Expr* arg : instance->args) {
    if (arg != nullptr) {
      CollectTreeClocks(arg->property_actual, registry, out, depth);
    }
  }
}

void CollectTreeClocks(const PropertyExprNode* node,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth) {
  if (node == nullptr) return;
  for (const EventExpr& ev : node->clock) AppendClockOnce(out, ev);
  if (node->sequence != nullptr) {
    CollectBodyClocks(node->sequence->seq_linear, registry, out, depth);
  }
  CollectInstanceClocks(node->boolean, registry, out, depth);
  for (const PropertyExprNode* operand : node->operands) {
    CollectTreeClocks(operand, registry, out, depth);
  }
}

Stmt* NewInstanceStmt(const ModuleItem* item, Arena& arena) {
  auto* stmt = arena.Create<Stmt>();
  switch (item->kind) {
    case ModuleItemKind::kAssumeProperty:
      stmt->kind = StmtKind::kAssumeImmediate;
      break;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      stmt->kind = StmtKind::kCoverImmediate;
      break;
    default:
      stmt->kind = StmtKind::kAssertImmediate;
      break;
  }
  stmt->cover_sequence = item->kind == ModuleItemKind::kCoverSequence;
  stmt->range.start = item->loc;
  stmt->label = item->name;
  return stmt;
}

void GiveSequenceProperty(Stmt* stmt, Expr* instance, Arena& arena) {
  stmt->assert_property = arena.Create<PropertyExprNode>();
  stmt->assert_property->kind = PropertyExprNode::Kind::kSequence;
  stmt->assert_property->sequence = SequenceInstanceBody(instance, arena);
  stmt->assert_property->strong =
      stmt->kind == StmtKind::kCoverImmediate || stmt->assert_strong;
}

bool SubstituteSequenceInstance(ModuleItem* item, const ModuleItem* decl,
                                const PropertyRegistry& registry,
                                Arena& arena) {
  auto* stmt = NewInstanceStmt(item, arena);
  stmt->assert_expr = item->assert_expr;
  GiveSequenceProperty(stmt, item->assert_expr, arena);
  stmt->is_concurrent_clocked = true;
  stmt->assert_pass_stmt = item->assert_pass_stmt;
  stmt->assert_fail_stmt = item->assert_fail_stmt;
  item->sensitivity =
      SequenceInstanceClock(decl, item->assert_expr, registry, arena);
  item->body = stmt;
  return true;
}

void GiveInstanceBody(Stmt* stmt, Expr* instance, const ModuleItem* decl,
                      const ActualsByFormal& actuals, Arena& arena) {
  if (TakesBooleanSubstitution(instance, decl)) {
    stmt->assert_expr = SubstituteFormals(decl->prop_body_expr, actuals, arena);
    stmt->assert_negated = decl->prop_negated;
    return;
  }
  stmt->assert_expr = instance;
  stmt->assert_property = arena.Create<PropertyExprNode>();
  stmt->assert_property->boolean = instance;
}

bool PropertyInstanceIsEvaluated(const ModuleItem* item, const ModuleItem* decl,
                                 DiagEngine& diag) {
  std::string name(item->prop_instance_name);
  if (decl->prop_body_expr == nullptr && decl->prop_body_tree == nullptr) {
    diag.Warning(item->loc,
                 "concurrent assertion is not evaluated: the body of property "
                 "\"" +
                     name +
                     "\" is not the @(event) boolean_expression this tool "
                     "evaluates",
                 Subclause("16.14"));
    return false;
  }
  return true;
}

void SubstitutePropertyInstance(ModuleItem* item, Arena& arena,
                                const PropertyRegistry& registry,
                                const InferredAtInstance& inferred,
                                DiagEngine& diag) {
  if (item->prop_instance_name.empty() || item->body != nullptr) return;
  const ModuleItem* decl = registry.Find(item->prop_instance_name);
  std::string name(item->prop_instance_name);
  if (decl != nullptr) NameInstanceByKey(item, arena);
  FillInferredDefaults(item->assert_expr, decl, inferred, arena, &diag);
  if (decl == nullptr || decl->kind != ModuleItemKind::kPropertyDecl) {
    item->prop_instance_name = {};
  }
  if (decl != nullptr && decl->kind == ModuleItemKind::kSequenceDecl) {
    SubstituteSequenceInstance(item, decl, registry, arena);
    return;
  }
  if (decl == nullptr || decl->kind != ModuleItemKind::kPropertyDecl) {
    SubstituteBooleanSpec(item, arena);
    return;
  }
  if (!PropertyInstanceIsEvaluated(item, decl, diag)) return;
  ActualsByFormal actuals;
  const std::vector<Expr*>& args = item->assert_expr->args;
  for (size_t i = 0; i < decl->prop_formals.size(); ++i) {
    if (i >= args.size() || args[i] == nullptr) {
      diag.Warning(item->loc,
                   "concurrent assertion is not evaluated: the instance of "
                   "property \"" +
                       name + "\" binds no actual argument to the formal \"" +
                       std::string(decl->prop_formals[i]) + "\"",
                   Subclause("16.14"));
      return;
    }
    actuals[decl->prop_formals[i]] =
        CastUntypedActual(args[i], decl->prop_formal_type_kw[i], arena);
  }
  auto* stmt = NewInstanceStmt(item, arena);
  GiveInstanceBody(stmt, item->assert_expr, decl, actuals, arena);
  stmt->assert_disable_iff =
      SubstituteFormals(decl->prop_disable_iff, actuals, arena);
  stmt->is_concurrent_clocked = true;
  stmt->assert_pass_stmt = item->assert_pass_stmt;
  stmt->assert_fail_stmt = item->assert_fail_stmt;
  item->sensitivity = PropertyInstanceClock(decl, actuals, registry, arena);
  item->body = stmt;
}

void PromotePropertyInstanceBoolean(ModuleItem* item, Arena& arena,
                                    const PropertyRegistry& registry,
                                    const InferredAtInstance& inferred) {
  Stmt* stmt = item->body;
  if (stmt == nullptr || stmt->assert_property != nullptr ||
      stmt->assert_sequence != nullptr || stmt->assert_expr == nullptr) {
    return;
  }
  Expr* instance = QualifiedInstance(stmt->assert_expr, registry, arena);
  if (instance->kind != ExprKind::kIdentifier &&
      instance->kind != ExprKind::kCall) {
    return;
  }
  const ModuleItem* decl = registry.FindInstance(instance);
  if (decl != nullptr && decl->kind == ModuleItemKind::kSequenceDecl) {
    GiveSequenceProperty(stmt, instance, arena);
    return;
  }
  if (decl == nullptr || decl->kind != ModuleItemKind::kPropertyDecl ||
      decl->prop_body_tree == nullptr) {
    return;
  }
  InferredAtInstance here = inferred;
  here.clock = item->sensitivity;
  FillInferredDefaults(instance, decl, here, arena);
  if (TakesBooleanSubstitution(instance, decl)) return;
  auto* root = arena.Create<PropertyExprNode>();
  root->boolean = stmt->assert_expr;
  if (stmt->assert_negated) {
    auto* whole = arena.Create<PropertyExprNode>();
    whole->kind = PropertyExprNode::Kind::kNot;
    whole->operands.push_back(root);
    root = whole;
  }
  stmt->assert_property = root;
  if (stmt->assert_disable_iff == nullptr) {
    stmt->assert_disable_iff = SubstituteFormals(
        decl->prop_disable_iff,
        BindActualsWithDefaults(decl->prop_formals, decl->prop_formal_defaults,
                                instance),
        arena);
  }
}

}  // namespace

void SubstituteBooleanSpec(ModuleItem* item, Arena& arena) {
  auto* stmt = NewInstanceStmt(item, arena);
  stmt->assert_expr = item->assert_expr;
  stmt->is_concurrent_clocked = true;
  stmt->assert_pass_stmt = item->assert_pass_stmt;
  stmt->assert_fail_stmt = item->assert_fail_stmt;
  item->body = stmt;
}

void Elaborator::ElaborateSequenceDeclItem(ModuleItem* item, RtlirModule* mod) {
  ResolveClassScopedFormalTypes(*item, unit_, BuildParamScope(mod), typedefs_,
                                arena_);
  sequence_names_.insert(item->name);
  mod->sequence_decls.push_back(item);
  mod->assertion_item_decls.push_back(
      RtlirAssertionItemDecl{item, {}, {}, nullptr});
  item->seq_triggered_unread = !unit_->triggered_names.contains(item->name);
  if (property_registry_.HasCyclicSequenceDependency(item)) {
    diag_.Error(item->loc,
                "cyclic dependency among named sequences involving \"" +
                    std::string(item->name) + "\"",
                Subclause("16.8"));
  }
  ValidateNoFormalShadowedByBodyLocal(item);
  ValidateClockingBlock(item, mod);
  if (!item->seq_clock.empty()) {
    ValidateMulticlockSequence(item, item->seq_clock, item->loc,
                               property_registry_, diag_);
  }
}

void Elaborator::CheckPropertyOperandInstances(const ModuleItem* item) {
  for (auto operand_ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(operand_ref);
    if (callee == nullptr || callee->kind != ModuleItemKind::kPropertyDecl) {
      continue;
    }
    if (property_registry_.FlattenedDisableIffCount(callee) > 0) {
      diag_.Error(item->loc,
                  "property \"" + std::string(operand_ref) +
                      "\" has a disable iff clause and cannot be used as an "
                      "operand of a property operator in \"" +
                      std::string(item->name) + "\"",
                  Subclause("16.12.1"));
    }
  }
}

static std::string_view DisableIffOperand(const PropertyExprNode* node,
                                          const PropertyRegistry& registry,
                                          int depth) {
  if (node == nullptr || depth > 64) return {};
  bool is_operator = node->kind != PropertyExprNode::Kind::kBoolean &&
                     node->kind != PropertyExprNode::Kind::kSequence;
  for (const PropertyExprNode* operand : node->operands) {
    if (operand == nullptr) continue;
    if (is_operator && operand->kind == PropertyExprNode::Kind::kBoolean) {
      const ModuleItem* decl = InstantiatedDecl(
          operand->boolean, ModuleItemKind::kPropertyDecl, registry);
      if (decl != nullptr && registry.FlattenedDisableIffCount(decl) > 0) {
        return decl->name;
      }
    }
    std::string_view hit = DisableIffOperand(operand, registry, depth + 1);
    if (!hit.empty()) return hit;
  }
  return {};
}

static void ReportDisableIffOperand(const PropertyExprNode* root,
                                    const PropertyRegistry& registry,
                                    SourceLoc loc, const ModuleItem* in,
                                    DiagEngine& diag) {
  std::string_view name = DisableIffOperand(root, registry, 0);
  if (name.empty()) return;
  std::string msg = "property \"" + std::string(name) +
                    "\" has a disable iff clause and cannot be used as an "
                    "operand of a property operator";
  if (in != nullptr) {
    for (std::string_view reported : in->prop_negated_instance_refs) {
      if (reported == name) return;
    }
    msg += " in \"" + std::string(in->name) + "\"";
  }
  diag.Error(loc, msg, Subclause("16.12.1"));
}

void PromoteSequenceInstancesInProperties(const ModuleDecl* decl,
                                          const PropertyRegistry& registry,
                                          Arena& arena) {
  for (ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      PromoteSequenceInstances(item->prop_body_tree, registry, arena);
    }
  }
}

void Elaborator::ElaboratePropertyDeclItem(ModuleItem* item, RtlirModule* mod) {
  ResolveClassScopedFormalTypes(*item, unit_, BuildParamScope(mod), typedefs_,
                                arena_);
  mod->property_decls.push_back(item);
  mod->assertion_item_decls.push_back(
      RtlirAssertionItemDecl{item, {}, {}, nullptr});
  ValidateSequenceDegeneracy(item->prop_body_tree, item->loc,
                             property_registry_, diag_);
  ValidateMulticlockSequences(item->prop_body_tree, item->prop_clock, item->loc,
                              property_registry_, diag_);
  if (property_registry_.FlattenedDisableIffCount(item) > 1) {
    diag_.Error(item->loc,
                "property \"" + std::string(item->name) +
                    "\" nests disable iff clauses",
                Subclause("16.12"));
  }
  CheckPropertyOperandInstances(item);
  ReportDisableIffOperand(item->prop_body_tree, property_registry_, item->loc,
                          item, diag_);
  ValidateNoFormalShadowedByBodyLocal(item);
  ValidateRecursiveProperty(item);
  ValidateClockingBlock(item, mod);
}

static void ReportNoLeadingClock(SourceLoc loc, DiagEngine& diag) {
  diag.Error(loc,
             "concurrent assertion has no leading clocking event: none is "
             "written, no default clocking is in scope and the property "
             "is no instance of a sequence or property declared with a "
             "unique leading clocking event",
             Subclause("16.16"));
}

void Elaborator::ResolveStaticAssertionClock(
    ModuleItem* item, const std::vector<EventExpr>& default_clock) {
  if (item->body == nullptr || item->body->is_deferred) return;
  if (item->sensitivity.empty()) {
    item->sensitivity = default_clock;
    item->body->assert_clock_inferred = !default_clock.empty();
    item->body->assert_clock_from_default_clocking =
        item->body->assert_clock_inferred;
  }
  if (item->sensitivity.empty()) {
    ReportNoLeadingClock(item->loc, diag_);
    item->body = nullptr;
    return;
  }
  if (!HasUniqueSemanticLeadingClock(item->body->assert_property,
                                     item->sensitivity, property_registry_)) {
    diag_.Error(item->loc, "the property has no unique semantic leading clock",
                Subclause("16.16.1"));
    item->body = nullptr;
  }
}

static InferredAtInstance InferredAt(const RtlirModule* mod) {
  InferredAtInstance inferred;
  inferred.clock = DefaultClockingEvent(mod);
  inferred.disable = mod != nullptr ? mod->default_disable_iff : nullptr;
  return inferred;
}

static void ElaborateRestrictPropertyItem(ModuleItem* item,
                                          const RtlirModule* mod, Arena& arena,
                                          const PropertyRegistry& registry,
                                          DiagEngine& diag) {
  const InferredAtInstance kInferred = InferredAt(mod);
  diag.PushSuppress();
  SubstitutePropertyInstance(item, arena, registry, kInferred, diag);
  diag.PopSuppress();
  Stmt* body = item->body;
  if (body == nullptr) return;
  if (body->assert_disable_iff == nullptr) {
    body->assert_disable_iff = kInferred.disable;
  }
  if (item->sensitivity.empty()) {
    item->sensitivity = kInferred.clock;
    body->assert_clock_inferred = !kInferred.clock.empty();
    body->assert_clock_from_default_clocking = body->assert_clock_inferred;
  }
  if (item->sensitivity.empty()) ReportNoLeadingClock(item->loc, diag);
  if (body->assert_clock.empty()) body->assert_clock = item->sensitivity;
}

static ModuleItem* GlobalClockInstanceActuals(
    ModuleItem* item, const std::vector<EventExpr>* global_event,
    Arena& arena) {
  if (global_event == nullptr || item->body != nullptr ||
      item->prop_instance_name.empty()) {
    return item;
  }
  Expr* call = SubstituteGlobalClockInInstanceActuals(item->assert_expr,
                                                      *global_event, arena);
  if (call == item->assert_expr) return item;
  auto* copy = arena.Create<ModuleItem>(*item);
  copy->assert_expr = call;
  return copy;
}

static void RecordGlobalLeadingClock(const ModuleItem* item, RtlirModule* mod,
                                     const std::vector<EventExpr>* global_event,
                                     Arena& arena) {
  if (mod == nullptr || mod->assertions.empty() || global_event == nullptr ||
      item->body == nullptr) {
    return;
  }
  auto* clock = arena.Create<std::vector<EventExpr>>(item->body->assert_clock);
  if (SubstituteGlobalClockLeadingEvent(*clock, *global_event)) {
    mod->assertions.back().leading_clock = clock;
  }
}

void Elaborator::ElaborateAssertPropertyItem(ModuleItem* item,
                                             RtlirModule* mod) {
  item = CheckerInstanceAssertion(item, mod, checker_tree_actuals_,
                                  property_registry_, arena_);
  item =
      GlobalClockInstanceActuals(item, module_global_clocking_event_, arena_);
  InferredAtInstance inferred = InferredAt(mod);
  SubstitutePropertyInstance(item, arena_, property_registry_, inferred, diag_);
  PromotePropertyInstanceBoolean(item, arena_, property_registry_, inferred);
  if (item->body != nullptr && item->body->assert_disable_iff == nullptr) {
    item->body->assert_disable_iff = inferred.disable;
  }
  ResolveStaticAssertionClock(item, inferred.clock);
  if (item->body != nullptr) {
    PromoteSequenceInstances(item->body->assert_property, property_registry_,
                             arena_);
  }
  CheckConcurrentAssertionNoChandle(item, mod, diag_);
  CheckConcurrentAssertionNoNonStaticMember(item, mod, unit_, diag_);
  if (item->body != nullptr) {
    ReportDisableIffOperand(item->body->assert_property, property_registry_,
                            item->loc, nullptr, diag_);
    ValidateSequenceDegeneracy(item->body->assert_property, item->loc,
                               property_registry_, diag_);
    ValidateSequenceUsedAsProperty(item->body->assert_sequence, item->loc,
                                   property_registry_, diag_);
    if (item->body->assert_clock.empty()) {
      item->body->assert_clock = item->sensitivity;
    }
    std::vector<EventExpr> named;
    CollectTreeClocks(item->body->assert_property, property_registry_, named,
                      0);
    for (const EventExpr& ev : named) AppendClockOnce(item->sensitivity, ev);
    ValidateMulticlockSequences(item->body->assert_property,
                                item->body->assert_clock, item->loc,
                                property_registry_, diag_);
    ValidateMulticlockSequence(item->body->assert_sequence,
                               item->body->assert_clock, item->loc,
                               property_registry_, diag_);
  }
  const ProcessBuildEnv kEnv{arena_, diag_, &inference_funcs_, &const_names_,
                             module_global_clocking_event_};
  if (IsStaticDeferredAssertion(item)) {
    AddStaticAssertionProcess(RtlirProcessKind::kAlwaysComb, item, mod, kEnv);
    return;
  }
  if (item->body != nullptr && !item->sensitivity.empty()) {
    AddStaticAssertionProcess(RtlirProcessKind::kAlwaysFF, item, mod, kEnv);
    mod->processes.back().is_concurrent_clocked =
        item->body->is_concurrent_clocked;
    if (module_global_clocking_event_ != nullptr &&
        FindGclkFunctionRefInItem(item, IsGlobalClockingFutureFunction, true) !=
            nullptr) {
      mod->processes.back().gclk_future_event = *module_global_clocking_event_;
    }
    return;
  }
  ValidateClockingBlock(item, mod);
}

static void RecordClockingBlock(ModuleItem* item, RtlirModule* mod) {
  mod->clocking_blocks.push_back(item);
  for (ModuleItem* decl : item->clocking_decls) {
    if (decl->kind == ModuleItemKind::kPropertyDecl) {
      mod->property_decls.push_back(decl);
    } else {
      mod->sequence_decls.push_back(decl);
    }
    mod->assertion_item_decls.push_back(
        RtlirAssertionItemDecl{decl, {}, {}, item});
  }
}

static bool IsAssertionItem(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
      return true;
    default:
      return false;
  }
}

bool Elaborator::ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod) {
  if (mod != nullptr && IsAssertionItem(item->kind)) {
    RtlirAssertion assertion;
    assertion.item = item;
    mod->assertions.push_back(assertion);
  }
  switch (item->kind) {
    case ModuleItemKind::kSequenceDecl:
      ElaborateSequenceDeclItem(item, mod);
      return true;
    case ModuleItemKind::kPropertyDecl:
      ElaboratePropertyDeclItem(item, mod);
      return true;
    case ModuleItemKind::kAssertProperty:
      ElaborateAssertPropertyItem(item, mod);
      break;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      if (FindConcurrentAssertionInPassStmt(item->assert_pass_stmt) !=
          nullptr) {
        diag_.Error(item->loc,
                    "the pass statement of a cover statement may not include a "
                    "concurrent assert, assume, or cover statement",
                    Subclause("16.14.3"));
      }
      ElaborateAssertPropertyItem(item, mod);
      break;
    case ModuleItemKind::kAssumeProperty:
      ElaborateAssertPropertyItem(item, mod);
      break;
    case ModuleItemKind::kRestrictProperty:
      ValidateClockingBlock(item, mod);
      ElaborateRestrictPropertyItem(item, mod, arena_, property_registry_,
                                    diag_);
      break;
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item, mod);
      if (mod != nullptr) RecordClockingBlock(item, mod);
      return true;
    default:
      return true;
  }
  RecordGlobalLeadingClock(item, mod, module_global_clocking_event_, arena_);
  return true;
}

}  // namespace delta
