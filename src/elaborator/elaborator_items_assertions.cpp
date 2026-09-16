#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/multiclock_sequence_rules.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sequence_match_class.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

// §16.14.3: a cover statement may have an optional pass statement
// (statement_or_null), and that pass statement "shall not include any
// concurrent assert, assume, or cover statement". A procedural concurrent
// assertion is parsed as an assert/assume/cover-immediate Stmt that carries
// is_procedural_concurrent; ordinary immediate assertions leave that flag clear
// and remain permitted. Returns the first offending statement, or nullptr when
// the pass statement contains none.
//
// §16.14.3 says "include" and names no statement the prohibition is lifted in,
// so this descends every link ForEachChildStmt in
// elaborator_validate_internal.h names. It wrote out nine of the thirteen, so a
// concurrent assertion written in a randcase arm or a randsequence code block
// was not found and the cover statement holding it elaborated clean. Two of the
// four links it now reaches cannot hold one: A.6.8 admits in a
// for_initialization only a list_of_variable_assignments or a
// for_variable_declaration, and in a for_step only an operator_assignment, an
// inc_or_dec_expression or a function_subroutine_call, so no assertion
// statement stands in a for header. Descending them costs nothing and keeps the
// walk from naming any link itself.
//
// ForEachChildStmt gives the visitor no way to stop, so the first offending
// statement is kept in `hit` and the recursion runs only while `hit` is null.
// That is what makes this walk report the first one in source order rather than
// whichever link the list happens to visit last.
const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s) {
  if (s == nullptr) return nullptr;
  if (s->is_procedural_concurrent && (s->kind == StmtKind::kAssertImmediate ||
                                      s->kind == StmtKind::kAssumeImmediate ||
                                      s->kind == StmtKind::kCoverImmediate)) {
    return s;
  }
  const Stmt* hit = nullptr;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (hit) return;
    hit = FindConcurrentAssertionInPassStmt(sub);
  });
  return hit;
}

// §16.6: an expression appearing in a concurrent assertion shall not reference
// a variable of chandle type. A concurrent assertion statement
// (assert/assume/cover/restrict property) keeps its property_spec expression in
// assert_expr, or, for the simple clocked boolean form, in the immediate body
// statement's assert_expr. Reports the first chandle reference once.
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

bool IsStaticDeferredAssertion(const ModuleItem* item) {  // §16.4.3
  return item->body != nullptr && item->body->is_deferred;
}

// §16.12.1: an instance of a named property can be used as a property_spec,
// and the assertion is then legal provided the property's body, substituted in
// place of the instance, is a legal property_spec. The parser records the name
// of an argument-less instance in prop_instance_name (see
// Parser::TryParsePropertyInstanceSpec); this makes the substitution when the
// body is the clocked boolean form the parser captured, giving `item` the
// clock and body an assertion written in that form has, so the caller lowers
// it to the same process. The property may name no formals, since an instance
// without arguments binds none; §16.12.1 puts substitution of actuals for
// formals ahead of the check, and there are none to substitute.
//
// §16.13: `ev` appended to `clock` unless an event of the same edge over a
// signal of the same spelling is there.
void AppendClockOnce(std::vector<EventExpr>& clock, const EventExpr& ev) {
  if (ev.signal == nullptr) return;
  for (const EventExpr& have : clock) {
    if (have.edge == ev.edge && have.signal != nullptr &&
        have.signal->text == ev.signal->text) {
      return;
    }
  }
  clock.push_back(ev);
}

void CollectBodyClocks(const SeqLinearBody& body,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth);

void CollectBodiesClocks(const std::vector<SeqLinearBody>& bodies,
                         const PropertyRegistry& registry,
                         std::vector<EventExpr>& out, int depth) {
  for (const SeqLinearBody& inner : bodies) {
    CollectBodyClocks(inner, registry, out, depth);
  }
}

// §16.13.1: the clocks the operands of a sequence body name, the bodies of
// the sequences it instantiates walked too, to a depth that reads a body
// once.
void CollectBodyClocks(const SeqLinearBody& body,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth) {
  for (const auto& clock : body.clocks) {
    for (const EventExpr& ev : clock) AppendClockOnce(out, ev);
  }
  if (depth < 4) {
    for (const Expr* operand : body.operands) {
      const ModuleItem* decl =
          InstantiatedDecl(operand, ModuleItemKind::kSequenceDecl, registry);
      if (decl != nullptr) {
        // §16.13.3: a sequence declared with a clock is evaluated on it.
        for (const EventExpr& ev : decl->seq_clock) AppendClockOnce(out, ev);
        CollectBodyClocks(decl->seq_linear, registry, out, depth + 1);
      }
    }
  }
  CollectBodiesClocks(body.intersects, registry, out, depth);
  CollectBodiesClocks(body.conjuncts, registry, out, depth);
  CollectBodiesClocks(body.alternatives, registry, out, depth);
}

void CollectTreeClocks(const PropertyExprNode* node,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth);

// §16.13.2 by way of §16.8.1: one event of an instantiated property's
// declared clock with the actual in the formal's place, for the process to
// wake on: an event actual supplies the edge and the signal, and any other
// stands as the signal under the edge the clock wrote.
EventExpr InstanceClockEvent(EventExpr ev, const ActualsByFormal& actuals) {
  if (ev.signal == nullptr || ev.signal->kind != ExprKind::kIdentifier) {
    return ev;
  }
  auto it = actuals.find(ev.signal->text);
  if (it == actuals.end() || it->second == nullptr) return ev;
  Expr* actual = it->second;
  if (actual->kind == ExprKind::kUnary &&
      (actual->op == TokenKind::kKwPosedge ||
       actual->op == TokenKind::kKwNegedge ||
       actual->op == TokenKind::kKwEdge)) {
    ev.edge = actual->op == TokenKind::kKwPosedge   ? Edge::kPosedge
              : actual->op == TokenKind::kKwNegedge ? Edge::kNegedge
                                                    : Edge::kEdge;
    ev.signal = actual->lhs;
    return ev;
  }
  ev.signal = actual;
  return ev;
}

// §16.13: the clocks an instance among the tree's booleans brings: those of
// the body of the property it instantiates and of the sequences and
// properties it takes as actuals.
void CollectInstanceClocks(const Expr* instance,
                           const PropertyRegistry& registry,
                           std::vector<EventExpr>& out, int depth) {
  if (instance == nullptr || depth >= 4) return;
  const ModuleItem* decl =
      InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry);
  if (decl != nullptr) {
    // §16.13.2: a property declared with a clock is evaluated on it, the
    // actuals in the formals' places.
    ActualsByFormal actuals = BindActuals(decl->prop_formals, instance);
    for (const EventExpr& ev : decl->prop_clock) {
      AppendClockOnce(out, InstanceClockEvent(ev, actuals));
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

// §16.13: the clocks the sequences of the tree name, those of the bodies of
// the properties it instantiates and of the sequences and properties its
// instances take as actuals included, for the assertion's process to wake
// on beside its leading clock.
void CollectTreeClocks(const PropertyExprNode* node,
                       const PropertyRegistry& registry,
                       std::vector<EventExpr>& out, int depth) {
  if (node == nullptr) return;
  // §16.13.2: an operand's own clock.
  for (const EventExpr& ev : node->clock) AppendClockOnce(out, ev);
  if (node->sequence != nullptr) {
    CollectBodyClocks(node->sequence->seq_linear, registry, out, depth);
  }
  CollectInstanceClocks(node->boolean, registry, out, depth);
  for (const PropertyExprNode* operand : node->operands) {
    CollectTreeClocks(operand, registry, out, depth);
  }
}

// The statement the elaborator makes for an assertion whose spec is an
// instance of a named sequence or property: the parser's kinds for the
// assert, assume and cover directives, a cover of either category running
// no fail statement and reporting no failure, a cover sequence marked for
// §16.14.3's results, and, §16.14, the item's label as a level of the name
// its action block reports, as the parser gives a body it makes itself.
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

// §16.13.4: an instance of a named sequence standing as the whole
// property_spec, `assert property (mult_s)`, is the sequential property the
// sequence is, evaluated on the clock the sequence is declared with.
bool SubstituteSequenceInstance(ModuleItem* item, const ModuleItem* decl,
                                Arena& arena) {
  // §16.16: a sequence declared with no clock leaves the statement its
  // clock to determine, the default clocking's or none.
  auto* stmt = NewInstanceStmt(item, arena);
  stmt->assert_expr = item->assert_expr;
  stmt->assert_property = arena.Create<PropertyExprNode>();
  stmt->assert_property->kind = PropertyExprNode::Kind::kSequence;
  stmt->assert_property->sequence =
      SequenceInstanceBody(item->assert_expr, arena);
  stmt->is_concurrent_clocked = true;
  stmt->assert_pass_stmt = item->assert_pass_stmt;
  stmt->assert_fail_stmt = item->assert_fail_stmt;
  item->sensitivity = decl->seq_clock;
  item->body = stmt;
  return true;
}

// The body the statement of the instance `instance` of `decl` carries: the
// boolean with the actuals substituted where the body is the clocked
// boolean form and every actual an expression, and otherwise, §16.12.17, a
// tree whose root is the instance, expanded at the run, its recursion
// included, with the actuals substituted there.
void GiveInstanceBody(Stmt* stmt, Expr* instance, const ModuleItem* decl,
                      const ActualsByFormal& actuals, Arena& arena) {
  if (decl->prop_body_expr != nullptr && !InstanceHasTreeActual(instance)) {
    stmt->assert_expr = SubstituteFormals(decl->prop_body_expr, actuals, arena);
    stmt->assert_negated = decl->prop_negated;
    return;
  }
  stmt->assert_expr = instance;
  stmt->assert_property = arena.Create<PropertyExprNode>();
  stmt->assert_property->boolean = instance;
}

// Whether the instance `item` of `decl` is one this tool evaluates, which
// needs `decl` to be a property whose body it reads and a clock, the
// property's own or the one flowing from its body; each want is reported
// under the rule Parser::WarnUnevaluatedConcurrentAssertion states.
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
  // §16.16: a property declared with no clock, and none flowing into it,
  // leaves the statement its clock to determine.
  return true;
}

// §16.16 (a): a spec that is one name which names no property or sequence
// is the boolean that name reads as, its clock the default clocking's; the
// statement is made as the parser makes one for a clocked boolean.
void SubstituteBooleanSpec(ModuleItem* item, Arena& arena) {
  auto* stmt = NewInstanceStmt(item, arena);
  stmt->assert_expr = item->assert_expr;
  stmt->is_concurrent_clocked = true;
  stmt->assert_pass_stmt = item->assert_pass_stmt;
  stmt->assert_fail_stmt = item->assert_fail_stmt;
  item->body = stmt;
}

// The rewrite is made on `item`, which every instance of the module shares,
// and it is made once: the property declaration is the same for every
// instance, so the second instance finds the body already there. Reports the
// assertion unevaluated, under the rule
// Parser::WarnUnevaluatedConcurrentAssertion states, when the name is no
// property's or the body is not that form; the parser left the report to here
// because it could not tell the two apart.
void SubstitutePropertyInstance(ModuleItem* item, Arena& arena,
                                const PropertyRegistry& registry,
                                const InferredAtInstance& inferred,
                                DiagEngine& diag) {
  if (item->prop_instance_name.empty() || item->body != nullptr) return;
  const ModuleItem* decl = registry.Find(item->prop_instance_name);
  std::string name(item->prop_instance_name);
  // §16.14.7: the instance is the top-level property expression of the
  // assertion statement, so the inferred functions among the defaults are
  // replaced by what is inferred at the statement, the default clocking and
  // the default disable iff in scope.
  FillInferredDefaults(item->assert_expr, decl, inferred, arena);
  if (decl != nullptr && decl->kind == ModuleItemKind::kSequenceDecl) {
    SubstituteSequenceInstance(item, decl, arena);
    return;
  }
  if (decl == nullptr || decl->kind != ModuleItemKind::kPropertyDecl) {
    SubstituteBooleanSpec(item, arena);
    return;
  }
  if (!PropertyInstanceIsEvaluated(item, decl, diag)) return;
  // §16.13.3 and §16.13.4: a property declared with no clock whose body is
  // a sequence declared with one is on that clock, `mult_p2` being
  // `mult_s`.
  const std::vector<EventExpr>& clock = decl->prop_clock.empty()
                                            ? FlowedBodyClock(decl, registry)
                                            : decl->prop_clock;
  // §16.12 and §16.8: the actual arguments of the instance are bound to the
  // formals by position, and §F.4.1's rewriting substitutes each for the
  // references to its formal in the clock, the disable condition and the
  // boolean. A formal left to its default actual, which this tool does not
  // keep, leaves the assertion unevaluated; the count of actuals against
  // formals is validated where §16.8's rules are.
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
    actuals[decl->prop_formals[i]] = args[i];
  }
  auto* stmt = NewInstanceStmt(item, arena);
  GiveInstanceBody(stmt, item->assert_expr, decl, actuals, arena);
  stmt->assert_disable_iff =
      SubstituteFormals(decl->prop_disable_iff, actuals, arena);
  stmt->is_concurrent_clocked = true;
  stmt->assert_pass_stmt = item->assert_pass_stmt;
  stmt->assert_fail_stmt = item->assert_fail_stmt;
  item->sensitivity.clear();
  for (const EventExpr& ev : clock) {
    item->sensitivity.push_back(SubstituteClockEvent(ev, actuals, arena));
  }
  item->body = stmt;
}

// §16.12.1 and §16.12.17: a clocked assertion whose boolean is an instance
// of a named property whose body is a tree, `@(posedge clk) prop_always(a)`,
// which the parser read as a boolean because a call and a variable's name
// read the same. The statement is given the instance as the root of a tree
// so that the evaluator expands it, its recursion included; a `not` before
// the instance negates the tree.
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
  const ModuleItem* decl = registry.Find(
      instance->kind == ExprKind::kCall ? instance->callee : instance->text);
  if (decl == nullptr || decl->kind != ModuleItemKind::kPropertyDecl ||
      decl->prop_body_tree == nullptr) {
    return;
  }
  // §16.14.7: the clocking event the assertion opens with is what is
  // inferred at the instance, and the default disable iff in scope.
  InferredAtInstance here = inferred;
  here.clock = item->sensitivity;
  FillInferredDefaults(instance, decl, here, arena);
  // §16.12.18: an instance of the clocked boolean form is left as the
  // boolean it was read as unless an actual is a tree, which the boolean
  // does not read.
  if (decl->prop_body_expr != nullptr && !InstanceHasTreeActual(instance)) {
    return;
  }
  auto* root = arena.Create<PropertyExprNode>();
  root->boolean = stmt->assert_expr;
  if (stmt->assert_negated) {
    auto* whole = arena.Create<PropertyExprNode>();
    whole->kind = PropertyExprNode::Kind::kNot;
    whole->operands.push_back(root);
    root = whole;
  }
  stmt->assert_property = root;
  // §16.15: the disable iff clause the property declares is the instance's
  // own, the actuals in the formals' places, ahead of any default.
  if (stmt->assert_disable_iff == nullptr) {
    stmt->assert_disable_iff =
        SubstituteFormals(decl->prop_disable_iff,
                          BindActuals(decl->prop_formals, instance), arena);
  }
}

}  // namespace

void Elaborator::ElaborateSequenceDeclItem(ModuleItem* item, RtlirModule* mod) {
  sequence_names_.insert(item->name);
  mod->sequence_decls.push_back(item);
  // §16.8: a cyclic dependency among named sequences is an error. All sequence
  // decls are registered before elaboration (see ElaborateModule), so this DFS
  // sees the full graph regardless of declaration order.
  if (property_registry_.HasCyclicSequenceDependency(item)) {
    diag_.Error(item->loc,
                "cyclic dependency among named sequences involving \"" +
                    std::string(item->name) + "\"",
                Subclause("16.8"));
  }
  // §16.10: a formal-argument name may not be redeclared as a body local.
  ValidateNoFormalShadowedByBodyLocal(item);
  ValidateClockingBlock(item, mod);
}

// §16.12.1: an instance of a named property used as a property_expr operand of
// any property-building operator must, once substituted, yield a legal
// property_expr. A disable iff clause makes the flattened body a property_spec,
// which is not a legal operand -- so such a property may not carry a disable
// iff clause when it appears as an operand. The parser records the instances
// that stand as the operand of a prefix or infix property operator (not,
// s_nexttime, s_eventually, s_always, and the right operand of
// s_until/s_until_with) in prop_negated_instance_refs.
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
  mod->property_decls.push_back(item);
  // §16.12.22: the sequences the body uses as properties and as antecedents
  // are checked where the body is declared, once for every instance.
  ValidateSequenceDegeneracy(item->prop_body_tree, item->loc,
                             property_registry_, diag_);
  ValidateMulticlockSequences(item->prop_body_tree, item->prop_clock, item->loc,
                              property_registry_, diag_);
  // §16.12: nesting of disable iff (explicitly or via property instantiation)
  // is forbidden; the §F.4.1 flattened count catches both.
  if (property_registry_.FlattenedDisableIffCount(item) > 1) {
    diag_.Error(item->loc,
                "property \"" + std::string(item->name) +
                    "\" nests disable iff clauses",
                Subclause("16.12"));
  }
  CheckPropertyOperandInstances(item);
  // §16.10: a formal-argument name may not be redeclared as a body local.
  ValidateNoFormalShadowedByBodyLocal(item);
  // §16.12.17 / §F.7: enforce the restrictions on recursive properties.
  ValidateRecursiveProperty(item);
  ValidateClockingBlock(item, mod);
}

// §16.16: the leading clocking event of a static concurrent assertion
// statement: (d) the one its spec opens with, or the one the instance its
// maximal property is determines, its declaration's or the one flowing into
// it; (a) else the default clocking event, as though written as the leading
// clocking event; (f) else none applies, and the statement is illegal, its
// maximal property being no instance for which a unique leading clocking
// event is determined.
void Elaborator::ResolveStaticAssertionClock(
    ModuleItem* item, const std::vector<EventExpr>& default_clock) {
  if (item->body == nullptr || !item->sensitivity.empty()) return;
  if (!default_clock.empty()) {
    item->sensitivity = default_clock;
    return;
  }
  diag_.Error(item->loc,
              "concurrent assertion has no leading clocking event: none is "
              "written, no default clocking is in scope and the property is "
              "no instance of a sequence or property declared with a unique "
              "leading clocking event",
              Subclause("16.16"));
  item->body = nullptr;
}

void Elaborator::ElaborateAssertPropertyItem(ModuleItem* item,
                                             RtlirModule* mod) {
  InferredAtInstance inferred;
  inferred.clock = DefaultClockingEvent(mod);
  inferred.disable = mod != nullptr ? mod->default_disable_iff : nullptr;
  SubstitutePropertyInstance(item, arena_, property_registry_, inferred, diag_);
  PromotePropertyInstanceBoolean(item, arena_, property_registry_, inferred);
  // §16.15: an assertion without a disable iff clause of its own, in the
  // spec or in the property it instantiates, within the scope of a default
  // disable iff declaration takes its condition; with none, none is
  // inferred.
  if (item->body != nullptr && item->body->assert_disable_iff == nullptr) {
    item->body->assert_disable_iff = inferred.disable;
  }
  ResolveStaticAssertionClock(item, inferred.clock);
  if (item->body != nullptr) {
    PromoteSequenceInstances(item->body->assert_property, property_registry_,
                             arena_);
  }
  CheckConcurrentAssertionNoChandle(item, mod, diag_);
  // §16.12.22: the sequences the property_spec uses as properties and as
  // antecedents, a sequential property standing as the whole spec included.
  if (item->body != nullptr) {
    ValidateSequenceDegeneracy(item->body->assert_property, item->loc,
                               property_registry_, diag_);
    ValidateSequenceUsedAsProperty(item->body->assert_sequence, item->loc,
                                   property_registry_, diag_);
    // §16.13: the statement keeps the leading clock, and the process wakes
    // on the clocks the sequences name beside it; the item is shared by
    // every instance of the module, so each clock is added once.
    if (item->body->assert_clock.empty()) {
      item->body->assert_clock = item->sensitivity;
    }
    std::vector<EventExpr> named;
    CollectTreeClocks(item->body->assert_property, property_registry_, named,
                      0);
    for (const EventExpr& ev : named) AppendClockOnce(item->sensitivity, ev);
    // §16.13.1: the rules on the sequences built of subsequences on
    // different clocks, under the leading clock.
    ValidateMulticlockSequences(item->body->assert_property,
                                item->body->assert_clock, item->loc,
                                property_registry_, diag_);
    ValidateMulticlockSequence(item->body->assert_sequence,
                               item->body->assert_clock, item->loc,
                               property_registry_, diag_);
  }
  // §16.5.2: `assert property(@$global_clock a);` under a
  // `global clocking @clk; endclocking` declaration is logically equivalent to
  // `assert property(@clk a);`, so the assertion's leading clocking event is
  // the event that declaration names. AddProcess substitutes it onto the
  // process rather than onto `item`, which the one ModuleDecl the parser built
  // for the module holds: §14.14 rule b) can give two instances of that module
  // different events, and a rewrite made on `item` would give both whichever
  // instance was elaborated first.
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_, &const_names_,
                             module_global_clocking_event_};
  // §16.4.3: a module-item deferred immediate assertion is a static deferred
  // assertion, modeled as an implicit always_comb procedure.
  if (IsStaticDeferredAssertion(item)) {
    AddProcess(RtlirProcessKind::kAlwaysComb, item, mod, kEnv);
    return;
  }
  // §16.14.5: a static concurrent assertion outside procedural code uses
  // `always` semantics. The parser captures the simple clocked boolean form as
  // a leading clock in item->sensitivity plus an immediate-assert body in
  // item->body; model it as a clocked process so the property is checked at
  // each leading clock edge.
  if (item->body != nullptr && !item->sensitivity.empty()) {
    AddProcess(RtlirProcessKind::kAlwaysFF, item, mod, kEnv);
    // §16.5: the process just added carries a concurrent assertion's property.
    // The mark is taken from the statement the parser built for that property
    // rather than set outright, so the one place that decides what a concurrent
    // assertion body is stays in the parser.
    mod->processes.back().is_concurrent_clocked =
        item->body->is_concurrent_clocked;
    // §16.9.4: the five future sampled value functions read a value "sampled at
    // the next global clock tick", so an attempt of a property naming one
    // cannot be answered at the assertion clock's own tick. The clause says
    // where it is answered instead -- "Execution of the action block of an
    // assertion containing global clocking future sampled value functions shall
    // be delayed until the global clocking tick that follows the last tick of
    // the assertion clock for the attempt" -- so the process carries that event
    // and waits for it before it evaluates. A property naming none carries
    // nothing and is evaluated where it always was.
    //
    // §16.9.4 also requires a global clocking declaration for any of the ten
    // functions, and ValidateGclkRequiresGlobalClocking reports a text that
    // names one without; where that report has been made there is no event to
    // carry, and the assertion is left alone rather than parked forever.
    if (module_global_clocking_event_ != nullptr &&
        FindGclkFunctionRefInItem(item, IsGlobalClockingFutureFunction,
                                  /*include_property_slot=*/true) != nullptr) {
      mod->processes.back().gclk_future_event = *module_global_clocking_event_;
    }
    return;
  }
  ValidateClockingBlock(item, mod);
}

bool Elaborator::ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kSequenceDecl:
      ElaborateSequenceDeclItem(item, mod);
      return true;
    case ModuleItemKind::kPropertyDecl:
      ElaboratePropertyDeclItem(item, mod);
      return true;
    case ModuleItemKind::kAssertProperty:
      ElaborateAssertPropertyItem(item, mod);
      return true;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      // §16.14.3: a cover statement's optional pass statement shall not include
      // any concurrent assert, assume, or cover statement.
      if (FindConcurrentAssertionInPassStmt(item->assert_pass_stmt) !=
          nullptr) {
        diag_.Error(item->loc,
                    "the pass statement of a cover statement may not include a "
                    "concurrent assert, assume, or cover statement",
                    Subclause("16.14.3"));
      }
      // Annex F.5.3.1 defines a cover property statement's satisfaction over
      // the words an assert property statement's is, so a cover property in
      // the clocked boolean form is a process as an assert property is; a
      // cover sequence has no body and takes the path's validation alone.
      ElaborateAssertPropertyItem(item, mod);
      return true;
    case ModuleItemKind::kAssumeProperty:
      // Annex F.5.3.1 defines an assume property statement's satisfaction as
      // the assert property statement's, so it takes the same path.
      ElaborateAssertPropertyItem(item, mod);
      return true;
    case ModuleItemKind::kRestrictProperty:
      ValidateClockingBlock(item, mod);
      return true;
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item, mod);
      // §14.3: a clocking block is a declaration the run needs, not only one
      // elaboration checks. Lowerer::LowerClockingBlocks registers it with the
      // ClockingManager, which is what makes §14.16's synchronous drive and
      // §14.10's clocking block event reach anything.
      if (mod != nullptr) {
        mod->clocking_blocks.push_back(item);
        // §16.16 (b): the block's declarations are the module's for the run
        // to expand, clocked by the block and named through it.
        for (ModuleItem* decl : item->clocking_decls) {
          if (decl->kind == ModuleItemKind::kPropertyDecl) {
            mod->property_decls.push_back(decl);
          } else {
            mod->sequence_decls.push_back(decl);
          }
        }
      }
      return true;
    default:
      // §23.10.4 kDefparam, kExportDecl, kNestedModuleDecl, and any remaining
      // kind are no-ops at behavioral elaboration; kDefaultDisableIff was read
      // ahead of the items, its effect being independent of its position.
      return true;
  }
}

}  // namespace delta
