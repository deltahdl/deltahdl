#pragma once

// Internal declarations shared between the translation units of the elaborator.
// Most were split out of elaborator_validate.cpp and are used by the
// elaborator_validate*.cpp files alone; ForEachChildStmt and AnyExprChild below
// are used by any elaborator translation unit that walks a statement or an
// expression tree. These helpers are file-local in spirit; the header exists
// only so that one translation unit can define a helper that another
// references, keeping a single definition of each symbol.

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;
using NameSet = std::unordered_set<std::string_view>;

// Hands `visit` every statement one rs_rule of a randsequence production holds.
// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }` and reaches one from two places in an rs_rule: an rs_prod may be a code
// block, whose statements the parser puts in RsProd::code_stmts, and a
// weight_specification may be followed by one, whose statements go in
// RsRule::weight_code. Both hold ordinary procedural statements, so a walker
// whose rule reaches a statement reaches these.
template <typename Rule, typename Visit>
void ForEachRandsequenceRuleStmt(Rule& rule, Visit visit) {
  for (auto& sub : rule.weight_code) visit(sub);
  for (auto& prod : rule.prods) {
    for (auto& sub : prod.code_stmts) visit(sub);
  }
}

// Hands `visit` every statement a randsequence statement holds, which is the
// only thing Stmt::rs_productions carries that is a statement at all. Call it
// from a walker that descends the other statement-holding fields of Stmt, so
// that a rule holds inside a randsequence as it holds outside one. The nesting
// is split across two functions because writing all four loops in one carries
// it past the readability-function-cognitive-complexity threshold of 15 that
// etc/clang_tidy/src.yml sets.
template <typename S, typename Visit>
void ForEachRandsequenceStmt(S* s, Visit visit) {
  for (auto& production : s->rs_productions) {
    for (auto& rule : production.rules) {
      ForEachRandsequenceRuleStmt(rule, visit);
    }
  }
}

// Hands `visit` every statement `s` holds, in every field of Stmt that holds
// one. src/parser/ast_stmt.h declares thirteen: stmts, then_branch,
// else_branch, for_inits, for_steps, for_body, case_items, fork_stmts, body,
// assert_pass_stmt, assert_fail_stmt, randcase_items and rs_productions.
//
// This is the list, stated once, that a walker over statements recurses on. A
// walker that writes its own runs a rule over the positions somebody happened
// to write down rather than over the positions Annex A admits, which is what
// #3141, #3165 and #3166 were each about. Where a rule genuinely cannot reach a
// field, say so in a comment above the walker rather than by dropping this call
// and writing a shorter list.
//
// `visit` is called with a null pointer for an absent single-statement field,
// which every walker here already answers with an early return.
//
// `visit` receives the field itself rather than a copy of it, so a walker given
// a `Stmt*` may assign a replacement child through it and one given a
// `const Stmt*` may not. That is what lets a walker that rewrites the tree
// share this list with the walkers that only read it, instead of writing a
// second copy of the list that drifts from this one.
template <typename S, typename Visit>
void ForEachChildStmt(S* s, Visit visit) {
  for (auto& sub : s->stmts) visit(sub);
  for (auto& sub : s->fork_stmts) visit(sub);
  for (auto& sub : s->for_inits) visit(sub);
  for (auto& sub : s->for_steps) visit(sub);
  visit(s->then_branch);
  visit(s->else_branch);
  visit(s->body);
  visit(s->for_body);
  visit(s->assert_pass_stmt);
  visit(s->assert_fail_stmt);
  for (auto& ci : s->case_items) visit(ci.body);
  for (auto& rc : s->randcase_items) visit(rc.second);
  ForEachRandsequenceStmt(s, visit);
}

// The expressions a randsequence production item holds: A.6.12 gives an
// rs_production a list of actual arguments, written the way a task call writes
// them.
template <typename Item, typename Visit>
void ForEachRandsequenceItemExpr(Item& item, Visit visit) {
  for (auto& arg : item.args) visit(arg);
}

// The expressions one production of a rule holds. A.6.12 admits four forms
// beyond the plain item and the code block: rs_if_else carries a condition and
// two items, rs_repeat a repeat count and an item, and rs_case a case
// expression and a list of arms, each arm carrying its own case-item
// expressions and its own item.
template <typename Prod, typename Visit>
void ForEachRandsequenceProdExpr(Prod& prod, Visit visit) {
  visit(prod.condition);
  visit(prod.repeat_count);
  visit(prod.case_expr);
  ForEachRandsequenceItemExpr(prod.item, visit);
  ForEachRandsequenceItemExpr(prod.if_true, visit);
  ForEachRandsequenceItemExpr(prod.if_false, visit);
  ForEachRandsequenceItemExpr(prod.repeat_item, visit);
  for (auto& ci : prod.case_items) {
    for (auto& p : ci.patterns) visit(p);
    ForEachRandsequenceItemExpr(ci.item, visit);
  }
}

// The expressions one rule holds. §18.17.1's rs_rule admits a
// weight_specification, and §18.17.5's rand_join admits an expression before
// its production list. The nesting is split across these three functions for
// the reason ForEachRandsequenceRuleStmt is split from ForEachRandsequenceStmt:
// written as one function it passes the
// readability-function-cognitive-complexity threshold of 15 that
// etc/clang_tidy/src.yml sets.
template <typename Rule, typename Visit>
void ForEachRandsequenceRuleExpr(Rule& rule, Visit visit) {
  visit(rule.weight);
  visit(rule.rand_join_expr);
  for (auto& item : rule.rand_join_items) {
    ForEachRandsequenceItemExpr(item, visit);
  }
  for (auto& prod : rule.prods) ForEachRandsequenceProdExpr(prod, visit);
}

// Hands `visit` every expression a randsequence statement holds outside its
// code blocks, which is everything Stmt::rs_productions carries that is an
// expression at all. The code blocks hold statements, and a walker reaches
// their expressions by descending them through ForEachChildStmt above.
template <typename S, typename Visit>
void ForEachRandsequenceExpr(S* s, Visit visit) {
  for (auto& production : s->rs_productions) {
    for (auto& rule : production.rules)
      ForEachRandsequenceRuleExpr(rule, visit);
  }
}

// The rs_production_items one rs_prod holds. A.6.12 gives an rs_prod five
// forms and four of them name a production: the plain rs_production_item, the
// two an rs_if_else selects between, the one an rs_repeat repeats, and the one
// each arm of an rs_case carries. The fifth is the rs_code_block, which names
// no production and holds statements ForEachRandsequenceRuleStmt above hands
// over instead.
//
// The items of the forms an rs_prod is not carry an empty name.
// Parser::ParseRsProd in src/parser/parser_verify.cpp fills the member its form
// uses and leaves the other three default-constructed, so RsProd::if_true is an
// empty name on every rs_prod that is not an rs_if_else and a visitor that
// reads a name skips an empty one.
template <typename Prod, typename Visit>
void ForEachRandsequenceProdItem(Prod& prod, Visit visit) {
  visit(prod.item);
  visit(prod.if_true);
  visit(prod.if_false);
  visit(prod.repeat_item);
  for (auto& ci : prod.case_items) visit(ci.item);
}

// The rs_production_items one rs_rule holds. §18.17.5's rand_join names the
// productions it interleaves in a list of its own, RsRule::rand_join_items,
// rather than through an rs_prod, so a walk that took the rs_prods alone would
// reach none of them.
template <typename Rule, typename Visit>
void ForEachRandsequenceRuleItem(Rule& rule, Visit visit) {
  for (auto& item : rule.rand_join_items) visit(item);
  for (auto& prod : rule.prods) ForEachRandsequenceProdItem(prod, visit);
}

// Hands `visit` every rs_production_item a randsequence statement holds, which
// is every position §18.17 admits a production identifier in bar the optional
// top-level name the statement's own parentheses carry in
// Stmt::rs_top_production.
//
// This is that list, stated once, for the reason ForEachChildStmt below states
// the statement links once: a walk that writes its own runs its rule over the
// positions somebody happened to write down. §18.17 makes every production
// identifier local to the scope the randsequence statement creates, so a rule
// about whether a production identifier resolves has to reach all of them or it
// passes an unresolvable name in the position it missed.
//
// The nesting is split across these three functions for the reason
// ForEachRandsequenceRuleStmt is split from ForEachRandsequenceStmt: written as
// one function it carries past the
// readability-function-cognitive-complexity threshold of 15 that
// etc/clang_tidy/src.yml sets.
template <typename S, typename Visit>
void ForEachRandsequenceItem(S* s, Visit visit) {
  for (auto& production : s->rs_productions) {
    for (auto& rule : production.rules)
      ForEachRandsequenceRuleItem(rule, visit);
  }
}

// The expressions Stmt holds directly, as against the statements
// ForEachChildStmt above hands over. src/parser/ast_stmt.h declares ten scalar
// Expr* members -- condition, lhs, rhs, delay, cycle_delay, for_cond, expr,
// assert_expr, repeat_event_count and var_init -- and reaches six more
// positions through members it holds: EventExpr::signal and
// EventExpr::iff_condition for each entry of events, wait_order_events, the
// weight of each randcase item, the patterns of each case item,
// var_unpacked_dims, and the randsequence expressions above.
//
// This is that list, stated once, for the same reason ForEachChildStmt states
// the statement links once. A walker that writes its own runs its rule over the
// positions somebody happened to write down rather than over the positions
// Annex A admits: #3303 records three walkers that each missed a different
// subset, so a $bits call in a for-loop condition, a rand_mode call in a #()
// delay and a sampled value function in a wait_order list each escaped the rule
// above it. Where a rule genuinely cannot reach a position, skip it in the
// visitor with a comment naming the clause rather than by dropping this call
// and writing a shorter list.
//
// `visit` is called with a null pointer for an absent scalar field, which every
// walker here already answers with an early return, and it receives the field
// itself rather than a copy, so a walker given a `Stmt*` may assign a
// replacement expression through it and one given a `const Stmt*` may not.
//
// A walker whose rule turns on which field an expression came from cannot use
// this, and should write its positions out with a comment saying so. `visit`
// receives the expression and not the member it stood in, so the visitor cannot
// tell a timing control expression from an ordinary one. CollectStmtReads in
// sensitivity.cpp is the case: §9.2.2.2.1 exception (c) excludes an identifier
// appearing only in a wait, event or delay expression, and that walk implements
// the exception by not reading Stmt::delay, Stmt::cycle_delay, Stmt::events,
// Stmt::repeat_event_count and Stmt::wait_order_events at all. Handing it this
// list would put every delay and event identifier into the implicit sensitivity
// list. That is a rule about which positions a walk reads, which is what this
// list settles; it is not a rule about which statements it descends, which is
// what ForEachChildStmt settles, and that walk does use ForEachChildStmt.
template <typename S, typename Visit>
void ForEachChildExpr(S* s, Visit visit) {
  visit(s->condition);
  visit(s->lhs);
  visit(s->rhs);
  visit(s->delay);
  visit(s->cycle_delay);
  visit(s->for_cond);
  visit(s->expr);
  visit(s->assert_expr);
  visit(s->repeat_event_count);
  visit(s->var_init);
  for (auto& ev : s->events) {
    visit(ev.signal);
    visit(ev.iff_condition);
  }
  for (auto& e : s->wait_order_events) visit(e);
  for (auto& rc : s->randcase_items) visit(rc.first);
  for (auto& ci : s->case_items) {
    for (auto& p : ci.patterns) visit(p);
  }
  for (auto& d : s->var_unpacked_dims) visit(d);
  ForEachRandsequenceExpr(s, visit);
}

// Whether `fn` holds for any child expression of `e`. Expr in
// src/parser/ast_expr.h carries thirteen links to other expressions, and this
// is the one place they are enumerated: a walk that names some of them answers
// a question about part of the tree while reading as though it answered it
// about all of it. ExprContainsIdent in elaborator_validate.cpp followed lhs
// and rhs alone, which is what made §6.20.5's two specparam checks accept a
// specparam reached through a call argument, a conditional, a concatenation, a
// replication count or an index. The three §11.5.1 walks in that same file
// followed lhs, rhs, base and index alone, which is what made a select of a
// real variable, a real parameter or a scalar legal in every one of the other
// nine positions.
//
// Extend this when Expr gains a child link. What it leaves out on purpose is
// everything that names something rather than holding an expression: `callee`
// and `scope_prefix` name a subroutine and a package, `arg_names` and
// `with_restrict_ids` are identifier lists, and `inline_constraint` is a
// ClassMember.
template <typename Fn>
bool AnyExprChild(const Expr* e, Fn&& fn) {
  for (const Expr* child :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->with_expr, e->repeat_count}) {
    if (fn(child)) return true;
  }
  for (const Expr* child : e->args) {
    if (fn(child)) return true;
  }
  for (const Expr* child : e->elements) {
    if (fn(child)) return true;
  }
  for (const Expr* child : e->pattern_keys) {
    if (fn(child)) return true;
  }
  return false;
}

// Runs `fn` over every child expression of `e`, for what it does rather than
// for an answer. It enumerates nothing itself: it asks AnyExprChild a question
// no child answers, so a walk written to report on a subtree reads the same
// list of children as a walk written to search one, and the two cannot come to
// disagree about what a child is.
template <typename Fn>
void ForEachExprChild(const Expr* e, Fn&& fn) {
  AnyExprChild(e, [&fn](const Expr* child) {
    fn(child);
    return false;
  });
}

// Parses the size prefix of an integer literal's text (the digits before the
// base tick "'"). Returns that width when present and positive, otherwise the
// default unsized-literal width of 32. Defined in elaborator_validate.cpp.
uint32_t ExtractLiteralWidth(std::string_view text);

// Defined in elaborator_validate.cpp.
std::optional<int64_t> ComputeDimSize(const Expr* dim);
std::string_view LhsBaseName(const Expr* e);
// §23.6 gives a hierarchical name as a sequence of components separated by
// periods, and §23.7 makes what the first of them resolves to decide whether
// the name is a hierarchical reference or a member select. Every rule that bars
// a reference by the scope its leftmost component names starts here, so the
// reduction is stated once for the elaborator rather than once per rule file.
// Returns an empty view for anything that is neither an identifier nor a member
// access chain ending in one.
inline std::string_view HierRefLeftmost(const Expr* e) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return HierRefLeftmost(e->lhs);
  return {};
}

bool ExprContainsIdent(const Expr* e, std::string_view name);
bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names);
void CheckNbaDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    const std::unordered_set<std::string_view>& dynsized_names,
    DiagEngine& diag);
void CollectProcTargets(const Stmt* s,
                        std::unordered_map<std::string_view, SourceLoc>& out);

void CollectForceReleaseTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out);
void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag);
void CheckInterconnectProceduralRead(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag);
void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag);
void CheckForceLhs(
    const Stmt* s, const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    DiagEngine& diag);
using SelectShapeMap = std::unordered_map<std::string_view, VarSelectShape>;

// What §11.5.1 needs to judge the operand of a select. Its second alternative
// names two operands, "a real variable or real parameter", carried in separate
// sets because the report names the noun the clause gives the one it found and
// a parameter is not a variable. Each set holds only the names declared with no
// unpacked dimension, since §11.5.2 makes one address written after such a name
// an element select. `shapes` answers for the addresses after that one, which
// §11.5.2 sends back to §11.5.1 once the element is selected.
struct SelectOperands {
  const NameSet& variables;
  const NameSet& parameters;
  const SelectShapeMap& shapes;
};

// §11.5.1: `operands` decides the operand report. `types` is read for the index
// expression only, which the clause bars separately from being of real type.
void CheckRealSelect(const Expr* e, const TypeMap& types,
                     const SelectOperands& operands, DiagEngine& diag);
void CheckScalarSelect(const Expr* e, const NameSet& scalars, DiagEngine& diag);
void CheckIndexedPartSelectWidth(const Expr* e, const ScopeMap& scope,
                                 DiagEngine& diag);
void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag);
void CheckRealSelectStmt(const Stmt* s, const TypeMap& types,
                         const SelectOperands& operands, DiagEngine& diag);
void CheckIndexedPartSelectWidthStmt(const Stmt* s, const ScopeMap& scope,
                                     DiagEngine& diag);

// Defined in elaborator_validate_matches.cpp.
bool IsArrayQueryFunc(std::string_view callee);
bool TypedefHasDynamicDim(const std::vector<Expr*>& dims);

}  // namespace delta
