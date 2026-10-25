#pragma once

// Internal declarations shared between the translation units of the elaborator.
// Most were split out of elaborator_validate.cpp and are used by the
// elaborator_validate*.cpp files alone; ForEachChildStmt and AnyExprChild below
// are used by any elaborator translation unit that walks a statement or an
// expression tree. These helpers are file-local in spirit; the header exists
// only so that one translation unit can define a helper that another
// references, keeping a single definition of each symbol.

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

struct CompilationUnit;
struct RtlirModule;
struct TypeShapeTables;

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
// Every item of `items` that owns a body a per-declaration check has to reach,
// and every class method the items declare.
//
// A rule stated of a statement names no enclosing declaration it is suspended
// in, so a check over one has to reach every body a declaration owns. The item
// loops these checks were written with reached a module's procedural blocks and
// its module-level subroutines, and no class: a class inside a module is a
// ModuleItemKind::kClassDecl item whose methods hang off ClassDecl::members and
// whose own func_body_stmts and body are empty, so it matched neither arm.
// Every rule those checks enforce was therefore unenforced in a class method,
// which is where a verification environment puts its code.
//
// `visit` receives a ModuleItem*, and a class method is one -- the ClassMember
// holds a kFunctionDecl or kTaskDecl item with its statements in
// func_body_stmts -- so a check's existing item-kind switch reaches a method
// with nothing added to it. Nested classes are descended, since a class member
// may be a class (§8.24) and its methods are bodies of the same kind.
template <typename Visit>
void ForEachClassBodyItem(const ClassDecl* cls, Visit visit) {
  if (cls == nullptr) return;
  for (const auto* m : cls->members) {
    if (m == nullptr) continue;
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      visit(m->method);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      ForEachClassBodyItem(m->nested_class, visit);
    }
  }
}

template <typename Visit>
void ForEachBodyOwningItem(const std::vector<ModuleItem*>& items, Visit visit) {
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kClassDecl) {
      ForEachClassBodyItem(item->class_decl, visit);
      continue;
    }
    visit(item);
  }
}

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

// §11.12 lists a sequential and a parallel block and a subroutine among the
// scopes a let may be declared in, and the parser keeps such a let as a
// kBlockItemDecl statement over the let's item (Parser::ParseBlockVarDecls):
// `visit` receives the item of each let `s` and the statements under it
// declare.
template <typename Visit>
void ForEachBlockLet(const Stmt* s, Visit visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kLetDecl)
    visit(s->decl_item);
  ForEachChildStmt(s,
                   [&visit](const Stmt* sub) { ForEachBlockLet(sub, visit); });
}

// The lets `items`, a package's or a compilation unit's, declare, and those
// the bodies of their subroutines and of their classes' methods declare.
template <typename Visit>
void ForEachScopeLet(const std::vector<ModuleItem*>& items, Visit visit) {
  for (ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kLetDecl) visit(item);
  }
  ForEachBodyOwningItem(items, [&visit](const ModuleItem* owner) {
    for (const Stmt* s : owner->func_body_stmts) ForEachBlockLet(s, visit);
  });
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
// Hands `visit` every `. variable_identifier` a pattern binds, the one form of
// Syntax 12-4 that declares a variable (§12.6). The walk follows the forms
// that hold a pattern: a `pattern &&& filter_expression` (§12.6.1) holds the
// pattern on its left, the filter on its right being an ordinary expression; a
// tagged pattern holds its member pattern in Expr::lhs; and a structure or
// array pattern holds one pattern per element. A constant expression pattern
// and the `.*` wildcard bind nothing. The uniqueness rule of §12.6
// (elaborator_validate_matches.cpp) and the scope rule of §23.9
// (elaborator_scope_rules_names.cpp) read the names off the same walk, so that
// a form one of them reached and the other did not cannot arise.
template <typename Visit>
void ForEachPatternBinding(const Expr* p, Visit visit) {
  if (p == nullptr) return;
  if (p->kind == ExprKind::kBinary && p->op == TokenKind::kAmpAmpAmp) {
    ForEachPatternBinding(p->lhs, visit);
    return;
  }
  if (p->kind == ExprKind::kIdentifier && p->is_pattern_binding) {
    visit(p);
    return;
  }
  if (p->kind == ExprKind::kTagged) {
    ForEachPatternBinding(p->lhs, visit);
    return;
  }
  if (p->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* e : p->elements) ForEachPatternBinding(e, visit);
  }
}

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

// Whether `e` names one of `vars`, the variables in scope where it stands,
// which no constant expression does (§11.2.1). A system function call is left
// alone: `$bits(v)` is constant.
template <typename Vars>
bool NamesAVariable(const Expr* e, const Vars& vars) {
  if (e == nullptr || e->kind == ExprKind::kSystemCall) return false;
  if (e->kind == ExprKind::kIdentifier) return vars.count(e->text) != 0;
  return AnyExprChild(
      e, [&](const Expr* child) { return NamesAVariable(child, vars); });
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

// Runs `fn` over `e` and every expression under it, the member a member
// access selects excepted: `h.tmp` and `L0[0].L1.my_let` name `tmp` and
// `my_let` within the scope their prefix names, not the scope written in.
template <typename Fn>
void ForEachExprUnder(const Expr* e, Fn& fn) {
  if (e == nullptr) return;
  fn(e);
  if (e->kind == ExprKind::kMemberAccess) {
    ForEachExprUnder(e->lhs, fn);
    return;
  }
  ForEachExprChild(e,
                   [&fn](const Expr* child) { ForEachExprUnder(child, fn); });
}

// One statement tree written in a module, together with the item that holds
// it. The location is the item's, which is where a report about the whole
// tree stands.
struct ProceduralRoot {
  const ModuleItem* item = nullptr;
  const Stmt* body = nullptr;
};

// Every statement tree of `items`: each process's body, each statement of a
// task or function body (func_body_stmts holds a vector rather than the single
// body a process holds), and those of every item a generate construct holds in
// gen_body, gen_else->gen_body and each entry of gen_case_items. The clocking
// rules of Clause 14 are stated against the module, interface, checker or
// program rather than against a process, so a walk that reads ModuleItem::body
// off the module's items alone misses a subroutine's and a generate block's.
// With `skip_defaulted` set, a generate body that declares its own default
// clocking is left out (§14.12). Defined in elaborator_validate_clocking.cpp.
void CollectProceduralRoots(const std::vector<ModuleItem*>& items,
                            std::vector<ProceduralRoot>& out,
                            bool skip_defaulted = false);

// §23.4: the module, interface, program and checker declarations `decl` is
// nested in, innermost first; empty for a declaration nested in none. Defined
// in elaborator_validate_clocking_signals.cpp.
std::vector<const ModuleDecl*> EnclosingDecls(const CompilationUnit* unit,
                                              const ModuleDecl* decl);

// Defined in elaborator_validate.cpp.
std::optional<int64_t> ComputeDimSize(const Expr* dim);

// A.8.2 with §13.5.4: the index into `expr->args` of the actual that binds to
// the formal at position `formal_index`, named `formal_name`, whether the call
// binds it by position or by name; the first `positional_count` actuals are
// the ordered ones. Returns -1 when no actual binds to the formal. Defined in
// elaborator_validate_array_args.cpp.
int ResolveActualArgIndex(const Expr* expr, size_t formal_index,
                          std::string_view formal_name,
                          size_t positional_count);

// §11.3 and §11.4.13: the variables of a module an operator is asked to take
// as a whole when it takes no aggregate -- those of an unpacked structure or
// union type, declared in place or through a name standing for one. Defined in
// elaborator_validate_operations_aggregate.cpp.
std::unordered_set<std::string_view> UnpackedStructVars(
    const ModuleDecl* decl, const TypedefMap& typedefs);

// §5.10, §5.11 and §10.9.1: the checks an assignment pattern written for an
// array, unpacked or packed (§7.4), has to pass, wherever it is written -- a
// declaration's initializer, a block's or the module's, the right-hand side of
// a procedural assignment, or a port connection. `typedefs` resolves a
// structure named as the element type and the packed dimensions a typedef
// carries, `aggregate_typedefs` names the typedefs that stand for an unpacked
// aggregate, and `var_types` the declared kind of a name written as an
// element or in an index key. Defined in elaborator_validate.cpp.
struct ArrayPatternCheck {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregate_typedefs;
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  DiagEngine& diag;

  // Checks `pattern` against an array of `elem_type` with the unpacked
  // dimensions `dims`, outermost first, and then the packed dimensions of
  // `elem_type`, reporting at `loc`. Nothing for an expression that is no
  // assignment pattern.
  void Check(const Expr* pattern, const DataType& elem_type,
             const std::vector<Expr*>& dims, SourceLoc loc) const;
  // As Check, with the unpacked dimensions given by their element counts,
  // folded already, as a port's are.
  void CheckSized(const Expr* pattern, const DataType& elem_type,
                  std::span<const uint32_t> unpacked_sizes,
                  SourceLoc loc) const;
};
// A.6.7.1 and §10.9.1: each index key of the array pattern `pattern` is a
// constant expression, which names none of `check.var_types`, and names its
// element once, a second key naming it reported at `loc`. `default` and a type
// key are no index keys. Defined in array_pattern_keys.cpp.
void CheckArrayPatternIndexKeys(const ArrayPatternCheck& check,
                                const Expr* pattern, SourceLoc loc);
// What two array pattern keys are the same key by. §10.9's array keys are
// constant expressions, so what a key names is its value: `3` and `N-1` with N
// of 4 name the element between them once, not twice. A key that does not fold
// here is answered for by how it was written, which still tells apart the two
// halves of a key written the same way twice. Nothing for a key that neither
// folds nor was written as a single name or literal -- there is no ground to
// call two of those the same, and calling them so would report every pair of
// them as a duplicate. Defined in array_pattern_keys.cpp.
std::optional<std::string> ArrayPatternKeyIdentity(const Expr* key);
std::string_view LhsBaseName(const Expr* e);
// §5.10 and §5.11: the replication an assignment pattern consists of,
// `'{n{...}}`, or null, and the items a positional pattern supplies, its
// elements or a replication's multiplier times the items inside it, or nothing
// where the multiplier does not fold. Defined in elaborator_validate.cpp.
const Expr* PatternReplication(const Expr* pattern);
std::optional<int64_t> PositionalItemCount(const Expr* pattern);

// Defined in struct_pattern_checks.cpp.
//
// Where a structure pattern is checked: the typedefs its types resolve
// through, and the position its reports stand at.
struct StructPatternTarget {
  const TypedefMap& typedefs;
  SourceLoc loc;
  DiagEngine& diag;
};
// The members of the structure `type` names, written inline or through a
// typedef, or null where it names none.
const std::vector<StructMember>* StructMembersOf(const DataType& type,
                                                 const TypedefMap& typedefs);
// §10.9.2's rules of a structure pattern against the structure's members:
// one item per member positionally, member keys naming members, and every
// member covered.
void CheckStructPattern(const Expr* pattern,
                        const std::vector<StructMember>& members,
                        const StructPatternTarget& target);
// §10.8 with §7.2.1: the packed value a positional pattern gives a structure
// of `type`, each item folded and placed at its member's bits, the first
// member most significant; nothing where an item does not fold or the
// structure is 64 bits wide or wider.
std::optional<int64_t> FoldPackedStructPattern(const Expr* pattern,
                                               const DataType& type,
                                               const TypedefMap& typedefs,
                                               const ScopeMap& scope);
// Checks `value` as a structure pattern where it is one: a typed pattern
// against the type its prefix names, an untyped one against `target_type`,
// the type of what it is assigned to, null where that is not known.
void CheckStructPatternFor(const Expr* value, const DataType* target_type,
                           const StructPatternTarget& target);
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

// Whether `e` is a real value: a real or a time literal (§5.8 reads a time
// literal as a realtime value), a real variable or an element of an array of
// reals, an arithmetic operation one of whose operands is real, or a
// conditional either of whose results is. `var_types` is the declared kind of
// each variable. Defined in elaborator_validate_cast_operand.cpp.
bool IsRealValued(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types);
bool ExprContainsIdent(const Expr* e, std::string_view name);
bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names);
// §6.21: reports each procedural continuous assignment in `s` and below it
// that writes an element of one of the dynamic arrays `dyn_names` names.
void CheckPcontDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag);
void CollectProcTargets(const std::vector<FunctionArg>& formals,
                        const std::vector<Stmt*>& body,
                        std::unordered_map<std::string_view, SourceLoc>& out);
// §10.6.1: reports each net of `net_names` a procedural assign or deassign in
// `body` names as its target, passing by a name `body` itself declares.
void ReportProcContAssignNets(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag);

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
// §28.3.2 with §10.3.4: reports (highz0, highz1) on a net declaration, a
// continuous assignment or a gate. Defined in elaborator_cont_assign.cpp.
void CheckHighzStrengthPair(const ModuleItem* item, DiagEngine& diag);
using SelectShapeMap = std::unordered_map<std::string_view, VarSelectShape>;

// What §11.5.1 needs to judge the operand of a select. Its second alternative
// names two operands, a real variable or a real parameter, carried in separate
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

// Defined in elaborator_validate_global_clocking.cpp.
//
// §16.9.4's ten sampled value functions, sought in one module item's slots.
// `match` selects which of them count -- IsGlobalClockingFutureFunction picks
// the five that read the next global clock tick -- and returns the first
// reference found or nullptr. With `include_property_slot` false the property
// body expression is skipped, which is how a validation asks for the
// procedural positions alone; §16.9.4 admits a future function in a
// property_expr and bars it everywhere else.
using GclkKindPredicate = bool (*)(GlobalClockingSampledFunction);
const Expr* FindGclkFunctionRefInItem(const ModuleItem* item,
                                      GclkKindPredicate match,
                                      bool include_property_slot);

// Defined in elaborator_validate_matches.cpp.
bool IsArrayQueryFunc(std::string_view callee);
// §7.5, §7.9, §7.10.2 and §7.12: whether `name` is a built-in method of some
// kind of array. Defined in elaborator_validate_array_methods.cpp.
bool IsArrayBuiltinMethodName(std::string_view name);
// §27.6: visits `item` and every item a generate construct holds under it, at
// every depth.
void ForEachItemAndGenerateDescendant(
    const ModuleItem* item, const std::function<void(const ModuleItem*)>& fn);
bool TypedefHasDynamicDim(const std::vector<Expr*>& dims);

// Defined in nba_dynamic_element.cpp.
//
// What §10.4.2's rule on elements of dynamically sized arrays reads a target's
// types with: the module's typedefs, the unpacked dimensions each typedef
// wrote and the class names, and the compilation unit a class is found in.
struct NbaDynamicTables {
  const TypeShapeTables& shape;
  const CompilationUnit* unit;
};
// Reports each nonblocking assignment in `decl`'s processes, subroutines,
// generate blocks and class methods that writes an element of a dynamically
// sized array.
void CheckNbaDynamicElements(const ModuleDecl* decl,
                             const NbaDynamicTables& tables, DiagEngine& diag);

// Defined in elaborator_validate_funcbody.cpp.
//
// §6.21's rule that a static variable declared with an initializer says
// `static` or `automatic`, over the tasks and functions of one package.
void ReportPackageSubroutineStaticInits(const PackageDecl* pkg,
                                        DiagEngine& diag);

// §20.6.3: reports each call of $isunbounded in `decl` whose argument is not
// the name of a parameter, a hierarchical name being read down the instances
// below `mod`. Defined in elaborator_validate_isunbounded.cpp.
void CheckIsunboundedArgs(const ModuleDecl* decl, const RtlirModule* mod,
                          DiagEngine& diag);

// §20.4.3: reports each call of $timeformat in `decl` that carries some but not
// all four of its arguments. Defined in elaborator_validate_timeformat.cpp.
void CheckTimeformatArgs(const ModuleDecl* decl, DiagEngine& diag);

// §23.9: the declarations a statement of a procedural body sees, innermost
// last, so a name is judged by the declaration it reaches rather than by any
// declaration of that name. They are a subroutine's formals, the variables of
// each begin-end and fork-join block that encloses the statement, and the loop
// variables §12.7.1 (printed page 330) declares with automatic lifetime in an
// implicit block around a for-loop. A name that reaches none of them is the
// enclosing scope's, a module's variable or net.
class BodyDeclScopes {
 public:
  struct Decl {
    std::string_view name;
    const DataType* type = nullptr;
    const std::vector<Expr*>* unpacked_dims = nullptr;
    bool automatic = false;
  };

  // `default_auto` is the lifetime §6.21 gives a variable that names none: an
  // automatic subroutine's, or a static scope's.
  explicit BodyDeclScopes(bool default_auto) : default_auto_(default_auto) {}

  void DeclareFormal(const FunctionArg& arg);

  const Decl* Find(std::string_view name) const;

  // Hands `visit` `s` and every statement below it, each with the declarations
  // it sees in view.
  void Walk(const Stmt* s, const std::function<void(const Stmt*)>& visit);

 private:
  bool default_auto_;
  std::vector<Decl> decls_;
};

// A.8.2: the name the subroutine call `call` names its subroutine by -- the
// bare callee, or for a call through the package scope resolution operator,
// `pk::t()`, which the parser keeps with no callee text and the scoped name as
// its base, "pk::t". Empty for a call naming none. Defined in
// elaborator_validate_subroutine.cpp.
std::string CallName(const Expr* call);

// A.6.9 with A.8.2: the name the statement `s` enables a subroutine by, the
// call it is (CallName) or the bare identifier it is, `t;`, since a tf_call's
// argument list is optional; empty for any other statement. Defined in
// elaborator_validate_subroutine.cpp.
std::string EnabledSubroutineName(const Stmt* s);

// §15.5.1 and §15.5.4: reports a trigger's target and a wait_order operand
// that the kinds the module's variables and nets are declared with, `kinds`,
// give a type other than event. Defined in
// elaborator_validate_event_operands.cpp.
void ReportNonEventOperands(const ModuleDecl* decl, const TypeMap& kinds,
                            DiagEngine& diag);

// §13.4.1 with §35.5: whether the task, function or imported subroutine
// declared by `subroutine` is a function whose return type is not void, which
// a call made as if it had no return value discards. Defined in
// elaborator_validate_subroutine_args.cpp.
bool ReturnsAValue(const ModuleItem* subroutine);

// §13.4.1: the warning owed where the nonvoid function `callee` is called at
// `loc` as if it had no return value, `remedy` ending the message with what
// the caller may do about it. Defined in
// elaborator_validate_subroutine_args.cpp.
void WarnDiscardedReturn(SourceLoc loc, std::string_view callee,
                         std::string_view remedy, DiagEngine& diag);

// §6.20.4 of the value parameters the generate construct `item` of `mod`
// declares, `scope` binding the module's own parameters. Run once the
// construct is elaborated, when the parameters its blocks declare are
// registered on `mod`. Defined in elaborator_validate_queries_dims.cpp.
void ValidateGenerateValueParams(const ModuleItem* item, const RtlirModule* mod,
                                 const ScopeMap& scope,
                                 const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
