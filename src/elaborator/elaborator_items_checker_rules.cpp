// The rules IEEE 1800-2023 §17.5 and §17.7 put on the items of a checker body
// and their statements, read by the item-classification pass in
// elaborator_items_udp.cpp for every item of a checker. Moved here from that
// file, which the A.4.1.4 rule on a checker's instance list took past the limit
// assert-no-oversized-source-files enforces.

#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"

namespace delta {

namespace {

// Whether `sub` stands in the header of the for loop `s` rather than in one of
// the positions A.6.4 gives a statement. A.6.8 writes `for_initialization ::=
// list_of_variable_assignments | for_variable_declaration {,
// for_variable_declaration}` and `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and
// Parser::ParseAssignmentOrExprNoSemi (src/parser/parser_stmt.cpp) records the
// assignment forms of both as a StmtKind::kBlockingAssign, so every for loop
// carries one in its header whatever its body assigns.
bool IsForHeaderStmt(const Stmt* s, const Stmt* sub) {
  for (const auto* init : s->for_inits)
    if (init == sub) return true;
  for (const auto* step : s->for_steps)
    if (step == sub) return true;
  return false;
}

// §17.5: walks a procedural statement tree looking for a blocking assignment.
// The clause lists what a checker always procedure may contain and writes
// "Blocking assignments (see 10.4.1; always_comb and always_latch procedures
// only)" on that list, naming no statement the restriction is lifted in, so
// this descends the links ForEachChildStmt in elaborator_validate_internal.h
// names rather than a list written out here. The list written here held six of
// the thirteen, so a blocking assignment in either arm of an immediate
// assertion's action block was never looked at: §17.5 puts immediate assertions
// on the same list, A.6.10 writes `simple_immediate_assert_statement ::= assert
// ( expression ) action_block`, and §16.3 writes `action_block ::=
// statement_or_null | [ statement ] else statement_or_null`, so both arms hold
// a statement. A randcase (§18.16) and a randsequence (A.6.12) are on §17.5's
// list of neither, so no conforming checker always procedure holds one; the
// walk descends them anyway, since what a checker procedure may hold is
// §17.5's own rule to report rather than a reason to keep a shorter list here.
//
// The visitor skips the two for-header links, which is the one position this
// rule does not reach. §17.5 admits "Loop statements (see 12.7)" in a checker
// always procedure with none of the always_comb/always_latch restriction it
// writes beside blocking assignments, and A.6.2 makes an operator_assignment
// and an inc_or_dec_expression -- two of the three forms A.6.8 gives a
// for_step_assignment, and the form it gives a for_initialization's
// variable_assignment -- alternatives of blocking_assignment. Reporting the
// header would therefore leave an always_ff no for loop that initializes or
// steps anything, which is not the loop statement §17.5 admits. The header
// holds no statement in the A.6.4 sense either, so nothing else is lost.
//
// ForEachChildStmt gives the visitor no way to stop, so the first hit is kept
// in `found` and the recursion runs only while `found` is false.
bool StmtContainsBlockingAssignment(const Stmt* stmt) {
  if (stmt == nullptr) return false;
  if (stmt->kind == StmtKind::kBlockingAssign) return true;
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found || IsForHeaderStmt(stmt, sub)) return;
    found = StmtContainsBlockingAssignment(sub);
  });
  return found;
}

// §17.5: walks a procedural statement tree looking for a timing control that is
// not an event control. Statement-level delay, cycle-delay, wait, and wait-fork
// controls are rejected, as is an intra-assignment delay or cycle delay on an
// assignment. An event control statement is itself permitted, but its
// controlled statement is still inspected in case a non-event control is nested
// inside.
//
// §17.5 says an initial procedure in a checker body "may contain let
// declarations, immediate, deferred, and concurrent assertions, and a
// procedural timing control statement using an event control only", and names
// no statement the rule is suspended in, so this descends the links
// ForEachChildStmt in elaborator_validate_internal.h names rather than a list
// written out here. The list written here held six of the thirteen, so a delay,
// a cycle delay or a wait in either arm of an immediate assertion's action
// block was never looked at: §17.5 puts immediate assertions on the same list,
// A.6.10 writes `simple_immediate_assert_statement ::= assert ( expression )
// action_block`, and §16.3 writes `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so both arms hold a statement.
//
// The other four links hold no such control in conforming source, and the walk
// descends them all the same. A.6.8 gives a for_initialization only a
// list_of_variable_assignments or for_variable_declarations and a
// for_step_assignment only an operator_assignment, an inc_or_dec_expression or
// a function_subroutine_call, none of which carries a delay_or_event_control or
// is a delay, cycle-delay or wait statement; a randcase (§18.16) and a
// randsequence (A.6.12) are on §17.5's list of neither.
//
// ForEachChildStmt gives the visitor no way to stop, so the first hit is kept
// in `found` and the recursion runs only while `found` is false.
bool StmtContainsNonEventTimingControl(const Stmt* stmt) {
  if (stmt == nullptr) return false;
  switch (stmt->kind) {
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
      return true;
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      // An intra-assignment event (`x <= @(ev) y;`) is an event control and is
      // allowed; only an intra-assignment delay or cycle delay is rejected.
      if (stmt->delay != nullptr || stmt->cycle_delay != nullptr) return true;
      break;
    default:
      break;
  }
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtContainsNonEventTimingControl(sub);
  });
  return found;
}

}  // namespace

// Emits the per-item legality diagnostics that depend only on the parent decl
// kind (no instance resolution): forbidden primitives/nets/always/nested decls
// inside programs/checkers/interfaces, and records port-less nested programs.
// §17.5/§17.7: the rules that govern what a checker body may contain -- no
// nets, no general `always`, no blocking assignment in an always_ff, only
// event-controlled timing in an initial procedure, and no design element other
// than a further checker.
void CheckCheckerBodyItemRules(const ModuleItem* item, const ModuleDecl* decl,
                               bool parent_is_checker, DiagEngine& diag) {
  if (!parent_is_checker) return;
  // A.10 item 6: "It shall be illegal for a checker_generate_item to include
  // any item that would be illegal in a checker_declaration outside a
  // checker_generate_item", so the items a generate construct holds -- in its
  // body, in its else body and in each of its case arms, the shape
  // CollectGenerateRoots in src/elaborator/elaborator_validate_clocking.cpp
  // walks -- are read by these same rules. The construct itself is none of
  // the items the rules below name, so it falls through them unreported.
  for (const auto* sub : item->gen_body) {
    CheckCheckerBodyItemRules(sub, decl, parent_is_checker, diag);
  }
  if (item->gen_else != nullptr) {
    CheckCheckerBodyItemRules(item->gen_else, decl, parent_is_checker, diag);
  }
  for (const auto& arm : item->gen_case_items) {
    for (const auto* sub : arm.body) {
      CheckCheckerBodyItemRules(sub, decl, parent_is_checker, diag);
    }
  }
  // §17.7: a checker body may define variables but not nets.
  if (item->kind == ModuleItemKind::kNetDecl) {
    diag.Error(item->loc,
               std::format("a net cannot be declared inside checker '{}'; "
                           "only variables may be defined in a checker body",
                           decl->name),
               Subclause("17.7"));
  }
  // §17.5: the only always procedures a checker admits are always_comb,
  // always_latch, and always_ff; a general 'always' is not among them (also
  // reflected in Annex C.2.7's removal of general always for checkers).
  if (item->kind == ModuleItemKind::kAlwaysBlock) {
    diag.Error(item->loc,
               std::format("a general 'always' procedure cannot be used "
                           "inside checker '{}'; use always_comb, "
                           "always_latch, or always_ff instead",
                           decl->name),
               Subclause("17.5"));
  }
  // §17.5/§17.7.1: a checker always_ff procedure may not use blocking
  // assignments (§17.7.1 states that only nonblocking assignments are allowed
  // there); blocking assignments are permitted only in always_comb and
  // always_latch.
  if (item->kind == ModuleItemKind::kAlwaysFFBlock &&
      StmtContainsBlockingAssignment(item->body)) {
    diag.Error(item->loc,
               std::format("a blocking assignment cannot appear in an "
                           "always_ff procedure of checker '{}'; use a "
                           "nonblocking assignment, or move it to an "
                           "always_comb or always_latch procedure",
                           decl->name),
               Subclause("17.7.1"));
  }
  // §17.5: an initial procedure in a checker body "may contain let
  // declarations, immediate, deferred, and concurrent assertions, and a
  // procedural timing control statement using an event control only". A.6.5
  // gives procedural_timing_control three alternatives -- delay_control,
  // event_control and cycle_delay -- so the other two are both excluded, as is
  // a wait. The message names all three rather than only the delay forms,
  // because a cycle delay is the one most easily mistaken for an event control:
  // §14.11 defines it as a wait for clocking block events, but the grammar
  // makes it its own alternative rather than an event_control.
  if (item->kind == ModuleItemKind::kInitialBlock &&
      StmtContainsNonEventTimingControl(item->body)) {
    diag.Error(item->loc,
               std::format("an initial procedure in checker '{}' may use only "
                           "an event control for timing; a delay, a cycle "
                           "delay and a wait are not allowed",
                           decl->name),
               Subclause("17.5"));
  }
  // §17.2: only further checkers may be declared inside a checker.
  if (item->kind == ModuleItemKind::kNestedModuleDecl &&
      item->nested_module_decl &&
      item->nested_module_decl->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("a module, interface, or program cannot be "
                           "declared inside checker '{}'",
                           decl->name),
               Subclause("17.2"));
  }
}

}  // namespace delta
