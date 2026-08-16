#pragma once

// Internal declarations shared between the elaborator_validate*.cpp translation
// units that were split out of elaborator_validate.cpp. These helpers are
// file-local in spirit; the header exists only so that one translation unit can
// define a helper that another references, keeping a single definition of each
// symbol.

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
template <typename Visit>
void ForEachRandsequenceRuleStmt(const RsRule& rule, Visit visit) {
  for (const auto* sub : rule.weight_code) visit(sub);
  for (const auto& prod : rule.prods) {
    for (const auto* sub : prod.code_stmts) visit(sub);
  }
}

// Hands `visit` every statement a randsequence statement holds, which is the
// only thing Stmt::rs_productions carries that is a statement at all. Call it
// from a walker that descends the other statement-holding fields of Stmt, so
// that a rule holds inside a randsequence as it holds outside one. The nesting
// is split across two functions because writing all four loops in one carries
// it past the readability-function-cognitive-complexity threshold of 15 that
// etc/clang_tidy/src.yml sets.
template <typename Visit>
void ForEachRandsequenceStmt(const Stmt* s, Visit visit) {
  for (const auto& production : s->rs_productions) {
    for (const auto& rule : production.rules) {
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
template <typename Visit>
void ForEachChildStmt(const Stmt* s, Visit visit) {
  for (const auto* sub : s->stmts) visit(sub);
  for (const auto* sub : s->fork_stmts) visit(sub);
  for (const auto* sub : s->for_inits) visit(sub);
  for (const auto* sub : s->for_steps) visit(sub);
  visit(s->then_branch);
  visit(s->else_branch);
  visit(s->body);
  visit(s->for_body);
  visit(s->assert_pass_stmt);
  visit(s->assert_fail_stmt);
  for (const auto& ci : s->case_items) visit(ci.body);
  for (const auto& rc : s->randcase_items) visit(rc.second);
  ForEachRandsequenceStmt(s, visit);
}

// Parses the size prefix of an integer literal's text (the digits before the
// base tick "'"). Returns that width when present and positive, otherwise the
// default unsized-literal width of 32. Defined in elaborator_validate.cpp.
uint32_t ExtractLiteralWidth(std::string_view text);

// Defined in elaborator_validate.cpp.
std::optional<int64_t> ComputeDimSize(const Expr* dim);
std::string_view LhsBaseName(const Expr* e);
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
