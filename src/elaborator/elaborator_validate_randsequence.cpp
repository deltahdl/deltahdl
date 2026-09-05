// §18.17 "Random sequence generation—randsequence" — resolving the production
// identifiers a randsequence statement writes. The clause makes that a
// question about the statement alone: "The randsequence statement creates an
// automatic scope. All production identifiers are local to the scope." So the
// set a production identifier resolves against is exactly the statement's own
// rs_productions, nothing an enclosing scope declares can answer one, and a
// name outside that set names no production at all.
//
// A translation unit of its own rather than an addition to
// elaborator_validate_jump_statements.cpp, which keeps §12.8's rules for break,
// continue and return together with §18.17.6's exemption from two of them.

#include <format>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

// The production identifiers `s` declares. §18.17 makes this the whole of the
// scope a production identifier written in `s` resolves against: the scope the
// randsequence statement creates is automatic and every production identifier
// is local to it, so no enclosing declaration reaches in and no production
// declared here reaches out.
NameSet DeclaredProductions(const Stmt* s) {
  NameSet declared;
  for (const auto& production : s->rs_productions) {
    declared.insert(production.name);
  }
  return declared;
}

// Reports one rs_production_item of `s` naming a production `declared` does not
// hold. Without this the name resolves to nothing at run time and generates
// nothing: FindProduction in src/simulator/stmt_exec_randsequence.cpp scans
// Stmt::rs_productions for the name and ExecRsProduction returns as though the
// production had been generated when the scan finds none, so a misspelled name
// costs the sequence that production and everything below it, silently.
//
// An item carrying no name is not one. Parser::ParseRsProd in
// src/parser/parser_randsequence.cpp fills the RsProd member its form uses and
// leaves the others default-constructed, so every rs_prod that is not an
// rs_if_else carries an empty RsProd::if_true. An empty name also stands where
// Parser::ParseRsProductionItem found no identifier, which it has reported
// already. That check runs before the location is read, and a
// default-constructed item is the only one carrying none.
//
// The report stands at the item's own identifier. It used to stand at the
// randsequence keyword, that being the only location the tree recorded, so two
// rules misspelling two different names produced two reports on one line and
// neither said which rule it was about.
void CheckProductionItem(const RsProductionItem& item, const NameSet& declared,
                         DiagEngine& diag) {
  if (item.name.empty()) return;
  if (declared.count(item.name) != 0) return;
  diag.Error(item.loc,
             std::format("randsequence production item names '{}', which is "
                         "not one of the productions this randsequence "
                         "statement declares",
                         item.name),
             Subclause("18.17"));
}

// Resolves every production identifier one randsequence statement writes.
void CheckRandsequence(const Stmt* s, DiagEngine& diag) {
  NameSet declared = DeclaredProductions(s);
  // §18.17: the keyword "can be followed by an optional production name
  // (inside the parentheses) that designates the name of the top-level
  // production. If unspecified, the first production becomes the top-level
  // production." Writing no name is that second case and names nothing, so
  // only a name that was written has a production to name.
  if (!s->rs_top_production.empty() &&
      declared.count(s->rs_top_production) == 0) {
    diag.Error(s->range.start,
               std::format("randsequence names '{}' as its top-level "
                           "production, which is not one of the productions it "
                           "declares",
                           s->rs_top_production),
               Subclause("18.17"));
  }
  // Every other production identifier comes from ForEachRandsequenceItem in
  // elaborator_validate_internal.h, which is the one list of the positions an
  // rs_production_item stands in.
  ForEachRandsequenceItem(s, [&](const RsProductionItem& item) {
    CheckProductionItem(item, declared, diag);
  });
}

// Walks one statement subtree, resolving the production identifiers of every
// randsequence statement in it. The child links come from ForEachChildStmt in
// elaborator_validate_internal.h, which is the one list of the fields of Stmt
// that hold a statement.
//
// A randsequence written inside another one's production code block is reached
// through that list and checked against its own productions, which is what
// §18.17 asks for: each statement creates a scope, and the identifiers of the
// inner one are local to the inner scope.
void CheckRandsequenceNames(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kRandsequence) CheckRandsequence(s, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckRandsequenceNames(sub, diag); });
}

// §6.18 / §18.17.7: rewrites each production's return type where it is written
// as a typedef name, so the value the production returns is sized by the type
// that name stands for. The simulator has no typedef table -- every site under
// src/simulator/ that sizes a production's return value reads the DataType and
// turns an unresolved 0 into 32 -- and this walk is the only one the elaborator
// has that reaches a randsequence statement at all.
//
// It walks beside CheckRandsequenceNames rather than inside it because the two
// answer different questions, and it takes a mutable statement because it
// writes: ForEachChildStmt hands out `Stmt* const&`, so the children of a
// statement reached from a const ModuleDecl are still writable.
void ResolveRandsequenceReturnTypes(Stmt* s, const TypedefMap& typedefs) {
  if (!s) return;
  if (s->kind == StmtKind::kRandsequence) {
    for (auto& production : s->rs_productions) {
      ResolveNamedReturnType(production.return_type, typedefs);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    ResolveRandsequenceReturnTypes(sub, typedefs);
  });
}

}  // namespace

void Elaborator::ValidateRandsequenceProductionNames(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      CheckRandsequenceNames(item->body, diag_);
      ResolveRandsequenceReturnTypes(item->body, typedefs_);
      continue;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts) {
        CheckRandsequenceNames(s, diag_);
        ResolveRandsequenceReturnTypes(s, typedefs_);
      }
    }
  }
}

}  // namespace delta
