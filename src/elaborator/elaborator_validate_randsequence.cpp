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
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
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

}  // namespace

void Elaborator::ValidateRandsequenceProductionNames(const ModuleDecl* decl) {
  CheckRandsequenceNamesIn(decl->items);
}

// §18.17 names no enclosing declaration the rule is suspended in, so every body
// a declaration owns is walked -- ForEachBodyOwningItem in
// elaborator_validate_internal.h is the one list of those, and a class method
// arrives as the kFunctionDecl or kTaskDecl item it is.
void Elaborator::CheckRandsequenceNamesIn(
    const std::vector<ModuleItem*>& items) {
  ForEachBodyOwningItem(items, [this](const ModuleItem* item) {
    if (IsProceduralItemKind(item->kind)) {
      CheckRandsequenceNames(item->body, diag_);
      return;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (const auto* s : item->func_body_stmts) {
        CheckRandsequenceNames(s, diag_);
      }
    }
  });
}

// §3.12.1 puts a declaration outside every design element in the
// compilation-unit scope and Clause 26 puts one in a package. Neither is
// elaborated through ElaborateItems, so RunPostItemValidations -- where the
// three per-declaration checks run, once per module -- never sees either, and
// every rule they enforce was unenforced there.
//
// The item lists walked here are the ones no module holds: the compilation
// unit's own, each package's, and the methods of each class declared outside
// every design element. A class declared inside a module or a package is
// reached through that scope's items by ForEachBodyOwningItem rather than here,
// so no body is walked twice and no report is made twice.
//
// The foreach check takes an array map built from the same items, which is what
// its dimension count is compared against; a name the map does not hold is left
// alone, exactly as it is for a module.
void Elaborator::ValidatePerDeclarationRulesInUnitScopes() {
  if (unit_ == nullptr) return;

  auto run_over = [this](const std::vector<ModuleItem*>& items) {
    std::unordered_map<std::string_view, const ModuleItem*> arrays;
    for (const auto* item : items) {
      if (item != nullptr && item->kind == ModuleItemKind::kVarDecl &&
          !item->name.empty()) {
        arrays.emplace(item->name, item);
      }
    }
    CheckJumpStatementsIn(items);
    CheckRandsequenceNamesIn(items);
    CheckForeachLoopsIn(items, arrays);
  };

  run_over(unit_->cu_items);
  for (const auto* pkg : unit_->packages) {
    if (pkg != nullptr) run_over(pkg->items);
  }
  for (const auto* cls : unit_->classes) {
    std::vector<ModuleItem*> methods;
    ForEachClassBodyItem(cls, [&](const ModuleItem* m) {
      methods.push_back(const_cast<ModuleItem*>(m));
    });
    run_over(methods);
  }
}

}  // namespace delta
