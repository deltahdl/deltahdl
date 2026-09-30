#pragma once

#include <string_view>
#include <unordered_set>
#include <utility>

#include "parser/parser.h"
#include "parser/scope_type_names.h"

namespace delta {

// §23.9 lists the elements that define a new scope: "Modules, Interfaces,
// Programs, Checkers, Packages, Classes, Tasks, Functions, begin-end blocks
// (named or unnamed), fork-join blocks (named or unnamed), Generate blocks"
// (printed page 761 of IEEE 1800-2023). A type name declared inside one
// is a type name there and not in the design element after it. Constructing
// this records what known_types_ and known_nettypes_ held on the way in;
// destroying it puts both back. §6.6.7's ParseNettypeDecl fills the two
// together, and a nettype name decides how `#` after an identifier is read,
// so restoring one without the other leaves the leak for that reading.
//
// All eleven of that list are guarded: a module, an interface, a program and
// a checker, plus the extern headers of the first three, at ParseModuleDecl,
// ParseInterfaceDecl, ParseProgramDecl, ParseCheckerDecl and
// ParseExternModuleDecl; a task, a function, a begin-end block, a fork-join
// block and a generate block, at ParseTaskDecl, ParseFunctionDecl,
// ParseBlockStmt, ParseForkStmt and ParseGenerateBody; and a package and a
// class, at ParsePackageDecl and ParseClassDecl. The last two guards are what
// package_types_ and class_types_ above exist for. Closing either scope takes
// its type names out of known_types_, and §26.3's import declaration and
// §8.13's extends clause are what put them back, in the scopes the standard
// says they are visible in and in no others.
//
// The last five are guarded for the same reason as the first four, and §23.9
// is what says a name inside them is never wanted outside. Its search runs
// upward and only upward: Figure 23-2 on printed page 762 gives block G the
// scopes containing it and denies it the scopes beside it, and a hierarchical
// path reaches a variable, a task, a function or a named block rather than a
// type. A data type is written as a bare or a package-scoped name, so a type
// declared in one of these five has no spelling that reaches it from outside,
// the named generate block included.
//
// A destructor rather than a save and a restore written at each site, because
// a parse function has more than one exit and error recovery takes some of
// them. A restore missed on one path reintroduces the leak for one kind of
// declaration while every test for the others stays green.
//
// Nothing guards the compilation unit itself. §3.12.1 makes a declaration at
// that scope visible in every design element of the unit, which is what
// leaving the outermost set alone gives, and it is why the built-in class
// names the constructor seeds stay visible throughout.
class TypeNameScope {
 public:
  explicit TypeNameScope(Parser& p)
      : parser_(p),
        saved_types_(p.known_types_),
        saved_nettypes_(p.known_nettypes_) {}
  ~TypeNameScope() {
    parser_.known_types_ = std::move(saved_types_);
    parser_.known_nettypes_ = std::move(saved_nettypes_);
  }
  TypeNameScope(const TypeNameScope&) = delete;
  TypeNameScope& operator=(const TypeNameScope&) = delete;

  // The names registered since this scope opened, which is what the scope's
  // own body declared. Call it before the scope closes: ParsePackageDecl and
  // ParseClassDecl each record the answer so that an import declaration or an
  // extends clause elsewhere can put those names back. A name declared by a
  // scope nested in this one is absent, because that scope's own guard
  // restored it away before this one is asked.
  ScopeTypeNames NamesAddedSoFar() const {
    ScopeTypeNames added;
    for (auto name : parser_.known_types_) {
      if (saved_types_.count(name) == 0) added.types.insert(name);
    }
    for (auto name : parser_.known_nettypes_) {
      if (saved_nettypes_.count(name) == 0) added.nettypes.insert(name);
    }
    return added;
  }

 private:
  Parser& parser_;
  std::unordered_set<std::string_view> saved_types_;
  std::unordered_set<std::string_view> saved_nettypes_;
};

}  // namespace delta
