#include "elaborator/elaborator_scope_rules_names.h"

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// A built-in data-type keyword (logic, bit, int, ...) parsed in expression
// position — e.g. the type argument of `$bits(logic [7:0])` — is materialized
// as a `kIdentifier` node carrying the keyword text (see
// ParseCastOrTypedPattern). Such a node is a type reference, not a value read,
// so it must never be checked against the value namespace. Mirrors
// IsCastTypeToken in the expression parser.
bool IsBuiltinTypeKeyword(std::string_view name) {
  static constexpr std::string_view kTypeKeywords[] = {
      "logic",   "bit",      "byte",   "int",       "shortint", "longint",
      "integer", "reg",      "real",   "shortreal", "realtime", "time",
      "signed",  "unsigned", "string", "const",     "void"};
  for (auto kw : kTypeKeywords) {
    if (name == kw) return true;
  }
  return false;
}

// True for a call whose arguments name something other than a value the
// enclosing scope declares, so that none of them is checked against it:
//
//   - an array manipulation method carrying a `with` clause. §7.12 gives
//     `q.sum(x) with (x * 10)` the iterator name `x` through that argument, and
//     §7.12.4 lets a second argument rename the index method, so both are
//     declared at the call rather than read from the module.
//   - randomize(). §18.11 rules that the arguments "designate the complete set
//     of random variables" of the calling object, so each names a property of
//     the object's class. Recognized in both the bare and the method-call form,
//     as Parser::CheckRandomizeArgList recognizes it.
bool CallArgsNameNoValue(const Expr* e) {
  if (e->kind != ExprKind::kCall) return false;
  if (e->with_expr != nullptr) return true;
  if (e->callee == "randomize") return true;
  return e->lhs != nullptr && e->lhs->kind == ExprKind::kMemberAccess &&
         e->lhs->rhs != nullptr && e->lhs->rhs->text == "randomize";
}

// §18.17.7: a production yields a readable value only where it declares a
// non-void return type. A production written with no return type "shall assume
// a void return type", so it declares no implicit variable at all and a read of
// its name resolves against nothing.
bool ProductionDeclaresReturnValue(const RsProduction& production) {
  return production.has_return_type &&
         production.return_type.kind != DataTypeKind::kVoid;
}

// §18.17.7: the names a randsequence statement declares for its own code blocks
// to read. "Within a rule, a variable is implicitly declared for each
// production (of the rule) that returns a value", carrying that production's
// name; and "a production creates a scope, which encompasses all its rules and
// code blocks", which is what makes a production's formal arguments readable
// throughout it.
//
// Collected flat over the whole statement, as every other name here is. The
// clause scopes an implicit variable to the rules that name its production --
// the same name is a scalar in one rule of §18.17.7's Example 2 and a 1..3
// array in another -- and it scopes a formal to its own production. A name that
// outlives either boundary can only suppress a report, never raise one, which
// is the trade the collection above is already written to.
void CollectRandsequenceDeclaredNames(
    const Stmt* s, std::unordered_set<std::string_view>& names) {
  for (const auto& production : s->rs_productions) {
    if (ProductionDeclaresReturnValue(production)) {
      names.insert(production.name);
    }
    for (const auto& port : production.ports) {
      if (!port.name.empty()) names.insert(port.name);
    }
  }
}

// §26.5 / Table 26-1: the enumeration constants declared inside a package's
// enum become directly visible through a wildcard import just like any other
// package declaration (the FALSE/TRUE members of the clause's example package
// p). Each member name is registered so that a name supplied by two
// wildcard-imported packages is detected as ambiguous, not just the enum type
// name itself. `origin` is the package declaring the enumeration.
//
// §6.19 has an enumerated type declare its literals as named constants of the
// scope holding the enum, and §23.9 lists no structure or union among the
// elements that define a scope, so an enum written as the type of a member of
// a structure or union (§7.2's struct_union_member takes any data_type, the
// enum form of Syntax 6-5 among them) declares its literals in the package as
// an enum written at the top of the declaration does. The member's type is
// held by StructMember::nested_type, and a structure nested in a member is
// descended into the same way; a member of a named type declares nothing.
//
// §6.19.2's Table 6-10 has a `name[N]` member generate name0 through nameN-1
// and a `name[N:M]` member nameN through nameM, the written name itself naming
// no constant, so each generated name is a name the package provides and the
// written one is not: `p1::VAL` for `VAL[3]` names nothing p1 declares, and
// `p2::VAL2` through p2's `export p1::*` names p1's constant. The bounds are
// folded against no scope, this walk running on the syntax tree alone with
// the package's parameters registered elsewhere (RegisterPackageParams in
// elaborator_resolve.cpp); a bound naming a parameter does not fold, and
// EnumMemberDeclaredNames then keeps the written name, which can only
// suppress a report, never raise one. The generated names are spelled by no
// declaration, which is why ProvidedNames owns its keys.
void AddEnumMemberNames(const DataType& type, std::string_view origin,
                        ProvidedNames& names) {
  const ScopeMap kNoScope;
  for (const auto& em : type.enum_members) {
    if (em.name.empty()) continue;
    for (const std::string& name : EnumMemberDeclaredNames(em, kNoScope)) {
      names.emplace(name, origin);
    }
  }
  for (const auto& sm : type.struct_members) {
    if (sm.nested_type != nullptr) {
      AddEnumMemberNames(*sm.nested_type, origin, names);
    }
  }
}

// The names one package item of `pkg` makes directly visible: its own name,
// the name of a class it declares, and any enumeration constants it brings,
// which may sit on a typedef's type, on a bare enum data declaration, or on a
// member of a structure or union either of those writes inline. Each is
// declared by `pkg`. A name already in the map keeps its first origin: the
// package's own items are added ahead of what its exports hand on, and §26.3
// has a declaration of the scope take the name over an import.
void AddPackageItemNames(const PackageDecl* pkg, const ModuleItem* pi,
                         ProvidedNames& names) {
  if (!pi->name.empty()) names.emplace(pi->name, pkg->name);
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
      !pi->class_decl->name.empty()) {
    names.emplace(pi->class_decl->name, pkg->name);
  }
  AddEnumMemberNames(pi->typedef_type, pkg->name, names);
  AddEnumMemberNames(pi->data_type, pkg->name, names);
}

const PackageDecl* FindPackageDecl(const CompilationUnit* unit,
                                   std::string_view pkg_name) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name == pkg_name) return pkg;
  }
  return nullptr;
}

void AddPackageProvidedNames(const CompilationUnit* unit,
                             const PackageDecl* pkg, ProvidedNames& names,
                             std::unordered_set<const PackageDecl*>& visited);

// The package declaring `name` as the package `src_name` provides it, which is
// what an explicit import or export of `src_name::name` reaches (§26.6: p2's
// `import p1::x; export p1::*;` makes p1::x and p2::x one declaration). The
// source package's provided names are gathered afresh over a copy of
// `visited`, so a source already on the chain, which a cycle of exports makes,
// contributes nothing and the name is taken as the source's own; so is a name
// the source does not provide, which the source itself is reported for.
std::string_view DeclaringPackageOf(
    const CompilationUnit* unit, std::string_view src_name,
    std::string_view name,
    const std::unordered_set<const PackageDecl*>& visited) {
  const PackageDecl* src = FindPackageDecl(unit, src_name);
  if (src == nullptr) return src_name;
  ProvidedNames provided;
  std::unordered_set<const PackageDecl*> sub = visited;
  AddPackageProvidedNames(unit, src, provided, sub);
  auto it = provided.find(name);
  return it == provided.end() ? src_name : it->second;
}

// The names `pkg` imports from the package `src_name`, which an export of
// that package hands on (§26.6): the one name of each explicit import, and
// for a wildcard import every name the source package provides. §26.6 hands
// on only what a wildcard import actually imported, which is decided by the
// references the package makes; every candidate is taken instead, which can
// only suppress a report, never raise one.
void AddImportedNamesFrom(const CompilationUnit* unit, const PackageDecl* pkg,
                          std::string_view src_name, ProvidedNames& names,
                          std::unordered_set<const PackageDecl*>& visited) {
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (imp.package_name != src_name) continue;
    if (!imp.is_wildcard) {
      names.emplace(imp.item_name,
                    DeclaringPackageOf(unit, src_name, imp.item_name, visited));
    } else if (const PackageDecl* src = FindPackageDecl(unit, src_name)) {
      AddPackageProvidedNames(unit, src, names, visited);
    }
  }
}

// §26.6: by default what a package imports is not visible through an import
// of that package, so an import item of `pkg` adds no name of its own here;
// an export declaration is what hands an imported name on. `export *::*`
// hands on every import of the package, `export src::*` those from one
// package, and `export src::name` the one name.
void AddExportedNames(const CompilationUnit* unit, const PackageDecl* pkg,
                      ProvidedNames& names,
                      std::unordered_set<const PackageDecl*>& visited) {
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const ImportItem& ex = item->import_item;
    if (ex.package_name == "*") {
      for (const auto* imp : pkg->items) {
        if (imp->kind != ModuleItemKind::kImportDecl) continue;
        AddImportedNamesFrom(unit, pkg, imp->import_item.package_name, names,
                             visited);
      }
    } else if (ex.is_wildcard) {
      AddImportedNamesFrom(unit, pkg, ex.package_name, names, visited);
    } else {
      names.emplace(ex.item_name, DeclaringPackageOf(unit, ex.package_name,
                                                     ex.item_name, visited));
    }
  }
}

// The names `pkg` makes directly visible to a scope that imports it by
// wildcard: its own declarations, and what its exports hand on of its
// imports. A package reached twice along a chain of exports adds its names
// once, which is also what ends a cycle of exports.
void AddPackageProvidedNames(const CompilationUnit* unit,
                             const PackageDecl* pkg, ProvidedNames& names,
                             std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (const auto* pi : pkg->items) AddPackageItemNames(pkg, pi, names);
  AddExportedNames(unit, pkg, names, visited);
}

// §21.2's display and write tasks, §21.2.3's strobe and monitor tasks, the
// file forms §21.3 gives each of them, and §20.10's severity tasks. Every
// argument of one is a value read as an assignment's right side is, so a bare
// identifier among them that names no declaration is §23.9's unresolved
// reference; `$display("%0d", x)` read an undeclared x with nothing said. The
// tasks that take a scope or a definition name, $dumpvars and the assertion
// control tasks of §20.11 among them, are not here, an argument of theirs
// naming no value.
bool IsValueListSystemTask(const Expr* call) {
  static constexpr std::string_view kTasks[] = {
      "$display",   "$displayb",  "$displayo",  "$displayh",  "$write",
      "$writeb",    "$writeo",    "$writeh",    "$strobe",    "$strobeb",
      "$strobeo",   "$strobeh",   "$monitor",   "$monitorb",  "$monitoro",
      "$monitorh",  "$fdisplay",  "$fdisplayb", "$fdisplayo", "$fdisplayh",
      "$fwrite",    "$fwriteb",   "$fwriteo",   "$fwriteh",   "$fstrobe",
      "$fstrobeb",  "$fstrobeo",  "$fstrobeh",  "$fmonitor",  "$fmonitorb",
      "$fmonitoro", "$fmonitorh", "$error",     "$warning",   "$info",
      "$fatal"};
  if (call->kind != ExprKind::kSystemCall) return false;
  for (std::string_view task : kTasks) {
    if (call->callee == task) return true;
  }
  return false;
}

}  // namespace

void PopulatePackageProvidedNames(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  ProvidedNames& names) {
  const PackageDecl* pkg = FindPackageDecl(unit, pkg_name);
  if (pkg == nullptr) return;
  std::unordered_set<const PackageDecl*> visited;
  AddPackageProvidedNames(unit, pkg, names, visited);
}

// The operands of `e` that a value read could name. Three kinds of node hold an
// identifier-shaped child that names something other than a value, and each is
// left out:
//
//   - the callee of a call, which Parser::ParseCallExpr writes into lhs. §23.9
//     rules that the search for "a task, function, named block, or generate
//     block ... continues to search higher level modules until found", so a
//     callee is not held to the module boundary a variable read is held to.
//   - the slice size or type of a §11.4.14.2 streaming concatenation, which
//     Parser::ParseStreamingConcat writes into lhs. `{<< 8 {a}}` puts the 8
//     there as an identifier node, and it names a width rather than a value.
//   - the member name of a §7.3.2 tagged union expression, which
//     Parser::ParseTaggedExpr writes into rhs. `tagged Valid x` names a member
//     of the union type there, not a declaration of the enclosing scope.
//
// Expr::with_expr is left out whatever the node is. §7.12.1 binds the iterator
// name an array method's `with` clause reads -- `q.sum() with (item)` declares
// `item` at the call -- and §18.7 resolves the names of an inline constraint
// block against the object being randomized, so neither is a name the enclosing
// module declares.
static void CollectBareIdentOperands(const Expr* e,
                                     std::vector<const Expr*>& out) {
  bool lhs_names_no_value =
      e->kind == ExprKind::kCall || e->kind == ExprKind::kStreamingConcat;
  if (!lhs_names_no_value) CollectBareIdents(e->lhs, out);
  if (e->kind != ExprKind::kTagged) CollectBareIdents(e->rhs, out);
  CollectBareIdents(e->base, out);
  CollectBareIdents(e->index, out);
  CollectBareIdents(e->index_end, out);
  CollectBareIdents(e->condition, out);
  CollectBareIdents(e->true_expr, out);
  CollectBareIdents(e->false_expr, out);
  CollectBareIdents(e->repeat_count, out);
  if (!CallArgsNameNoValue(e)) {
    for (const auto* a : e->args) CollectBareIdents(a, out);
  }
  for (const auto* el : e->elements) CollectBareIdents(el, out);
}

// Collects standalone identifier operands of `e`, deliberately NOT descending
// into member-access subtrees (so the base of `a.b`, `s.field`, `$root.x`, or
// `pkg::x` is never collected) and skipping scope-prefixed identifiers. Only
// the plain `kIdentifier` reads that must resolve to a local declaration
// survive.
void CollectBareIdents(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) return;
  if (e->kind == ExprKind::kIdentifier) {
    // `null` (§6.24.1) and the `$` of an open range or a queue's last index
    // (§7.10.1) parse as identifier-shaped nodes and name no declaration, so
    // neither is a read this can find a declaration for. Nor is a §12.6
    // pattern's `. variable_identifier`, which declares the variable it names
    // (Expr::is_pattern_binding); it is reached here through a matches
    // condition, whose pattern side is the expression's right operand.
    if (e->scope_prefix.empty() && !IsBuiltinTypeKeyword(e->text) &&
        e->text != "null" && e->text != "$" && !e->is_pattern_binding) {
      out.push_back(e);
    }
    return;
  }
  CollectBareIdentOperands(e, out);
}

// The packages a module imports by wildcard. §26.3 makes every name such a
// package declares directly visible, so a bare read of one resolves, and the
// module's own symbol table does not enumerate them. Each name is looked up in
// these packages rather than the module skipped whole, because skipping
// silences the check on every other name of the module too.
std::vector<std::string_view> WildcardImportedPackages(const RtlirModule* mod) {
  std::vector<std::string_view> pkgs;
  for (const auto& imp : mod->imports) {
    if (imp.is_wildcard) pkgs.push_back(imp.package_name);
  }
  return pkgs;
}

static void CollectGenerateBodyNames(
    const std::vector<ModuleItem*>& items,
    std::unordered_set<std::string_view>& names);

// The names one generate construct declares: the label of each of its blocks,
// the loop variable §27.4 makes an implicit localparam of each generated block,
// and the name of every item declared inside one.
static void CollectOneGenerateNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& names) {
  const Stmt* init = item->gen_init;
  if (init != nullptr && init->lhs != nullptr &&
      init->lhs->kind == ExprKind::kIdentifier) {
    names.insert(init->lhs->text);
  }
  if (init != nullptr && !init->var_name.empty()) names.insert(init->var_name);
  CollectGenerateBodyNames(item->gen_body, names);
  if (item->gen_else != nullptr) {
    CollectGenerateBodyNames(item->gen_else->gen_body, names);
  }
  for (const auto& ci : item->gen_case_items) {
    CollectGenerateBodyNames(ci.body, names);
  }
}

// Over-approximated set of the names a module's generate constructs declare,
// and of its genvars. §23.9 makes a generate block a scope of its own, so the
// elaborated module's symbol table does not list what one declares, and a flat
// set holds names that are declared per block rather than module-wide.
// Over-approximating is safe for the reason CollectProcLocalNames records: a
// name in the set can only suppress a diagnostic, never raise one.
static void CollectGenerateBodyNames(
    const std::vector<ModuleItem*>& items,
    std::unordered_set<std::string_view>& names) {
  for (const auto* item : items) {
    if (!item->name.empty()) names.insert(item->name);
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      CollectOneGenerateNames(item, names);
    }
  }
}

// The same over a module's own items, where only a genvar and what a generate
// construct declares are names the module's symbol table does not already list.
void CollectModuleGenerateNames(const std::vector<ModuleItem*>& items,
                                std::unordered_set<std::string_view>& names) {
  for (const auto* item : items) {
    if (item->is_genvar && !item->name.empty()) names.insert(item->name);
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      CollectOneGenerateNames(item, names);
    }
  }
}

// Over-approximated set of names that are local to a procedural block: block
// (begin/end) variable declarations, for-loop control variables, foreach index
// variables, and the two kinds of name §18.17.7 gives a randsequence statement.
// Collected flat across the whole block tree without tracking scope
// boundaries — that can only ever SUPPRESS a diagnostic, never raise one, so a
// missed boundary is always safe.
void CollectProcLocalNames(const Stmt* s,
                           std::unordered_set<std::string_view>& names) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    names.insert(s->var_name);
  }
  for (auto v : s->foreach_vars) names.insert(v);
  // A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`,
  // and the target of one such assignment is an expression rather than a
  // statement, so the control variable it declares is read here and not
  // through the descent below. §12.7.1 makes it a declaration of the loop.
  for (const auto* fi : s->for_inits) {
    if (fi && fi->lhs && fi->lhs->kind == ExprKind::kIdentifier) {
      names.insert(fi->lhs->text);
    }
  }
  CollectRandsequenceDeclaredNames(s, names);
  // §6.5 rules that "Data shall be declared before they are used, apart from
  // implicit nets", and puts no condition on the statement the declaration
  // stands in, so every position a statement holds a statement in is a
  // position this collection reaches. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here. The
  // visitor takes `Stmt* const&` because `s` is a `const Stmt*`, which is how
  // ForEachChildStmt lets a walk that only reads the tree share its list with
  // the walks that rewrite it.
  //
  // The list written out here before was nine of the thirteen links, missing
  // Stmt::assert_pass_stmt, Stmt::assert_fail_stmt, the body of a randcase
  // item, and the two statement lists Stmt::rs_productions holds. That
  // omission cost a report made wrongly rather than a report not made: a name
  // declared in one of those positions was absent from `names`, so the read of
  // it that CollectProcRhsIdents below hands to ReportUnresolvedRefs resolves
  // against nothing and is reported under §23.9 as unresolved. Nothing
  // observed the false positive because CollectProcRhsIdents was short by the
  // same four links and never collected the read either, which is why the two
  // halves of the check are put on this list together.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectProcLocalNames(sub, names); });
}

// Collects the bare identifier reads of every procedural blocking/nonblocking
// assignment's right side, dropping the ones a block-local declaration names.
// The caller then rejects any that resolve to no declaration.
//
// CollectBareIdents is what walks each right side, so a read written inside a
// larger expression is reached under the same guards a continuous assignment's
// whole right side is already walked under: no descent into a member access, so
// the base of `a.b`, `pkg::x` and a `with` clause hanging off one is never
// collected, and no scope-prefixed name, builtin type keyword, `null` or `$`.
// Those guards are what keep this free of false positives; an earlier version
// took the right side only when the whole of it was one identifier, which left
// `r = v + 0;` unchecked.
void CollectProcRhsIdents(const Stmt* s,
                          const std::unordered_set<std::string_view>& locals,
                          std::vector<const Expr*>& out) {
  if (!s) return;
  const Expr* read = nullptr;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    read = s->rhs;
  } else if (const Expr* call = SubroutineCallOfStmt(s);
             call != nullptr && IsValueListSystemTask(call)) {
    read = call;
  }
  std::vector<const Expr*> refs;
  CollectBareIdents(read, refs);
  // §23.9 and §6.5 say nothing about the position a read stands in, and an
  // assignment's right side is one of several a statement evaluates: the
  // condition of an if, a while, a repeat, a do-while or a wait and the
  // selector of a case (Stmt::condition), a for loop's condition, a case
  // item's pattern (a value the selector is compared with, §12.5 -- unless the
  // case is §12.6's `matches`, whose patterns declare rather than read), and
  // the expressions a randsequence statement holds outside its code blocks: an
  // rs_if_else condition, an rs_case expression and its arms, a rule's weight,
  // a rand join's expression and a production item's actual arguments
  // (ForEachRandsequenceExpr in elaborator_validate_internal.h). Left to the
  // right side alone, `if (undeclared) x = 1;` elaborated clean. A statement's
  // delay, event control, disable target, initializer and assertion are not
  // read here.
  CollectBareIdents(s->condition, refs);
  CollectBareIdents(s->for_cond, refs);
  if (!s->case_matches) {
    for (const auto& ci : s->case_items) {
      for (const auto* p : ci.patterns) CollectBareIdents(p, refs);
    }
  }
  ForEachRandsequenceExpr(s,
                          [&](Expr* const& e) { CollectBareIdents(e, refs); });
  for (const auto* r : refs) {
    if (locals.count(r->text) == 0) out.push_back(r);
  }
  // §6.5's declared-before-use rule is broken by the assignment wherever the
  // assignment stands, and §26.3 makes an identifier a package supplies
  // visible "within the current scope without a package name qualifier"
  // wherever the read of it stands, so every position a statement holds a
  // statement in is a position one of these reads is written in.
  // ForEachChildStmt in elaborator_validate_internal.h states those positions
  // once for the whole elaborator, which is why the list is not written out
  // again here.
  //
  // The list written out here before was the same nine links
  // CollectProcLocalNames above wrote out, missing the same four. That
  // omission cost a report not made: an assignment whose right side read a
  // name nothing declares was never collected when it stood in an immediate
  // assertion's pass statement, in its fail statement, in a randcase item, or
  // in either code block of a randsequence production, so §23.9's "reference to
  // unresolved identifier" was never reported for it and the source elaborated
  // clean.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectProcRhsIdents(sub, locals, out); });
}

// The names a subroutine's body may read without the module declaring them:
// §13.3 makes each formal argument a declaration of the subroutine, §13.4.1
// makes a function's own name a variable of it, and a body may declare its own.
void CollectSubroutineLocalNames(const ModuleItem* item,
                                 std::unordered_set<std::string_view>& names) {
  if (!item->name.empty()) names.insert(item->name);
  for (const auto& arg : item->func_args) {
    if (!arg.name.empty()) names.insert(arg.name);
  }
  for (const auto* stmt : item->func_body_stmts) {
    if (stmt != nullptr && stmt->kind == StmtKind::kBlockItemDecl &&
        stmt->decl_item != nullptr && !stmt->decl_item->name.empty()) {
      names.insert(stmt->decl_item->name);
    }
    CollectProcLocalNames(stmt, names);
  }
}

}  // namespace delta
