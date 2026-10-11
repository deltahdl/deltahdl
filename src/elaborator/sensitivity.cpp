#include "elaborator/sensitivity.h"

#include <cstddef>
#include <functional>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// The prefix is spelled as the simulator names what it reads, an element by
// its index's 32 bits (LongestStaticStorageName): `p[-1]` of `p [-1:0]` is
// held as p[4294967295], and spelled p[-1] it named no variable, so a
// continuous assignment reading it ran once and never again.
static void CollectSelectReads(const Expr* expr,
                               std::unordered_set<std::string>& out) {
  out.insert(LongestStaticStorageName(expr));

  const Expr* cur = expr;
  while (cur && cur->kind == ExprKind::kSelect) {
    if (cur->index && cur->index->kind != ExprKind::kIntegerLiteral) {
      CollectExprReads(cur->index, out);
    }
    cur = cur->base;
  }
  // §9.2.2.2.1 asks for the expansion of the longest static prefix of every net
  // or variable identifier or select expression read, and the prefix itself is
  // not always one of those expansions. Where the index folds,
  // BuildSelectPrefix returns the text `b[3]`, which names a position within a
  // vector and no object: SimContext::FindVariable resolves a declared name
  // against variables_, and `logic [3:0] b` is one Variable named `b`. So the
  // name reached nothing and AnyChangeAwaiter::await_suspend armed no watcher
  // at all -- silently, since it drops a name it cannot resolve. The identifier
  // the chain stands on is the coarsest expansion, and it is always an object.
  //
  // It is the only name a distributed instance-array terminal ever gets:
  // InstanceArrayElementTerminals in elaborator_gates.cpp connects element p
  // through MakeBitSelect with a literal index, so every element of
  // `udp_and2 ga [3:0] (y, a, b)` watched nothing and evaluated once. Where the
  // index does not fold the prefix is already the bare name, which is why the
  // genvar-indexed form in test/src/e2e/udp_generate.sv kept working.
  //
  // The added name over-triggers: a change anywhere in `b` wakes a process that
  // reads `b[3]` alone. Every consumer re-reads what it watches -- a UDP
  // coroutine its terminals, a continuous assignment its right-hand side, a
  // wait its condition -- so a wake with nothing changed commits the value that
  // already stood. An always_comb keeps its own output out of its list by the
  // same root name, since CollectAssignLhsName below walks a written select
  // down to the identifier it stands on, which is what §9.2.2.2.1's exception
  // (b) needs it to be.
  if (cur && cur->kind == ExprKind::kIdentifier) {
    if (!cur->text.empty()) out.insert(std::string(cur->text));
    return;
  }
  // A select the elaborator built over an expression rather than a name:
  // EmitConcatContAssigns in elaborator_cont_assign.cpp hands each element of
  // a concatenation target its slice of the whole right-hand side as
  // `(rhs + 0)[hi:lo]`, so the chain stands on the widened expression and on
  // no identifier at all. Its operands are what the slice reads, and they were
  // read by nothing here: `assign {c, s} = a + b;` was evaluated once and
  // never again, whatever a and b later did.
  CollectExprReads(cur, out);
}

bool DottedNamePath(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->lhs == nullptr ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (!DottedNamePath(expr->lhs, out)) return false;
  out += expr->is_scope_resolution ? "::" : ".";
  out += expr->rhs->text;
  return true;
}

void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.insert(std::string(expr->text));
    return;
  }
  // §25.10 with §10.3.2 and §23.6: a member access down a path of names reads
  // the variable held under the dotted name, a member of an interface
  // instance, `assign w = dif.clk;`, or of a module instance, as well as the
  // parts the recursion below collects (a struct member's variable is its
  // base's). §26.3 and §8.23 make `p::g` such a path too, a package's variable
  // or a class's static property. A name no variable is held under is dropped
  // by the reader (DropUnwatchableNames). Collected as `dif` and `clk` alone,
  // the reads named no variable, and a port connected to `dif.clk` never
  // followed it.
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string dotted;
    if (DottedNamePath(expr, dotted)) out.insert(dotted);
  }
  if (expr->kind == ExprKind::kSelect) {
    CollectSelectReads(expr, out);
    return;
  }
  if (expr->kind == ExprKind::kCall) {
    // A call contributes to the implicit sensitivity list only through its
    // argument expressions. The callee reference itself adds nothing: a plain
    // function name is neither a net nor a variable, and a reference to a class
    // object on which a method is invoked (or a class scope-resolved name)
    // contributes only via the arguments passed to the call.
    for (auto* arg : expr->args) CollectExprReads(arg, out);
    return;
  }
  CollectExprReads(expr->lhs, out);
  CollectExprReads(expr->rhs, out);
  CollectExprReads(expr->condition, out);
  CollectExprReads(expr->true_expr, out);
  CollectExprReads(expr->false_expr, out);
  CollectExprReads(expr->base, out);
  CollectExprReads(expr->index, out);
  for (auto* arg : expr->args) CollectExprReads(arg, out);
  for (auto* elem : expr->elements) CollectExprReads(elem, out);
}

// The index expressions of an assignment's left-hand side, which are read where
// the object they address is written; those of each target a concatenation
// left-hand side writes, `{y[i], z} = d`, included (§9.4.2.2).
static void ForEachLhsIndexRead(const Expr* lhs,
                                const std::function<void(const Expr*)>& fn) {
  for (const Expr* cur = lhs; cur != nullptr; cur = cur->base) {
    if (cur->kind == ExprKind::kConcatenation) {
      for (const Expr* target : cur->elements) ForEachLhsIndexRead(target, fn);
      return;
    }
    if (cur->kind != ExprKind::kSelect) return;
    if (cur->index) fn(cur->index);
  }
}

// True when `sub` is one of the two statements of `owner`'s assertion action
// block. §9.2.2.2.1 (printed page 223) says an expression in an assertion
// action block adds nothing to an always_comb's implicit sensitivity list, and
// its example has the always_comb trigger on b, c and e while `disable_error`,
// read in the else branch of `A1:assert (a != e) else if (!disable_error)
// $error("failed");`, stays out. So the two walks that collect reads stop at
// these, and the two that collect writes and block-local declarations do not:
// exception (b) is about where a name is written and exception (a) about where
// one is declared, and neither is a rule about what contributes.
//
// The sentence before it puts the asserted expression itself in the list, as
// though it were an if statement's condition, which is Stmt::assert_expr and is
// read directly rather than through this descent.
bool IsAssertionActionBlock(const Stmt* owner, const Stmt* sub) {
  return sub != nullptr &&
         (sub == owner->assert_pass_stmt || sub == owner->assert_fail_stmt);
}

// §9.2.2.2.1 takes the longest static prefix of every net or variable read
// within the block. Its three exceptions name no statement position, and the
// one position the clause does exclude is the assertion action block
// IsAssertionActionBlock above answers for, so a read counts wherever else a
// statement holds a statement.
//
// ForEachChildStmt in elaborator_validate_internal.h states those thirteen
// positions, once for the whole elaborator, which is why the list is not
// written out again here. It hands the visitor the field itself, so a walk that
// only reads the tree takes a `Stmt* const&`.
//
// The expression fields are read one by one rather than through the
// ForEachChildExpr beside it, because exception (c) excludes an identifier that
// appears only in a timing control expression and not reading those fields is
// how this function implements it. ForEachChildExpr hands over Stmt::delay,
// Stmt::cycle_delay, Stmt::events, Stmt::repeat_event_count and
// Stmt::wait_order_events along with the rest, giving the visitor no way to
// tell a timing control expression from an ordinary one; a wait statement's
// condition is skipped here for the same reason. The positions read are
// Stmt::condition, Stmt::rhs, Stmt::expr, Stmt::for_cond, Stmt::assert_expr,
// Stmt::var_init, the weight of each Stmt::randcase_items entry and the
// patterns of each Stmt::case_items entry.
void ForEachStmtReadExpr(const Stmt* stmt,
                         const std::function<void(const Expr*)>& fn) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    ForEachLhsIndexRead(stmt->lhs, fn);
  }
  if (stmt->kind != StmtKind::kWait) {
    fn(stmt->condition);
  }
  fn(stmt->rhs);
  fn(stmt->expr);
  fn(stmt->for_cond);
  fn(stmt->assert_expr);
  // A.2.4 gives a variable_decl_assignment an initializer, which the parser
  // keeps in Stmt::var_init. It is an ordinary expression and not a timing
  // control, so exception (c) leaves what it reads in the list, and exception
  // (a) removes the name being declared rather than the names its initializer
  // reads.
  fn(stmt->var_init);
  // §18.16 makes a randcase weight an expression the statement evaluates:
  // the randcase weights may be any expressions, not constants alone, and its
  // example weighs branches by `a + b` over two byte variables, each weight
  // expression being evaluated at most once per execution. A variable named
  // there is therefore read within the block, and no exception of §9.2.2.2.1
  // removes it. That is the same answer WalkStmtCaseIdents in
  // elaborator_scope_rules.cpp gives the position for §26.3.
  for (const auto& rc : stmt->randcase_items) fn(rc.first);
  // The case-item bodies are statements the descent below reaches; the patterns
  // are expressions it does not, so they are read here.
  for (const auto& ci : stmt->case_items) {
    for (const auto* pat : ci.patterns) fn(pat);
  }
  ForEachChildStmt(stmt, [stmt, &fn](Stmt* const& sub) {
    if (IsAssertionActionBlock(stmt, sub)) return;
    ForEachStmtReadExpr(sub, fn);
  });
}

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out) {
  ForEachStmtReadExpr(stmt,
                      [&out](const Expr* e) { CollectExprReads(e, out); });
}

// The names an assignment's left-hand side `lhs` writes: the identifier each
// target stands on, and, for a select, its longest static prefix as
// CollectSelectReads spells a read of it, `y[0]`, so that §9.2.2.2.1's
// exception (b) takes out a select the block both writes and reads, which the
// identifier alone does not name. Each target of a concatenation is a write.
static void CollectAssignLhsName(const Expr* lhs,
                                 std::unordered_set<std::string>& out) {
  if (!lhs) return;
  if (lhs->kind == ExprKind::kConcatenation) {
    for (const Expr* target : lhs->elements) CollectAssignLhsName(target, out);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) out.insert(LongestStaticStorageName(lhs));
  const Expr* e = lhs;
  while (e->kind == ExprKind::kSelect && e->base) e = e->base;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty())
    out.insert(std::string(e->text));
}

// §9.2.2.2.1 exception (b) leaves out of the list any expression also written
// within the block, and names no statement position either, so a write counts
// wherever a statement holds a statement. A write this walk does not reach is a
// name the exception does not remove, which puts the process's own output in
// its sensitivity list and re-triggers it on its own assignment.
//
// The positions come from ForEachChildStmt in
// elaborator_validate_internal.h, stated there once for the whole elaborator.
void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    CollectAssignLhsName(stmt->lhs, out);
  }
  ForEachChildStmt(stmt,
                   [&out](Stmt* const& sub) { CollectWrittenNames(sub, out); });
}

// §9.2.2.2.1 exception (a) leaves out of the list any expansion of a variable
// declared within the block, and names no statement position, so a declaration
// counts wherever a statement holds a statement. A.6.3 admits a
// block_item_declaration at the head of every seq_block, and a seq_block stands
// in each of those positions, so a declaration this walk does not reach is a
// block-local name the exception does not remove and the list then carries a
// name no net or variable of the design answers to.
//
// The positions come from ForEachChildStmt in elaborator_validate_internal.h,
// stated there once for the whole elaborator.
static void CollectBlockLocalNames(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kVarDecl && !stmt->var_name.empty()) {
    out.insert(std::string(stmt->var_name));
  }
  ForEachChildStmt(
      stmt, [&out](Stmt* const& sub) { CollectBlockLocalNames(sub, out); });
}

// The key a call's function stands under in the FuncMap, the path of names
// its callee spells: `f`; the "p::f" RecordPackageFuncNames
// (elaborator_items_udp.cpp) enters a package's function under (§26.3); and
// the "C::f", "p::C::f" and "s.t.f" AddScopedCallFunctions enters a class's
// static method and a function a hierarchical path reaches under (§8.23,
// §23.6). A callee that is no
// such path, and a call with no callee node, a constructor's `new`, spell an
// empty key the table holds nothing under.
static std::string CalledFunctionKey(const Expr& call) {
  std::string path;
  if (call.lhs != nullptr) DottedNamePath(call.lhs, path);
  return path;
}

static void CollectCallNamesFromExpr(const Expr* expr,
                                     std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall) out.insert(CalledFunctionKey(*expr));
  CollectCallNamesFromExpr(expr->lhs, out);
  CollectCallNamesFromExpr(expr->rhs, out);
  CollectCallNamesFromExpr(expr->condition, out);
  CollectCallNamesFromExpr(expr->true_expr, out);
  CollectCallNamesFromExpr(expr->false_expr, out);
  CollectCallNamesFromExpr(expr->base, out);
  CollectCallNamesFromExpr(expr->index, out);
  for (auto* arg : expr->args) CollectCallNamesFromExpr(arg, out);
  for (auto* elem : expr->elements) CollectCallNamesFromExpr(elem, out);
}

// §9.2.2.2.1 counts a read inside any function the block calls, and puts no
// condition on where in the block the call stands, so a call counts wherever a
// statement holds a statement. A call this walk does not reach contributes none
// of the called function's reads.
//
// The positions come from ForEachChildStmt in
// elaborator_validate_internal.h, and the expressions are read one by one for
// the reason CollectStmtReads above gives.
static void CollectCallNamesFromStmt(const Stmt* stmt,
                                     std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind != StmtKind::kWait) {
    CollectCallNamesFromExpr(stmt->condition, out);
  }
  CollectCallNamesFromExpr(stmt->rhs, out);
  CollectCallNamesFromExpr(stmt->expr, out);
  CollectCallNamesFromExpr(stmt->for_cond, out);
  CollectCallNamesFromExpr(stmt->assert_expr, out);
  // Stmt::var_init and a randcase weight are expressions the block evaluates,
  // for the reasons CollectStmtReads above gives, so a function called from
  // either is called within the block and contributes its own reads.
  CollectCallNamesFromExpr(stmt->var_init, out);
  for (const auto& rc : stmt->randcase_items) {
    CollectCallNamesFromExpr(rc.first, out);
  }
  ForEachChildStmt(stmt, [stmt, &out](Stmt* const& sub) {
    if (IsAssertionActionBlock(stmt, sub)) return;
    CollectCallNamesFromStmt(sub, out);
  });
}

// The scope a called function's own names are read in, as the prefix its
// FuncMap key carries: "p::" of "p::f", "C::" of "C::f", "s." of "s.f". A bare
// key carries none, and for a package's function an import entered under its
// bare name the prefix is that of the "p::f" key RecordPackageFuncNames
// (elaborator_items_udp.cpp) enters it under as well (§26.3); empty for a
// function the module declares.
static std::string_view ScopeOf(std::string_view key, const ModuleItem* func,
                                const FuncMap& funcs) {
  auto end = key.find_last_of(":.");
  if (end != std::string_view::npos) return key.substr(0, end + 1);
  for (const auto& [other, item] : funcs) {
    auto scope = other.find("::");
    if (item == func && scope != std::string_view::npos) {
      return other.substr(0, scope + 2);
    }
  }
  return {};
}

// The scope enclosing the class scope `scope`: "p::" of "p::C::", the scope
// of a class the package p declares (§26.3). Empty for a class the module or
// the compilation unit declares, "C::", whose enclosing names are spelled
// bare, and for a package's "p::" and an instance's "s.", which a function of
// theirs sees past only to the names spelled bare.
static std::string_view EnclosingScope(std::string_view scope) {
  if (!scope.ends_with("::")) return {};
  auto pos = scope.rfind("::", scope.size() - 3);
  return pos == std::string_view::npos ? std::string_view{}
                                       : scope.substr(0, pos + 2);
}

// A function a call reaches: the key the table holds it under and its
// declaration, the declaration null where the call reaches none.
using FoundFunction = std::pair<std::string_view, const ModuleItem*>;

// Asked for a scoped key the table does not hold: enters in the table the
// function the key names and answers it, or answers no declaration.
using MissedKeyHandler = std::function<FoundFunction(const std::string& key)>;

// The function a call `name` in the body of a function of the scope `scope`
// reaches: the scope's own function of that name first, the "p::h" a bare h(x)
// inside a function of the package p names (§26.3), and likewise a class's
// static method or an instance's function; then the same from each scope
// enclosing it, and last the name as written. A scoped key the table does not
// hold is handed in its turn to `on_miss`, where there is one.
static FoundFunction FindCalledFunction(const FuncMap& funcs,
                                        std::string_view scope,
                                        const std::string& name,
                                        const MissedKeyHandler& on_miss) {
  for (;; scope = EnclosingScope(scope)) {
    const std::string kKey = std::string(scope) + name;
    auto it = funcs.find(kKey);
    if (it != funcs.end()) return *it;
    if (on_miss && kKey.find_first_of(".:") != std::string::npos) {
      FoundFunction found = on_miss(kKey);
      if (found.second != nullptr) return found;
    }
    if (scope.empty()) return {};
  }
}

// The keys of every function the block calls, directly or through the
// functions it calls, each call inside a function looked up from that
// function's scope.
static std::unordered_set<std::string_view> ResolveCalledFunctions(
    const Stmt* body, const FuncMap& funcs, const MissedKeyHandler& on_miss) {
  std::unordered_set<std::string_view> visited;
  std::unordered_set<std::string> names;
  CollectCallNamesFromStmt(body, names);
  std::vector<std::pair<std::string, std::string>> pending;
  pending.reserve(names.size());
  for (const auto& name : names) pending.emplace_back("", name);
  while (!pending.empty()) {
    auto [scope, name] = std::move(pending.back());
    pending.pop_back();
    auto [key, func] = FindCalledFunction(funcs, scope, name, on_miss);
    if (func == nullptr || !visited.insert(key).second) continue;
    std::unordered_set<std::string> inner;
    for (auto* s : func->func_body_stmts) {
      CollectCallNamesFromStmt(s, inner);
    }
    const std::string kScope(ScopeOf(key, func, funcs));
    for (const auto& callee : inner) pending.emplace_back(kScope, callee);
  }
  return visited;
}

// The base identifier a read's longest static prefix (e.g. "state[0]", "s.f")
// stands on. It is one of the two names the prefix expands to, and the one that
// always denotes a simulation object: `logic [7:0] a` is a single Variable
// named `a`, so a bit-select read of it can only be watched through that name.
// A package's object or a class's static property is spelled "X::name"
// (DottedNamePath, MergeNamesOfScope), and the scope's name is part of its
// base.
static std::string_view BaseSignalName(std::string_view name) {
  auto scope = name.find("::");
  auto pos =
      name.find_first_of("[.", scope == std::string_view::npos ? 0 : scope + 2);
  return pos == std::string_view::npos ? name : name.substr(0, pos);
}

static void MergeOneCalledFunctionReads(
    const ModuleItem* func, std::unordered_set<std::string>& reads) {
  for (auto* s : func->func_body_stmts) {
    CollectStmtReads(s, reads);
  }
}

static void MergeOneCalledFunctionLocals(
    const ModuleItem* func, std::unordered_set<std::string>& locals) {
  for (const auto& arg : func->func_args) {
    if (!arg.name.empty()) locals.insert(std::string(arg.name));
  }
  for (auto* s : func->func_body_stmts) {
    CollectBlockLocalNames(s, locals);
  }
}

static void MergeOneCalledFunctionWritten(
    const ModuleItem* func, std::unordered_set<std::string>& written) {
  for (auto* s : func->func_body_stmts) {
    CollectWrittenNames(s, written);
  }
}

// Copies into `out` every name of `names` whose longest static prefix does not
// stand on one of `locals`, the names a called function declares. §9.2.2.2.1
// excludes a formal or a block-local of the function from the reads made
// within it, and the function's names reach no further: a formal named as a
// variable of the module says nothing about the block's own read of that
// variable, which stays in the list. Merging the function's locals into the
// block's exclusions had a function taking `input int opcode` silence the
// block's `seen = opcode`, so a write of opcode never re-ran it.
static void MergeNamesNotLocalTo(const std::unordered_set<std::string>& names,
                                 const std::unordered_set<std::string>& locals,
                                 std::unordered_set<std::string>& out) {
  for (const auto& name : names) {
    if (locals.count(std::string(BaseSignalName(name))) != 0) continue;
    out.insert(name);
  }
}

// The three signal-name accumulators collected while inferring an implicit
// sensitivity list (IEEE 1800 §9.2.2.2.1, @* / @(*)): identifiers read by the
// process (reads), identifiers that are block-local declarations or formal
// arguments and therefore excluded (locals), and identifiers written by the
// process when self-trigger suppression is requested (written). They describe
// one domain object -- the signal classification of a process body -- so they
// travel together.
struct SignalSets {
  std::unordered_set<std::string> reads;
  std::unordered_set<std::string> locals;
  std::unordered_set<std::string> written;
};

// Copies into `out` the names `names` holds, each one a called function reads
// or writes beyond its own formals and locals. A function of a package, a
// class or a child instance names the objects of its own scope, which the
// calling module may not name at all, so each is spelled with the scope's
// prefix (ScopeOf), "p::g", "C::g" or "s.g", and watched by the name the
// simulator holds it under (EmitSignalEvent); taken bare, `g` of `p::f` named
// nothing in the module and a write of p::g never re-ran the block. A name
// already written through a package's or a class's scope, `p::g`, is kept as
// written. A class's static method takes the class's prefix only for the
// names `class_names` says the class declares; any other name it reads is
// one of the scope enclosing the class (§23.9), the module's `ext` read from
// C::f staying `ext`, which `C::ext` designated nothing in place of.
static void MergeNamesOfScope(
    std::string_view scope,
    const std::unordered_set<std::string_view>* class_names,
    const std::unordered_set<std::string>& names,
    std::unordered_set<std::string>& out) {
  for (const auto& name : names) {
    if (name.find("::") != std::string::npos) {
      out.insert(name);
      continue;
    }
    const bool kOwn =
        class_names == nullptr || class_names->count(BaseSignalName(name)) != 0;
    out.insert(std::string(kOwn ? scope : EnclosingScope(scope)) + name);
  }
}

static void MergeCalledFunctionSignals(const Stmt* body,
                                       const InferenceFuncs& calls,
                                       bool exclude_written, SignalSets& sigs) {
  auto called = ResolveCalledFunctions(body, calls.funcs, {});
  for (auto& fname : called) {
    const auto* func = calls.funcs.at(fname);
    const std::string_view kScope = ScopeOf(fname, func, calls.funcs);
    auto cls = calls.class_names.find(kScope);
    const auto* own = cls == calls.class_names.end() ? nullptr : &cls->second;
    std::unordered_set<std::string> func_locals;
    MergeOneCalledFunctionLocals(func, func_locals);
    std::unordered_set<std::string> func_reads;
    MergeOneCalledFunctionReads(func, func_reads);
    std::unordered_set<std::string> kept;
    MergeNamesNotLocalTo(func_reads, func_locals, kept);
    MergeNamesOfScope(kScope, own, kept, sigs.reads);
    if (exclude_written) {
      std::unordered_set<std::string> func_written;
      MergeOneCalledFunctionWritten(func, func_written);
      kept.clear();
      MergeNamesNotLocalTo(func_written, func_locals, kept);
      MergeNamesOfScope(kScope, own, kept, sigs.written);
    }
  }
}

// Records one watchable name, deduped, as a plain identifier event the
// simulator resolves through FindVariable. §26.3 and §8.23 spell a package's
// variable and a class's static property alike, "X::n", and the simulator
// holds the first under the "X.n" key its storage stands under (PackageDataKey
// in src/simulator/lowerer_package_data.cpp) and watches the second as written
// (NamesStaticProperty in src/simulator/awaiters.h), so both spellings are
// recorded and the one that designates no object is dropped
// (DropUnwatchableNames).
static void EmitSignalEvent(std::string_view text,
                            std::unordered_set<std::string_view>& emitted,
                            std::vector<EventExpr>& events, Arena& arena) {
  if (text.empty() || !emitted.insert(text).second) return;
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = std::string_view(arena.AllocString(text.data(), text.size()),
                                text.size());
  events.push_back({Edge::kNone, expr});
  auto scope = text.find("::");
  if (scope == std::string_view::npos) return;
  std::string dotted(text);
  dotted.replace(scope, 2, ".");
  EmitSignalEvent(
      std::string_view(arena.AllocString(dotted.data(), dotted.size()),
                       dotted.size()),
      emitted, events, arena);
}

static std::vector<EventExpr> BuildSensitivityEvents(
    const SignalSets& sigs, bool exclude_written,
    const std::unordered_set<std::string_view>* const_names, Arena& arena) {
  std::vector<EventExpr> events;
  events.reserve(sigs.reads.size());
  // The read names retain their longest static prefix for the locals/written
  // exclusion checks (§9.2.2.2.1), but several selects of one signal collapse
  // to a single base-name event, so dedupe the emitted identifiers.
  std::unordered_set<std::string_view> emitted;
  for (const auto& name : sigs.reads) {
    if (sigs.locals.count(name)) continue;
    if (exclude_written && sigs.written.count(name)) continue;
    std::string_view base = BaseSignalName(name);
    // §9.2.2.2.1: only nets and variables populate the list. A read of a
    // parameter/localparam/specparam (the base of the prefix, or a constant
    // select index that survived as its own read) is dropped -- a constant
    // never changes, so it cannot be part of a sensitivity list.
    if (const_names && const_names->count(base)) continue;
    EmitSignalEvent(base, emitted, events, arena);
    // §9.2.2.2.1 asks for the expansion of the longest static prefix of every
    // net or variable identifier or select expression read, and the prefix is
    // the other expansion. The base name alone is enough for a packed vector,
    // whose bits all live in the one Variable it names, and is not enough for
    // an unpacked array, whose elements are Variables of their own:
    // `always_comb b = mem[2];` watched `mem`, whose value models one element
    // and never moves, while every element writer -- WriteVar through
    // TryResolveArrayElement, the pattern writers, the §21.4 loaders --
    // notifies `mem[2]`, so the block never re-ran. Emitting both is what
    // CollectSelectReads already does for the `wait` route, which is why that
    // route wakes; a prefix that names no object, `a[1]` of a packed `a` among
    // them, is dropped by DropUnwatchableNames in the simulator and skipped by
    // EventAwaiter, so neither path is asked to arm on a name it cannot
    // resolve.
    if (std::string_view(name) != base)
      EmitSignalEvent(name, emitted, events, arena);
  }
  return events;
}

std::vector<EventExpr> InferSensitivity(
    const Stmt* body, Arena& arena, const InferenceFuncs* calls,
    bool exclude_written,
    const std::unordered_set<std::string_view>* const_names) {
  SignalSets sigs;
  CollectStmtReads(body, sigs.reads);
  CollectBlockLocalNames(body, sigs.locals);
  if (exclude_written) {
    CollectWrittenNames(body, sigs.written);
  }

  if (calls && !calls->funcs.empty()) {
    MergeCalledFunctionSignals(body, *calls, exclude_written, sigs);
  }

  return BuildSensitivityEvents(sigs, exclude_written, const_names, arena);
}

// Enters each static function `cls` declares under the key its call through
// the class's scope spells, the class's own prefix "C::" or, for a class the
// package p declares, "p::C::" (§8.23, §26.3), and records under that prefix
// every property the class and the classes it extends declare (§8.13), the
// names its methods read as the class's own (MergeNamesOfScope).
static void AddClassScope(const ClassDecl& cls, std::string_view package,
                          const CompilationUnit& unit, Arena& arena,
                          InferenceFuncs& calls) {
  const std::string_view kScope = *arena.Create<std::string>(
      std::string(package) + std::string(cls.name) + "::");
  auto& names = calls.class_names[kScope];
  for (const ClassDecl* c = &cls; c != nullptr; c = FindBaseClass(c, &unit)) {
    for (const ClassMember* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty) names.insert(m->name);
    }
  }
  for (const ClassMember* m : cls.members) {
    const ModuleItem* method = m->method;
    if (method == nullptr || !method->is_static_method ||
        method->kind != ModuleItemKind::kFunctionDecl) {
      continue;
    }
    calls.funcs[*arena.Create<std::string>(std::string(kScope) +
                                           std::string(method->name))] = method;
  }
}

// The class `name` among the class items of `items`, or null.
static const ClassDecl* ClassAmong(const std::vector<ModuleItem*>& items,
                                   std::string_view name) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl->name == name) {
      return item->class_decl;
    }
  }
  return nullptr;
}

// Enters the class a call key "C::f" or "p::C::f" goes through (AddClassScope):
// the package p's class C, or else the class C a module of `site`'s chain
// declares, innermost first, or the compilation unit's.
static void EnterClassOfKey(std::string_view key, const ScopedCallSite& site,
                            Arena& arena, InferenceFuncs& calls) {
  std::string_view scope = key.substr(0, key.rfind("::"));
  auto sep = scope.rfind("::");
  if (sep != std::string_view::npos) {
    for (const PackageDecl* pkg : site.unit.packages) {
      const ClassDecl* cls = ClassAmong(pkg->items, scope.substr(sep + 2));
      if (cls != nullptr && pkg->name == scope.substr(0, sep)) {
        AddClassScope(*cls, scope.substr(0, sep + 2), site.unit, arena, calls);
      }
    }
    return;
  }
  for (auto it = site.decl_path.rbegin(); it != site.decl_path.rend(); ++it) {
    if (const ClassDecl* cls = ClassAmong((*it)->items, scope)) {
      AddClassScope(*cls, "", site.unit, arena, calls);
      return;
    }
  }
  for (const ClassDecl* cls : site.unit.classes) {
    if (cls->name == scope) AddClassScope(*cls, "", site.unit, arena, calls);
  }
}

// The module the instance `inst` of `decl` instantiates, or null.
static const ModuleDecl* InstanceModule(const ModuleDecl& decl,
                                        std::string_view inst,
                                        const ScopedCallSite& site) {
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kModuleInst && item->inst_name == inst) {
      return site.find_module(item->inst_module);
    }
  }
  return nullptr;
}

// The function the steps of `path` from `first` on name below `decl`: each
// step but the last an instance, the last a function of the module the steps
// before it reach (§23.6); null where a step names none.
static const ModuleItem* FunctionBelow(
    const ModuleDecl* decl, const std::vector<std::string_view>& path,
    size_t first, const ScopedCallSite& site) {
  for (size_t i = first; i + 1 < path.size(); ++i) {
    decl = InstanceModule(*decl, path[i], site);
    if (decl == nullptr) return nullptr;
  }
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl &&
        item->name == path.back()) {
      return item;
    }
  }
  return nullptr;
}

// The function the dotted key "s.t.f" names, searched from the block's module
// out through each module enclosing it (§23.8): from each, first as a
// downward path whose first step is an instance the module declares, then as
// one whose first step is the module's own name, `top.s.f` or `mid.f`.
static const ModuleItem* FunctionOfPath(std::string_view key,
                                        const ScopedCallSite& site) {
  std::vector<std::string_view> path;
  for (size_t start = 0;;) {
    auto dot = key.find('.', start);
    path.push_back(key.substr(start, dot - start));
    if (dot == std::string_view::npos) break;
    start = dot + 1;
  }
  for (auto it = site.decl_path.rbegin(); it != site.decl_path.rend(); ++it) {
    if (const ModuleItem* func = FunctionBelow(*it, path, 0, site)) return func;
    const size_t kOwnName = path.front() == (*it)->name ? 1 : 0;
    if (const ModuleItem* func = FunctionBelow(*it, path, kOwnName, site)) {
      return func;
    }
  }
  return nullptr;
}

void AddScopedCallFunctions(const Stmt* body, const ScopedCallSite& site,
                            Arena& arena, InferenceFuncs& calls) {
  auto enter = [&](const std::string& key) -> FoundFunction {
    if (key.find('.') == std::string::npos) {
      EnterClassOfKey(key, site, arena, calls);
      auto it = calls.funcs.find(key);
      return it == calls.funcs.end() ? FoundFunction{} : FoundFunction(*it);
    }
    const ModuleItem* func = FunctionOfPath(key, site);
    if (func == nullptr) return {};
    std::string_view stored = *arena.Create<std::string>(key);
    calls.funcs[stored] = func;
    return {stored, func};
  };
  ResolveCalledFunctions(body, calls.funcs, enter);
}

}  // namespace delta
