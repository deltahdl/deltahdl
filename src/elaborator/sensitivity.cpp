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
  if (cur && cur->kind == ExprKind::kIdentifier) {
    if (!cur->text.empty()) out.insert(std::string(cur->text));
    return;
  }
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
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string dotted;
    if (DottedNamePath(expr, dotted)) out.insert(dotted);
  }
  if (expr->kind == ExprKind::kSelect) {
    CollectSelectReads(expr, out);
    return;
  }
  if (expr->kind == ExprKind::kCall) {
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

bool IsAssertionActionBlock(const Stmt* owner, const Stmt* sub) {
  return sub != nullptr &&
         (sub == owner->assert_pass_stmt || sub == owner->assert_fail_stmt);
}

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
  fn(stmt->var_init);
  for (const auto& rc : stmt->randcase_items) fn(rc.first);
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

static void CollectBlockLocalNames(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kVarDecl && !stmt->var_name.empty()) {
    out.insert(std::string(stmt->var_name));
  }
  ForEachChildStmt(
      stmt, [&out](Stmt* const& sub) { CollectBlockLocalNames(sub, out); });
}

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
  CollectCallNamesFromExpr(stmt->var_init, out);
  for (const auto& rc : stmt->randcase_items) {
    CollectCallNamesFromExpr(rc.first, out);
  }
  ForEachChildStmt(stmt, [stmt, &out](Stmt* const& sub) {
    if (IsAssertionActionBlock(stmt, sub)) return;
    CollectCallNamesFromStmt(sub, out);
  });
}

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

static std::string_view EnclosingScope(std::string_view scope) {
  if (!scope.ends_with("::")) return {};
  auto pos = scope.rfind("::", scope.size() - 3);
  return pos == std::string_view::npos ? std::string_view{}
                                       : scope.substr(0, pos + 2);
}

using FoundFunction = std::pair<std::string_view, const ModuleItem*>;

using MissedKeyHandler = std::function<FoundFunction(const std::string& key)>;

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

static void MergeNamesNotLocalTo(const std::unordered_set<std::string>& names,
                                 const std::unordered_set<std::string>& locals,
                                 std::unordered_set<std::string>& out) {
  for (const auto& name : names) {
    if (locals.count(std::string(BaseSignalName(name))) != 0) continue;
    out.insert(name);
  }
}

struct SignalSets {
  std::unordered_set<std::string> reads;
  std::unordered_set<std::string> locals;
  std::unordered_set<std::string> written;
};

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
  std::unordered_set<std::string_view> emitted;
  for (const auto& name : sigs.reads) {
    if (sigs.locals.count(name)) continue;
    if (exclude_written && sigs.written.count(name)) continue;
    std::string_view base = BaseSignalName(name);
    if (const_names && const_names->count(base)) continue;
    EmitSignalEvent(base, emitted, events, arena);
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
