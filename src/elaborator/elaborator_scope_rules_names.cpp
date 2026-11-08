#include "elaborator/elaborator_scope_rules_names.h"

#include <cstddef>
#include <functional>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/package_references.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

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

bool CallArgsNameNoValue(const Expr* e) {
  if (e->kind != ExprKind::kCall) return false;
  if (e->with_expr != nullptr) return true;
  if (e->callee == "randomize") return true;
  return e->lhs != nullptr && e->lhs->kind == ExprKind::kMemberAccess &&
         e->lhs->rhs != nullptr && e->lhs->rhs->text == "randomize";
}

bool ArgNamesCoverageScope(const Expr* e, std::size_t index) {
  if (e->kind != ExprKind::kSystemCall) return false;
  if (e->callee == "$coverage_control") return index == 3;
  return (e->callee == "$coverage_get_max" || e->callee == "$coverage_get") &&
         index == 2;
}

bool ProductionDeclaresReturnValue(const RsProduction& production) {
  return production.has_return_type &&
         production.return_type.kind != DataTypeKind::kVoid;
}

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

void AddPackageItemNames(const PackageDecl* pkg, const ModuleItem* pi,
                         ProvidedNames& names) {
  if (!pi->name.empty()) names.emplace(pi->name, pkg->name);
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
      !pi->class_decl->name.empty()) {
    names.emplace(pi->class_decl->name, pkg->name);
  }
  if (pi->kind == ModuleItemKind::kNestedModuleDecl) {
    names.emplace(pi->nested_module_decl->name, pkg->name);
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
      ProvidedNames candidates;
      AddPackageProvidedNames(unit, src, candidates, visited);
      const std::unordered_set<std::string_view> kReferenced =
          PackageReferencedNames(pkg);
      for (const auto& [name, origin] : candidates) {
        if (kReferenced.contains(name)) names.emplace(name, origin);
      }
    }
  }
}

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

void AddPackageProvidedNames(const CompilationUnit* unit,
                             const PackageDecl* pkg, ProvidedNames& names,
                             std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (const auto* pi : pkg->items) AddPackageItemNames(pkg, pi, names);
  AddExportedNames(unit, pkg, names, visited);
}

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

bool ArgNamesDesignElement(const Expr* e) {
  return e->kind == ExprKind::kSystemCall &&
         (e->callee == "$timeunit" || e->callee == "$timeprecision");
}

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

void PopulatePackageProvidedNames(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  ProvidedNames& names) {
  const PackageDecl* pkg = FindPackageDecl(unit, pkg_name);
  if (pkg == nullptr) return;
  std::unordered_set<const PackageDecl*> visited;
  AddPackageProvidedNames(unit, pkg, names, visited);
}

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
  CollectBareIdents(e->stream_range, out);
  if (!CallArgsNameNoValue(e) && !ArgNamesDesignElement(e)) {
    for (std::size_t i = 0; i < e->args.size(); ++i) {
      if (!ArgNamesCoverageScope(e, i)) CollectBareIdents(e->args[i], out);
    }
  }
  for (const auto* el : e->elements) CollectBareIdents(el, out);
}

void CollectBareIdents(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) return;
  if (e->kind == ExprKind::kIdentifier) {
    if (e->scope_prefix.empty() && !IsBuiltinTypeKeyword(e->text) &&
        e->text != "null" && e->text != "$" && e->text != ".*" &&
        !e->is_pattern_binding) {
      out.push_back(e);
    }
    return;
  }
  CollectBareIdentOperands(e, out);
}

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

static void CollectMatchesBindings(
    const Expr* e, std::unordered_set<std::string_view>& names) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kKwMatches) {
    ForEachPatternBinding(e->rhs,
                          [&](const Expr* b) { names.insert(b->text); });
  }
  AnyExprChild(e, [&](const Expr* child) {
    CollectMatchesBindings(child, names);
    return false;
  });
}

static void CollectCaseItemBindings(
    const CaseItem& ci, std::unordered_set<std::string_view>& names) {
  for (const Expr* p : ci.patterns) {
    ForEachPatternBinding(p, [&](const Expr* b) { names.insert(b->text); });
  }
}

static void CollectCaseMatchesBindings(
    const Stmt* s, std::unordered_set<std::string_view>& names) {
  if (!s->case_matches) return;
  for (const auto& ci : s->case_items) CollectCaseItemBindings(ci, names);
}

static std::string_view PersistentName(std::string name) {
  static std::unordered_set<std::string> pool;
  return *pool.insert(std::move(name)).first;
}

static void CollectBlockEnumMemberNames(
    const Stmt* s, std::unordered_set<std::string_view>& names) {
  const ScopeMap kNoScope;
  auto collect = [&](std::string_view, const DataType& type) {
    for (const auto& em : type.enum_members) {
      for (auto& n : EnumMemberDeclaredNames(em, kNoScope))
        names.insert(PersistentName(std::move(n)));
    }
  };
  if (s->kind == StmtKind::kVarDecl) {
    if (s->var_decl_type.kind == DataTypeKind::kEnum)
      collect({}, s->var_decl_type);
    return;
  }
  if (s->kind != StmtKind::kBlockItemDecl || s->decl_item == nullptr ||
      s->decl_item->kind != ModuleItemKind::kTypedef)
    return;
  ForEachEnumTypeOfItem(s->decl_item, collect);
}

static void CollectBlockLetName(const Stmt* s,
                                std::unordered_set<std::string_view>& names) {
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kLetDecl)
    names.insert(s->decl_item->name);
}

static void CollectLocalNames(const Stmt* s,
                              std::unordered_set<std::string_view>& names,
                              bool with_for_headers, bool with_bindings,
                              bool with_lets_and_enum_members) {
  if (!s) return;
  if (with_bindings) {
    CollectCaseMatchesBindings(s, names);
    CollectMatchesBindings(s->condition, names);
    CollectMatchesBindings(s->rhs, names);
    CollectMatchesBindings(SubroutineCallOfStmt(s), names);
  }
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    names.insert(s->var_name);
  }
  if (with_lets_and_enum_members) {
    CollectBlockLetName(s, names);
    CollectBlockEnumMemberNames(s, names);
  }
  for (auto v : s->foreach_vars) names.insert(v);
  for (size_t k = 0; k < s->for_inits.size(); ++k) {
    const Stmt* fi = s->for_inits[k];
    if (!with_for_headers && k < s->for_init_types.size() &&
        s->for_init_types[k].kind != DataTypeKind::kImplicit)
      continue;
    if (fi && fi->lhs && fi->lhs->kind == ExprKind::kIdentifier) {
      names.insert(fi->lhs->text);
    }
  }
  CollectRandsequenceDeclaredNames(s, names);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectLocalNames(sub, names, with_for_headers, with_bindings,
                      with_lets_and_enum_members);
  });
}

void CollectProcLocalNames(const Stmt* s,
                           std::unordered_set<std::string_view>& names) {
  CollectLocalNames(s, names, true, true, true);
}

void CollectProcVariableNames(const Stmt* s,
                              std::unordered_set<std::string_view>& names) {
  CollectLocalNames(s, names, true, true, false);
}

void CollectProcReadableNames(const Stmt* s,
                              std::unordered_set<std::string_view>& names) {
  CollectLocalNames(s, names, false, false, true);
}

std::unordered_set<std::string_view> MatchesBindingsOf(const Expr* e) {
  std::unordered_set<std::string_view> names;
  CollectMatchesBindings(e, names);
  return names;
}

static void MarkBoundReads(const Expr* e,
                           const std::unordered_set<std::string_view>& in_scope,
                           std::unordered_set<const Expr*>& bound) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    if (in_scope.count(e->text) != 0) bound.insert(e);
    return;
  }
  if (e->kind == ExprKind::kTernary) {
    std::unordered_set<std::string_view> inner = in_scope;
    inner.merge(MatchesBindingsOf(e->condition));
    MarkBoundReads(e->condition, inner, bound);
    MarkBoundReads(e->true_expr, inner, bound);
    MarkBoundReads(e->false_expr, in_scope, bound);
    return;
  }
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kAmpAmpAmp) {
    std::unordered_set<std::string_view> inner = in_scope;
    inner.merge(MatchesBindingsOf(e->lhs));
    MarkBoundReads(e->lhs, in_scope, bound);
    MarkBoundReads(e->rhs, inner, bound);
    return;
  }
  ForEachExprChild(
      e, [&](const Expr* child) { MarkBoundReads(child, in_scope, bound); });
}

static void KeepUndeclaredReads(
    const std::vector<const Expr*>& refs,
    std::initializer_list<const Expr*> exprs,
    const std::unordered_set<std::string_view>& locals,
    std::vector<const Expr*>& out) {
  std::unordered_set<const Expr*> bound;
  for (const Expr* e : exprs) MarkBoundReads(e, {}, bound);
  for (const auto* r : refs) {
    if (locals.count(r->text) == 0 && bound.count(r) == 0) out.push_back(r);
  }
}

static void CollectBoundProcRhsIdents(
    const Stmt* s, const std::unordered_set<std::string_view>& locals,
    const std::unordered_set<std::string_view>& bound,
    std::vector<const Expr*>& out) {
  if (bound.empty()) {
    CollectProcRhsIdents(s, locals, out);
    return;
  }
  std::unordered_set<std::string_view> inner = locals;
  inner.insert(bound.begin(), bound.end());
  CollectProcRhsIdents(s, inner, out);
}

static void CollectProcRhsIdentsIn(
    const Stmt* s, const std::unordered_set<std::string_view>& locals,
    std::vector<const Expr*>& out) {
  const Expr* read = nullptr;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    read = s->rhs;
  } else if (s->kind == StmtKind::kReturn) {
    read = s->expr;
  } else if (const Expr* call = SubroutineCallOfStmt(s);
             call != nullptr && IsValueListSystemTask(call)) {
    read = call;
  }
  std::vector<const Expr*> refs;
  CollectBareIdents(read, refs);
  CollectBareIdents(s->condition, refs);
  CollectBareIdents(s->var_decl_type.type_ref_expr, refs);
  CollectBareIdents(s->for_cond, refs);
  for (const EventExpr& ev : s->events) {
    CollectBareIdents(ev.signal, refs);
    CollectBareIdents(ev.iff_condition, refs);
  }
  if (!s->case_matches) {
    for (const auto& ci : s->case_items) {
      for (const auto* p : ci.patterns) CollectBareIdents(p, refs);
    }
  }
  ForEachRandsequenceExpr(s,
                          [&](Expr* const& e) { CollectBareIdents(e, refs); });
  KeepUndeclaredReads(refs, {read, s->condition, s->for_cond}, locals, out);
  ForEachChildStmtWithBindings(
      s,
      [&](const Stmt* sub, const std::unordered_set<std::string_view>& bound) {
        CollectBoundProcRhsIdents(sub, locals, bound, out);
      });
}

std::vector<std::string_view> ForHeaderDeclaredNames(const Stmt* s) {
  std::vector<std::string_view> names;
  for (size_t k = 0; k < s->for_inits.size() && k < s->for_init_types.size();
       ++k) {
    const Stmt* fi = s->for_inits[k];
    if (s->for_init_types[k].kind == DataTypeKind::kImplicit) continue;
    if (fi && fi->lhs && fi->lhs->kind == ExprKind::kIdentifier) {
      names.push_back(fi->lhs->text);
    }
  }
  return names;
}

void ForEachChildStmtWithBindings(
    const Stmt* s,
    const std::function<void(
        const Stmt*, const std::unordered_set<std::string_view>&)>& visit) {
  if (s->kind == StmtKind::kIf) {
    visit(s->then_branch, MatchesBindingsOf(s->condition));
    visit(s->else_branch, {});
    return;
  }
  if (s->case_matches) {
    for (const auto& ci : s->case_items) {
      std::unordered_set<std::string_view> bound;
      CollectCaseItemBindings(ci, bound);
      visit(ci.body, bound);
    }
    return;
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) { visit(sub, {}); });
}

void CollectProcRhsIdents(const Stmt* s,
                          const std::unordered_set<std::string_view>& locals,
                          std::vector<const Expr*>& out) {
  if (!s) return;
  std::vector<std::string_view> header = ForHeaderDeclaredNames(s);
  if (!header.empty()) {
    std::unordered_set<std::string_view> inner = locals;
    inner.insert(header.begin(), header.end());
    CollectProcRhsIdentsIn(s, inner, out);
    return;
  }
  CollectProcRhsIdentsIn(s, locals, out);
}

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
    CollectProcReadableNames(stmt, names);
  }
}

}  // namespace delta
