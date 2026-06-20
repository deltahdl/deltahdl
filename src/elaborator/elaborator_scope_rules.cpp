#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

struct ScopeWalk {
  std::vector<std::pair<std::string_view, SourceLoc>> block_labels;
  std::unordered_set<std::string_view> local_names;
  std::vector<std::pair<std::string_view, SourceLoc>> proc_lhs;
};

void CollectScopeWalk(const Stmt* s, ScopeWalk& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlock && !s->label.empty()) {
    out.block_labels.emplace_back(s->label, s->range.start);
  }
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.local_names.insert(s->var_name);
  }
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
    out.proc_lhs.emplace_back(s->lhs->text, s->range.start);
  }
  for (const auto* sub : s->stmts) CollectScopeWalk(sub, out);
  for (const auto* sub : s->fork_stmts) CollectScopeWalk(sub, out);
  CollectScopeWalk(s->then_branch, out);
  CollectScopeWalk(s->else_branch, out);
  CollectScopeWalk(s->body, out);
  CollectScopeWalk(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectScopeWalk(fi, out);
  for (const auto* fs : s->for_steps) CollectScopeWalk(fs, out);
  for (const auto& ci : s->case_items) CollectScopeWalk(ci.body, out);
}

bool IsProcBodyItem(ModuleItemKind k) {
  return k == ModuleItemKind::kInitialBlock ||
         k == ModuleItemKind::kFinalBlock ||
         k == ModuleItemKind::kAlwaysBlock ||
         k == ModuleItemKind::kAlwaysCombBlock ||
         k == ModuleItemKind::kAlwaysFFBlock ||
         k == ModuleItemKind::kAlwaysLatchBlock;
}

}  // namespace

namespace {

void WalkExprIdents(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    WalkExprIdents(e->lhs, out);
    return;
  }
  WalkExprIdents(e->lhs, out);
  WalkExprIdents(e->rhs, out);
  WalkExprIdents(e->base, out);
  WalkExprIdents(e->index, out);
  WalkExprIdents(e->index_end, out);
  WalkExprIdents(e->condition, out);
  WalkExprIdents(e->true_expr, out);
  WalkExprIdents(e->false_expr, out);
  WalkExprIdents(e->repeat_count, out);
  WalkExprIdents(e->with_expr, out);
  for (const auto* a : e->args) WalkExprIdents(a, out);
  for (const auto* el : e->elements) WalkExprIdents(el, out);
}

void WalkStmtIdents(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  WalkExprIdents(s->condition, out);
  WalkExprIdents(s->lhs, out);
  WalkExprIdents(s->rhs, out);
  WalkExprIdents(s->delay, out);
  WalkExprIdents(s->cycle_delay, out);
  WalkExprIdents(s->for_cond, out);
  WalkExprIdents(s->expr, out);
  WalkExprIdents(s->assert_expr, out);
  WalkExprIdents(s->repeat_event_count, out);
  WalkExprIdents(s->var_init, out);
  for (const auto* e : s->wait_order_events) WalkExprIdents(e, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) WalkExprIdents(p, out);
    WalkStmtIdents(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    WalkExprIdents(w, out);
    WalkStmtIdents(body, out);
  }
  for (const auto* sub : s->stmts) WalkStmtIdents(sub, out);
  for (const auto* sub : s->fork_stmts) WalkStmtIdents(sub, out);
  WalkStmtIdents(s->then_branch, out);
  WalkStmtIdents(s->else_branch, out);
  WalkStmtIdents(s->body, out);
  WalkStmtIdents(s->for_body, out);
  for (const auto* fi : s->for_inits) WalkStmtIdents(fi, out);
  for (const auto* fs : s->for_steps) WalkStmtIdents(fs, out);
  WalkStmtIdents(s->assert_pass_stmt, out);
  WalkStmtIdents(s->assert_fail_stmt, out);
}

}  // namespace

void Elaborator::ValidatePackageImportRules(const ModuleDecl* decl) {
  explicit_imports_.clear();
  wildcard_packages_.clear();
  wildcard_claimed_.clear();

  wildcard_packages_.push_back("std");

  auto package_declared = [&](std::string_view pkg_name) {
    if (pkg_name == "std") return true;
    for (const auto* pkg : unit_->packages) {
      if (pkg->name == pkg_name) return true;
    }
    return false;
  };

  auto provides = [&](std::string_view pkg_name,
                      std::string_view name) -> bool {
    auto it = pkg_provided_names_.find(pkg_name);
    if (it == pkg_provided_names_.end()) {
      auto& s = pkg_provided_names_[pkg_name];
      for (const auto* pkg : unit_->packages) {
        if (pkg->name != pkg_name) continue;
        for (const auto* pi : pkg->items) {
          if (!pi->name.empty()) s.insert(pi->name);
          if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
              !pi->class_decl->name.empty()) {
            s.insert(pi->class_decl->name);
          }
        }
      }
      it = pkg_provided_names_.find(pkg_name);
    }
    return it->second.count(name) != 0;
  };

  std::unordered_set<std::string_view> seen_decls;
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) seen_decls.insert(port.name);
  }
  for (const auto& [pname, pval] : decl->params) {
    if (!pname.empty()) seen_decls.insert(pname);
  }

  auto track_decl = [&](std::string_view name, SourceLoc loc) {
    if (name.empty()) return;
    auto wit = wildcard_claimed_.find(name);
    if (wit != wildcard_claimed_.end()) {
      diag_.Error(loc, std::format("declaration of '{}' follows a reference "
                                   "resolved through a wildcard package import",
                                   name));
    }
    seen_decls.insert(name);
  };

  auto process_ref = [&](const Expr* e) {
    auto name = e->text;
    if (name.empty()) return;
    if (seen_decls.count(name)) return;
    std::vector<std::string_view> providers;
    for (auto pkg : wildcard_packages_) {
      if (provides(pkg, name)) providers.push_back(pkg);
    }
    if (providers.size() > 1) {
      diag_.Error(e->range.start,
                  std::format("reference to '{}' is ambiguous between wildcard "
                              "imports of packages '{}' and '{}'",
                              name, providers[0], providers[1]));
      return;
    }
    if (providers.size() == 1) {
      wildcard_claimed_[name] = e->range.start;
      seen_decls.insert(name);
    }
  };

  for (const auto* item : decl->items) {
    switch (item->kind) {
      case ModuleItemKind::kImportDecl: {
        auto pkg_name = item->import_item.package_name;
        if (!package_declared(pkg_name)) {
          diag_.Error(
              item->loc,
              std::format("import from unknown package '{}'; the package "
                          "must be declared before any scope that imports "
                          "from it",
                          pkg_name));
          break;
        }
        if (item->import_item.is_wildcard) {
          if (std::find(wildcard_packages_.begin(), wildcard_packages_.end(),
                        pkg_name) == wildcard_packages_.end()) {
            wildcard_packages_.push_back(pkg_name);
          }
          break;
        }
        auto name = item->import_item.item_name;
        auto eit = explicit_imports_.find(name);
        if (eit != explicit_imports_.end()) {
          if (eit->second.first == pkg_name) break;
          diag_.Error(
              item->loc,
              std::format("explicit import of '{}::{}' conflicts with earlier "
                          "explicit import from '{}'",
                          pkg_name, name, eit->second.first));
          break;
        }
        if (seen_decls.count(name)) {
          auto wit = wildcard_claimed_.find(name);
          if (wit != wildcard_claimed_.end()) {
            diag_.Error(
                item->loc,
                std::format("explicit import of '{}::{}' is illegal because "
                            "'{}' was already referenced through a wildcard "
                            "package import",
                            pkg_name, name, name));
          } else {
            diag_.Error(item->loc,
                        std::format("explicit import of '{}::{}' collides with "
                                    "existing declaration of '{}'",
                                    pkg_name, name, name));
          }
          break;
        }
        explicit_imports_[name] = {pkg_name, item->loc};
        seen_decls.insert(name);
        break;
      }
      case ModuleItemKind::kInitialBlock:
      case ModuleItemKind::kFinalBlock:
      case ModuleItemKind::kAlwaysBlock:
      case ModuleItemKind::kAlwaysCombBlock:
      case ModuleItemKind::kAlwaysFFBlock:
      case ModuleItemKind::kAlwaysLatchBlock: {
        std::vector<const Expr*> refs;
        WalkStmtIdents(item->body, refs);
        for (const auto* e : refs) process_ref(e);
        break;
      }
      case ModuleItemKind::kContAssign: {
        std::vector<const Expr*> refs;
        WalkExprIdents(item->assign_lhs, refs);
        WalkExprIdents(item->assign_rhs, refs);
        for (const auto* e : refs) process_ref(e);
        break;
      }
      case ModuleItemKind::kModuleInst:
        track_decl(item->inst_name, item->loc);
        break;
      case ModuleItemKind::kGateInst:
      case ModuleItemKind::kUdpInst:
        track_decl(item->gate_inst_name, item->loc);
        break;
      case ModuleItemKind::kClassDecl:
        if (item->class_decl) track_decl(item->class_decl->name, item->loc);
        break;
      default:
        track_decl(item->name, item->loc);
        break;
    }
  }
}

void Elaborator::ValidateScopeRules(const ModuleDecl* decl) {
  ScopeWalk walk;
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) {
      CollectScopeWalk(item->body, walk);
    }
  }
  for (const auto& [label, loc] : walk.block_labels) {
    if (!declared_names_.insert(label).second) {
      diag_.Error(loc, std::format("redeclaration of '{}'", label));
    }
  }
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (walk.local_names.count(name)) continue;
    if (IsNameInModuleScope(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name));
  }
}

bool Elaborator::IsNameInModuleScope(std::string_view name) const {
  if (declared_names_.count(name)) return true;
  if (ansi_port_names_.count(name)) return true;
  if (non_ansi_complete_ports_.count(name)) return true;
  if (non_ansi_partial_ports_.count(name)) return true;
  if (const_names_.count(name)) return true;
  if (enum_member_names_.count(name)) return true;
  if (specparam_names_.count(name)) return true;
  if (class_names_.count(name)) return true;
  if (class_var_names_.count(name)) return true;
  if (task_names_.count(name)) return true;
  if (func_decls_.count(name)) return true;
  if (interface_inst_types_.count(name)) return true;
  if (checker_inst_names_.count(name)) return true;
  return false;
}

void Elaborator::ValidateForwardTypedefsInScope(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    bool resolved = false;
    for (const auto* other : decl->items) {
      if (other == item) continue;
      if (other->kind == ModuleItemKind::kTypedef &&
          other->name == item->name &&
          other->typedef_type.kind != DataTypeKind::kImplicit) {
        resolved = true;
        break;
      }
      if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
          other->class_decl->name == item->name) {
        resolved = true;
        break;
      }
    }
    if (!resolved && class_names_.count(item->name) > 0) {
      resolved = true;
    }
    if (!resolved) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name));
    }
  }
}

void Elaborator::ValidateForwardTypedefScopePrefix(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kNamed) continue;
    if (item->typedef_type.scope_name.empty()) continue;
    auto scope = item->typedef_type.scope_name;
    bool is_forward_in_scope = false;
    bool resolves_to_class = class_names_.count(scope) > 0;
    for (const auto* other : decl->items) {
      if (other->kind == ModuleItemKind::kTypedef && other->name == scope &&
          other->typedef_type.kind == DataTypeKind::kImplicit) {
        is_forward_in_scope = true;
      }
      if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
          other->class_decl->name == scope) {
        resolves_to_class = true;
      }
    }
    if (!is_forward_in_scope) continue;
    if (!resolves_to_class) {
      diag_.Error(item->loc,
                  std::format("scope-resolution prefix '{}' of a typedef does "
                              "not resolve to a class",
                              scope));
    }
  }
}

namespace {

void CollectMemberAccess(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) {
    out.push_back(e);
  }
  CollectMemberAccess(e->lhs, out);
  CollectMemberAccess(e->rhs, out);
  CollectMemberAccess(e->base, out);
  CollectMemberAccess(e->index, out);
  CollectMemberAccess(e->index_end, out);
  CollectMemberAccess(e->condition, out);
  CollectMemberAccess(e->true_expr, out);
  CollectMemberAccess(e->false_expr, out);
  CollectMemberAccess(e->repeat_count, out);
  CollectMemberAccess(e->with_expr, out);
  for (const auto* a : e->args) CollectMemberAccess(a, out);
  for (const auto* el : e->elements) CollectMemberAccess(el, out);
}

void CollectMemberAccessInStmt(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  CollectMemberAccess(s->condition, out);
  CollectMemberAccess(s->lhs, out);
  CollectMemberAccess(s->rhs, out);
  CollectMemberAccess(s->delay, out);
  CollectMemberAccess(s->cycle_delay, out);
  CollectMemberAccess(s->for_cond, out);
  CollectMemberAccess(s->expr, out);
  CollectMemberAccess(s->assert_expr, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) CollectMemberAccess(p, out);
    CollectMemberAccessInStmt(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    CollectMemberAccess(w, out);
    CollectMemberAccessInStmt(body, out);
  }
  for (const auto* sub : s->stmts) CollectMemberAccessInStmt(sub, out);
  for (const auto* sub : s->fork_stmts) CollectMemberAccessInStmt(sub, out);
  CollectMemberAccessInStmt(s->then_branch, out);
  CollectMemberAccessInStmt(s->else_branch, out);
  CollectMemberAccessInStmt(s->body, out);
  CollectMemberAccessInStmt(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectMemberAccessInStmt(fi, out);
  for (const auto* fs : s->for_steps) CollectMemberAccessInStmt(fs, out);
  CollectMemberAccessInStmt(s->assert_pass_stmt, out);
  CollectMemberAccessInStmt(s->assert_fail_stmt, out);
}

}  // namespace

void Elaborator::ValidateHierRefToImportedName(const ModuleDecl* decl,
                                               const RtlirModule* mod) {
  if (!mod || mod->children.empty()) return;
  std::unordered_map<std::string_view, const RtlirModule*> inst_type;
  for (const auto& child : mod->children) {
    if (child.resolved) inst_type[child.inst_name] = child.resolved;
  }
  if (inst_type.empty()) return;

  auto imported_into = [&](const RtlirModule* m, std::string_view name) {
    for (const auto& imp : m->imports) {
      if (!imp.is_wildcard && imp.item_name == name) return true;
      if (imp.is_wildcard) {
        for (const auto* pkg : unit_->packages) {
          if (pkg->name != imp.package_name) continue;
          for (const auto* pi : pkg->items) {
            if (pi->name == name) return true;
            if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
                pi->class_decl->name == name)
              return true;
          }
        }
      }
    }
    return false;
  };

  auto check_member_access = [&](const Expr* ma) {
    if (!ma || ma->kind != ExprKind::kMemberAccess) return;
    if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
    if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
    auto it = inst_type.find(ma->lhs->text);
    if (it == inst_type.end()) return;
    if (imported_into(it->second, ma->rhs->text)) {
      diag_.Error(
          ma->range.start,
          std::format("hierarchical reference '{}.{}' targets a name imported "
                      "into '{}' from a package; imported names are not "
                      "visible through hierarchical references",
                      ma->lhs->text, ma->rhs->text, it->second->name));
    }
  };

  std::vector<const Expr*> accesses;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProcBodyItem(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }
  for (const auto* ma : accesses) check_member_access(ma);
}

void Elaborator::ValidateHierRefInstanceArray(const ModuleDecl* decl) {
  struct ArrayBounds {
    int64_t low;
    int64_t high;
  };
  std::unordered_map<std::string_view, ArrayBounds> arrayed;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (!item->inst_range_left || !item->inst_range_right) continue;
    auto lhi = ConstEvalInt(item->inst_range_left);
    auto rhi = ConstEvalInt(item->inst_range_right);
    if (!lhi || !rhi) continue;
    ArrayBounds b;
    b.low = std::min(*lhi, *rhi);
    b.high = std::max(*lhi, *rhi);
    arrayed[item->inst_name] = b;
  }
  if (arrayed.empty()) return;

  std::vector<const Expr*> accesses;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProcBodyItem(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }

  for (const auto* ma : accesses) {
    if (!ma || ma->kind != ExprKind::kMemberAccess || !ma->lhs) continue;
    const Expr* base = ma->lhs;
    std::string_view name;
    const Expr* select_index = nullptr;
    if (base->kind == ExprKind::kIdentifier) {
      name = base->text;
    } else if (base->kind == ExprKind::kSelect && base->base &&
               base->base->kind == ExprKind::kIdentifier) {
      name = base->base->text;
      select_index = base->index;
    } else {
      continue;
    }
    auto it = arrayed.find(name);
    if (it == arrayed.end()) continue;
    if (!select_index) {
      diag_.Error(ma->range.start,
                  std::format("hierarchical reference to instance array '{}' "
                              "requires an instance select",
                              name));
      continue;
    }
    auto idx = ConstEvalInt(select_index);
    if (!idx) continue;
    if (*idx < it->second.low || *idx > it->second.high) {
      diag_.Error(select_index->range.start,
                  std::format("instance select [{}] is out of range for "
                              "instance array '{}' [{}:{}]",
                              *idx, name, it->second.high, it->second.low));
    }
  }
}

}  // namespace delta
