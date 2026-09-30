#include "elaborator/package_assertion_scope.h"

#include <string>
#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "elaborator/assertion_body_slots.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

bool IsSequenceOrProperty(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kSequenceDecl ||
         item->kind == ModuleItemKind::kPropertyDecl;
}

// Whether an expression reads `item` by its name: a sequence or property,
// a parameter or variable, a function or a let.
bool IsReadByName(const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kParamDecl:
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kLetDecl:
      return true;
    default:
      return false;
  }
}

// The names `pkg` declares that an expression in it reads.
std::unordered_set<std::string_view> PackageNames(const PackageDecl* pkg) {
  std::unordered_set<std::string_view> own;
  for (const ModuleItem* item : pkg->items) {
    if (IsReadByName(item)) own.insert(item->name);
  }
  return own;
}

// The names the declaration `item` binds for its body, its formals and its
// locals, which hide the package's names of the same spelling.
std::unordered_set<std::string_view> BoundNames(const ModuleItem* item) {
  std::unordered_set<std::string_view> bound(item->prop_formals.begin(),
                                             item->prop_formals.end());
  bound.insert(item->prop_seq_assert_vars.begin(),
               item->prop_seq_assert_vars.end());
  for (const SeqLocalDecl& local : item->prop_locals) bound.insert(local.name);
  CollectBodyLocals(item->seq_linear, bound);
  if (item->prop_body_tree != nullptr) {
    CollectTreeLocals(item->prop_body_tree, bound);
  }
  return bound;
}

// Each call under `e` whose callee is one of `scoped`'s names made a call
// through the path that stands for it, `pk::s2(x, y)` as the parser reads it.
void ScopeCallees(Expr* e, const ActualsByFormal& scoped) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) {
    auto it = scoped.find(e->callee);
    if (it != scoped.end()) {
      e->lhs = it->second;
      e->callee = {};
    }
  }
  Expr* children[] = {
      e->lhs,       e->rhs,       e->base,       e->index,        e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count, e->with_expr};
  for (Expr* c : children) ScopeCallees(c, scoped);
  for (Expr* a : e->args) ScopeCallees(a, scoped);
  for (Expr* el : e->elements) ScopeCallees(el, scoped);
}

// `item`, a sequence or property of package `pkg`, with each name of `own`
// it reads and does not bind itself made `pkg::name`.
void ResolveInPackage(ModuleItem* item, std::string_view pkg,
                      const std::unordered_set<std::string_view>& own,
                      Arena& arena) {
  std::unordered_set<std::string_view> bound = BoundNames(item);
  ActualsByFormal scoped;
  for (std::string_view name : own) {
    if (bound.count(name) != 0) continue;
    Expr* path = MemberOf(pkg, name, item->loc, arena);
    path->is_scope_resolution = true;
    scoped[name] = path;
  }
  auto resolve = [&scoped, &arena](Expr*& e) {
    e = SubstituteFormals(e, scoped, arena);
    ScopeCallees(e, scoped);
  };
  ForEachBodySlot(item->seq_linear, resolve);
  ForEachEventSlot(item->seq_clock, resolve);
  resolve(item->prop_body_expr);
  resolve(item->prop_disable_iff);
  ForEachEventSlot(item->prop_clock, resolve);
  if (item->prop_body_tree != nullptr) {
    ForEachTreeSlot(item->prop_body_tree, resolve);
  }
  for (Expr*& actual : item->prop_formal_defaults) resolve(actual);
}

}  // namespace

void ResolvePackageAssertionNames(const CompilationUnit* unit, Arena& arena) {
  for (const PackageDecl* pkg : unit->packages) {
    std::unordered_set<std::string_view> own = PackageNames(pkg);
    PropertyRegistry registry;
    for (ModuleItem* item : pkg->items) {
      if (!IsSequenceOrProperty(item)) continue;
      ResolveInPackage(item, pkg->name, own, arena);
      registry.RegisterAs(
          *arena.Create<std::string>(std::string(pkg->name) +
                                     "::" + std::string(item->name)),
          item);
    }
    // §16.13.4: a sequence the body names is a sequence there, as a module's
    // property's is once the module's registry holds it.
    for (ModuleItem* item : pkg->items) {
      if (item->kind == ModuleItemKind::kPropertyDecl) {
        PromoteSequenceInstances(item->prop_body_tree, registry, arena);
      }
    }
  }
}

}  // namespace delta
