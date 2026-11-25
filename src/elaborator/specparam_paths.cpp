#include "elaborator/specparam_paths.h"

#include <algorithm>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/design_name_lookup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

namespace {

bool DeclaresSpecparam(const std::vector<ModuleItem*>& items,
                       std::string_view name) {
  return std::ranges::any_of(items, [name](const ModuleItem* item) {
    if (item->kind == ModuleItemKind::kSpecparam) return item->name == name;
    return std::ranges::any_of(
        item->specify_items, [name](const SpecifyItem* specify) {
          return specify->kind == SpecifyItemKind::kSpecparam &&
                 specify->param_name == name;
        });
  });
}

bool Instantiates(const std::vector<ModuleItem*>& items, std::string_view name);

bool ItemInstantiates(const ModuleItem& item, std::string_view name) {
  if (item.kind == ModuleItemKind::kModuleInst) {
    return item.inst_module == name;
  }
  return Instantiates(item.gen_body, name) ||
         std::ranges::any_of(item.gen_case_items,
                             [name](const GenerateCaseItem& arm) {
                               return Instantiates(arm.body, name);
                             }) ||
         (item.gen_else != nullptr && ItemInstantiates(*item.gen_else, name));
}

bool Instantiates(const std::vector<ModuleItem*>& items,
                  std::string_view name) {
  return std::ranges::any_of(items, [name](const ModuleItem* item) {
    return ItemInstantiates(*item, name);
  });
}

InstancePath RootOf(const Expr& name) {
  if (name.scope_prefix.empty()) return {name.text};
  if (name.scope_prefix == "$root") return {name.scope_prefix, name.text};
  return {};
}

InstancePath MemberPathOf(const Expr& access) {
  InstancePath path = InstancePathOf(*access.lhs);
  if (!path.empty()) path.push_back(access.rhs->text);
  return path;
}

}  // namespace

InstancePath InstancePathOf(const Expr& name) {
  switch (name.kind) {
    case ExprKind::kIdentifier:
      return RootOf(name);
    case ExprKind::kSelect:
      return InstancePathOf(*name.base);
    case ExprKind::kMemberAccess:
      return MemberPathOf(name);
    default:
      return {};
  }
}

const ModuleDecl* SpecparamPaths::ModuleAt(
    const std::vector<ModuleItem*>& items, InstancePathView path) const {
  if (path.empty()) return nullptr;
  for (const ModuleItem* item : items) {
    const ModuleDecl* found = ModuleThrough(*item, path);
    if (found != nullptr) return found;
  }
  return nullptr;
}

const ModuleDecl* SpecparamPaths::ModuleThrough(const ModuleItem& item,
                                                InstancePathView path) const {
  if (item.kind == ModuleItemKind::kModuleInst) {
    if (item.inst_name != path.front()) return nullptr;
    const ModuleDecl* instantiated = FindDefinition(&unit_, item.inst_module);
    if (instantiated == nullptr || path.size() == 1) return instantiated;
    return ModuleAt(instantiated->items, path.subspan(1));
  }
  const auto kThroughBlock =
      [&](std::string_view name, bool has_begin_end,
          const std::vector<ModuleItem*>& body) -> const ModuleDecl* {
    if (!has_begin_end) return ModuleAt(body, path);
    return name == path.front() ? ModuleAt(body, path.subspan(1)) : nullptr;
  };
  const ModuleDecl* found =
      kThroughBlock(item.name, item.gen_body_has_begin_end, item.gen_body);
  for (const GenerateCaseItem& arm : item.gen_case_items) {
    if (found != nullptr) return found;
    found = kThroughBlock(arm.label, arm.has_begin_end, arm.body);
  }
  if (found != nullptr || item.gen_else == nullptr) return found;
  return ModuleThrough(*item.gen_else, path);
}

const ModuleDecl* SpecparamPaths::BoundModule(const BindDirective& bind) const {
  InstancePath path;
  path.reserve(bind.target.segments.size());
  for (const BindTargetSegment& segment : bind.target.segments) {
    path.push_back(segment.name);
  }
  const InstancePathView kPath(path);
  const ModuleDecl* root = FindDefinition(&unit_, path.front());
  if (root != nullptr && path.size() == 1) return root;
  if (root != nullptr) return ModuleAt(root->items, kPath.subspan(1));
  for (const ModuleDecl* decl : unit_.modules) {
    const ModuleDecl* found = ModuleAt(decl->items, kPath);
    if (found != nullptr) return found;
  }
  return nullptr;
}

bool SpecparamPaths::ReachesIn(const std::vector<ModuleItem*>& items,
                               const InstancePath& path) const {
  const ModuleDecl* found =
      ModuleAt(items, InstancePathView(path).first(path.size() - 1));
  return found != nullptr && DeclaresSpecparam(found->items, path.back());
}

std::vector<const ModuleDecl*> SpecparamPaths::Instantiators(
    std::string_view name) const {
  std::vector<const ModuleDecl*> found;
  for (const auto* decls : {&unit_.modules, &unit_.interfaces}) {
    for (const ModuleDecl* decl : *decls) {
      if (Instantiates(decl->items, name)) found.push_back(decl);
    }
  }
  for (const BindDirective* bind : unit_.bind_directives) {
    if (bind->instantiation->inst_module != name) continue;
    const ModuleDecl* target = BoundModule(*bind);
    if (target != nullptr) found.push_back(target);
  }
  return found;
}

bool SpecparamPaths::ReachesUpward(
    const ModuleDecl& from, const InstancePath& path,
    std::unordered_set<const ModuleDecl*>& seen) const {
  if (!seen.insert(&from).second) return false;
  return std::ranges::any_of(
      Instantiators(from.name), [&](const ModuleDecl* decl) {
        return ReachesIn(decl->items, path) || ReachesUpward(*decl, path, seen);
      });
}

bool SpecparamPaths::EndsAtSpecparam(const InstancePath& path,
                                     const ModuleDecl* from) const {
  InstancePath below = path;
  if (below.front() == "$root") below.erase(below.begin());
  const ModuleDecl* top = FindDefinition(&unit_, below.front());
  below.erase(below.begin());
  if (top != nullptr &&
      (below.size() == 1 ? DeclaresSpecparam(top->items, below.front())
                         : ReachesIn(top->items, below))) {
    return true;
  }
  std::unordered_set<const ModuleDecl*> seen;
  return from != nullptr && ReachesUpward(*from, path, seen);
}

}  // namespace delta
