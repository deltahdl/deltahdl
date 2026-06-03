#include "elaborator/property_rewrite.h"

#include <unordered_set>
#include <vector>

namespace delta {

void PropertyRegistry::Register(const ModuleItem* decl) {
  if (decl == nullptr) return;
  if (decl->kind != ModuleItemKind::kPropertyDecl &&
      decl->kind != ModuleItemKind::kSequenceDecl) {
    return;
  }
  by_name_.emplace(decl->name, decl);
}

const ModuleItem* PropertyRegistry::Find(std::string_view name) const {
  auto it = by_name_.find(name);
  if (it == by_name_.end()) return nullptr;
  return it->second;
}

int PropertyRegistry::FlattenedDisableIffCount(const ModuleItem* decl) const {
  if (decl == nullptr) return 0;
  // visited prevents recursive properties from forcing an infinite walk.
  std::unordered_set<const ModuleItem*> visited;
  std::vector<const ModuleItem*> stack;
  stack.push_back(decl);
  int total = 0;
  while (!stack.empty()) {
    const ModuleItem* cur = stack.back();
    stack.pop_back();
    if (!visited.insert(cur).second) continue;
    total += cur->prop_disable_iff_count;
    for (auto ref : cur->prop_instance_refs) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      stack.push_back(it->second);
    }
  }
  return total;
}

FlattenedProperty PropertyRegistry::Flatten(
    std::string_view name, std::size_t actual_arg_count) const {
  FlattenedProperty fp;
  fp.name = name;
  const ModuleItem* decl = Find(name);
  if (decl == nullptr) {
    fp.legal = false;
    return fp;
  }
  fp.formal_count = decl->prop_formals.size();
  fp.disable_iff_count = FlattenedDisableIffCount(decl);
  fp.remaining_instances = 0;
  // §16.12: actuals must bind every formal, otherwise the substituted body
  // would still reference an unbound formal.
  bool args_ok = actual_arg_count == fp.formal_count;
  // §16.12: nesting of disable iff, explicitly or through instantiation, is
  // not allowed.
  bool no_disable_iff_nesting = fp.disable_iff_count <= 1;
  fp.legal = args_ok && no_disable_iff_nesting;
  return fp;
}

bool PropertyRegistry::IsAcceptableAsTopLevelConcurrent(
    const FlattenedProperty& fp) {
  return fp.legal && fp.remaining_instances == 0;
}

bool PropertyRegistry::HasCyclicSequenceDependency(
    const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kSequenceDecl) return false;

  // Three-color DFS: `path` marks nodes on the current descent — re-visiting
  // one means there is a back-edge, which is exactly §16.8's cycle.
  std::unordered_set<const ModuleItem*> path;
  std::unordered_set<const ModuleItem*> done;

  auto dfs = [&](auto& self, const ModuleItem* node) -> bool {
    if (!path.insert(node).second) return true;
    for (auto ref : node->prop_instance_refs) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      const ModuleItem* next = it->second;
      // Only sequence-to-sequence edges count for §16.8's cycle rule.
      if (next->kind != ModuleItemKind::kSequenceDecl) continue;
      if (done.count(next) != 0) continue;
      if (self(self, next)) return true;
    }
    path.erase(node);
    done.insert(node);
    return false;
  };

  return dfs(dfs, decl);
}

bool PropertyRegistry::IsRecursiveProperty(const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kPropertyDecl) return false;

  // Push every property reachable in one step from `node`. Edges run only
  // between named properties; instantiations of named sequences are not part
  // of the property dependency digraph.
  auto push_property_callees = [&](const ModuleItem* node,
                                   std::vector<const ModuleItem*>& stack) {
    for (auto ref : node->prop_instance_refs) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      if (it->second->kind != ModuleItemKind::kPropertyDecl) continue;
      stack.push_back(it->second);
    }
  };

  // Recursive iff, starting from `decl`'s callees, we can arrive back at
  // `decl`.
  std::unordered_set<const ModuleItem*> visited;
  std::vector<const ModuleItem*> stack;
  push_property_callees(decl, stack);
  while (!stack.empty()) {
    const ModuleItem* cur = stack.back();
    stack.pop_back();
    if (cur == decl) return true;
    if (!visited.insert(cur).second) continue;
    push_property_callees(cur, stack);
  }
  return false;
}

bool PropertyRegistry::ReachesRecursiveProperty(const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kPropertyDecl) return false;

  std::unordered_set<const ModuleItem*> visited;
  std::vector<const ModuleItem*> stack;
  stack.push_back(decl);
  while (!stack.empty()) {
    const ModuleItem* cur = stack.back();
    stack.pop_back();
    if (!visited.insert(cur).second) continue;
    if (IsRecursiveProperty(cur)) return true;
    for (auto ref : cur->prop_instance_refs) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      if (it->second->kind != ModuleItemKind::kPropertyDecl) continue;
      stack.push_back(it->second);
    }
  }
  return false;
}

}  // namespace delta
