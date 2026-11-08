#include "elaborator/property_rewrite.h"

#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/sampled_value.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

bool SequenceCycleDfs(const PropertyRegistry& registry, const ModuleItem* node,
                      std::unordered_set<const ModuleItem*>& path,
                      std::unordered_set<const ModuleItem*>& done) {
  if (!path.insert(node).second) return true;
  for (auto ref : registry.DependencyRefs(node)) {
    const ModuleItem* next = registry.Find(ref);
    if (next == nullptr || next->kind != ModuleItemKind::kSequenceDecl) {
      continue;
    }
    if (done.count(next) != 0) continue;
    if (SequenceCycleDfs(registry, next, path, done)) return true;
  }
  path.erase(node);
  done.insert(node);
  return false;
}

void CollectNames(const Expr* e, std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) out.push_back(e->text);
  if (e->kind == ExprKind::kCall) out.push_back(e->callee);
  ForEachExprChild(e, [&](const Expr* child) { CollectNames(child, out); });
}

template <typename Fn>
void ForEachCall(const Expr* e, const Fn& fn) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) fn(e);
  ForEachExprChild(e, [&](const Expr* child) { ForEachCall(child, fn); });
}

template <typename Fn>
void ForEachBodyExpr(const SeqLinearBody& body, const Fn& fn) {
  for (const Expr* operand : body.operands) fn(operand);
  for (const SeqLinearBody& inner : body.intersects) {
    ForEachBodyExpr(inner, fn);
  }
  for (const SeqLinearBody& inner : body.conjuncts) ForEachBodyExpr(inner, fn);
  for (const SeqLinearBody& inner : body.alternatives) {
    ForEachBodyExpr(inner, fn);
  }
}

template <typename Fn>
void ForEachTreeExpr(const PropertyExprNode* node, const Fn& fn) {
  if (node == nullptr) return;
  fn(node->boolean);
  if (node->sequence != nullptr)
    ForEachBodyExpr(node->sequence->seq_linear, fn);
  for (const PropertyExprNode* operand : node->operands) {
    ForEachTreeExpr(operand, fn);
  }
}

}  // namespace

bool DisableConditionSampledValueRequiresExplicitClock(
    SampledValueFunction fn) {
  return fn != SampledValueFunction::kSampled;
}

bool DisableConditionSampledValueClockIsWellFormed(
    SampledValueFunction fn, bool clock_explicitly_specified) {
  if (DisableConditionSampledValueRequiresExplicitClock(fn)) {
    return clock_explicitly_specified;
  }
  return true;
}

void PropertyRegistry::Register(const ModuleItem* decl) {
  if (decl == nullptr) return;
  if (decl->kind != ModuleItemKind::kPropertyDecl &&
      decl->kind != ModuleItemKind::kSequenceDecl) {
    return;
  }
  by_name_.emplace(decl->name, decl);
  RecordArgumentRefs(decl);
}

void PropertyRegistry::RecordArgumentRefs(const ModuleItem* decl) {
  for (const Expr* actual : decl->prop_formal_defaults) {
    CollectNames(actual, argument_refs_[decl->name]);
  }
  auto record = [&](const Expr* e) {
    ForEachCall(e, [&](const Expr* call) {
      for (const Expr* arg : call->args) {
        CollectNames(arg, argument_refs_[call->callee]);
      }
    });
  };
  ForEachBodyExpr(decl->seq_linear, record);
  ForEachTreeExpr(decl->prop_body_tree, record);
}

std::vector<std::string_view> PropertyRegistry::DependencyRefs(
    const ModuleItem* decl) const {
  std::vector<std::string_view> refs(decl->prop_instance_refs.begin(),
                                     decl->prop_instance_refs.end());
  auto it = argument_refs_.find(decl->name);
  if (it != argument_refs_.end()) {
    refs.insert(refs.end(), it->second.begin(), it->second.end());
  }
  return refs;
}

void PropertyRegistry::RegisterShadowing(const ModuleItem* decl) {
  by_name_.erase(decl->name);
  Register(decl);
}

void PropertyRegistry::RegisterAs(std::string_view name,
                                  const ModuleItem* decl) {
  by_name_.emplace(name, decl);
}

const ModuleItem* PropertyRegistry::Find(std::string_view name) const {
  auto it = by_name_.find(name);
  if (it == by_name_.end()) return nullptr;
  return it->second;
}

const ModuleItem* PropertyRegistry::FindInstance(const Expr* instance) const {
  std::string name = InstanceDeclName(instance);
  return name.empty() ? nullptr : Find(name);
}

int PropertyRegistry::FlattenedDisableIffCount(const ModuleItem* decl) const {
  if (decl == nullptr) return 0;
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
  bool args_ok = actual_arg_count <= fp.formal_count;
  for (size_t i = actual_arg_count; i < fp.formal_count; ++i) {
    bool has_default = i < decl->prop_formal_has_default.size() &&
                       decl->prop_formal_has_default[i];
    args_ok = args_ok && has_default;
  }
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

  std::unordered_set<const ModuleItem*> path;
  std::unordered_set<const ModuleItem*> done;
  return SequenceCycleDfs(*this, decl, path, done);
}

bool PropertyRegistry::IsRecursiveProperty(const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kPropertyDecl) return false;

  auto push_property_callees = [&](const ModuleItem* node,
                                   std::vector<const ModuleItem*>& stack) {
    for (auto ref : DependencyRefs(node)) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      if (it->second->kind != ModuleItemKind::kPropertyDecl) continue;
      stack.push_back(it->second);
    }
  };

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

bool PropertyRegistry::IsOnZeroWeightCycle(const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kPropertyDecl) return false;

  auto push_zero_weight_callees = [&](const ModuleItem* node,
                                      std::vector<const ModuleItem*>& stack) {
    for (auto ref : node->prop_untimed_instance_refs) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      if (it->second->kind != ModuleItemKind::kPropertyDecl) continue;
      stack.push_back(it->second);
    }
  };

  std::unordered_set<const ModuleItem*> visited;
  std::vector<const ModuleItem*> stack;
  push_zero_weight_callees(decl, stack);
  while (!stack.empty()) {
    const ModuleItem* cur = stack.back();
    stack.pop_back();
    if (cur == decl) return true;
    if (!visited.insert(cur).second) continue;
    push_zero_weight_callees(cur, stack);
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
    for (auto ref : DependencyRefs(cur)) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      if (it->second->kind != ModuleItemKind::kPropertyDecl) continue;
      stack.push_back(it->second);
    }
  }
  return false;
}

BlockDeclarationShadow::BlockDeclarationShadow(
    PropertyRegistry* registry, const std::vector<ModuleItem*>& items)
    : registry_(registry) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kPropertyDecl &&
        item->kind != ModuleItemKind::kSequenceDecl) {
      continue;
    }
    if (!enclosing_) enclosing_ = *registry_;
    registry_->RegisterShadowing(item);
  }
}

BlockDeclarationShadow::~BlockDeclarationShadow() {
  if (enclosing_) *registry_ = std::move(*enclosing_);
}

}  // namespace delta
