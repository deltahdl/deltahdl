#include "elaborator/property_rewrite.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/sampled_value.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

// §16.8 three-color DFS body: `path` marks nodes on the current descent —
// re-visiting one means there is a back-edge, which is exactly the cycle.
// Only sequence-to-sequence edges count for the cycle rule.
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

// The names `e` writes, as identifiers or as the callees of calls.
void CollectNames(const Expr* e, std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) out.push_back(e->text);
  if (e->kind == ExprKind::kCall) out.push_back(e->callee);
  ForEachExprChild(e, [&](const Expr* child) { CollectNames(child, out); });
}

// Each call `e` holds, `e` itself among them, handed to `fn`.
template <typename Fn>
void ForEachCall(const Expr* e, const Fn& fn) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) fn(e);
  ForEachExprChild(e, [&](const Expr* child) { ForEachCall(child, fn); });
}

// Each operand expression of the sequence body `body`.
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

// Each expression of the property tree under `node` an instance may stand
// in.
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
  // §16.12 head: $sampled is the sole sampled value function that carries no
  // clocking event of its own, so it alone may omit the explicit clock; every
  // other sampled value function must name its clock in the disable condition.
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

// §16.8 and §16.12: the edges of the dependency digraph the body scan does
// not record: from `decl` to each declaration a formal's default actual
// instantiates, and from the declaration each instance in `decl`'s body
// names to each one the instance's actual arguments instantiate.
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
  // §F.4.1.1 step 2: each formal takes the actual bound to it in the
  // instance, or the default actual declared for it where none is bound; so
  // with the actuals bound positionally, the count may fall short of the
  // formals only where every formal it leaves unbound declares a default,
  // and may not exceed them.
  bool args_ok = actual_arg_count <= fp.formal_count;
  for (size_t i = actual_arg_count; i < fp.formal_count; ++i) {
    bool has_default = i < decl->prop_formal_has_default.size() &&
                       decl->prop_formal_has_default[i];
    args_ok = args_ok && has_default;
  }
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

  // Three-color DFS over sequence-to-sequence instance references (see
  // SequenceCycleDfs); `decl` is on a cycle iff that walk finds a back-edge.
  std::unordered_set<const ModuleItem*> path;
  std::unordered_set<const ModuleItem*> done;
  return SequenceCycleDfs(*this, decl, path, done);
}

bool PropertyRegistry::IsRecursiveProperty(const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kPropertyDecl) return false;

  // Push every property reachable in one step from `node`. Edges run only
  // between named properties; instantiations of named sequences are not part
  // of the property dependency digraph.
  auto push_property_callees = [&](const ModuleItem* node,
                                   std::vector<const ModuleItem*>& stack) {
    for (auto ref : DependencyRefs(node)) {
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

bool PropertyRegistry::IsOnZeroWeightCycle(const ModuleItem* decl) const {
  if (decl == nullptr) return false;
  if (decl->kind != ModuleItemKind::kPropertyDecl) return false;

  // Push every property reached from `node` by a zero-weight (untimed) edge.
  // These edges are the instances recorded with no preceding positive time
  // advance; a cycle among them alone has total weight zero.
  auto push_zero_weight_callees = [&](const ModuleItem* node,
                                      std::vector<const ModuleItem*>& stack) {
    for (auto ref : node->prop_untimed_instance_refs) {
      auto it = by_name_.find(ref);
      if (it == by_name_.end()) continue;
      if (it->second->kind != ModuleItemKind::kPropertyDecl) continue;
      stack.push_back(it->second);
    }
  };

  // On a zero-weight cycle iff, following only zero-weight edges from `decl`'s
  // callees, we can arrive back at `decl`.
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

}  // namespace delta
