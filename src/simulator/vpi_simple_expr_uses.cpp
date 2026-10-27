#include "simulator/vpi_simple_expr_uses.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <unordered_set>
#include <utility>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// Whether `obj` selects out of the object it reaches through vpiParent: a
// select or a bit of a vector, or a member of an array.
bool SelectsFromParent(const VpiObject& obj) {
  switch (obj.type) {
    case vpiBitSelect:
    case vpiPartSelect:
    case vpiIndexedPartSelect:
    case vpiVarSelect:
    case vpiRegBit:
    case vpiNetBit:
      return true;
    default:
      return obj.array_member;
  }
}

// Whether `obj` is one bit of a vector: a bit select, a var bit or a net bit.
bool IsBit(const VpiObject& obj) {
  return obj.type == vpiBitSelect || obj.type == vpiRegBit ||
         obj.type == vpiNetBit;
}

// §37.58 detail 1: whether `node` is the vector `vector` or a select of it,
// reached from it through selects alone.
bool IsVectorOrSelectOf(const VpiObject* node, const VpiObject* vector) {
  for (; node != nullptr; node = node->parent) {
    if (node == vector) return true;
    if (!SelectsFromParent(*node)) return false;
  }
  return false;
}

// The lowest and highest index the part select `select` holds, where the
// bounds, or the base and the width, it was written with hold values at
// elaboration; none for an object written with no bounds, which is no part
// select.
std::optional<std::pair<int64_t, int64_t>> PartSelectSpan(
    const VpiObject& select) {
  if (select.type == vpiIndexedPartSelect) {
    const std::optional<int64_t> kBase = VpiElaborationValue(select.base_expr);
    const std::optional<int64_t> kWidth =
        VpiElaborationValue(select.width_expr);
    if (!kBase || !kWidth) return std::nullopt;
    if (select.indexed_part_select_type == vpiPosIndexed) {
      return std::pair{*kBase, *kBase + *kWidth - 1};
    }
    return std::pair{*kBase - *kWidth + 1, *kBase};
  }
  const std::optional<int64_t> kLeft = VpiElaborationValue(select.left_range);
  const std::optional<int64_t> kRight = VpiElaborationValue(select.right_range);
  if (!kLeft || !kRight) return std::nullopt;
  return std::pair{std::min(*kLeft, *kRight), std::max(*kLeft, *kRight)};
}

// §37.58 detail 2: whether `node` uses the bit `bit`: it is that bit, the
// vector `bit` is a bit of, a bit select of that vector at the same constant
// index, or a part select of it whose constant bounds hold the bit.
bool IsUseOfBit(const VpiObject* node, const VpiObject& bit) {
  if (node == &bit || node == bit.parent) return true;
  if (bit.parent == nullptr || node->parent != bit.parent) return false;
  const std::optional<int64_t> kIndex = VpiElaborationValue(bit.index_expr);
  if (!kIndex) return false;
  if (IsBit(*node)) return VpiElaborationValue(node->index_expr) == kIndex;
  const auto kSpan = PartSelectSpan(*node);
  return kSpan && kSpan->first <= *kIndex && *kIndex <= kSpan->second;
}

}  // namespace

bool VpiExpressionUses(const VpiObject* node, const VpiObject& expr) {
  // A net or a variable the expression names is the object itself, whose own
  // children are its bits and its drivers and loads, none written in the
  // expression.
  if (node == nullptr) return false;
  if (IsBit(expr) ? IsUseOfBit(node, expr) : IsVectorOrSelectOf(node, &expr)) {
    return true;
  }
  for (const VpiObject* part :
       {node->index_expr, node->base_expr, node->width_expr, node->left_range,
        node->right_range}) {
    if (VpiExpressionUses(part, expr)) return true;
  }
  if (!VpiIsExprType(node->type)) return false;
  return std::ranges::any_of(
      VpiSubexpressions(*node),
      [&](const VpiObject* sub) { return VpiExpressionUses(sub, expr); });
}

namespace {

// Whether `obj` is of a kind §37.58's figure draws vpiUse to.
bool IsUseKind(VpiHandle obj) {
  switch (obj->type) {
    case vpiPrimTerm:
    case vpiPathTerm:
    case vpiTchkTerm:
    case vpiDelayTerm:
    case vpiContAssign:
    case vpiContAssignBit:
      return true;
    default:
      return VpiIsPortsType(obj->type) || VpiIsAtomicStmtObject(obj);
  }
}

void GatherUses(VpiObject* scope, const VpiObject& expr,
                std::unordered_set<const VpiObject*>& seen,
                std::vector<VpiObject*>& uses);

// Gathers into `uses` those of the delay terms standing on the net `net` that
// use `expr`. §37.45 keeps a delay device out of its module's children, so
// its terms are reached through the net, among whose children they hang
// (vpi_delay_devices.cpp).
void GatherDelayTermUses(const VpiObject& net, const VpiObject& expr,
                         std::unordered_set<const VpiObject*>& seen,
                         std::vector<VpiObject*>& uses) {
  for (VpiObject* term : net.children) {
    if (term->type == vpiDelayTerm) GatherUses(term, expr, seen, uses);
  }
}

// Gathers into `uses`, once each, the uses of `expr` held under `scope`, the
// statements inside a statement among them. An expression's children are
// walked by ExpressionUses alone, a statement written as a call excepted, and
// of a net's only the delay terms standing on it.
void GatherUses(VpiObject* scope, const VpiObject& expr,
                std::unordered_set<const VpiObject*>& seen,
                std::vector<VpiObject*>& uses) {
  if (scope == nullptr || !seen.insert(scope).second) return;
  if (IsUseKind(scope) && VpiUsesExpr(*scope, expr)) uses.push_back(scope);
  for (VpiObject* child : scope->children) {
    if (!VpiIsOperandObject(child)) {
      GatherUses(child, expr, seen, uses);
    } else if (VpiIsNetsType(child->type)) {
      GatherDelayTermUses(*child, expr, seen, uses);
    }
  }
  GatherUses(scope->body, expr, seen, uses);
  GatherUses(scope->else_stmt, expr, seen, uses);
}

}  // namespace

bool VpiUsesExpr(const VpiObject& use, const VpiObject& expr) {
  // §37.47 gives a cont assign bit no sides of its own: its value is its bit
  // of the assignment's, so it reads what the assignment reads.
  if (use.type == vpiContAssignBit) {
    return use.parent != nullptr && VpiUsesExpr(*use.parent, expr);
  }
  // A path term and a tchk term hold the expression of their terminal (§37.39,
  // §37.40), and a delay term the net it stands on (§37.45).
  for (const VpiObject* side : {use.lhs, use.rhs, use.high_conn, use.low_conn,
                                use.term_expr, use.term_net}) {
    if (VpiExpressionUses(side, expr)) return true;
  }
  return std::ranges::any_of(use.children, [&](VpiObject* child) {
    return VpiIsOperandObject(child) && VpiExpressionUses(child, expr);
  });
}

bool VpiIsSimpleExpr(VpiHandle obj) {
  if (obj == nullptr) return false;
  switch (obj->type) {
    case vpiRefObj:
    case vpiParameter:
    case vpiSpecParam:
    case vpiVarSelect:
    case vpiBitSelect:
      return true;
    default:
      return VpiIsNetsType(obj->type) || VpiIsVariablesType(obj->type);
  }
}

std::vector<VpiObject*> VpiSimpleExprUses(VpiHandle expr) {
  // The uses of an object are written in the design it is part of, which the
  // top it stands under holds.
  std::vector<VpiObject*> uses;
  VpiObject* root = expr;
  while (root->parent != nullptr) root = root->parent;
  std::unordered_set<const VpiObject*> seen;
  GatherUses(root, *expr, seen, uses);
  return uses;
}

}  // namespace delta
