#include "elaborator/rewrite_item.h"

#include "parser/ast_expr.h"

namespace delta {

ItemExpr ItemExpr::Wrap(const Expr* e, ItemOperandKind kind) {
  return ItemExpr(e, kind);
}

bool ItemExpr::Admits(ItemOperation op) const {
  if (kind_ == ItemOperandKind::kUndefinedType) return false;

  switch (op) {
    case ItemOperation::kNamedItemOfTypeOp:
      return true;
    case ItemOperation::kSequenceInstanceOp:
      return kind_ == ItemOperandKind::kSequence;
    case ItemOperation::kPropertyInstanceOp:
      return kind_ == ItemOperandKind::kProperty ||
             kind_ == ItemOperandKind::kTopLevelProperty;
  }
  return false;
}

}  // namespace delta
