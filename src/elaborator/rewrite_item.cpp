#include "elaborator/rewrite_item.h"

namespace delta {

ItemExpr ItemExpr::Wrap(const Expr* e, ItemOperandKind kind) {
  return ItemExpr(e, kind);
}

bool ItemExpr::Admits(ItemOperation op) const {
  // §F.4 final sentence: undefined-typed expressions get no extra
  // operations from item.
  if (kind_ == ItemOperandKind::kUndefinedType) return false;

  switch (op) {
    case ItemOperation::kNamedItemOfTypeOp:
      // §F.4: every defined-type kind admits named-item-of-type
      // operations because each carries a type that anchors them.
      return true;
    case ItemOperation::kSequenceInstanceOp:
      // §F.4: sequence-instance operations are admitted only when e is
      // itself a sequence.
      return kind_ == ItemOperandKind::kSequence;
    case ItemOperation::kPropertyInstanceOp:
      // §F.4: property-instance operations are admitted for any property,
      // explicitly including the top-level case.
      return kind_ == ItemOperandKind::kProperty ||
             kind_ == ItemOperandKind::kTopLevelProperty;
  }
  return false;
}

}  // namespace delta
