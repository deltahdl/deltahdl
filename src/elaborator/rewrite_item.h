#pragma once

#include <cstdint>

#include "parser/ast_expr.h"

namespace delta {

enum class ItemOperandKind : std::uint8_t {
  kUndefinedType,
  kTypedExpr,
  kSequence,
  kProperty,
  kTopLevelProperty,
};

enum class ItemOperation : std::uint8_t {
  kNamedItemOfTypeOp,
  kSequenceInstanceOp,
  kPropertyInstanceOp,
};

class ItemExpr {
 public:
  static ItemExpr Wrap(const Expr* e, ItemOperandKind kind);

  const Expr* Wrapped() const { return wrapped_; }
  ItemOperandKind Kind() const { return kind_; }

  bool BehavesLikeWrapped() const { return wrapped_ != nullptr; }

  bool Admits(ItemOperation op) const;

  static constexpr bool IsSystemVerilogFunction() { return false; }

 private:
  ItemExpr(const Expr* e, ItemOperandKind k) : wrapped_(e), kind_(k) {}
  const Expr* wrapped_ = nullptr;
  ItemOperandKind kind_ = ItemOperandKind::kUndefinedType;
};

}  // namespace delta
