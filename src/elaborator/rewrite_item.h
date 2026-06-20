#pragma once

#include <cstdint>

#include "parser/ast.h"

namespace delta {

// §F.4 defines the auxiliary function `item` used by the rewriting
// algorithm. The model here captures the wrapper's semantics: which
// operations on the underlying expression are admitted by `item(e)`,
// keyed off the role `e` plays in the source program.

enum class ItemOperandKind : std::uint8_t {
  // §F.4 final sentence: when e has an undefined type, item adds nothing.
  kUndefinedType,
  // §F.4: ordinary typed expression. item enables operations valid on a
  // reference to or instance of a named item of e's type.
  kTypedExpr,
  // §F.4: e is a sequence; item additionally enables operations valid on
  // a named-sequence instance.
  kSequence,
  // §F.4: e is a non-top-level property; item additionally enables
  // operations valid on a named-property instance.
  kProperty,
  // §F.4: e is a top-level property. The text calls this out explicitly
  // ("including a top-level property"), so it has its own kind to make
  // the case observable.
  kTopLevelProperty,
};

// §F.4 lists three classes of operation that `item(e)` may re-admit on
// top of e's own operations. Callers ask whether a given class is allowed.
enum class ItemOperation : std::uint8_t {
  // Operation legal on a reference to or instance of a named item that
  // shares e's type (e.g., a part-select on a logic[0:3] reference).
  kNamedItemOfTypeOp,
  // Operation legal on an instance of a named sequence.
  kSequenceInstanceOp,
  // Operation legal on an instance of a named property.
  kPropertyInstanceOp,
};

class ItemExpr {
 public:
  // §F.4: `item` may be applied to any expression that may appear as an
  // actual argument in a sequence/property/checker/let instance. The
  // caller asserts that constraint before wrapping; this class does not
  // re-derive it from the AST.
  static ItemExpr Wrap(const Expr* e, ItemOperandKind kind);

  const Expr* Wrapped() const { return wrapped_; }
  ItemOperandKind Kind() const { return kind_; }

  // §F.4: item(e) behaves like e in all respects except for the operation
  // extensions modeled below; this accessor preserves identity of the
  // wrapped node so passes that lower `item` can reach the original.
  bool BehavesLikeWrapped() const { return wrapped_ != nullptr; }

  // §F.4: returns true iff `op` is admitted on this item-wrapped
  // expression by the §F.4 extension rules. The base operations of the
  // wrapped expression are evaluated by callers on `wrapped()` directly;
  // this method only answers the "also allowed" question.
  bool Admits(ItemOperation op) const;

  // §F.4: item is not a SystemVerilog function; it is introduced only in
  // the rewriting algorithm. Front-end passes use this to reject any user
  // attempt to call item() from source code.
  static constexpr bool IsSystemVerilogFunction() { return false; }

 private:
  ItemExpr(const Expr* e, ItemOperandKind k) : wrapped_(e), kind_(k) {}
  const Expr* wrapped_ = nullptr;
  ItemOperandKind kind_ = ItemOperandKind::kUndefinedType;
};

}  // namespace delta
