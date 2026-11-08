#include "elaborator/annex_f_property_rewrite.h"

#include <memory>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"

namespace delta {

namespace {

std::shared_ptr<ClockedProperty> Make(ClockedProperty::Kind kind) {
  auto node = std::make_shared<ClockedProperty>();
  node->kind = kind;
  return node;
}

}  // namespace

std::shared_ptr<const ClockedProperty> ClkBoolean(
    std::shared_ptr<const BooleanExpr> b) {
  auto node = Make(ClockedProperty::Kind::kBoolean);
  node->boolean = std::move(b);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkStrong(
    std::shared_ptr<const SequenceExpr> r) {
  auto node = Make(ClockedProperty::Kind::kStrong);
  node->sequence = std::move(r);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkWeak(
    std::shared_ptr<const SequenceExpr> r) {
  auto node = Make(ClockedProperty::Kind::kWeak);
  node->sequence = std::move(r);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkClock(
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const ClockedProperty> p) {
  auto node = Make(ClockedProperty::Kind::kClock);
  node->boolean = std::move(clock);
  node->lhs = std::move(p);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p) {
  auto node = Make(ClockedProperty::Kind::kDisableIff);
  node->boolean = std::move(b);
  node->lhs = std::move(p);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p) {
  auto node = Make(ClockedProperty::Kind::kAcceptOn);
  node->boolean = std::move(b);
  node->lhs = std::move(p);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkSyncAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p) {
  auto node = Make(ClockedProperty::Kind::kSyncAcceptOn);
  node->boolean = std::move(b);
  node->lhs = std::move(p);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkNot(
    std::shared_ptr<const ClockedProperty> p) {
  auto node = Make(ClockedProperty::Kind::kNot);
  node->lhs = std::move(p);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const ClockedProperty> consequent) {
  auto node = Make(ClockedProperty::Kind::kImplication);
  node->sequence = std::move(antecedent);
  node->lhs = std::move(consequent);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkOr(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b) {
  auto node = Make(ClockedProperty::Kind::kOr);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkAnd(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b) {
  auto node = Make(ClockedProperty::Kind::kAnd);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkNexttime(
    std::shared_ptr<const ClockedProperty> p) {
  auto node = Make(ClockedProperty::Kind::kNexttime);
  node->lhs = std::move(p);
  return node;
}

std::shared_ptr<const ClockedProperty> ClkUntil(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b) {
  auto node = Make(ClockedProperty::Kind::kUntil);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

bool ClockedPropertyEqual(const ClockedProperty& lhs,
                          const ClockedProperty& rhs) {
  if (lhs.kind != rhs.kind) {
    return false;
  }
  auto boolean_equal = [](const std::shared_ptr<const BooleanExpr>& a,
                          const std::shared_ptr<const BooleanExpr>& b) {
    if (!a || !b) {
      return a == b;
    }
    return BooleanExprEqual(*a, *b);
  };
  auto sequence_equal = [](const std::shared_ptr<const SequenceExpr>& a,
                           const std::shared_ptr<const SequenceExpr>& b) {
    if (!a || !b) {
      return a == b;
    }
    return SequenceExprEqual(*a, *b);
  };
  auto child_equal = [](const std::shared_ptr<const ClockedProperty>& a,
                        const std::shared_ptr<const ClockedProperty>& b) {
    if (!a || !b) {
      return a == b;
    }
    return ClockedPropertyEqual(*a, *b);
  };
  return boolean_equal(lhs.boolean, rhs.boolean) &&
         sequence_equal(lhs.sequence, rhs.sequence) &&
         child_equal(lhs.lhs, rhs.lhs) && child_equal(lhs.rhs, rhs.rhs);
}

std::shared_ptr<const ClockedProperty> RewritePropertyUnderClock(
    const ClockedProperty& property,
    const std::shared_ptr<const BooleanExpr>& clock) {
  switch (property.kind) {
    case ClockedProperty::Kind::kBoolean:
      return std::make_shared<ClockedProperty>(property);
    case ClockedProperty::Kind::kStrong:
      return ClkStrong(RewriteSequenceUnderClock(*property.sequence, clock));
    case ClockedProperty::Kind::kWeak:
      return ClkWeak(RewriteSequenceUnderClock(*property.sequence, clock));
    case ClockedProperty::Kind::kClock:
      return RewritePropertyUnderClock(*property.lhs, property.boolean);
    case ClockedProperty::Kind::kDisableIff:
      return ClkDisableIff(property.boolean,
                           RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kAcceptOn:
      return ClkAcceptOn(property.boolean,
                         RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kSyncAcceptOn:
      return ClkAcceptOn(BoolAnd(property.boolean, clock),
                         RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kNot:
      return ClkNot(RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kImplication:
      return ClkImplication(
          RewriteSequenceUnderClock(*property.sequence, clock),
          RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kOr:
      return ClkOr(RewritePropertyUnderClock(*property.lhs, clock),
                   RewritePropertyUnderClock(*property.rhs, clock));
    case ClockedProperty::Kind::kAnd:
      return ClkAnd(RewritePropertyUnderClock(*property.lhs, clock),
                    RewritePropertyUnderClock(*property.rhs, clock));
    case ClockedProperty::Kind::kNexttime: {
      auto inner = RewritePropertyUnderClock(*property.lhs, clock);
      auto not_clock = ClkBoolean(BoolNot(clock));
      auto on_clock = ClkBoolean(clock);
      auto wait_then_body = ClkUntil(not_clock, ClkAnd(on_clock, inner));
      auto step = ClkNexttime(wait_then_body);
      return ClkUntil(not_clock, ClkAnd(on_clock, step));
    }
    case ClockedProperty::Kind::kUntil: {
      auto left = RewritePropertyUnderClock(*property.lhs, clock);
      auto right = RewritePropertyUnderClock(*property.rhs, clock);
      auto on_clock = ClkBoolean(clock);
      auto guard = ClkNot(ClkAnd(on_clock, ClkNot(left)));
      auto release = ClkAnd(on_clock, right);
      return ClkUntil(guard, release);
    }
  }
  return std::make_shared<ClockedProperty>(property);
}

bool PropertyIsUnclocked(const ClockedProperty& property) {
  if (property.kind == ClockedProperty::Kind::kClock ||
      property.kind == ClockedProperty::Kind::kSyncAcceptOn) {
    return false;
  }
  if (property.sequence != nullptr && ContainsClock(*property.sequence)) {
    return false;
  }
  if (property.lhs != nullptr && !PropertyIsUnclocked(*property.lhs)) {
    return false;
  }
  return property.rhs == nullptr || PropertyIsUnclocked(*property.rhs);
}

}  // namespace delta
