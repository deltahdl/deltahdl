#include "elaborator/annex_f_property_rewrite.h"

#include <memory>

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
      // A Boolean already names a level-sensitive condition; nothing to push.
      return std::make_shared<ClockedProperty>(property);
    case ClockedProperty::Kind::kStrong:
      // §F.5.1.2: T^p(strong(r), c) = (strong(T^s(r, c))).
      return ClkStrong(RewriteSequenceUnderClock(*property.sequence, clock));
    case ClockedProperty::Kind::kWeak:
      // §F.5.1.2: T^p(weak(r), c) = (weak(T^s(r, c))).
      return ClkWeak(RewriteSequenceUnderClock(*property.sequence, clock));
    case ClockedProperty::Kind::kClock:
      // §F.5.1.2: T^p((@(c2) p), c1) = T^p(p, c2). The inner clock c2 takes
      // over and the incoming clock c1 is discarded.
      return RewritePropertyUnderClock(*property.lhs, property.boolean);
    case ClockedProperty::Kind::kDisableIff:
      // §F.5.1.2: T^p((disable iff(b) p), c) = (disable iff(b) T^p(p, c)).
      return ClkDisableIff(property.boolean,
                           RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kAcceptOn:
      // §F.5.1.2: T^p((accept_on(b) p), c) = (accept_on(b) T^p(p, c)). The
      // asynchronous abort condition b is left untouched.
      return ClkAcceptOn(property.boolean,
                         RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kSyncAcceptOn:
      // §F.5.1.2: T^p((sync_accept_on(b) p), c) = (accept_on(b && c) T^p(p,c)).
      // The synchronous abort is sampled with the clock, so its condition is
      // conjoined with c and it becomes an ordinary accept_on.
      return ClkAcceptOn(BoolAnd(property.boolean, clock),
                         RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kNot:
      // §F.5.1.2: T^p((not p), c) = (not T^p(p, c)).
      return ClkNot(RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kImplication:
      // §F.5.1.2: T^p((r |-> p), c) = (T^s(r, c) |-> T^p(p, c)).
      return ClkImplication(
          RewriteSequenceUnderClock(*property.sequence, clock),
          RewritePropertyUnderClock(*property.lhs, clock));
    case ClockedProperty::Kind::kOr:
      // §F.5.1.2: T^p((p1 or p2), c) = (T^p(p1, c) or T^p(p2, c)).
      return ClkOr(RewritePropertyUnderClock(*property.lhs, clock),
                   RewritePropertyUnderClock(*property.rhs, clock));
    case ClockedProperty::Kind::kAnd:
      // §F.5.1.2: T^p((p1 and p2), c) = (T^p(p1, c) and T^p(p2, c)).
      return ClkAnd(RewritePropertyUnderClock(*property.lhs, clock),
                    RewritePropertyUnderClock(*property.rhs, clock));
    case ClockedProperty::Kind::kNexttime: {
      // §F.5.1.2: T^p((nexttime p), c) =
      //   (!c until (c and nexttime(!c until (c and T^p(p, c))))).
      // The clock may idle, then on a clock tick the body must hold one further
      // clocked step later, with the same idle-then-tick pattern repeated.
      auto inner = RewritePropertyUnderClock(*property.lhs, clock);
      auto not_clock = ClkBoolean(BoolNot(clock));
      auto on_clock = ClkBoolean(clock);
      auto wait_then_body = ClkUntil(not_clock, ClkAnd(on_clock, inner));
      auto step = ClkNexttime(wait_then_body);
      return ClkUntil(not_clock, ClkAnd(on_clock, step));
    }
    case ClockedProperty::Kind::kUntil: {
      // §F.5.1.2: T^p((p1 until p2), c) =
      //   ((not(c and not T^p(p1, c))) until (c and T^p(p2, c))).
      // Off the clock the obligation idles; on a clock tick p1 must hold until
      // a clock tick on which p2 holds.
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

}  // namespace delta
