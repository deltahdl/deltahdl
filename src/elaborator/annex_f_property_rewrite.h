#pragma once

#include <cstdint>
#include <memory>

#include "elaborator/annex_f_grammar.h"

namespace delta {

struct ClockedProperty {
  enum class Kind : std::uint8_t {
    kBoolean,
    kStrong,
    kWeak,
    kClock,
    kDisableIff,
    kAcceptOn,
    kSyncAcceptOn,
    kNot,
    kImplication,
    kOr,
    kAnd,
    kNexttime,
    kUntil,
  };

  Kind kind = Kind::kBoolean;
  std::shared_ptr<const BooleanExpr> boolean;
  std::shared_ptr<const SequenceExpr> sequence;
  std::shared_ptr<const ClockedProperty> lhs;
  std::shared_ptr<const ClockedProperty> rhs;
};

std::shared_ptr<const ClockedProperty> ClkBoolean(
    std::shared_ptr<const BooleanExpr> b);
std::shared_ptr<const ClockedProperty> ClkStrong(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const ClockedProperty> ClkWeak(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const ClockedProperty> ClkClock(
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkSyncAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkNot(
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const ClockedProperty> consequent);
std::shared_ptr<const ClockedProperty> ClkOr(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b);
std::shared_ptr<const ClockedProperty> ClkAnd(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b);
std::shared_ptr<const ClockedProperty> ClkNexttime(
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkUntil(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b);

bool ClockedPropertyEqual(const ClockedProperty& lhs,
                          const ClockedProperty& rhs);

std::shared_ptr<const ClockedProperty> RewritePropertyUnderClock(
    const ClockedProperty& property,
    const std::shared_ptr<const BooleanExpr>& clock);

bool PropertyIsUnclocked(const ClockedProperty& property);

}  // namespace delta
