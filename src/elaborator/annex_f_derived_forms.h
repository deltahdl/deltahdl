#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"

namespace delta {

enum class ConcurrentAssertionDirective : std::uint8_t {
  kAssert,
  kAssume,
  kCover,
  kRestrict,
};

AssertionStatement::Role RoleOfConcurrentAssertionDirective(
    ConcurrentAssertionDirective directive);

std::shared_ptr<const SequenceExpr> SeqRepeatExactly(
    std::shared_ptr<const SequenceExpr> r, unsigned int m);

std::shared_ptr<const SequenceExpr> SeqRepeatRange(
    std::shared_ptr<const SequenceExpr> r, unsigned int m, unsigned int n);

std::shared_ptr<const SequenceExpr> SeqRepeatAtLeast(
    std::shared_ptr<const SequenceExpr> r, unsigned int m);

std::shared_ptr<const SequenceExpr> SeqRepeatZeroOrMore(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqRepeatOneOrMore(
    std::shared_ptr<const SequenceExpr> r);

std::shared_ptr<const SequenceExpr> SeqDelayRange(
    unsigned int m, unsigned int n, std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqDelayAtLeast(
    unsigned int m, std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqDelayExactly(
    unsigned int m, std::shared_ptr<const SequenceExpr> r);

std::shared_ptr<const SequenceExpr> SeqDelayZeroOrMore(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqDelayOneOrMore(
    std::shared_ptr<const SequenceExpr> r);

std::shared_ptr<const SequenceExpr> SeqConcatDelayRange(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m, unsigned int n,
    std::shared_ptr<const SequenceExpr> r2);

std::shared_ptr<const SequenceExpr> SeqConcatDelayAtLeast(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m,
    std::shared_ptr<const SequenceExpr> r2);

std::shared_ptr<const SequenceExpr> SeqConcatDelayExactly(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m,
    std::shared_ptr<const SequenceExpr> r2);

std::shared_ptr<const SequenceExpr> SeqGotoRange(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m,
    unsigned int n);
std::shared_ptr<const SequenceExpr> SeqGotoAtLeast(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);
std::shared_ptr<const SequenceExpr> SeqGotoExactly(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);
std::shared_ptr<const SequenceExpr> SeqNonconsecutiveRange(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m,
    unsigned int n);
std::shared_ptr<const SequenceExpr> SeqNonconsecutiveAtLeast(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);
std::shared_ptr<const SequenceExpr> SeqNonconsecutiveExactly(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);

std::shared_ptr<const SequenceExpr> SeqAnd(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> r2);

std::shared_ptr<const SequenceExpr> SeqWithin(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> r2);

std::shared_ptr<const SequenceExpr> SeqThroughout(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const SequenceExpr> r);

std::shared_ptr<const SequenceExpr> SeqWithLocalAssignments(
    std::shared_ptr<const SequenceExpr> r,
    const std::vector<std::string>& names);

enum class SequencePropertyContext : std::uint8_t {
  kAssertProperty,
  kAssumeProperty,
  kCoverProperty,
  kRestrictProperty,
  kExpect,
};

bool BareSequenceIsStrong(SequencePropertyContext context);

std::shared_ptr<const PropertyExpr> PropOfBareSequence(
    std::shared_ptr<const SequenceExpr> r, SequencePropertyContext context);
std::shared_ptr<const ClockedProperty> ClkOfBareSequence(
    std::shared_ptr<const SequenceExpr> r, SequencePropertyContext context);

std::shared_ptr<const PropertyExpr> PropImplies(
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2);
std::shared_ptr<const PropertyExpr> PropIff(
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2);
std::shared_ptr<const ClockedProperty> ClkImplies(
    std::shared_ptr<const ClockedProperty> p1,
    std::shared_ptr<const ClockedProperty> p2);
std::shared_ptr<const ClockedProperty> ClkIff(
    std::shared_ptr<const ClockedProperty> p1,
    std::shared_ptr<const ClockedProperty> p2);

std::shared_ptr<const PropertyExpr> PropNonoverlappingImplication(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const ClockedProperty> ClkNonoverlappingImplication(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q);

std::shared_ptr<const PropertyExpr> PropIf(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropIfElse(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2);
std::shared_ptr<const ClockedProperty> ClkIf(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkIfElse(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const ClockedProperty> q1,
    std::shared_ptr<const ClockedProperty> q2);

using CaseMatch = std::function<std::shared_ptr<const BooleanExpr>(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::shared_ptr<const BooleanExpr>& item)>;

struct PropCaseItem {
  std::shared_ptr<const BooleanExpr> b;
  std::shared_ptr<const PropertyExpr> property;
};
struct ClkCaseItem {
  std::shared_ptr<const BooleanExpr> b;
  std::shared_ptr<const ClockedProperty> property;
};

std::shared_ptr<const PropertyExpr> PropCase(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::vector<PropCaseItem>& items,
    std::shared_ptr<const PropertyExpr> default_property,
    const CaseMatch& match);
std::shared_ptr<const ClockedProperty> ClkCase(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::vector<ClkCaseItem>& items,
    std::shared_ptr<const ClockedProperty> default_property,
    const CaseMatch& match);

std::shared_ptr<const PropertyExpr> PropFollowedBy(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropNonoverlappingFollowedBy(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const ClockedProperty> ClkFollowedBy(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkNonoverlappingFollowedBy(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q);

std::shared_ptr<const PropertyExpr> PropRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSyncAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSyncRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const ClockedProperty> ClkRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkSyncRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);

std::shared_ptr<const PropertyExpr> PropAlways(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSEventually(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSUntil(
    const std::shared_ptr<const PropertyExpr>& p,
    const std::shared_ptr<const PropertyExpr>& q);
std::shared_ptr<const PropertyExpr> PropUntilWith(
    const std::shared_ptr<const PropertyExpr>& p,
    std::shared_ptr<const PropertyExpr> q);
std::shared_ptr<const PropertyExpr> PropSUntilWith(
    const std::shared_ptr<const PropertyExpr>& p,
    std::shared_ptr<const PropertyExpr> q);
std::shared_ptr<const ClockedProperty> ClkAlways(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkSEventually(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkSUntil(
    const std::shared_ptr<const ClockedProperty>& q1,
    const std::shared_ptr<const ClockedProperty>& q2);
std::shared_ptr<const ClockedProperty> ClkUntilWith(
    const std::shared_ptr<const ClockedProperty>& q1,
    std::shared_ptr<const ClockedProperty> q2);
std::shared_ptr<const ClockedProperty> ClkSUntilWith(
    const std::shared_ptr<const ClockedProperty>& q1,
    std::shared_ptr<const ClockedProperty> q2);

std::shared_ptr<const PropertyExpr> PropSNexttime(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropNexttimeExactly(
    std::shared_ptr<const PropertyExpr> p, unsigned int m);
std::shared_ptr<const PropertyExpr> PropSNexttimeExactly(
    std::shared_ptr<const PropertyExpr> p, unsigned int m);
std::shared_ptr<const PropertyExpr> PropEventuallyRange(
    const std::shared_ptr<const PropertyExpr>& p, unsigned int m,
    unsigned int n);
std::shared_ptr<const PropertyExpr> PropAlwaysRange(
    const std::shared_ptr<const PropertyExpr>& p, unsigned int m,
    unsigned int n);
std::shared_ptr<const PropertyExpr> PropAlwaysAtLeast(
    std::shared_ptr<const PropertyExpr> p, unsigned int m);
std::shared_ptr<const PropertyExpr> PropSEventuallyRange(
    std::shared_ptr<const PropertyExpr> p, unsigned int m, unsigned int n);
std::shared_ptr<const PropertyExpr> PropSEventuallyAtLeast(
    std::shared_ptr<const PropertyExpr> p, unsigned int m);
std::shared_ptr<const PropertyExpr> PropSAlwaysRange(
    std::shared_ptr<const PropertyExpr> p, unsigned int m, unsigned int n);
std::shared_ptr<const ClockedProperty> ClkSNexttime(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkNexttimeExactly(
    std::shared_ptr<const ClockedProperty> q, unsigned int m);
std::shared_ptr<const ClockedProperty> ClkSNexttimeExactly(
    std::shared_ptr<const ClockedProperty> q, unsigned int m);
std::shared_ptr<const ClockedProperty> ClkEventuallyRange(
    const std::shared_ptr<const ClockedProperty>& q, unsigned int m,
    unsigned int n);
std::shared_ptr<const ClockedProperty> ClkAlwaysRange(
    const std::shared_ptr<const ClockedProperty>& q, unsigned int m,
    unsigned int n);
std::shared_ptr<const ClockedProperty> ClkAlwaysAtLeast(
    std::shared_ptr<const ClockedProperty> q, unsigned int m);
std::shared_ptr<const ClockedProperty> ClkSEventuallyRange(
    std::shared_ptr<const ClockedProperty> q, unsigned int m, unsigned int n);
std::shared_ptr<const ClockedProperty> ClkSEventuallyAtLeast(
    std::shared_ptr<const ClockedProperty> q, unsigned int m);
std::shared_ptr<const ClockedProperty> ClkSAlwaysRange(
    std::shared_ptr<const ClockedProperty> q, unsigned int m, unsigned int n);

struct LocalVarDeclaration {
  std::string type;
  std::string name;
};

std::shared_ptr<const SequenceExpr> SeqLocalVarDecls(
    const std::vector<LocalVarDeclaration>& declarations,
    std::shared_ptr<const SequenceExpr> rest);
std::shared_ptr<const LvProperty> LvLocalVarDecls(
    const std::vector<LocalVarDeclaration>& declarations,
    std::shared_ptr<const LvProperty> body);
std::shared_ptr<const LvTopLevelProperty> LvTopLocalVarDecls(
    const std::vector<LocalVarDeclaration>& declarations,
    std::shared_ptr<const LvTopLevelProperty> body);

using FreeCheckerEquality =
    std::function<std::shared_ptr<const BooleanExpr>(const std::string& u)>;
using FreeCheckerNextValue = std::function<std::shared_ptr<const BooleanExpr>(
    const std::string& u, const std::shared_ptr<const BooleanExpr>& c)>;

EnabledAssertion FreeCheckerRandAssignment(
    const std::string& u, const FreeCheckerEquality& equality,
    std::shared_ptr<const BooleanExpr> enabling);
EnabledAssertion FreeCheckerAlwaysFfAssignment(
    const std::string& u, const std::shared_ptr<const BooleanExpr>& c,
    const FreeCheckerNextValue& next_value,
    std::shared_ptr<const BooleanExpr> enabling);

}  // namespace delta
