#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

struct SemanticLeadingClock {
  bool inherited = true;
  std::string event_expression;
};

SemanticLeadingClock InheritedLeadingClock();
SemanticLeadingClock ExplicitLeadingClock(std::string_view event_expression);

std::string KappaForLocalVarRewrite(const SemanticLeadingClock& leading_clock);

enum class AdmitsEmptyForm : uint8_t {
  kBoolean,
  kLocalVarDeclThenRest,
  kOneTickWithLocalVarAssignment,
  kParenthesized,
  kDelay1,
  kDelay0,
  kOr,
  kIntersect,
  kFirstMatch,
  kStarZero,
  kPlusBounded,
  kClockedAt,
};

bool AdmitsEmpty(AdmitsEmptyForm form, bool first_child_admits_empty,
                 bool second_child_admits_empty);

enum class SequenceLocalVarDeclRewrite : uint8_t {
  kGeneral,
  kSimplifiedNonEmpty,
  kSimplifiedEmpty,
};

SequenceLocalVarDeclRewrite RewriteSequenceLocalVarDecl(bool rest_admits_empty);

enum class PushSite : uint8_t {
  kLocalVarDeclThenProp,
  kLocalVarAssignThenProp,
  kSequenceAsProperty,
  kOverlappingImplication,
  kNonoverlappingImplication,
  kIfElse,
  kDisableIff,
  kClockedAtProp,
  kParenthesized,
  kNot,
  kOr,
  kAnd,
};

enum class PushRouting : uint8_t {
  kPrependLocalVarDecl,
  kPrependLocalVarAssignment,
  kAttachKappaWithDelayZero,
  kAttachKappaToBothSides,
  kRecurseBothBranches,
  kRecurseInner,
  kAttachKappaWithDelayOneToBoth,
  kGuardWithImplicationThenBranches,
};

PushRouting RoutePush(PushSite site, bool list_empty, bool right_admits_empty);

}  // namespace delta
