#pragma once

#include <cstdint>
#include <optional>

#include "elaborator/rewrite_algorithm.h"

namespace delta {

enum class CheckerRewriteStage : std::uint8_t {
  kCheckerInstances,
};

CheckerRewriteStage FirstCheckerRewriteStage();

CheckerRewriteStage NextCheckerRewriteStage(CheckerRewriteStage stage);

std::optional<ActualArgumentSource> CheckerActualArgumentFor(
    bool bound_in_instance, bool default_declared);

bool CheckerAlgorithmHandlesFormal(FormalKind kind);

ReferenceReplacement ReplaceCheckerFormalReference(FormalKind kind,
                                                   ActualNature actual);

enum class LvalueProhibitionScope : std::uint8_t {
  kWholeChecker,
};

struct CastReplacedFormalLvalueRule {
  bool replacement_may_be_lvalue = false;
  LvalueProhibitionScope scope = LvalueProhibitionScope::kWholeChecker;
};

CastReplacedFormalLvalueRule CheckerCastReplacedFormalLvalueRule();

bool CheckerParenthesizedActualNeedsParentheses(
    bool reference_already_parenthesized);

struct FlattenedCheckerShape {
  bool prepends_local_var_declarations = false;
  bool appends_match_item_assignments = false;
  bool enclosed_in_parentheses = false;
};

FlattenedCheckerShape FlattenedCheckerForm();

}  // namespace delta
