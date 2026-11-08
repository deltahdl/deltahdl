#pragma once

#include <memory>

#include "elaborator/annex_f_grammar.h"

namespace delta {

std::shared_ptr<const SequenceExpr> RewriteSequenceUnderClock(
    const SequenceExpr& sequence,
    const std::shared_ptr<const BooleanExpr>& clock);

std::shared_ptr<const SequenceExpr> RewriteClockedSequence(
    const SequenceExpr& sequence);

bool ClockEventsAreLocalVariableIndependent(const SequenceExpr& sequence);

}  // namespace delta
