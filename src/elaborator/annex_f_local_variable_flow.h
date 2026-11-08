#pragma once

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"

namespace delta {

std::set<std::string> SampleLocals(const SequenceExpr& sequence);

std::set<std::string> BlockLocals(const SequenceExpr& sequence);

std::set<std::string> FlowLocals(const std::set<std::string>& incoming,
                                 const SequenceExpr& sequence);

}  // namespace delta
