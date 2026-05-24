#pragma once

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"

namespace delta {

// §F.5.4 defines inductively how local variable names flow through unclocked
// sequences. It introduces three functions over the §F.3.2 sequence model,
// each returning a set of local variable names. The set operations are the
// usual union, intersection, difference, and the empty set.

// §F.5.4 "sample": the set of local variable names that are sampled (i.e.,
// assigned) within the sequence.
std::set<std::string> SampleLocals(const SequenceExpr& sequence);

// §F.5.4 "block": the set of local variable names that are blocked from
// flowing out of the sequence.
std::set<std::string> BlockLocals(const SequenceExpr& sequence);

// §F.5.4 "flow": given the set of names flowing into the sequence, the set of
// names that flow out of it.
std::set<std::string> FlowLocals(const std::set<std::string>& incoming,
                                 const SequenceExpr& sequence);

}  // namespace delta
