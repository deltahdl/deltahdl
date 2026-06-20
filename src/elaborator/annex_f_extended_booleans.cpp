#include "elaborator/annex_f_extended_booleans.h"

#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

namespace {

// Append `context` to `out` unless an equal context is already present, so a
// nondeterministic relation never reports a duplicate witness.
void AddUnique(std::vector<LocalContext>& out, LocalContext context) {
  for (const LocalContext& existing : out) {
    if (LocalContextEqual(existing, context)) {
      return;
    }
  }
  out.push_back(std::move(context));
}

// The finite subword w^{lo,hi-1}: letters lo through hi-1 inclusive, i.e. the
// half-open slice [lo, hi) of `word`. §F.6.1 reasons over such subwords ending
// or starting at the point j.
Word Subword(const Word& word, std::size_t lo, std::size_t hi) {
  return Word(word.begin() + static_cast<std::ptrdiff_t>(lo),
              word.begin() + static_cast<std::ptrdiff_t>(hi));
}

// The sequence c[->1] (goto repetition, once): a run of zero or more letters
// none of which satisfies c, followed by a single letter that does. §F.6.1 uses
// it to require that the destination clock c ticks exactly once, at the end of
// the gap subword.
std::shared_ptr<const SequenceExpr> GotoOnce(
    const std::shared_ptr<const BooleanExpr>& c) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(c))), SeqBoolean(c));
}

// Compute the merged output context L_1 for one tight-satisfaction witness
// `inner` of T, given the incoming context `input` (with precomputed domain
// `in_domain`) and the actual-argument set `actuals` = V. Per §F.6.1:
// D = dom(L_0) - (dom(L) & V) is the set of incoming names the call leaves
// intact, and L_1 = L_0|_D U L|_V. The two restricted domains are disjoint by
// construction, so the union is taken directly.
LocalContext MergeTriggeredOutput(const LocalContext& input,
                                  const std::set<std::string>& in_domain,
                                  const std::set<std::string>& actuals,
                                  const LocalContext& inner) {
  const std::set<std::string> kInnerDomain = ContextDomain(inner);
  std::set<std::string> overwritten;  // dom(L) & V
  for (const std::string& name : kInnerDomain) {
    if (actuals.count(name) != 0) {
      overwritten.insert(name);
    }
  }
  std::set<std::string> d;
  for (const std::string& name : in_domain) {
    if (overwritten.count(name) == 0) {
      d.insert(name);
    }
  }
  LocalContext out = RestrictContext(input, d);
  for (const auto& entry : RestrictContext(inner, actuals)) {
    out.insert(entry);
  }
  return out;
}

}  // namespace

std::vector<LocalContext> TriggeredOutputs(const ExtendedBooleanQuery& query,
                                           const LocalContext& input) {
  std::vector<LocalContext> result;
  if (query.j >= query.word.size()) {
    return result;  // §F.6.1 requires 0 <= j < |w|.
  }
  const std::set<std::string> kInDomain = ContextDomain(input);
  // §F.6.1: try every start point 0 <= i <= j; the subword w^{i,j} must tightly
  // satisfy T from the empty context.
  for (std::size_t i = 0; i <= query.j; ++i) {
    const Word kSlice = Subword(query.word, i, query.j + 1);
    for (const LocalContext& inner :
         TightSatisfactionOutputs(kSlice, query.sequence, LocalContext{})) {
      AddUnique(result,
                MergeTriggeredOutput(input, kInDomain, query.actuals, inner));
    }
  }
  return result;
}

bool TriggeredSatisfies(const ExtendedBooleanQuery& query,
                        const LocalContext& input, const LocalContext& output) {
  for (const LocalContext& candidate : TriggeredOutputs(query, input)) {
    if (LocalContextEqual(candidate, output)) {
      return true;
    }
  }
  return false;
}

std::vector<LocalContext> MatchedOutputs(
    const ExtendedBooleanQuery& query,
    const std::shared_ptr<const BooleanExpr>& clock,
    const LocalContext& input) {
  std::vector<LocalContext> result;
  if (query.j >= query.word.size()) {
    return result;  // §F.6.1 requires 0 <= j < |w|.
  }
  const std::shared_ptr<const SequenceExpr> kGotoOnce = GotoOnce(clock);
  // §F.6.1: try every earlier trigger point 0 <= i < j. The clock c must tick
  // exactly once over the gap w^{i+1,j}; that gap is independent of the output
  // context, so it is checked once per i.
  for (std::size_t i = 0; i < query.j; ++i) {
    const Word kGap = Subword(query.word, i + 1, query.j + 1);
    if (!TightlySatisfiesWithLocals(kGap, *kGotoOnce, LocalContext{},
                                    LocalContext{})) {
      continue;
    }
    const ExtendedBooleanQuery kTriggerQuery{query.word, i, query.sequence,
                                             query.actuals};
    for (LocalContext out : TriggeredOutputs(kTriggerQuery, input)) {
      AddUnique(result, std::move(out));
    }
  }
  return result;
}

bool MatchedSatisfies(const ExtendedBooleanQuery& query,
                      const std::shared_ptr<const BooleanExpr>& clock,
                      const LocalContext& input, const LocalContext& output) {
  for (const LocalContext& candidate : MatchedOutputs(query, clock, input)) {
    if (LocalContextEqual(candidate, output)) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
