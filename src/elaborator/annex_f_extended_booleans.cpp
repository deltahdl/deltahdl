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

}  // namespace

std::vector<LocalContext> TriggeredOutputs(
    const Word& word, std::size_t j, const SequenceExpr& sequence,
    const std::set<std::string>& actuals, const LocalContext& input) {
  std::vector<LocalContext> result;
  if (j >= word.size()) {
    return result;  // §F.6.1 requires 0 <= j < |w|.
  }
  const std::set<std::string> in_domain = ContextDomain(input);
  // §F.6.1: try every start point 0 <= i <= j; the subword w^{i,j} must tightly
  // satisfy T from the empty context.
  for (std::size_t i = 0; i <= j; ++i) {
    const Word slice = Subword(word, i, j + 1);
    for (const LocalContext& inner :
         TightSatisfactionOutputs(slice, sequence, LocalContext{})) {
      // D = dom(L_0) - (dom(L) & V): the incoming names the call leaves intact.
      const std::set<std::string> inner_domain = ContextDomain(inner);
      std::set<std::string> overwritten;  // dom(L) & V
      for (const std::string& name : inner_domain) {
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
      // L_1 = L_0|_D U L|_V. The two domains, D and dom(L) & V, are disjoint by
      // construction, so the union is taken directly.
      LocalContext out = RestrictContext(input, d);
      for (const auto& entry : RestrictContext(inner, actuals)) {
        out.insert(entry);
      }
      AddUnique(result, std::move(out));
    }
  }
  return result;
}

bool TriggeredSatisfies(const Word& word, std::size_t j,
                        const SequenceExpr& sequence,
                        const std::set<std::string>& actuals,
                        const LocalContext& input, const LocalContext& output) {
  for (const LocalContext& candidate :
       TriggeredOutputs(word, j, sequence, actuals, input)) {
    if (LocalContextEqual(candidate, output)) {
      return true;
    }
  }
  return false;
}

std::vector<LocalContext> MatchedOutputs(
    const Word& word, std::size_t j, const SequenceExpr& sequence,
    const std::set<std::string>& actuals,
    const std::shared_ptr<const BooleanExpr>& clock, const LocalContext& input) {
  std::vector<LocalContext> result;
  if (j >= word.size()) {
    return result;  // §F.6.1 requires 0 <= j < |w|.
  }
  const std::shared_ptr<const SequenceExpr> goto_once = GotoOnce(clock);
  // §F.6.1: try every earlier trigger point 0 <= i < j. The clock c must tick
  // exactly once over the gap w^{i+1,j}; that gap is independent of the output
  // context, so it is checked once per i.
  for (std::size_t i = 0; i < j; ++i) {
    const Word gap = Subword(word, i + 1, j + 1);
    if (!TightlySatisfiesWithLocals(gap, *goto_once, LocalContext{},
                                    LocalContext{})) {
      continue;
    }
    for (LocalContext out :
         TriggeredOutputs(word, i, sequence, actuals, input)) {
      AddUnique(result, std::move(out));
    }
  }
  return result;
}

bool MatchedSatisfies(const Word& word, std::size_t j,
                      const SequenceExpr& sequence,
                      const std::set<std::string>& actuals,
                      const std::shared_ptr<const BooleanExpr>& clock,
                      const LocalContext& input, const LocalContext& output) {
  for (const LocalContext& candidate :
       MatchedOutputs(word, j, sequence, actuals, clock, input)) {
    if (LocalContextEqual(candidate, output)) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
