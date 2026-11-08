#include "elaborator/annex_f_past.h"

#include <cstddef>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

namespace {

Word Subword(const Word& word, std::size_t lo, std::size_t hi) {
  return Word(word.begin() + static_cast<std::ptrdiff_t>(lo),
              word.begin() + static_cast<std::ptrdiff_t>(hi));
}

std::shared_ptr<const SequenceExpr> GatingSequence(
    const std::shared_ptr<const BooleanExpr>& g, unsigned int n) {
  const std::shared_ptr<const SequenceExpr> kActive = SeqBoolean(g);
  const std::shared_ptr<const SequenceExpr> kInactiveRun =
      SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(g)));

  std::shared_ptr<const SequenceExpr> nonconsecutive = kInactiveRun;
  const unsigned int kRepeats = n - 1;
  if (kRepeats > 0) {
    const std::shared_ptr<const SequenceExpr> kGotoUnit =
        SeqConcat(kInactiveRun, kActive);
    std::shared_ptr<const SequenceExpr> goto_m = kGotoUnit;
    for (unsigned int k = 1; k < kRepeats; ++k) {
      goto_m = SeqConcat(goto_m, kGotoUnit);
    }
    nonconsecutive = SeqConcat(goto_m, kInactiveRun);
  }

  return SeqConcat(kActive, SeqConcat(nonconsecutive, SeqBoolean(BoolTrue())));
}

}  // namespace

std::vector<std::size_t> PastSourceIndices(
    const Word& word, std::size_t j, unsigned int n,
    const std::shared_ptr<const BooleanExpr>& gate,
    const std::shared_ptr<const BooleanExpr>& clock) {
  std::vector<std::size_t> result;
  if (j >= word.size()) {
    return result;
  }
  if (n < 1) {
    return result;
  }
  const std::shared_ptr<const BooleanExpr> kActive = BoolAnd(clock, gate);
  const std::shared_ptr<const SequenceExpr> kGating =
      GatingSequence(kActive, n);
  for (std::size_t i = 0; i < j; ++i) {
    const Word kSlice = Subword(word, i, j + 1);
    if (TightlySatisfies(kSlice, *kGating)) {
      result.push_back(i);
    }
  }
  return result;
}

bool PastSamplesInitialValue(const Word& word, std::size_t j, unsigned int n,
                             const std::shared_ptr<const BooleanExpr>& gate,
                             const std::shared_ptr<const BooleanExpr>& clock) {
  if (j >= word.size() || n < 1) {
    return false;
  }
  return PastSourceIndices(word, j, n, gate, clock).empty();
}

std::optional<std::size_t> PastGclkSourceIndex(const Word& word,
                                               std::size_t j) {
  if (j >= word.size()) {
    return std::nullopt;
  }
  if (j == 0) {
    return std::nullopt;
  }
  return j - 1;
}

bool PastInitialValue(VariableKind kind,
                      std::optional<bool> declaration_assignment,
                      bool type_default) {
  if (kind == VariableKind::kStatic && declaration_assignment) {
    return *declaration_assignment;
  }
  return type_default;
}

ExtendedExpression PastOfAtom(const std::string& name, unsigned int n,
                              std::shared_ptr<const BooleanExpr> gate,
                              std::shared_ptr<const BooleanExpr> clock,
                              bool initial) {
  return [name, n, gate = std::move(gate), clock = std::move(clock), initial](
             const Word& word, std::size_t j) -> std::optional<bool> {
    if (j >= word.size() || n == 0) {
      return std::nullopt;
    }
    const std::vector<std::size_t> kSources =
        PastSourceIndices(word, j, n, gate, clock);
    if (kSources.empty()) {
      return initial;
    }
    return LetterSatisfiesBoolean(word[kSources.front()], *BoolAtom(name));
  };
}

ExtendedExpression PastOfAtom(const std::string& name, bool initial) {
  return PastOfAtom(name, 1, BoolTrue(), BoolTrue(), initial);
}

}  // namespace delta
