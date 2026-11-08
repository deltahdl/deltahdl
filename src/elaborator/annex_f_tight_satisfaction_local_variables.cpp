#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

#include <cstddef>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_local_variable_flow.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {

std::set<std::string> ContextDomain(const LocalContext& context) {
  std::set<std::string> names;
  for (const auto& entry : context) {
    names.insert(entry.first);
  }
  return names;
}

LocalContext RestrictContext(const LocalContext& context,
                             const std::set<std::string>& domain) {
  LocalContext result;
  for (const auto& entry : context) {
    if (domain.count(entry.first) != 0) {
      result.insert(entry);
    }
  }
  return result;
}

LocalContext RemoveName(const LocalContext& context, const std::string& name) {
  LocalContext result = context;
  result.erase(name);
  return result;
}

LocalContext RestrictToName(const LocalContext& context,
                            const std::string& name) {
  LocalContext result;
  auto it = context.find(name);
  if (it != context.end()) {
    result.insert(*it);
  }
  return result;
}

bool LetterEqual(const Letter& lhs, const Letter& rhs) {
  if (lhs.kind != rhs.kind) {
    return false;
  }
  if (lhs.kind == Letter::Kind::kAtomSet) {
    return lhs.atoms == rhs.atoms;
  }
  return true;
}

bool LocalContextEqual(const LocalContext& lhs, const LocalContext& rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (const auto& entry : lhs) {
    auto it = rhs.find(entry.first);
    if (it == rhs.end() || !LetterEqual(entry.second, it->second)) {
      return false;
    }
  }
  return true;
}

namespace {

void AddUnique(std::vector<LocalContext>& out, LocalContext context) {
  for (const LocalContext& existing : out) {
    if (LocalContextEqual(existing, context)) {
      return;
    }
  }
  out.push_back(std::move(context));
}

void AppendUniqueBranches(std::vector<LocalContext>& out,
                          std::vector<LocalContext> branches) {
  for (LocalContext& branch : branches) {
    AddUnique(out, std::move(branch));
  }
}

bool MergeContexts(const LocalContext& a, const LocalContext& b,
                   LocalContext& out) {
  out = a;
  for (const auto& entry : b) {
    auto it = out.find(entry.first);
    if (it == out.end()) {
      out.insert(entry);
    } else if (!LetterEqual(it->second, entry.second)) {
      return false;
    }
  }
  return true;
}

std::vector<LocalContext> OutputsForSlice(const Word& word, std::size_t lo,
                                          std::size_t hi,
                                          const SequenceExpr& seq,
                                          const LocalContext& input);

std::vector<LocalContext> OutputsForBoolean(const Word& word, std::size_t lo,
                                            std::size_t length,
                                            const SequenceExpr& seq,
                                            const LocalContext& input) {
  std::vector<LocalContext> result;
  if (length == 1 && LetterSatisfiesBoolean(word[lo], *seq.boolean)) {
    result.push_back(input);
  }
  return result;
}

std::vector<LocalContext> OutputsForLocalVarSampling(
    const Word& word, std::size_t lo, std::size_t length,
    const SequenceExpr& seq, const LocalContext& input) {
  std::vector<LocalContext> result;
  if (length == 1) {
    LocalContext out = RemoveName(input, seq.local_var_name);
    out[seq.local_var_name] = word[lo];
    result.push_back(std::move(out));
  }
  return result;
}

std::vector<LocalContext> OutputsForLocalVarDecl(const Word& word,
                                                 std::size_t lo, std::size_t hi,
                                                 const SequenceExpr& seq,
                                                 const LocalContext& input) {
  std::vector<LocalContext> result;
  const std::string& v = seq.local_var_name;
  const LocalContext kOuterV = RestrictToName(input, v);
  const LocalContext kBodyInput = RemoveName(input, v);
  for (const LocalContext& inner :
       OutputsForSlice(word, lo, hi, *seq.lhs, kBodyInput)) {
    LocalContext out = RemoveName(inner, v);
    for (const auto& entry : kOuterV) {
      out.insert(entry);
    }
    AddUnique(result, std::move(out));
  }
  return result;
}

std::vector<LocalContext> OutputsForConcat(const Word& word, std::size_t lo,
                                           std::size_t hi,
                                           const SequenceExpr& seq,
                                           const LocalContext& input) {
  std::vector<LocalContext> result;
  for (std::size_t mid = lo; mid <= hi; ++mid) {
    for (const LocalContext& mid_ctx :
         OutputsForSlice(word, lo, mid, *seq.lhs, input)) {
      for (LocalContext out :
           OutputsForSlice(word, mid, hi, *seq.rhs, mid_ctx)) {
        AddUnique(result, std::move(out));
      }
    }
  }
  return result;
}

std::vector<LocalContext> OutputsForFusion(const Word& word, std::size_t lo,
                                           std::size_t hi,
                                           const SequenceExpr& seq,
                                           const LocalContext& input) {
  std::vector<LocalContext> result;
  for (std::size_t p = lo; p < hi; ++p) {
    for (const LocalContext& mid_ctx :
         OutputsForSlice(word, lo, p + 1, *seq.lhs, input)) {
      for (LocalContext out : OutputsForSlice(word, p, hi, *seq.rhs, mid_ctx)) {
        AddUnique(result, std::move(out));
      }
    }
  }
  return result;
}

std::vector<LocalContext> OutputsForOr(const Word& word, std::size_t lo,
                                       std::size_t hi, const SequenceExpr& seq,
                                       const LocalContext& input) {
  std::vector<LocalContext> result;
  const std::set<std::string> kDomain = FlowLocals(ContextDomain(input), seq);
  std::vector<LocalContext> branch =
      OutputsForSlice(word, lo, hi, *seq.lhs, input);
  for (LocalContext out : OutputsForSlice(word, lo, hi, *seq.rhs, input)) {
    branch.push_back(std::move(out));
  }
  for (const LocalContext& candidate : branch) {
    AddUnique(result, RestrictContext(candidate, kDomain));
  }
  return result;
}

std::set<std::string> IntersectOutputDomain(
    const std::set<std::string>& in_domain, const SequenceExpr& operand,
    const std::set<std::string>& blocked,
    const std::set<std::string>& sibling_sample) {
  std::set<std::string> domain;
  for (const std::string& name : FlowLocals(in_domain, operand)) {
    if (blocked.count(name) == 0 && sibling_sample.count(name) == 0) {
      domain.insert(name);
    }
  }
  return domain;
}

std::vector<LocalContext> OutputsForIntersect(const Word& word, std::size_t lo,
                                              std::size_t hi,
                                              const SequenceExpr& seq,
                                              const LocalContext& input) {
  std::vector<LocalContext> result;
  const std::set<std::string> kInDomain = ContextDomain(input);
  const std::set<std::string> kBlocked = BlockLocals(seq);
  const std::set<std::string> kSampleLhs = SampleLocals(*seq.lhs);
  const std::set<std::string> kSampleRhs = SampleLocals(*seq.rhs);
  const std::set<std::string> kDLhs =
      IntersectOutputDomain(kInDomain, *seq.lhs, kBlocked, kSampleRhs);
  const std::set<std::string> kDRhs =
      IntersectOutputDomain(kInDomain, *seq.rhs, kBlocked, kSampleLhs);
  for (const LocalContext& lhs_ctx :
       OutputsForSlice(word, lo, hi, *seq.lhs, input)) {
    for (const LocalContext& rhs_ctx :
         OutputsForSlice(word, lo, hi, *seq.rhs, input)) {
      LocalContext merged;
      if (MergeContexts(RestrictContext(lhs_ctx, kDLhs),
                        RestrictContext(rhs_ctx, kDRhs), merged)) {
        AddUnique(result, std::move(merged));
      }
    }
  }
  return result;
}

std::vector<LocalContext> OutputsForFirstMatch(const Word& word, std::size_t lo,
                                               std::size_t hi,
                                               const SequenceExpr& seq,
                                               const LocalContext& input) {
  for (std::size_t mid = lo; mid < hi; ++mid) {
    if (!OutputsForSlice(word, lo, mid, *seq.lhs, input).empty()) {
      return std::vector<LocalContext>{};
    }
  }
  return OutputsForSlice(word, lo, hi, *seq.lhs, input);
}

std::vector<LocalContext> OutputsForUnboundedRepeat(const Word& word,
                                                    std::size_t lo,
                                                    std::size_t hi,
                                                    const SequenceExpr& seq,
                                                    const LocalContext& input) {
  std::vector<LocalContext> result;
  AppendUniqueBranches(result, OutputsForSlice(word, lo, hi, *seq.lhs, input));
  for (std::size_t mid = lo + 1; mid < hi; ++mid) {
    for (const LocalContext& mid_ctx :
         OutputsForSlice(word, lo, mid, *seq.lhs, input)) {
      for (LocalContext out : OutputsForSlice(word, mid, hi, seq, mid_ctx)) {
        AddUnique(result, std::move(out));
      }
    }
  }
  return result;
}

std::vector<LocalContext> OutputsForSlice(const Word& word, std::size_t lo,
                                          std::size_t hi,
                                          const SequenceExpr& seq,
                                          const LocalContext& input) {
  const std::size_t kLength = hi - lo;
  std::vector<LocalContext> result;
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean:
      return OutputsForBoolean(word, lo, kLength, seq, input);
    case SequenceExpr::Kind::kLocalVarSampling:
      return OutputsForLocalVarSampling(word, lo, kLength, seq, input);
    case SequenceExpr::Kind::kLocalVarDecl:
      return OutputsForLocalVarDecl(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kParen:
      return OutputsForSlice(word, lo, hi, *seq.lhs, input);
    case SequenceExpr::Kind::kConcat:
      return OutputsForConcat(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kFusion:
      return OutputsForFusion(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kOr:
      return OutputsForOr(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kIntersect:
      return OutputsForIntersect(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kFirstMatch:
      return OutputsForFirstMatch(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kNullRepeat: {
      if (kLength == 0) {
        result.push_back(input);
      }
      return result;
    }
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      if (kLength == 0) {
        result.push_back(input);
        return result;
      }
      [[fallthrough]];
    case SequenceExpr::Kind::kUnboundedRepeat:
      return OutputsForUnboundedRepeat(word, lo, hi, seq, input);
    case SequenceExpr::Kind::kClock:
      return result;
  }
  return result;
}

}  // namespace

std::vector<LocalContext> TightSatisfactionOutputs(const Word& word,
                                                   const SequenceExpr& sequence,
                                                   const LocalContext& input) {
  if (ContainsClock(sequence)) {
    auto unclocked = RewriteClockedSequence(sequence);
    return OutputsForSlice(word, 0, word.size(), *unclocked, input);
  }
  return OutputsForSlice(word, 0, word.size(), sequence, input);
}

bool TightlySatisfiesWithLocals(const Word& word, const SequenceExpr& sequence,
                                const LocalContext& input,
                                const LocalContext& output) {
  for (const LocalContext& candidate :
       TightSatisfactionOutputs(word, sequence, input)) {
    if (LocalContextEqual(candidate, output)) {
      return true;
    }
  }
  return false;
}

bool IsNondegenerateSequenceWithLocals(const SequenceExpr& sequence) {
  return IsNondegenerateSequenceImpl(
      sequence,
      [](const Word& word, std::size_t length, const SequenceExpr& seq) {
        return !OutputsForSlice(word, 0, length, seq, LocalContext{}).empty();
      });
}

}  // namespace delta
