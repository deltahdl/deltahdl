#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

#include <cstddef>
#include <memory>
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

// Append `context` to `out` unless an equal context is already present, so the
// nondeterministic relation never reports a duplicate witness.
void AddUnique(std::vector<LocalContext>& out, LocalContext context) {
  for (const LocalContext& existing : out) {
    if (LocalContextEqual(existing, context)) {
      return;
    }
  }
  out.push_back(std::move(context));
}

// AddUnique each of `branches` into `out`. Used by the repeat rules to fold a
// single-piece (j = 1) match into the result before peeling longer chains.
void AppendUniqueBranches(std::vector<LocalContext>& out,
                          std::vector<LocalContext> branches) {
  for (LocalContext& branch : branches) {
    AddUnique(out, std::move(branch));
  }
}

// §F.5.5: the union L'|_D' U L''|_D'' used by the intersect rule. The remark in
// §F.5.5 proves the union is a function; should the operands disagree on a
// shared name the merge is rejected (it cannot arise for a well-formed model)
// by returning false.
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

// §F.5.5: the set of output contexts L_1 such that w[lo,hi), L_0, L_1 |== seq,
// where the half-open slice [lo, hi) of `word` plays the role of w. The slice
// representation lets the recursive cases split a word without copying.
std::vector<LocalContext> OutputsForSlice(const Word& word, std::size_t lo,
                                          std::size_t hi,
                                          const SequenceExpr& seq,
                                          const LocalContext& input) {
  const std::size_t length = hi - lo;
  std::vector<LocalContext> result;
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean: {
      // §F.5.5: w, L_0, L_1 |== b iff |w| = 1 and w^0 |= b[L_0] and L_1 = L_0.
      // Boolean leaves model atomic propositions rather than local-variable
      // expressions, so b[L_0] is b; the context passes through unchanged.
      if (length == 1 && LetterSatisfiesBoolean(word[lo], *seq.boolean)) {
        result.push_back(input);
      }
      return result;
    }
    case SequenceExpr::Kind::kLocalVarSampling: {
      // §F.5.5: w, L_0, L_1 |== (1, v = e) iff |w| = 1 and w^0 |= 1 and
      // L_1 = {(v, e[L_0, w^0])} U L_0\v. The "1" Boolean always holds; the
      // assigned value is the observed letter, the realization of e[L_0, w^0].
      if (length == 1) {
        LocalContext out = RemoveName(input, seq.local_var_name);
        out[seq.local_var_name] = word[lo];
        result.push_back(std::move(out));
      }
      return result;
    }
    case SequenceExpr::Kind::kLocalVarDecl: {
      // §F.5.5: w, L_0, L_1 |== (t v; R) iff there exists L with
      // w, L_0\v, L |== R and L_1 = L_0[v] U (L\v). The declared name is hidden
      // from the body and its outer binding, if any, is restored afterwards.
      const std::string& v = seq.local_var_name;
      const LocalContext outer_v = RestrictToName(input, v);
      const LocalContext body_input = RemoveName(input, v);
      for (LocalContext inner :
           OutputsForSlice(word, lo, hi, *seq.lhs, body_input)) {
        LocalContext out = RemoveName(inner, v);
        for (const auto& entry : outer_v) {
          out.insert(entry);
        }
        AddUnique(result, std::move(out));
      }
      return result;
    }
    case SequenceExpr::Kind::kParen:
      // §F.5.5: w, L_0, L_1 |== (R) iff w, L_0, L_1 |== R.
      return OutputsForSlice(word, lo, hi, *seq.lhs, input);
    case SequenceExpr::Kind::kConcat: {
      // §F.5.5: w, L_0, L_1 |== (R1 ##1 R2) iff w = xy and x, L_0, L' |== R1
      // and y, L', L_1 |== R2 for some split point and intermediate context L'.
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
    case SequenceExpr::Kind::kFusion: {
      // §F.5.5: w, L_0, L_1 |== (R1 ##0 R2) iff w = xyz with |y| = 1, and
      // xy, L_0, L' |== R1 and yz, L', L_1 |== R2. The overlap letter y sits at
      // position p, so R1 covers [lo, p+1) and R2 covers [p, hi).
      for (std::size_t p = lo; p < hi; ++p) {
        for (const LocalContext& mid_ctx :
             OutputsForSlice(word, lo, p + 1, *seq.lhs, input)) {
          for (LocalContext out :
               OutputsForSlice(word, p, hi, *seq.rhs, mid_ctx)) {
            AddUnique(result, std::move(out));
          }
        }
      }
      return result;
    }
    case SequenceExpr::Kind::kOr: {
      // §F.5.5: w, L_0, L_1 |== (R1 or R2) iff some L' satisfies one operand
      // and L_1 = L'|_D with D = flow(dom(L_0), (R1 or R2)). Restricting to the
      // flow domain discards names that do not escape the chosen alternative.
      const std::set<std::string> domain =
          FlowLocals(ContextDomain(input), seq);
      std::vector<LocalContext> branch =
          OutputsForSlice(word, lo, hi, *seq.lhs, input);
      for (LocalContext out : OutputsForSlice(word, lo, hi, *seq.rhs, input)) {
        branch.push_back(std::move(out));
      }
      for (const LocalContext& candidate : branch) {
        AddUnique(result, RestrictContext(candidate, domain));
      }
      return result;
    }
    case SequenceExpr::Kind::kIntersect: {
      // §F.5.5: w, L_0, L_1 |== (R1 intersect R2) iff w, L_0, L' |== R1 and
      // w, L_0, L'' |== R2 and L_1 = L'|_D' U L''|_D'', where
      //   D'  = flow(dom(L_0), R1) - (block(R1 intersect R2) U sample(R2))
      //   D'' = flow(dom(L_0), R2) - (block(R1 intersect R2) U sample(R1))
      const std::set<std::string> in_domain = ContextDomain(input);
      const std::set<std::string> blocked = BlockLocals(seq);
      const std::set<std::string> sample_lhs = SampleLocals(*seq.lhs);
      const std::set<std::string> sample_rhs = SampleLocals(*seq.rhs);
      std::set<std::string> d_lhs;
      for (const std::string& name : FlowLocals(in_domain, *seq.lhs)) {
        if (blocked.count(name) == 0 && sample_rhs.count(name) == 0) {
          d_lhs.insert(name);
        }
      }
      std::set<std::string> d_rhs;
      for (const std::string& name : FlowLocals(in_domain, *seq.rhs)) {
        if (blocked.count(name) == 0 && sample_lhs.count(name) == 0) {
          d_rhs.insert(name);
        }
      }
      for (const LocalContext& lhs_ctx :
           OutputsForSlice(word, lo, hi, *seq.lhs, input)) {
        for (const LocalContext& rhs_ctx :
             OutputsForSlice(word, lo, hi, *seq.rhs, input)) {
          LocalContext merged;
          if (MergeContexts(RestrictContext(lhs_ctx, d_lhs),
                            RestrictContext(rhs_ctx, d_rhs), merged)) {
            AddUnique(result, std::move(merged));
          }
        }
      }
      return result;
    }
    case SequenceExpr::Kind::kFirstMatch: {
      // §F.5.5: w, L_0, L_1 |== first_match(R) iff w, L_0, L_1 |== R and no
      // proper prefix of w tightly satisfies R; a shorter match would leave a
      // nonempty remainder, which the rule forbids.
      for (std::size_t mid = lo; mid < hi; ++mid) {
        if (!OutputsForSlice(word, lo, mid, *seq.lhs, input).empty()) {
          return result;  // a proper prefix matches, so first_match yields none
        }
      }
      return OutputsForSlice(word, lo, hi, *seq.lhs, input);
    }
    case SequenceExpr::Kind::kNullRepeat: {
      // §F.5.5: w, L_0, L_1 |== R[*0] iff |w| = 0 and L_1 = L_0.
      if (length == 0) {
        result.push_back(input);
      }
      return result;
    }
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      // [*0:$], produced by the §F.5.1.1 rewrite of a Boolean: the empty word
      // leaves the context unchanged, otherwise it behaves exactly like [*1:$]
      // and shares the kUnboundedRepeat body below.
      if (length == 0) {
        result.push_back(input);
        return result;
      }
      [[fallthrough]];
    case SequenceExpr::Kind::kUnboundedRepeat: {
      // §F.5.5: w, L_0, L_1 |== R[*1:$] iff w = w1 w2 ... wj (j >= 1) and the
      // contexts chain L_0 = L_(0), ..., L_(j) = L_1 with each wi, L_(i-1),
      // L_(i) |== R. One piece covering the whole slice is the j = 1 case;
      // longer chains peel off a nonempty first piece and recurse.
      AppendUniqueBranches(result,
                           OutputsForSlice(word, lo, hi, *seq.lhs, input));
      for (std::size_t mid = lo + 1; mid < hi; ++mid) {
        for (const LocalContext& mid_ctx :
             OutputsForSlice(word, lo, mid, *seq.lhs, input)) {
          for (LocalContext out :
               OutputsForSlice(word, mid, hi, seq, mid_ctx)) {
            AddUnique(result, std::move(out));
          }
        }
      }
      return result;
    }
    case SequenceExpr::Kind::kClock:
      // Clocks are removed by the §F.5.1.1 rewrite before evaluation, so a raw
      // clock form never reaches this point and yields no output context.
      return result;
  }
  return result;
}

}  // namespace

std::vector<LocalContext> TightSatisfactionOutputs(const Word& word,
                                                   const SequenceExpr& sequence,
                                                   const LocalContext& input) {
  if (ContainsClock(sequence)) {
    // §F.5.5: w, L_0, L_1 |== S iff w, L_0, L_1 |== S', the unclocked rewrite.
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
