#include "elaborator/annex_f_tight_satisfaction.h"

#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {

Letter LetterTop() { return Letter{Letter::Kind::kTop, {}}; }

Letter LetterBottom() { return Letter{Letter::Kind::kBottom, {}}; }

Letter LetterAtoms(std::set<std::string> atoms) {
  return Letter{Letter::Kind::kAtomSet, std::move(atoms)};
}

namespace {

// §F.5: for a letter in 2^P, a Boolean expression holds when its proposition
// structure evaluates to true under the set of true propositions.
bool AtomSetSatisfies(const std::set<std::string>& atoms,
                      const BooleanExpr& b) {
  switch (b.kind) {
    case BooleanExpr::Kind::kTrue:
      return true;
    case BooleanExpr::Kind::kAtom:
      return atoms.count(b.atom) != 0;
    case BooleanExpr::Kind::kNot:
      return !AtomSetSatisfies(atoms, *b.operand_a);
    case BooleanExpr::Kind::kAnd:
      return AtomSetSatisfies(atoms, *b.operand_a) &&
             AtomSetSatisfies(atoms, *b.operand_b);
  }
  return false;
}

// Tight satisfaction over the half-open slice [lo, hi) of `word`. The slice
// representation lets the recursive cases split a word without copying.
bool TightSlice(const Word& word, std::size_t lo, std::size_t hi,
                const SequenceExpr& seq) {
  const std::size_t length = hi - lo;
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean:
      // §F.5.2: w |== b iff |w| = 1 and w^0 |= b.
      return length == 1 && LetterSatisfiesBoolean(word[lo], *seq.boolean);
    case SequenceExpr::Kind::kParen:
      // §F.5.2: w |== (R) iff w |== R.
      return TightSlice(word, lo, hi, *seq.lhs);
    case SequenceExpr::Kind::kConcat:
      // §F.5.2: w |== (R1 ##1 R2) iff w = xy with x |== R1 and y |== R2.
      for (std::size_t mid = lo; mid <= hi; ++mid) {
        if (TightSlice(word, lo, mid, *seq.lhs) &&
            TightSlice(word, mid, hi, *seq.rhs)) {
          return true;
        }
      }
      return false;
    case SequenceExpr::Kind::kFusion:
      // §F.5.2: w |== (R1 ##0 R2) iff w = xyz with |y| = 1, xy |== R1 and
      // yz |== R2. The single overlap letter y sits at position `p`.
      for (std::size_t p = lo; p < hi; ++p) {
        if (TightSlice(word, lo, p + 1, *seq.lhs) &&
            TightSlice(word, p, hi, *seq.rhs)) {
          return true;
        }
      }
      return false;
    case SequenceExpr::Kind::kOr:
      // §F.5.2: w |== (R1 or R2) iff w |== R1 or w |== R2.
      return TightSlice(word, lo, hi, *seq.lhs) ||
             TightSlice(word, lo, hi, *seq.rhs);
    case SequenceExpr::Kind::kIntersect:
      // §F.5.2: w |== (R1 intersect R2) iff w |== R1 and w |== R2.
      return TightSlice(word, lo, hi, *seq.lhs) &&
             TightSlice(word, lo, hi, *seq.rhs);
    case SequenceExpr::Kind::kFirstMatch: {
      // §F.5.2: w |== first_match(R) iff w |== R and every prefix x with
      // x |== R is all of w (no shorter match exists).
      if (!TightSlice(word, lo, hi, *seq.lhs)) {
        return false;
      }
      for (std::size_t mid = lo; mid < hi; ++mid) {
        if (TightSlice(word, lo, mid, *seq.lhs)) {
          return false;
        }
      }
      return true;
    }
    case SequenceExpr::Kind::kNullRepeat:
      // §F.5.2: w |== R[*0] iff |w| = 0.
      return length == 0;
    case SequenceExpr::Kind::kUnboundedRepeat: {
      // §F.5.2: w |== R[*1:$] iff w = w1 w2 ... wj (j >= 1) with each wi |== R.
      if (TightSlice(word, lo, hi, *seq.lhs)) {
        return true;
      }
      for (std::size_t mid = lo + 1; mid < hi; ++mid) {
        if (TightSlice(word, lo, mid, *seq.lhs) &&
            TightSlice(word, mid, hi, seq)) {
          return true;
        }
      }
      return false;
    }
    case SequenceExpr::Kind::kZeroOrMoreRepeat: {
      // [*0:$], produced by the §F.5.1.1 rewrite: zero pieces match the empty
      // word, otherwise it behaves like [*1:$].
      if (length == 0) {
        return true;
      }
      if (TightSlice(word, lo, hi, *seq.lhs)) {
        return true;
      }
      for (std::size_t mid = lo + 1; mid < hi; ++mid) {
        if (TightSlice(word, lo, mid, *seq.lhs) &&
            TightSlice(word, mid, hi, seq)) {
          return true;
        }
      }
      return false;
    }
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kLocalVarDecl:
    case SequenceExpr::Kind::kLocalVarSampling:
      // §F.5.2 defines tight satisfaction for unclocked sequences without
      // local variables; clocks are removed before evaluation and the
      // local-variable forms are out of scope here.
      return false;
  }
  return false;
}

}  // namespace

bool LetterSatisfiesBoolean(const Letter& letter, const BooleanExpr& b) {
  switch (letter.kind) {
    case Letter::Kind::kTop:
      return true;
    case Letter::Kind::kBottom:
      return false;
    case Letter::Kind::kAtomSet:
      return AtomSetSatisfies(letter.atoms, b);
  }
  return false;
}

bool TightlySatisfies(const Word& word, const SequenceExpr& sequence) {
  if (ContainsClock(sequence)) {
    auto unclocked = RewriteClockedSequence(sequence);
    return TightSlice(word, 0, word.size(), *unclocked);
  }
  return TightSlice(word, 0, word.size(), sequence);
}

bool TightlySatisfiedByEmptyWord(const SequenceExpr& sequence) {
  return TightlySatisfies(Word{}, sequence);
}

bool IsNondegenerateSequence(const SequenceExpr& sequence) {
  return IsNondegenerateSequenceImpl(
      sequence,
      [](const Word& word, std::size_t length, const SequenceExpr& seq) {
        return TightSlice(word, 0, length, seq);
      });
}

}  // namespace delta
