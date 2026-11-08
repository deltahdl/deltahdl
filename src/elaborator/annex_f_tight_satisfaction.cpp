#include "elaborator/annex_f_tight_satisfaction.h"

#include <cstddef>
#include <set>
#include <string>
#include <utility>

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

bool TightSlice(const Word& word, std::size_t lo, std::size_t hi,
                const SequenceExpr& seq);

bool TightSliceConcat(const Word& word, std::size_t lo, std::size_t hi,
                      const SequenceExpr& seq) {
  for (std::size_t mid = lo; mid <= hi; ++mid) {
    if (TightSlice(word, lo, mid, *seq.lhs) &&
        TightSlice(word, mid, hi, *seq.rhs)) {
      return true;
    }
  }
  return false;
}

bool TightSliceFusion(const Word& word, std::size_t lo, std::size_t hi,
                      const SequenceExpr& seq) {
  for (std::size_t p = lo; p < hi; ++p) {
    if (TightSlice(word, lo, p + 1, *seq.lhs) &&
        TightSlice(word, p, hi, *seq.rhs)) {
      return true;
    }
  }
  return false;
}

bool TightSliceFirstMatch(const Word& word, std::size_t lo, std::size_t hi,
                          const SequenceExpr& seq) {
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

bool TightSliceRepeatTail(const Word& word, std::size_t lo, std::size_t hi,
                          const SequenceExpr& seq) {
  if (TightSlice(word, lo, hi, *seq.lhs)) {
    return true;
  }
  for (std::size_t mid = lo + 1; mid < hi; ++mid) {
    if (TightSlice(word, lo, mid, *seq.lhs) && TightSlice(word, mid, hi, seq)) {
      return true;
    }
  }
  return false;
}

bool TightSlice(const Word& word, std::size_t lo, std::size_t hi,
                const SequenceExpr& seq) {
  const std::size_t kLength = hi - lo;
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean:
      return kLength == 1 && LetterSatisfiesBoolean(word[lo], *seq.boolean);
    case SequenceExpr::Kind::kParen:
      return TightSlice(word, lo, hi, *seq.lhs);
    case SequenceExpr::Kind::kConcat:
      return TightSliceConcat(word, lo, hi, seq);
    case SequenceExpr::Kind::kFusion:
      return TightSliceFusion(word, lo, hi, seq);
    case SequenceExpr::Kind::kOr:
      return TightSlice(word, lo, hi, *seq.lhs) ||
             TightSlice(word, lo, hi, *seq.rhs);
    case SequenceExpr::Kind::kIntersect:
      return TightSlice(word, lo, hi, *seq.lhs) &&
             TightSlice(word, lo, hi, *seq.rhs);
    case SequenceExpr::Kind::kFirstMatch:
      return TightSliceFirstMatch(word, lo, hi, seq);
    case SequenceExpr::Kind::kNullRepeat:
      return kLength == 0;
    case SequenceExpr::Kind::kUnboundedRepeat:
      return TightSliceRepeatTail(word, lo, hi, seq);
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      return kLength == 0 || TightSliceRepeatTail(word, lo, hi, seq);
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kLocalVarDecl:
    case SequenceExpr::Kind::kLocalVarSampling:
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
