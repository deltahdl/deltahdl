#include "elaborator/annex_f_tight_satisfaction.h"

#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"

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

void CollectAtoms(const BooleanExpr& b, std::set<std::string>& out) {
  switch (b.kind) {
    case BooleanExpr::Kind::kTrue:
      return;
    case BooleanExpr::Kind::kAtom:
      out.insert(b.atom);
      return;
    case BooleanExpr::Kind::kNot:
      CollectAtoms(*b.operand_a, out);
      return;
    case BooleanExpr::Kind::kAnd:
      CollectAtoms(*b.operand_a, out);
      CollectAtoms(*b.operand_b, out);
      return;
  }
}

void CollectSequenceAtoms(const SequenceExpr& seq, std::set<std::string>& out,
                          std::size_t& leaf_count) {
  if (seq.kind == SequenceExpr::Kind::kBoolean && seq.boolean != nullptr) {
    CollectAtoms(*seq.boolean, out);
    ++leaf_count;
  }
  if (seq.kind == SequenceExpr::Kind::kClock && seq.boolean != nullptr) {
    CollectAtoms(*seq.boolean, out);
  }
  if (seq.kind == SequenceExpr::Kind::kLocalVarSampling) {
    ++leaf_count;
  }
  if (seq.lhs != nullptr) {
    CollectSequenceAtoms(*seq.lhs, out, leaf_count);
  }
  if (seq.rhs != nullptr) {
    CollectSequenceAtoms(*seq.rhs, out, leaf_count);
  }
}

// Build the candidate alphabet for the witness search: T, _|_, and every
// subset of the mentioned atoms. The subset enumeration is capped so the
// search stays finite; that is ample for the sequences this model evaluates.
std::vector<Letter> CandidateAlphabet(const std::set<std::string>& atoms) {
  std::vector<Letter> letters{LetterTop(), LetterBottom()};
  std::vector<std::string> names(atoms.begin(), atoms.end());
  if (names.size() > 6) {
    return letters;
  }
  const std::size_t subset_count = std::size_t{1} << names.size();
  for (std::size_t mask = 0; mask < subset_count; ++mask) {
    std::set<std::string> subset;
    for (std::size_t i = 0; i < names.size(); ++i) {
      if ((mask & (std::size_t{1} << i)) != 0) {
        subset.insert(names[i]);
      }
    }
    letters.push_back(LetterAtoms(std::move(subset)));
  }
  return letters;
}

bool SomeWordOfLengthSatisfies(const std::vector<Letter>& alphabet,
                               std::size_t length, const SequenceExpr& seq) {
  const std::size_t base = alphabet.size();
  std::size_t total = 1;
  for (std::size_t i = 0; i < length; ++i) {
    total *= base;
  }
  for (std::size_t code = 0; code < total; ++code) {
    Word word(length);
    std::size_t rest = code;
    for (std::size_t pos = 0; pos < length; ++pos) {
      word[pos] = alphabet[rest % base];
      rest /= base;
    }
    if (TightSlice(word, 0, length, seq)) {
      return true;
    }
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
  std::shared_ptr<const SequenceExpr> owner;
  const SequenceExpr* target = &sequence;
  if (ContainsClock(sequence)) {
    owner = RewriteClockedSequence(sequence);
    target = owner.get();
  }

  std::set<std::string> atoms;
  std::size_t leaf_count = 0;
  CollectSequenceAtoms(*target, atoms, leaf_count);

  const std::vector<Letter> alphabet = CandidateAlphabet(atoms);
  const std::size_t max_length = leaf_count + 2;
  for (std::size_t length = 1; length <= max_length; ++length) {
    if (SomeWordOfLengthSatisfies(alphabet, length, *target)) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
