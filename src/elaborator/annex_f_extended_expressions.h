#pragma once

#include <cstddef>
#include <functional>
#include <optional>
#include <string>
#include <vector>

#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.6 is the heading under which the extended Booleans (§F.6.1), the past
// expressions (§F.6.2) and the future expression (§F.6.3) are defined, and
// its opening paragraph fixes what the three share: each is a construct used
// like an expression whose meaning at a point of a word may depend both on
// the letter at that point and on other letters of the word, and each is
// written e[w^j], by an abuse of notation the subclause owns to, so that the
// definitions of the preceding subclauses, which read a Boolean at a letter
// alone, can be used together with them. This file models that: an extended
// expression as a meaning at a point read from the whole word, the reading of
// such an expression into the letters of a word as an atom the relations of
// §F.5 then read at each letter alone, and the dependence on other letters
// that sets an extended expression apart from a Boolean.

// §F.6: an extended expression, e[w^j] for the word w and the point j; empty
// where the subclauses leave the value undefined, as §F.6.3 does at the last
// letter of a finite word.
using ExtendedExpression =
    std::function<std::optional<bool>(const Word& word, std::size_t j)>;

// A Boolean atom read as an extended expression: its meaning at a point is
// the letter there alone, T satisfying it and _|_ not.
ExtendedExpression AtomAsExtendedExpression(const std::string& name);

// §F.6.2: $past_gclk(e)[w^j] for e the atom named, which is e[w^{j-1}] at
// j > 0 and the initial value given at w^0.
ExtendedExpression PastGclkOfAtom(const std::string& name, bool initial);

// §F.6.3: $future_gclk(e)[w^j] for e the atom named, which is e[w^{j+1}]
// where a following letter exists and undefined at the last letter of a
// finite word.
ExtendedExpression FutureGclkOfAtom(const std::string& name);

// §F.6: the combination with the preceding subclauses. Their relations read a
// letter alone, so an extended expression is read into the letters: the word
// w in which the atom named is present at each point j at which e[w^j] holds
// and absent at each at which it does not, a letter at which e is undefined,
// and the letters T and _|_, which satisfy every Boolean and none, kept as
// they are.
Word WordWithExtendedAtom(const Word& word, const std::string& name,
                          const ExtendedExpression& e);

// §F.6: whether the meaning of e at the point j of w depends on a letter
// other than the one there, shown by the words given: true iff some word
// among them carries the same letter at j as w and gives e a different value
// there. A word that differs from w at j shows nothing and is passed over.
bool DependsOnOtherLetters(const ExtendedExpression& e, const Word& word,
                           std::size_t j, const std::vector<Word>& others);

}  // namespace delta
