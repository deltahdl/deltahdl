#pragma once

// §18.17.7's implicit variables, shared by the two files that answer for them.
//
// A randsequence production may return a value, and a rule that names such a
// production declares an implicit variable to hold what it returned. These two
// types say which productions a rule names and which appearance a generation is
// filling. src/simulator/stmt_exec_randsequence_values.cpp computes them and
// src/simulator/stmt_exec_randsequence.cpp generates against them, so neither
// file owns them and both need the definitions complete: a function passing one
// across the two translation units cannot take it by an incomplete type, and a
// definition written twice is one a later change makes disagree.

#include <string_view>
#include <unordered_map>

namespace delta {

struct RsProductionItem;

// §18.17.7: the implicit variables one rule declares for the value-returning
// productions it names. `total` holds how many times the rule names each such
// production, which decides whether its implicit variable is the scalar named
// after the production or an element of an array indexed 1..N, and `ordinal`
// gives each appearance its 1-based index in that array. The index is fixed by
// where the appearance is written and not by when it generates: §18.17.7 says
// of `if (cond) D(5) else D(20)` that the first element takes D(5)'s value and
// the second D(20)'s, so the else branch writes the second element even when it
// is the only branch that generated.
struct RuleValueCapture {
  std::unordered_map<std::string_view, int> total;
  std::unordered_map<const RsProductionItem*, int> ordinal;
};

// §18.17.7: one appearance of a value-returning production within a rule. name
// is the production's name, idx the 1-based ordinal of this appearance, and
// total how many times the rule names the production: a total above one means
// the implicit variable is the idx-th element of a 1..N array, a total of one
// means the scalar named after the production. An idx of zero means the rule
// declares no implicit variable for this generation.
struct RuleProductionSlot {
  std::string_view name;
  int idx;
  int total;
};

}  // namespace delta
