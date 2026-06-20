#pragma once

#include <optional>
#include <string_view>

namespace delta {

// §F.3.3 fixes the metavariable conventions used throughout the rest of
// Annex F. Each lowercase/uppercase letter denotes a fixed category of
// abstract-syntax object; subscripted forms of a letter share its
// category; and the conventions hold annex-wide unless a later passage
// overrides them. This model records the mapping so passes that consume
// Annex F notation can resolve a symbol to the category it stands for.

// The categories a §F.3.3 metavariable can denote.
enum class NotationCategory {
  kBooleanExpression,           // b, c
  kType,                        // t
  kLocalVariableName,           // v
  kFreeCheckerVariableName,     // u
  kExpression,                  // e
  kUnclockedSequence,           // uppercase R
  kClockedSequence,             // uppercase S
  kUnclockedProperty,           // uppercase P
  kClockedProperty,             // uppercase Q
  kUnclockedTopLevelProperty,   // uppercase T
  kClockedTopLevelProperty,     // uppercase U
  kSequence,                    // lowercase r, s: clocked or unclocked
  kProperty,                    // lowercase p, q: clocked/unclocked,
                                // top-level or not
  kAssertion,                   // uppercase A
  kNonNegativeIntegerConstant,  // i, j, k, m, n
};

// Resolve an Annex F metavariable to the category §F.3.3 assigns it.
// A trailing subscript (e.g. b1, R_2) is stripped first, since §F.3.3
// states the conventions cover subscripted versions of each notation.
// Lookup is case-sensitive: §F.3.3 distinguishes, e.g., uppercase R (an
// unclocked sequence) from lowercase r (a sequence of either flavor), and
// t (a type) from T (an unclocked top-level property). A symbol that
// §F.3.3 gives no convention yields no category.
std::optional<NotationCategory> ClassifyAnnexFNotation(std::string_view symbol);

// True when the category names some flavor of sequence (unclocked,
// clocked, or the either-flavor lowercase form).
bool DenotesSequence(NotationCategory category);

// True when the category names some flavor of property (unclocked,
// clocked, top-level of either clock, or the unrestricted lowercase form).
bool DenotesProperty(NotationCategory category);

}  // namespace delta
