#pragma once

#include <string>

// A reserved-word sweep puts each word of a keyword table into an identifier
// slot and checks that the source is rejected. Two small groups of words
// cannot be driven that way at every stage, because the slot they land in is
// read as the opening of a construct rather than as a name, and the parser
// mis-reads it identically with no `begin_keywords region in force at all --
// so the fault is not the keyword list's. A sweep skips them and says which
// stage carries them instead.

// Six of Table 22-1's entries name a gate primitive whose keyword may open a
// gate instantiation with no leading type, so a declaration whose identifier
// slot holds one is read as a malformed instantiation. The elaborator cannot
// be driven through that; the parser stage rejects the same source without
// incident and sweeps these six there.
inline bool IsGatePrimitiveWord(const std::string& word) {
  return word == "and" || word == "nand" || word == "nor" || word == "or" ||
         word == "xnor" || word == "xor";
}

// Two of Table 22-4's entries open an aggregate type declaration, so a
// declaration whose identifier slot holds one is read as the start of such a
// type and the parse does not come back. Neither the parser nor the elaborator
// can be driven through that; the lexer and preprocessor stages observe the
// reserved word list without parsing and sweep these two there.
inline bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}
