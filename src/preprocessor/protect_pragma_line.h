#pragma once

#include <cstddef>
#include <string_view>
#include <vector>

namespace delta {

// Reading one line of source text for the protect pragma expressions it
// carries.
//
// §22.11 spells a pragma directive and §22.5.1 spells the expressions written
// on one, so what a line says about a protected region is settled before
// anything about protected regions comes into it. That is why this is a unit of
// its own: every part of envelope processing that asks a question of a line --
// which keyword it names, what it wrote against that keyword, whether it named
// the keyword standing alone -- asks it here, and the answer is the same
// question of the directive grammar whichever subclause is doing the asking.
//
// Nothing here decides what a keyword means. The names are §34.4's and their
// definitions are §34.5's; what these functions report is which of them a line
// wrote and how.

// The text of `text` with the whitespace positioning it removed from the front,
// and from the back.
std::string_view TrimLeading(std::string_view text);
std::string_view TrimTrailing(std::string_view text);

// True when `line` is a directive naming the pragma that describes protected
// envelopes, with `*body` left holding the expression list written after the
// name. These are the only lines envelope processing reads; every other line it
// copies without asking what it says.
bool ProtectPragmaLine(std::string_view line, std::string_view* body);

// Advances past a string value, returning the index just after its closing
// quote. A quote written behind a backslash is content rather than the end.
size_t SkipStringValue(std::string_view body, size_t i);

// True when a one-line comment starts at `i`. A comment is not part of an
// expression list at all, so whatever walks one stops where a comment begins.
bool StartsLineComment(std::string_view body, size_t i);

// One keyword a directive's expression list names, and whether a pragma_value
// was written against it. §22.5.1 spells a pragma expression either way, and a
// keyword whose own definition admits one of the two spellings is read against
// this, so the walk that finds a name also records how the name was written.
//
// `value` is the text of that pragma_value as the directive wrote it, quotes
// and all, and is empty where the keyword stood alone. A keyword whose
// definition turns on what its value says -- rather than only on whether one
// was written -- is read against this.
struct ListedKeyword {
  std::string_view name;
  bool has_value;
  std::string_view value;
};

// The keywords a directive's expression list names at its own level, in
// writing order. A word inside a parenthesized value, one inside a string, and
// one standing on the right of an '=' all qualify a value rather than naming
// an expression of the list, so none of them is collected. A one-line comment
// is not part of the list at all and ends the walk.
//
// A value written in parentheses or in quotes is stepped over whole, so
// neither the '=' inside one nor the words it separates reach this level at
// all, and each '=' that does reach it belongs to a name of the list.
std::vector<ListedKeyword> TopLevelKeywords(std::string_view body);

// The pragma_value a protect pragma directive line writes against `keyword` on
// its own expression list, and an empty view where the line is not such a
// directive, does not name that keyword at its own level, or names it with no
// value written against it.
std::string_view KeywordValueOnLine(std::string_view line,
                                    std::string_view keyword);

// True when a protect pragma directive line names `keyword` on its own
// expression list with nothing written against it.
//
// A keyword whose definition writes it standing alone is read against this
// rather than against a value: §34.5.13.1, §34.5.19.1 and §34.5.26.1 define
// their keywords that way, what the keyword designates being written on the
// line beneath rather than on the line itself, so a line is only announcing
// that designation when it named the keyword in the spelling the keyword is
// defined in.
bool NamesBareKeyword(std::string_view line, std::string_view keyword);

// True when a protect pragma directive line names `keyword` on its own
// expression list, in either of the two spellings §22.5.1 gives a pragma
// expression.
//
// A rule about a keyword being written at all rather than about what it
// carries is read against this. §34.5.15 states one: a data block found in an
// input file is an error wherever no previously generated protected block
// encloses it, and it is the naming of the keyword that puts a block there,
// whether the block is written on the line after it or as the value against
// it.
bool NamesKeyword(std::string_view line, std::string_view keyword);

}  // namespace delta
