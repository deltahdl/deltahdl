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

// True when `value` is a pragma_value written in the parenthesized spelling: a
// list of further pragma expressions rather than one written thing.
//
// §22.5.1 spells a pragma_value as one written thing -- a string, a number, an
// identifier -- or as that list, and the two are not interchangeable. The
// expressions between the parentheses name parts of a value rather than being
// one, so a keyword whose own definition writes one written thing against it
// carries no value at all where a list is what stands there.
//
// The parenthesized spelling is the one that announces itself in its first
// character: every other pragma_value opens with a quote, a digit, a letter or
// the punctuation a name may start with.
bool IsParenthesizedPragmaValue(std::string_view value);

// The same, narrowed to a value the keyword can be said to carry on its own:
// an empty view where the line wrote the parenthesized spelling of a
// pragma_value against `keyword`, and the value otherwise.
//
// §22.5.1 spells a pragma_value as one written thing -- a string, a number, an
// identifier -- or as a parenthesized list of further pragma expressions, and
// the two are not interchangeable. A list qualifies the value by naming parts
// of it, so the characters between the parentheses are the expressions of that
// list rather than the text the keyword stands for. A keyword whose own
// definition writes one written thing against it is read against this, so that
// a list is turned away here rather than recorded as though the parentheses and
// everything inside them were the value.
//
// This is the distinction the directive's own token reading already draws, by
// keeping a parenthesized value apart from a single one instead of offering
// both as the value written. Drawing it here as well is what keeps the two
// readings of one line in step: a spelling that carries a value to one of them
// and not to the other would have them disagree about what the line wrote.
std::string_view KeywordSingleValueOnLine(std::string_view line,
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
// it. §34.5.27 states the same rule for the key block, and §34.5.22 states one
// of the same shape: a digest_block found in an input file is a request to
// generate a digest, so what a text wrote against the keyword decides no more
// there than it does for the other two.
//
// Those three are the whole of it. A keyword whose rule turns on the line
// beneath it is read against NamesBareKeyword above, and §34.5.22's keyword is
// read against both, one predicate for each of the two things it does.
bool NamesKeyword(std::string_view line, std::string_view keyword);

}  // namespace delta
