#pragma once

#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// §34.4 sets aside a fixed set of pragma keyword names for the protect pragma
// and tabulates them; §34.5 is where each of those names is defined. One entry
// of that table: the name, and what the table says the name does.
struct ProtectPragmaKeyword {
  std::string_view name;
  // The account the table gives of the name. It rides beside the name so a
  // name is never listed without what listing it was for.
  std::string_view description;
};

// Every name the table lists, in the order it lists them -- which is also the
// order the definitions behind them are written in. A name that is not here is
// not a pragma keyword of the protect pragma, whichever directive it is
// written on and however it is spelled.
std::span<const ProtectPragmaKeyword> ProtectPragmaKeywords();

// Whether `name` is one of them.
bool IsProtectPragmaKeyword(std::string_view name);

// What the table says `name` does. A name outside the table has no entry, so
// there is nothing to say about it and the result is empty.
std::string_view ProtectPragmaKeywordDescription(std::string_view name);

// A pragma_value spelled as a string carries its quotes. What the keyword
// records is written between them; a value spelled any other way records
// itself.
std::string_view ProtectPragmaValueBody(std::string_view value);

// The value a protect pragma keyword has. `defaulted` marks the value §34.4
// puts in the place of a keyword no directive has written: an envelope missing
// a keyword is described by that keyword's default rather than left
// undescribed, so the absence is something to fill rather than something to
// report.
struct ProtectKeywordValue {
  std::string value;
  bool defaulted;
};

// The protect pragma keyword values a source text has put in effect at the
// point the reading has reached.
//
// The scope tracked here is the lexical one: a value belongs to the position
// in the text where it was written and to everything the reading goes on to
// reach, rather than to the declarative region or the declaration the
// directive happens to stand in. Reading crosses out of a declaration, out of
// a file and on into an included file without any of the values being put
// back, so one of these follows a whole compilation input rather than a file
// or a design element.
class ProtectKeywordScope {
 public:
  // Applies one pragma expression of a protect pragma directive: `keyword`
  // names it, and `value` is the pragma_value written against it, empty where
  // the expression is the keyword standing alone. A name the table does not
  // list is not a protect pragma keyword, so nothing is put in effect for it.
  void Apply(std::string_view keyword, std::string_view value);

  // The value in effect for `keyword`, which is its default until a directive
  // writes one.
  ProtectKeywordValue ValueOf(std::string_view keyword) const;

 private:
  struct Entry {
    std::string keyword;
    std::string value;
  };
  // One entry per keyword a directive has written, in first-written order. A
  // keyword written again keeps its entry and takes the newer value, because
  // what is in effect is the most recent writing of it.
  std::vector<Entry> in_effect_;
};

// What a tool writes into an envelope of its own making to say how that
// envelope was made.
//
// §34.4 asks a tool that produces envelopes to state every keyword bearing on
// each one, and the reason is the lexical scope the same subclause gives those
// keywords. A keyword an envelope leaves unwritten is filled from whatever the
// reading had in effect on arriving there, which is a different value
// depending on what the envelope was placed beside and which file it was read
// after. An envelope stating its own is read the same way wherever it ends up.
//
// The three named here are the ones that bear on an envelope this
// implementation writes: who made it, what its data are under, and how its
// encoded block is spelled. Their values are the tool's own, because the
// standard settles neither the cipher a tool encrypts with nor the scheme it
// writes the encrypted block in.
struct ProtectEnvelopeDescription {
  std::string_view encrypt_agent;
  std::string_view data_method;
  std::string_view encoding;
};

// Those keywords as directives, one per line, for writing inside an envelope a
// tool has just produced.
std::string ProtectEnvelopeDescriptionDirectives(
    const ProtectEnvelopeDescription& description);

// The directive that puts the protect pragma keywords back to their default
// values. §34.4 recommends one after each envelope, so that what an envelope
// stated about itself is not left standing over whatever comes after it.
std::string ProtectKeywordResetDirective();

}  // namespace delta
