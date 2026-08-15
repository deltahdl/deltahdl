#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"

namespace delta {

// One line of a source text as the encrypting half of §34.3 has to read it,
// which is a different reading from the one the preprocessor gives the same
// line. That half interprets protect pragma directives and carries every other
// character across as the bytes it is written with, so what it asks of a line
// is where the line stands rather than what it declares: whether a previously
// generated begin_protected-end_protected block contains it, whether it
// delimits a region to encrypt, and whether what it holds is one of the things
// §34.5 makes an error in an input file.
//
// The three questions are answered here together because the first decides the
// other two. §34.5.3 leaves the protect pragma expressions inside such a block
// uninterpreted, so a line inside one delimits nothing however it is spelled
// and carries no error however it is written.

// Splits `text` at every newline, keeping each terminator with the line it
// ends, so putting the pieces back together reproduces `text` byte for byte.
std::vector<std::string_view> SplitLines(std::string_view text);

// Where a report about one line of the input stands. Every condition reported
// here is a condition on a whole line -- a word opening a region, a block found
// where no envelope encloses it -- so a report stands at the first column of
// the line carrying it.
SourceLoc LineOf(uint32_t file_id, uint32_t line);

// Which of the two encryption envelope delimiters a directive line carries.
enum class EnvelopeDelimiter : uint8_t { kNone, kBegin, kEnd };

// A delimiter found on a directive line, together with the word that spelled
// it. The word is kept as a view into the line so the rest of the line can be
// told apart from it: the expressions written beside a delimiter specify the
// envelope it opens or closes, and they are carried into the envelope that
// takes its place rather than being read as part of the delimiter.
struct DelimiterMatch {
  EnvelopeDelimiter kind;
  std::string_view keyword;
};

// A line whose delimiting word was written with a pragma_value against it is a
// line that delimits nothing: §34.5.1.1 defines the opening word standing
// alone and §34.5.2.1 defines the closing word the same way, so the walk
// carries on past either one and, finding no delimiter, leaves the line among
// the text an encrypting tool copies rather than reads.
//
// A closing word written that way leaves the region it was meant to close
// still open, so the reading runs on to whatever closes next -- or to the end
// of the text, where a region that was never closed goes back as it was
// written. Reading such a word as the end of the region anyway would seal it
// at a point the standard does not put an end there.
DelimiterMatch DelimiterOfLine(std::string_view line);

// The directive that delimits a decryption envelope where `line` delimited an
// encryption one.
//
// Only the word naming the delimiter is transformed, because only that word
// said which of the two modes the envelope was defined for. Every expression
// beside it -- who wrote the design, which algorithm and key name were asked
// for, what a run of it is licensed on -- specified the encryption envelope,
// and each is written out again exactly as it stands so that it goes on
// specifying the envelope standing in its place. The line's own leading
// whitespace and directive text are kept for the same reason.
//
// An expression written ahead of the delimiter describes the envelope and an
// expression written after it describes the enclosed region, so carrying each
// one across on the side it was written on is what keeps the two apart.
std::string TransformedDelimiterLine(std::string_view line,
                                     const DelimiterMatch& delimiter,
                                     std::string_view replacement);

// How many previously generated begin_protected-end_protected blocks the
// reading stands inside.
//
// §34.5.3 has the contents of such a block treated as input cleartext: the
// protect pragma expressions written in it are not interpreted and do not
// override the values the current encryption has in effect. The reading
// therefore has to know it is inside one before it reads a line rather than
// after, so a whole source text is walked through one of these.
//
// The two delimiting expressions are inside as well. What they describe is the
// envelope some earlier encryption produced, and letting that description into
// the reading is exactly the corruption of the current encryption's values
// §34.5.3 rules out, so the block runs from the line opening it through the
// line closing it.
//
// §34.5.1 allows further such blocks inside one, treating them as bytes of it
// like everything else, so what ends a block is the closing expression
// matching its own opening one rather than the first one encountered. A
// closing expression with nothing open closes nothing and is a line of the
// text like any other.
class PreviouslyProtectedBlock {
 public:
  // Applies one line, and returns whether that line belongs to a previously
  // generated protected block.
  //
  // §34.5.3.1 defines the word opening such a block as the pragma_keyword
  // standing alone, so a line is only opening one where it named that word in
  // that spelling. A line writing a pragma_value against the word opens
  // nothing and is text of whatever region encloses it, which is what keeps
  // this walk from taking an arbitrary run of an author's design for somebody
  // else's already-protected model.
  //
  // §34.5.4.1 defines the word closing such a block the same way, and both
  // words are spelled in protect_envelope.h beside those definitions, so the
  // line this walk takes as the start or the end of an already-protected model
  // is the line the envelope state takes for the same thing. A line writing a
  // pragma_value against the closing word ends nothing here either: the model
  // runs on, and the design written after it stays inside a block whose bytes
  // travel into the enclosing envelope unread.
  bool Contains(std::string_view line);

 private:
  size_t depth_ = 0;
};

// One line of the input, read for the two things an encrypting tool has to
// know about it before it does anything else with it: whether a previously
// generated protected block contains it, and which delimiter of an encryption
// envelope it carries.
struct InputLine {
  bool previously_protected;
  DelimiterMatch delimiter;
};

// §34.5.1 makes a region opened inside a region that is still open an error.
// The opening expression marks the point encryption begins at, and a text that
// marks a second such point before marking where the first region ends has
// asked for one block of cleartext inside another. `delimiter` is what the line
// standing at `loc` carries, and only an opening one is reported.
//
// The line is still read as the text it is: the transformation runs to the end
// of the input either way, and §34.5.1 has everything standing between an
// opening expression and the closing one that answers it -- other protect
// pragmas included -- encrypted into the enclosing region's block. What the
// condition costs is the report rather than the transformation, which is how
// every other condition an encrypting tool's input can carry is treated here.
//
// It is a delimiter of the encrypting half's own reading that counts. A line a
// previously generated protected block contains delimits nothing, because
// §34.5.3 leaves its expressions uninterpreted, so an already-protected model
// sealed inside a region is the arrangement §34.5.1 permits rather than the one
// it rules out. So is an opening word written with a pragma_value against it,
// which §34.5.1.1 leaves naming no opening expression at all.
//
// `diag` may be null for a caller with nothing to report to, and nothing is
// reported then.
void ReportNestedRegion(const DelimiterMatch& delimiter, DiagEngine* diag,
                        SourceLoc loc);

// Reads one line of the input, advancing `block` over the previously generated
// protected blocks the text holds, and reports what §34.5.15 and §34.5.27 make
// an error in an input file. `loc` is where the line stands, and `diag` may be
// null for a caller with nothing to report to.
InputLine ReadInputLine(std::string_view line, PreviouslyProtectedBlock* block,
                        DiagEngine* diag, SourceLoc loc);

}  // namespace delta
