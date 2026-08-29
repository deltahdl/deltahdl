#pragma once

#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>

namespace delta {

// §34.5.9 answers a question the rest of the protect pragma leaves open. The
// blocks an envelope carries -- the encrypted design, the keys it is reached
// through, the digest it can be checked against -- come out of a cipher as
// arbitrary bytes, and a source text is characters. The encoding keyword is
// what settles the writing that turns the one into the other, so that every
// byte an encryption produces can travel as text.
//
// The keyword's own name, as §34.4 tabulates it.
inline constexpr std::string_view kEncodingKeyword = "encoding";

// The three names its value is spelled with. §34.5.9.1 writes the value as a
// parenthesized list of these rather than as a single word, because a coding
// scheme alone does not say how long a line may be or how much data the block
// stands for, and both are things a reader needs.
inline constexpr std::string_view kEnctypeSubkeyword = "enctype";
inline constexpr std::string_view kLineLengthSubkeyword = "line_length";
inline constexpr std::string_view kBytesSubkeyword = "bytes";

// The identifiers Table 34-2 sets aside, spelled once here so that no reader
// of one comes to hold a spelling the others do not.
inline constexpr std::string_view kUuencodeEnctype = "uuencode";
inline constexpr std::string_view kBase64Enctype = "base64";
inline constexpr std::string_view kQuotedPrintableEnctype = "quoted-printable";
inline constexpr std::string_view kRawEnctype = "raw";

// The identifier this implementation writes its own blocks under. §34.5.9
// leaves further identifiers and the schemes behind them to the
// implementation, so a scheme that is not one of the tabulated four is named
// as this implementation's own rather than claiming a name the standard has
// already given away.
//
// This is also the scheme a text that never wrote an encoding expression is
// read in. §34.4 fills a keyword no directive has written from that keyword's
// default, and the standard settles no default for this one, so the default is
// the scheme the tool itself writes.
inline constexpr std::string_view kBlockEnctype = "x-deltahdl-block";

// One row of Table 34-2: the identifier, whether every implementation has to
// provide it, and the published algorithm the identifier stands for.
//
// The required/optional column is part of what the table says rather than an
// aside about it. An identifier marked required names a scheme any tool can be
// handed a block in; one marked optional names a scheme a tool may know, and a
// text using it has assumed something about its reader.
struct ProtectEncodingAlgorithm {
  std::string_view enctype;
  bool required;
  std::string_view algorithm;
};

// Every row of the table, in the order the table lists them.
std::span<const ProtectEncodingAlgorithm> ProtectEncodingAlgorithms();

// Whether `enctype` is one of the identifiers the table sets aside. An
// identifier outside the table is not thereby meaningless -- the subclause
// admits further ones -- but what it stands for is not something the standard
// decides.
bool IsProtectEncodingAlgorithm(std::string_view enctype);

// Whether the table marks `enctype` as one every implementation provides.
bool IsRequiredProtectEncodingAlgorithm(std::string_view enctype);

// Whether a block written under `enctype` stands on one line: the characters
// that scheme writes hold no line break.
//
// §34.5.9 leaves a tool free to encode a block under whichever scheme a text
// asks for, and §34.5.15.2 has a block begin on the line beneath the keyword
// announcing it and says nothing about where it ends. This implementation reads
// one line -- Preprocessor::TakeDataBlockValue (preprocessor/preprocessor.h)
// takes the line the keyword announced and nothing after it -- so a scheme
// spelling a block over several lines is not one a block can be written under
// here, and writing one would produce an envelope this tool could not read
// back. The two schemes that stand on one line are accepted by the reading side
// either way, so nothing is lost by writing under one of them and saying so.
// #3431 covers reading a block that spans several lines.
bool ProtectEncodingFitsOneLine(std::string_view enctype);

// Whether this implementation can write and read a block under `enctype`.
// That covers every tabulated identifier, the required ones because they have
// to be covered and the optional ones because they are, and the identifier
// this implementation defines for its own blocks.
bool ProtectEncodingIsAvailable(std::string_view enctype);

// One encoding pragma expression, read into the parts §34.5.9.1 spells it
// with.
//
// `line_length` is zero where no length was written, a maximum of no
// characters being a length no block could be written within. `has_bytes`
// stands apart from `bytes` for the same reason in reverse: a block of no
// bytes is a block a text may well describe, so the absence of the subkeyword
// has to be recorded as something other than the value zero.
struct ProtectEncoding {
  std::string enctype;
  size_t line_length = 0;
  size_t bytes = 0;
  bool has_bytes = false;
};

// The encoding a text is read and written in where it has written none. The
// scheme is this implementation's own, and neither a line length nor a byte
// count is assumed on a text's behalf.
ProtectEncoding DefaultProtectEncoding();

// Reads the pragma_value of an encoding expression: the parenthesized list of
// subkeyword expressions, with or without the parentheses around it. An
// optional subkeyword the list does not write is left at its default, and a
// name the subclause does not define qualifies nothing here.
//
// The scheme is the one subkeyword §34.5.9.1 writes outside brackets, and it
// writes it as a string. A list that names no scheme, or names one in any
// spelling other than a string, is therefore not the value this keyword is
// defined with, and the result is a descriptor stating nothing at all --
// neither a scheme nor the length and count that would have described a block
// written under one.
ProtectEncoding ParseProtectEncoding(std::string_view value);

// The same value written back out, in the shape §34.5.9.1 defines: the
// required enctype first, then whichever of the two optional subkeywords the
// descriptor carries.
std::string ProtectEncodingValue(const ProtectEncoding& encoding);

// That value as a whole protect pragma directive, for a tool stating the
// encoding of a block it is about to write.
std::string ProtectEncodingDirective(const ProtectEncoding& encoding);

// The same directive for a tool about to write one encoded value, stating
// against the bytes subkeyword how much data that value stands for before any
// of the writing was applied to it.
//
// §34.5.9 has the count added by the encrypting tool for each block it writes,
// and lets an expression stand ahead of each of the values an envelope carries
// rather than once for the envelope as a whole. A count therefore describes one
// value: an envelope carrying several writes one of these ahead of each, and a
// value left standing under some other value's count would be measured by its
// reader against a size describing something else entirely.
std::string ProtectEncodedValueDirective(const ProtectEncoding& encoding,
                                         size_t bytes);

// Writes `bytes` as the text a block carries, under the scheme `encoding`
// names and within the line length it states.
//
// A line length is a maximum on the characters of one line after the encoding
// has been applied, so it is honored by breaking the encoded text rather than
// by encoding less of it. Where the scheme is the identity transformation
// there is no encoded text to break -- the block is the data -- so a line
// length asks for nothing there and nothing is inserted.
//
// The result is empty where `encoding` names a scheme this implementation does
// not provide, there being no writing to produce.
std::string EncodeProtectBlock(std::string_view bytes,
                               const ProtectEncoding& encoding);

// The inverse: recovers into `*bytes` the data that `text` is the encoding of
// under `enctype`. Returns false, leaving `*bytes` untouched, where `enctype`
// names a scheme this implementation does not provide or where `text` is not
// something that scheme produces.
//
// A line break is the one thing a decoding ignores rather than reads. §34.5.9
// has the breaks inserted so the encoded text can be handled by ordinary text
// tools, which makes them a property of the writing rather than of the data --
// except under the identity transformation, where nothing was inserted and
// every byte is data.
bool DecodeProtectBlock(std::string_view text, std::string_view enctype,
                        std::string* bytes);

// How reading one encoded value of a protected envelope came out.
//
// §34.5.9 governs more than the block carrying a region's data. The blocks
// holding the keys and the digest are written under the same scheme, and so
// are the values a text writes beneath the keywords that announce a key -- the
// public key a region's own keys are under among them, which is where §34.5.26
// sends its reader. Every one of those values is read the same way, so the
// reading is written once and the two things that can stop it are told apart
// here rather than at each place a value is read.
//
// A scheme nothing here provides is one no value can be read under at all:
// Table 34-2 names four identifiers and leaves further ones to the
// implementation, so an identifier outside both sets stands for no writing.
// Text that is not something an available scheme writes is a different matter
// -- the scheme is known and the value was not written under it -- and a
// reader that reported the two alike would leave an author unable to tell an
// unsupported envelope from a mis-declared one.
enum class ProtectEncodedValueRead : uint8_t {
  kRead,
  kSchemeUnavailable,
  kNotWrittenInScheme,
};

// Reads `text` as a value written under `encoding`, leaving what it stands for
// in `*bytes`. `*bytes` is untouched unless the result is kRead.
ProtectEncodedValueRead ReadProtectEncodedValue(std::string_view text,
                                                const ProtectEncoding& encoding,
                                                std::string* bytes);

// Whether a value standing for `bytes` bytes is the size `encoding` declares.
//
// §34.5.9 has a decrypting tool take two things from the expression: the
// algorithm a value's characters were produced by, and how much data those
// characters stand for. Reading the value out of the scheme answers the first;
// this answers the second. A value the count refuses is not that expression's
// value at all, whatever else can be done with its bytes.
//
// A descriptor stating no count declares no size, so any quantity satisfies it.
// A text may name a scheme without saying how much data any value under it
// holds, and inventing a size on such a text's behalf would refuse envelopes
// the standard admits.
//
// Only the decrypting side has cause to ask. The same subclause has an
// encrypting tool disregard the count in the text it reads, so the half that
// encodes a region's own designations measures nothing against one.
bool ProtectEncodedValueHasStatedSize(const ProtectEncoding& encoding,
                                      size_t bytes);

}  // namespace delta
