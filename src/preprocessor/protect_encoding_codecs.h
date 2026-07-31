#pragma once

#include <cstddef>
#include <string>
#include <string_view>

namespace delta {

// The coding schemes Table 34-2 names, each written as the pair of
// transformations it is: one that turns bytes into the characters standing for
// them, and one that turns those characters back. A scheme is only of use when
// both halves are present and each undoes the other, so they are declared in
// pairs rather than apart.
//
// Every decoding here returns false rather than a partial result when the text
// it is given is not text its own encoding produced, and leaves the caller's
// string untouched, so a block written under one scheme and read under another
// is reported rather than silently taken for data.

// IETF RFC 2045, also the algorithm IEEE Std 1003.1 reaches through uuencode
// -m: three bytes to four characters of a sixty-four character alphabet, with
// a final short group filled out by the padding character.
std::string EncodeBase64(std::string_view bytes);
bool DecodeBase64(std::string_view text, std::string* bytes);

// The historical algorithm of IEEE Std 1003.1: the data are written a line at
// a time, each line opening with a character giving how many bytes of data it
// carries and continuing with those bytes six bits to a character, and the
// last line carrying no data at all.
//
// `line_length` is the maximum a written line may reach, and zero asks for the
// longest line the algorithm itself allows. Because the length character and
// the four-character groups after it are what a line is made of, the bytes per
// line are chosen so that the characters standing for them fit inside it.
std::string EncodeUuencode(std::string_view bytes, size_t line_length);
bool DecodeUuencode(std::string_view text, std::string* bytes);

// IETF RFC 2045: a byte that is already a printable character stands for
// itself, and every other byte is written as an equals sign and the two hex
// digits of its value. A line that would run past `line_length` is broken with
// a soft line break, which is an equals sign at the end of the line and stands
// for nothing in the data. Zero asks for the longest line that standard
// allows.
std::string EncodeQuotedPrintable(std::string_view bytes, size_t line_length);
bool DecodeQuotedPrintable(std::string_view text, std::string* bytes);

// This implementation's own scheme, and the one its envelopes are written in.
// It writes three bytes to four characters as base64 does, but over an
// alphabet holding neither a quotation mark nor a solidus and needing no
// padding character, so a block of it can be written as the pragma_value of an
// expression without any of it closing the value or opening a comment.
std::string EncodeProtectBlockAlphabet(std::string_view bytes);
bool DecodeProtectBlockAlphabet(std::string_view text, std::string* bytes);

}  // namespace delta
