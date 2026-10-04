#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>

namespace delta {

// §34.5.28 and §34.5.29 are the two places the protect pragma asks a tool for
// permission rather than for a key.
//
// A key decides whether a region can be opened at all, and anybody holding it
// opens the region. A licence decides whether the tool doing the opening is
// entitled to, and it is answered by a library the author ships rather than by
// the text. So the two are asked of different parties, and an envelope may hand
// its key to a reader whose tool the author never licensed.
//
// The two subclauses put the same question at different moments. §34.5.28.2
// asks it before the decrypted text is processed, so a tool that fails it
// decrypts nothing; §34.5.29.2 asks it before the model is executed, so a tool
// that fails it may read the model and must not run it. Nothing else separates
// them: the value is spelled the same way, and the five names mean the same
// thing on both.
//
// The two keyword names, as §34.4 tabulates them.
inline constexpr std::string_view kDecryptLicenseKeyword = "decrypt_license";
inline constexpr std::string_view kRuntimeLicenseKeyword = "runtime_license";

// The five names the value of either is spelled with. §34.5.28.1 and
// §34.5.29.1 write the same list for both: the library to load, the entry point
// in it to call, the feature string to pass that entry point, and optionally an
// exit point to call on the way out and a number to compare the entry point's
// return value against.
inline constexpr std::string_view kLibrarySubkeyword = "library";
inline constexpr std::string_view kEntrySubkeyword = "entry";
inline constexpr std::string_view kFeatureSubkeyword = "feature";
inline constexpr std::string_view kExitSubkeyword = "exit";
inline constexpr std::string_view kMatchSubkeyword = "match";

// One licence expression, read back as the five parts the two Syntax
// subclauses write it with.
struct ProtectLicense {
  // The three the syntax line writes outside brackets. §34.5.28.2 spends all
  // three in one sentence -- the tool loads the library, calls the entry
  // function in it, and passes that function the feature string -- so a licence
  // short of any one of them asks for nothing that can be carried out.
  std::string library;
  std::string entry;
  std::string feature;
  // The function §34.5.28.2 has called before the tool exits, so the licence is
  // released.
  //
  // `has_exit` stands apart from the string because §34.5.28.2 turns on whether
  // an exit function was specified rather than on what it is called. A licence
  // naming none releases nothing, and one naming the empty string has named a
  // function; a reading that recorded both as an empty string would call
  // nothing in the second case, and the licence would stay held.
  std::string exit;
  bool has_exit = false;
  // The value §34.5.28.2 compares the entry function's return against.
  //
  // `has_match` says whether the text wrote the number. Neither Syntax
  // subclause, neither Description, nor Table 34-1 states a default for it, and
  // the NOTE closing both subclauses has a user defeat the check with a library
  // "that returns a 0", which avoids it only where 0 is the answer a licence
  // asks for. So a licence that writes no number is held to 0, the value
  // `match` holds when `has_match` is false.
  uint64_t match = 0;
  bool has_match = false;
  // Whether the value read was written in the spelling the Syntax subclauses
  // define.
  //
  // The three strings do not answer that between them. A value naming none of
  // the three reads back as three empty strings, and so does one naming all
  // three against empty strings, and the first is no licence at all while the
  // second is a licence whose library has no name.
  bool stated = false;
};

// The licence a pragma_value states, and an unstated one where the value is
// written in any other spelling than §34.5.28.1's and §34.5.29.1's.
//
// Those two write the value as a parenthesized list naming a library, an entry
// and a feature, each against a <string>, with an exit against a <string> and a
// match against a <number> admitted after them. A value that is not
// parenthesized at all, or that leaves one of the three required names out, or
// that writes something other than a string against one of them, is not the
// value either subclause defines and states no licence.
//
// An optional name the list does not write is left absent rather than given a
// value, and one written in a spelling its own definition does not admit is
// absent too: a match written as a string states no number, and reading it as
// one would hand §34.5.28.2 a value to compare against that the text never
// wrote.
//
// The order the names are written in is not read. §22.5.1 spells the value as a
// list of pragma expressions, which name what they carry rather than standing
// at a position, and §34.5.9.1's and §34.5.32.1's values are read the same way.
ProtectLicense ParseProtectLicense(std::string_view value);

// What asking a licence's library came to: whether its entry function was
// called with the feature string and what it returned, or, where it was not
// called, why -- the library could not be loaded, or defines no entry function
// of that name. §34.5.28.2 and §34.5.29.2 have the tool report the value the
// entry function returned, so the value travels with the answer.
struct ProtectLicenseAnswer {
  bool called = false;
  int64_t returned = 0;
  std::string why_not_called;
};

// Asks the library a licence names, as §34.5.28.2 and §34.5.29.2 have a tool
// do on meeting the licence in an encrypted model. The preprocessor reads
// source text and loads no object code itself, so the run reading it supplies
// the asking.
using ProtectLicenseAsk =
    std::function<ProtectLicenseAnswer(const ProtectLicense&)>;

// Whether `answer` licenses the tool: §34.5.28.2 and §34.5.29.2 have the
// returned value compare equal to the match value where the tool is licensed
// and nonequal otherwise. An entry function never called returned nothing to
// compare, so it licenses nothing.
bool ProtectLicenseGranted(const ProtectLicense& license,
                           const ProtectLicenseAnswer& answer);

// The error a tool the licence `keyword` states does not license is reported
// with. Both subclauses have it include the value the entry function returned;
// where the function was not called, it says why instead.
std::string ProtectLicenseRefusal(std::string_view keyword,
                                  const ProtectLicense& license,
                                  const ProtectLicenseAnswer& answer);

}  // namespace delta
