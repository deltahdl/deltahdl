#pragma once

#include <string>
#include <string_view>

namespace delta {

// §34.5.32 answers what a protected envelope lets a tool look at.
//
// Everything else in §34.5 seals a design away. §34.4 tabulates this one name
// as the one that modifies the scope of access into a decryption envelope, and
// §34.5.32.2 says which way it modifies it: the expression describes objects
// within the current protected envelope for which access shall be permitted by
// the SystemVerilog tool. So a text carrying one is asking for less protection
// than the envelope would otherwise give, and naming what to give up.
//
// The keyword's own name, as §34.4 tabulates it.
inline constexpr std::string_view kViewportKeyword = "viewport";

// The two names its value is spelled with. §34.5.32.1 writes the value as a
// parenthesized list of these rather than as a single word, because an object
// alone does not say what may be done with it and an access alone does not say
// what it is an access to.
inline constexpr std::string_view kObjectSubkeyword = "object";
inline constexpr std::string_view kAccessSubkeyword = "access";

// One viewport expression, read back as the two things §34.5.32.1 writes it
// with.
//
// `object` is the name §34.5.32.2 requires to be contained within the current
// envelope. `access` is what the expression asks be permitted for it, and
// §34.5.32.2 leaves that value to the implementation: it is an
// implementation-specific relaxation of protection, so no value of it is
// better spelled than another and nothing here judges one.
struct ProtectViewport {
  std::string object;
  std::string access;
  // Whether the value read was written in the spelling §34.5.32.1 defines.
  //
  // The two strings do not answer that between them. A value naming neither
  // name reads back as two empty strings, and so does a value naming both
  // against empty strings, and the first of those is not a viewport at all
  // while the second is one describing an object with no name.
  bool stated = false;
};

// The viewport a pragma_value states, and an unstated one where the value is
// written in any other spelling than §34.5.32.1's.
//
// §34.5.32.1 writes the value as a parenthesized list naming an object and an
// access, each against a <string>. A value that is not parenthesized at all, or
// that leaves one of the two names out, or that writes something other than a
// string against either, is not the value the subclause defines and states no
// viewport.
//
// The order the two are written in is not read. §22.5.1 spells the value as a
// list of pragma expressions, which name what they carry rather than standing
// at a position, and §34.5.9.1's value is read the same way here.
ProtectViewport ParseProtectViewport(std::string_view value);

}  // namespace delta
