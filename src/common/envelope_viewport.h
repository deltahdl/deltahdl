#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

// §34.5.32.2: the access value of a viewport is an implementation-specific
// relaxation of protection. These are the two this tool defines, which the
// README lists: "r" lets a VPI application read the named object as it reads
// an unprotected one, and "rw" lets it write the object's value as well.
inline constexpr std::string_view kViewportReadAccess = "r";
inline constexpr std::string_view kViewportReadWriteAccess = "rw";

// What a viewport relaxes of §37.3.6's protection of the object it names.
enum class ViewportAccess : uint8_t { kNone, kRead, kReadWrite };

// The relaxation an access value written in a viewport grants, and none for a
// value this tool does not define.
inline ViewportAccess ViewportAccessOf(std::string_view access) {
  if (access == kViewportReadAccess) return ViewportAccess::kRead;
  if (access == kViewportReadWriteAccess) return ViewportAccess::kReadWrite;
  return ViewportAccess::kNone;
}

// One viewport of an envelope a reading met, kept for the stages after the
// preprocessor. §34.5.32.2 requires the object it names to be contained within
// its envelope, and §34.4 makes an envelope a lexical region, so the envelope
// is kept as the text it spans.
//
// A decryption envelope's text is the source its data block recovered to, and
// every source registered while that text was read, which are the ones its
// nested envelopes and included files recovered to. Sources are numbered in
// the order they are registered, so those are the ids from `first_source` to
// `last_source`.
//
// An encryption envelope this tool compiles where it is written, never
// encrypting it, is the lines from its begin to its end in the source holding
// them, `region_source` from `first_line` to `last_line`, and the sources
// registered between the two, which its included files and nested decryption
// envelopes recovered to. `region_source` is 0 for a decryption envelope.
//
// An envelope a precompiled library record carries, of either kind, is the
// lines of the record's text that came out of it, so a run binding the record
// keeps it as `region_source`, the record's text, from `first_line` to
// `last_line`, with no sources beside.
struct EnvelopeViewport {
  std::string object;
  std::string access;
  // Where the viewport pragma expression was written.
  SourceLoc loc;
  uint32_t first_source = 0;
  uint32_t last_source = 0;
  uint32_t region_source = 0;
  uint32_t first_line = 0;
  uint32_t last_line = 0;
};

}  // namespace delta
