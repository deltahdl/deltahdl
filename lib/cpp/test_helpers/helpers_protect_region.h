#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "helpers_text_lines.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// The entity holding the key an encryption region reaches, the name that
// selects that key, and the key itself. §34.5.10 and §34.5.12 have a region
// designate its key by owner and by name, so the three travel together: a
// region that writes the first two reaches the third.
inline constexpr std::string_view kKeyOwner = "acme";
inline constexpr std::string_view kKeyName = "acme-2026";
inline constexpr std::string_view kRegionKey = "acme-region-exchange-key";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
inline constexpr std::string_view kSealedDesign =
    "module sealed_m; endmodule\n";

// Where the expression recording one envelope's sealed region begins. What
// stands between the quotation marks after it is the block itself.
inline constexpr std::string_view kBlockOpening =
    "`pragma protect data_block=\"";

// The two words §34.5.3.1 and §34.5.4.1 define, which delimit a model an
// encryption sealed already -- as the encrypting half writes them, and as a
// text carrying somebody else's sealed model writes them.
inline constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
inline constexpr std::string_view kEndProtected =
    "`pragma protect end_protected\n";

// The one key a region reaches, held under the names that select it.
inline ProtectKeyList TheRegionsKey() {
  ProtectKeyList held;
  held.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(kRegionKey)});
  return held;
}

// A key of the same entity held under some other name, for the region that
// reaches no key at all. A tool holding this has keys, and none of them is the
// one the region asked for, so a region left untransformed was left so for want
// of its own key rather than for want of any.
inline ProtectKeyList AKeyUnderAnotherName() {
  ProtectKeyList held;
  held.Add(
      {std::string(kKeyOwner), "some-other-key-name", std::string(kRegionKey)});
  return held;
}

// The expression naming the entity that provided the key, as §34.5.10 writes
// it, and the expression picking that provider's key out by name, as §34.5.12
// writes it.
inline std::string DesignatesTheProvider() {
  std::string written = "`pragma protect data_keyowner=\"";
  written.append(kKeyOwner).append("\"\n");
  return written;
}

inline std::string DesignatesTheKey() {
  std::string written = "`pragma protect data_keyname=\"";
  written.append(kKeyName).append("\"\n");
  return written;
}

// Both designations together, which is what a region has to write to reach a
// key at all.
inline std::string ReachesTheKey() {
  return DesignatesTheProvider() + DesignatesTheKey();
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with `inside`
// between them.
inline std::string RegionAround(std::string_view inside) {
  std::string written = "`pragma protect begin\n";
  written.append(inside).append("`pragma protect end\n");
  return written;
}

// The text one such region encloses: the designations reaching its key, then
// `written`, then the design it seals.
//
// The designations come first so that every region is one there is something to
// encrypt in, and the design comes last so that a `written` the reading passed
// over is a `written` that went into the block ahead of it.
inline std::string RegionBody(std::string_view written) {
  std::string inside = ReachesTheKey();
  inside.append(written).append(kSealedDesign);
  return inside;
}

// That body between the two words delimiting a region to be encrypted.
inline std::string RegionWriting(std::string_view written) {
  return RegionAround(RegionBody(written));
}

// The text standing where the encryption envelopes of `source` were written,
// for a tool holding the key those regions name.
inline std::string Encrypted(std::string_view source) {
  return EncryptEnvelopes(source, "", TheRegionsKey());
}

// The same, for a tool holding a key of that entity under another name.
inline std::string EncryptedWithoutTheKey(std::string_view source) {
  return EncryptEnvelopes(source, "", AKeyUnderAnotherName());
}

// The characters recording one envelope's sealed region: what stands between
// the quotation marks of its data_block expression, and empty where the text
// carries no such expression.
inline std::string DataBlockOf(std::string_view envelope) {
  size_t opens = envelope.find(kBlockOpening);
  if (opens == std::string_view::npos) return {};
  size_t from = opens + kBlockOpening.size();
  size_t to = envelope.find('"', from);
  if (to == std::string_view::npos) return {};
  return std::string(envelope.substr(from, to - from));
}

// The text that block records, recovered under the key the region was sealed
// with, and empty where the block does not open.
//
// A rule about what a block shall not hold is settled by opening the block and
// looking. The characters a block is written as say nothing about what went
// into it, so a reading that only searched the produced text could not tell a
// line that was kept out of the block from one that is in there unreadably.
inline std::string OpenedBlockOf(std::string_view envelope) {
  std::string recovered;
  if (!DecryptProtectedRegion(DataBlockOf(envelope), kRegionKey, &recovered)) {
    return {};
  }
  return recovered;
}

// The same, over a region writing `written` inside itself.
inline std::string OpenedBlockWriting(std::string_view written) {
  return OpenedBlockOf(Encrypted(RegionWriting(written)));
}
