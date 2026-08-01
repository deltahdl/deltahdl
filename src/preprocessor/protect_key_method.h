#pragma once

#include <span>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {

// §34.5.24 settles one thing about a protected envelope: which algorithm the
// keys that encrypt a region's data are themselves encrypted with.
//
// A region's data are encrypted under a key, and that key need not be one the
// reader already holds: it may travel with the region. Travelling in the clear
// it would open the very block it was carried beside, so it travels encrypted,
// and this keyword is where the two sides write down what encrypted it. On the
// writing side it names the algorithm the data's keys are put under; on the
// reading side it names the algorithm the block holding those keys is opened
// with. It is not the algorithm the data themselves are under -- that one is
// named by data_method, and a producer may keep the two apart.
//
// The keyword's own name, as §34.4 tabulates it.
inline constexpr std::string_view kKeyMethodKeyword = "key_method";

// One row of the table of encryption algorithm identifiers: the identifier,
// whether every implementation provides the cipher behind it, and the published
// cipher that identifier stands for.
//
// The required/optional column is part of what the table says rather than an
// aside about it. An identifier marked required names a cipher any tool can be
// handed a block under; one marked optional names a cipher a tool may know, and
// a text using it has assumed something about its reader.
struct ProtectEncryptionAlgorithm {
  std::string_view identifier;
  bool required;
  std::string_view algorithm;
};

// Every row of that table, in the order the table lists them.
//
// The table is §34.5.11's, written there for the keyword that names the cipher
// a region's data are under. §34.5.24 does not tabulate a second set for the
// keyword that names the cipher a region's keys are under: it sends the reader
// to that one, so one table answers for both keywords and an identifier
// admitted for either is admitted for the other.
std::span<const ProtectEncryptionAlgorithm> ProtectEncryptionAlgorithms();

// Whether `identifier` is one of the values this keyword identifies an
// encryption algorithm by, which is to say one of the values tabulated there.
//
// A value outside the table is not thereby meaningless -- further identifiers
// are admitted and left to the implementation -- but what it names is not
// something the standard decides, so a text using one has assumed a reader that
// knows the same private name for the same cipher.
bool IsProtectKeyMethodIdentifier(std::string_view identifier);

// Whether the table marks `identifier` as one every implementation provides.
bool IsRequiredProtectEncryptionAlgorithm(std::string_view identifier);

// The identifier in effect at the point the reading has reached, reported
// beside whether no directive put it there.
//
// This subclause settles no default. §34.4 fills a keyword no directive has
// written from that keyword's default value, and what stands here where nothing
// was written is therefore an empty identifier rather than a cipher of this
// implementation's choosing: a key block read under a cipher nobody named would
// come out as bytes that decrypt to nothing, and reporting no identifier says
// so where naming one would not.
ProtectKeywordValue ProtectKeyMethodInEffect(const ProtectKeywordScope& scope);

}  // namespace delta
