#pragma once

#include <span>
#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {

// §34.5.21 settles one thing about a protected envelope: which algorithm the
// message digests written into it are computed with.
//
// A digest is a short value standing in for a long one. It is computed from a
// block, travels beside it, and is computed again by whatever reads the block,
// so a block that arrived altered is one whose two digests disagree. That only
// works while both computations are the same computation, and this keyword is
// where the two sides write down which one it is. The blocks it governs are the
// ones written after it -- a region's data and a region's keys alike -- and on
// the reading side it is what says which algorithm a digest is regenerated from
// a data block with.
//
// The keyword's own name, as §34.4 tabulates it.
inline constexpr std::string_view kDigestMethodKeyword = "digest_method";

// The identifiers Table 34-4 sets aside, spelled once here so that no reader of
// one comes to hold a spelling the others do not.
inline constexpr std::string_view kSha1DigestMethod = "sha1";
inline constexpr std::string_view kMd5DigestMethod = "md5";
inline constexpr std::string_view kMd2DigestMethod = "md2";
inline constexpr std::string_view kRipemd160DigestMethod = "ripemd-160";

// One row of Table 34-4: the identifier, whether every implementation has to
// provide the algorithm behind it, and the published algorithm that identifier
// stands for.
//
// The required/optional column is part of what the table says rather than an
// aside about it. An identifier marked required names an algorithm any tool can
// be handed a digest under; one marked optional names an algorithm a tool may
// know, and a text using it has assumed something about its reader.
struct ProtectDigestAlgorithm {
  std::string_view identifier;
  bool required;
  std::string_view algorithm;
};

// Every row of the table, in the order the table lists them.
std::span<const ProtectDigestAlgorithm> ProtectDigestAlgorithms();

// Whether `identifier` is one of the values the table sets aside. A value
// outside the table is not thereby meaningless -- the subclause admits further
// ones and leaves them to the implementation -- but what it names is not
// something the standard decides.
bool IsProtectDigestAlgorithm(std::string_view identifier);

// Whether the table marks `identifier` as one every implementation provides.
bool IsRequiredProtectDigestAlgorithm(std::string_view identifier);

// Whether this implementation can compute a digest under `identifier`.
//
// The two the table requires are provided. The two it marks optional are not,
// an optional identifier naming an algorithm a tool may know rather than one it
// has to, and the two questions are therefore separate: a value can be a
// tabulated identifier and still name no computation available here. Answering
// them alike would leave a digest computed under whatever algorithm was nearest
// to hand and written beside a name promising another -- a value no reader of
// that name could reproduce, which is the one thing a digest may not be.
bool ProtectDigestIsAvailable(std::string_view identifier);

// The identifier a text that has written no digest_method is read under.
//
// §34.4 fills a keyword no directive has written from that keyword's default,
// and the standard settles no default for this one, so what stands here is this
// implementation's choice. It is one of the two the table requires rather than
// an identifier of this implementation's own: a digest under a required
// identifier is one any tool can recompute, and being recomputed elsewhere is
// the whole use a digest is put to.
inline constexpr std::string_view kDefaultDigestMethod = kSha1DigestMethod;

// The identifier in effect at the point the reading has reached, reported
// beside whether a default put it there rather than a directive.
ProtectKeywordValue ProtectDigestMethodInEffect(
    const ProtectKeywordScope& scope);

// The digest of `data` under the algorithm `identifier` names, left in
// `*digest`.
//
// Returns false, leaving `*digest` untouched, where the identifier names no
// algorithm available here: a digest is the value the named algorithm produces
// or it is nothing at all, so there is no result to give rather than a shorter
// or a different one.
bool ProtectMessageDigest(std::string_view data, std::string_view identifier,
                          std::string* digest);

}  // namespace delta
