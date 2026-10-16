#include "preprocessor/protect_designation_reports.h"

#include <algorithm>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_region_lines.h"

namespace delta {
namespace {

// Whether two of `values` that were written are the same value.
bool RepeatsAValue(std::initializer_list<std::string_view> values) {
  std::vector<std::string_view> written;
  for (std::string_view value : values) {
    if (value.empty()) continue;
    if (std::find(written.begin(), written.end(), value) != written.end()) {
      return true;
    }
    written.push_back(value);
  }
  return false;
}

}  // namespace

// §34.5.10, §34.5.16 and §34.5.23: the values written against the names that
// designate one entity's key are unique for that entity, so one value written
// against two of them designates neither, and the encrypting run reports it as
// a reading does.
void ReportRepeatedDesignations(const RegionKeyReader& in_effect,
                                DiagEngine* diag, SourceLoc opened) {
  const RegionKeyNames& names = in_effect.names;
  struct Designations {
    bool repeated;
    std::string_view owner_keyword;
    std::string_view subclause;
  };
  const Designations kAll[] = {
      {RepeatsAValue({ProtectPragmaValueBody(names.data_keyname),
                      names.data_public_key, in_effect.data_decrypt_key}),
       kDataKeyownerKeyword, "34.5.10"},
      {RepeatsAValue({ProtectPragmaValueBody(names.digest_keyname),
                      names.digest_public_key, in_effect.digest_decrypt_key}),
       kDigestKeyownerKeyword, "34.5.16"},
      {RepeatsAValue(
           {ProtectPragmaValueBody(names.key_keyname), names.key_public_key}),
       kKeyKeyownerKeyword, "34.5.23"},
  };
  for (const Designations& designations : kAll) {
    if (!designations.repeated) continue;
    diag->Error(opened,
                std::string("protect pragma writes one value against two of "
                            "the names that designate a key of the ")
                    .append(designations.owner_keyword)
                    .append(" in effect"),
                Subclause(designations.subclause));
  }
}

// §34.5.13, §34.5.19 and §34.5.26: a name given to one of an entity's keys and
// a public key written beside it refer to the same key. It is only decided
// where the run holds a key under each.
void ReportDisagreeingDesignations(const RegionKeyNames& names,
                                   const ProtectKeyList& keys, DiagEngine* diag,
                                   SourceLoc opened) {
  struct Pair {
    std::string_view owner;
    std::string_view name;
    std::string_view public_key;
    std::string_view prefix;
    std::string_view subclause;
  };
  std::string_view data_owner = ProtectPragmaValueBody(names.data_keyowner);
  std::string_view digest_owner =
      names.digest_keyowner.empty()
          ? data_owner
          : ProtectPragmaValueBody(names.digest_keyowner);
  const Pair kPairs[] = {
      {data_owner, ProtectPragmaValueBody(names.data_keyname),
       names.data_public_key, "data", "34.5.13"},
      {digest_owner, ProtectPragmaValueBody(names.digest_keyname),
       names.digest_public_key, "digest", "34.5.19"},
      {ProtectPragmaValueBody(names.key_keyowner),
       ProtectPragmaValueBody(names.key_keyname), names.key_public_key, "key",
       "34.5.26"},
  };
  for (const Pair& pair : kPairs) {
    std::string_view under_name = keys.KeyFor(pair.owner, pair.name);
    std::string_view under_public = keys.KeyFor(pair.owner, pair.public_key);
    if (under_name.empty() || under_public.empty() ||
        under_name == under_public) {
      continue;
    }
    std::string message = "protect pragma ";
    message.append(pair.prefix).append("_public_key and ");
    message.append(pair.prefix).append("_keyname designate different keys of ");
    message.append("the ").append(pair.prefix).append("_keyowner in effect");
    diag->Error(opened, message, Subclause(pair.subclause));
  }
}

}  // namespace delta
