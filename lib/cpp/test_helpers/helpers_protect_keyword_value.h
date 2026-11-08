#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

inline std::string InQuotes(std::string_view value) {
  std::string text = "\"";
  text.append(value).append("\"");
  return text;
}

inline std::string ThroughEndProtected(const std::string& envelope) {
  constexpr std::string_view kEnds = "`pragma protect end_protected\n";
  std::size_t at = envelope.rfind(kEnds);
  EXPECT_NE(at, std::string::npos) << envelope;
  if (at == std::string::npos) return envelope;
  return envelope.substr(0, at + kEnds.size());
}

struct ReadKeywordScope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadKeywordScope(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
    EXPECT_FALSE(diag.HasErrors()) << src;
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  std::string_view KeyBlockKeyReached(const ProtectKeyList& keys) const {
    return ProtectKeyBlockKey(pp.ProtectKeywords(), keys);
  }
};
