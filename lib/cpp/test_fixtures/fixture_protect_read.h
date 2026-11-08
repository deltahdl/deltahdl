#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

inline constexpr std::string_view kReadingExchangeKey = "acme-exchange-key";

inline std::string EncryptedByTheAuthor(const std::string& src) {
  return EncryptEnvelopes(src, kReadingExchangeKey);
}

struct EncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  std::string text;

  explicit EncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, kReadingExchangeKey, ProtectKeyList(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

struct KeylessEncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  std::string text;

  explicit KeylessEncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, ProtectKeyList(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

struct ReadSource {
  static PreprocConfig KeyConfig(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }

  static PreprocConfig KeysConfig(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  Preprocessor pp;
  std::string text;

  explicit ReadSource(const std::string& src, std::string_view key = {})
      : pp(mgr, diag, KeyConfig(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ReadSource(const std::string& src, const PreprocConfig& config)
      : pp(mgr, diag, config) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  size_t OpenEncryptionEnvelopes() const {
    return pp.ProtectEnvelopes().EncryptionEnvelopeDepth();
  }

  size_t OpenDecryptionEnvelopes() const {
    return pp.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }

  bool Protected() const { return pp.ProtectEnvelopes().InProtectedRegion(); }

  const std::vector<ProtectedEnvelope>& Closed() const {
    return pp.ProtectEnvelopes().ClosedEnvelopes();
  }

  const std::vector<ProtectedEnvelope>& Open() const {
    return pp.ProtectEnvelopes().OpenEnvelopes();
  }

  const std::vector<std::string>& Pending() const {
    return pp.ProtectEnvelopes().PendingEnvelopeKeywords();
  }
};
