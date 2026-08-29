#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// The key an author's own regions are sealed under. Every test that reads a
// produced envelope back needs the key it was formed under, or the region would
// stay sealed and its absence from the output would say nothing at all.
//
// The name says which fixture the key belongs to because
// test_fixtures/fixture_protect_encoding.h declares one of its own, and both
// are inline at namespace scope. A file including both took the two under one
// name until issue #3416, which a compiler reports as a redefinition naming a
// line in neither file and a linker need not report at all.
inline constexpr std::string_view kReadingExchangeKey = "acme-exchange-key";

// Envelope encryption over a source text, under that key.
inline std::string EncryptedByTheAuthor(const std::string& src) {
  return EncryptEnvelopes(src, kReadingExchangeKey);
}

// The same, with the reports the transformation made about its input kept
// beside the text it produced. The transformation runs to the end of the input
// whatever it found, so the two are read together rather than one in place of
// the other.
//
// The source is added to the manager so that a report can stand at the line of
// it that carries the breach, which is what a case naming one reads back
// through ReportedError in lib/cpp/test_helpers/helpers_reported_error.h.
struct EncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit EncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, kReadingExchangeKey, ProtectKeyList(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

// The same reading with no key supplied at all, which is the state a region has
// nothing to be encrypted under in. A caller holding an engine is still owed
// the reading, so the text comes back read through from end to end rather than
// merely handed back, and what it holds is what a region no key reached leaves
// behind.
struct KeylessEncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit KeylessEncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, ProtectKeyList(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

// A source text read through the preprocessor, with what the reading left
// behind kept beside it.
//
// Which envelopes a directive opened or closed is state the preprocessor
// carries from one directive to the next rather than anything the output text
// shows, so the Preprocessor outlives the call and the text it produced is kept
// for the claims about what reaches the step after.
//
// `key` is the one a user supplies for reading protected regions back. Tests
// about which directives open or close a region need none; the ones that read a
// produced envelope need the key it was formed under.
struct ReadSource {
  // What the reading is configured with, which is the key and nothing else. It
  // stands ahead of the constructor because the constructor's own member
  // initializer is what calls it.
  static PreprocConfig KeyConfig(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }

  // The other way a reading is configured: the keys supplied under the names
  // that select them. Which of the two a test wants is what it is asking
  // about -- the first says which key a block was really written under, and the
  // second whether the names the block carries reached a key at all.
  static PreprocConfig KeysConfig(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
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

  // How many envelopes of each mode the reading still has open where the text
  // ends. A word acts on one of the two, and the two words share their opening
  // letters, so the count that did not move is as much a part of a claim as the
  // one that did.
  size_t OpenEncryptionEnvelopes() const {
    return pp.ProtectEnvelopes().EncryptionEnvelopeDepth();
  }

  size_t OpenDecryptionEnvelopes() const {
    return pp.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }

  // Whether the reading stands inside protected code where the text ends. This
  // is the shorter question the counts above answer at length, and it is the
  // condition the reading of a block and of an announced key are both gated on.
  bool Protected() const { return pp.ProtectEnvelopes().InProtectedRegion(); }

  // The envelopes the reading opened and then closed, in closing order.
  const std::vector<ProtectedEnvelope>& Closed() const {
    return pp.ProtectEnvelopes().ClosedEnvelopes();
  }

  // The envelopes whose closing expression has not been read yet.
  const std::vector<ProtectedEnvelope>& Open() const {
    return pp.ProtectEnvelopes().OpenEnvelopes();
  }

  // The keywords the reading is holding for whichever envelope opens next. A
  // word turned away for its spelling describes nothing either, so it is absent
  // from here as well as from the counts above.
  const std::vector<std::string>& Pending() const {
    return pp.ProtectEnvelopes().PendingEnvelopeKeywords();
  }
};
