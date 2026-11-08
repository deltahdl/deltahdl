#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_keywords.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(GateKeywordLexing, AllTwentySixKeywords) {
  for (const auto& entry : kGateKeywords) {
    auto r = LexOne(entry.text);
    EXPECT_EQ(r.token.kind, entry.expected) << "keyword: " << entry.text;
  }
}

TEST(GateKeywordLexing, NearMissSpellingsAreIdentifiers) {
  constexpr const char* kNearMisses[] = {
      "andx", "buff",  "nott",     "cmoss", "trann",   "bufif2",
      "gate", "xnorx", "rtranif2", "notif", "pullups",
  };
  for (const char* spelling : kNearMisses) {
    auto r = LexOne(spelling);
    EXPECT_EQ(r.token.kind, TokenKind::kIdentifier) << "spelling: " << spelling;
  }
}

}  // namespace
