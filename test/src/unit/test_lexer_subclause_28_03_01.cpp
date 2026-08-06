

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_keywords.h"

using namespace delta;

namespace {

TEST(GateKeywordLexing, AllTwentySixKeywords) {
  for (const auto& entry : kGateKeywords) {
    auto r = LexOne(entry.text);
    EXPECT_EQ(r.token.kind, entry.expected) << "keyword: " << entry.text;
  }
}

// §28.3.1 negative form: Table 28-1 fixes the exact spellings that begin a
// gate/switch declaration. A near-miss identifier (a keyword with an extra
// character, a wrong suffix, or the plain word "gate") is NOT one of the 26
// entries, so the lexer must tokenize it as an ordinary identifier rather than
// any gate-keyword token.
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
