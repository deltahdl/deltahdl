

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

}  // namespace
