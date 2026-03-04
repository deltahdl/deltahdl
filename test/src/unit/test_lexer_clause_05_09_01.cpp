#include <gtest/gtest.h>

#include "lexer/string_escape.h"

using namespace delta;

TEST(LexerCh50901, OctalMaxDigits) {

  EXPECT_EQ(InterpretStringEscapes(R"(\1019)"), "A9");
}
