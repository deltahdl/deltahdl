#include <gtest/gtest.h>

#include "lexer/string_escape.h"

using namespace delta;

// --- §5.9.1: Special characters in strings ---

TEST(LexerCh50901, OctalMaxDigits) {
  // §5.9.1: Octal escape consumes 1 to 3 digits; \1019 -> 'A' then '9'.
  EXPECT_EQ(InterpretStringEscapes(R"(\1019)"), "A9");
}
