// §5.3: White space

#include "fixture_parser.h"

using namespace delta;

namespace {

// =========================================================================
// White space as token delimiter
// =========================================================================
// Tab, newline, and space are all equivalent token delimiters.
TEST(ParserCh501, Sec5_1_WhitespaceTabDelimiter) {
  // Tabs instead of spaces between all tokens.
  EXPECT_TRUE(ParseOk("module\tt;\tlogic\ta;\tendmodule"));
}

}  // namespace
