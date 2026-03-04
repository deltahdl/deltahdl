// Annex A.1.1: Library source text

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// A null library description (bare semicolon) is valid.
TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
}

}  // namespace
