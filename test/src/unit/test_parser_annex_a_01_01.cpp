#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
}

}  // namespace
