// §9.3.4: Block names

#include "fixture_parser.h"

using namespace delta;

namespace {

// Checker with end label.
TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
