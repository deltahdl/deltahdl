#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ConfigDefaultClause, DefaultUseClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default use work.alt;\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigDefaultClause, DefaultLiblistAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
