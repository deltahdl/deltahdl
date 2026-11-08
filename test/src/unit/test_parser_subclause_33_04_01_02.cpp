#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConfigDefaultClause, DefaultUseClauseRejected) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default use work.alt;\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "not through a use clause", 3, "33.4.1.2"));
}

TEST(ConfigDefaultClause, DefaultUseClauseIsTheOnlyReport) {
  auto r = Parse(
      "config c;\n"
      "  design work.top;\n"
      "  default use work.alt;\n"
      "  cell adder liblist work;\n"
      "endconfig\n"
      "module top;\n"
      "endmodule\n");
  EXPECT_EQ(r.diags.size(), 1u);
  EXPECT_TRUE(
      ReportedError(r.diags, "not through a use clause", 3, "33.4.1.2"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
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
