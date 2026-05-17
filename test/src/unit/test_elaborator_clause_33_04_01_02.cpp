#include "fixture_elaborator.h"

namespace {

TEST(ConfigDefaultClause, DuplicateDefaultLiblistRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "  default liblist other;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigDefaultClause, SingleDefaultLiblistAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

}
