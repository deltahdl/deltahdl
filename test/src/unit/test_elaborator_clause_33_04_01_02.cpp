#include "fixture_elaborator.h"

namespace {

// §33.4.1.2 item 3: there cannot be more than one default clause per
// config (for the liblist expansion clause, since use is forbidden by
// item 2).  Two `default liblist ...` rules in the same config must be
// rejected.
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

// Positive control: a single default-liblist rule does not trigger the
// duplicate diagnostic.
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

}  // namespace
