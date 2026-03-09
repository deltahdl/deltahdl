

#include "fixture_elaborator.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ElabClause09_03_04, NamedSeqBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin : blk\n"
      "    x = 42;\n"
      "  end : blk\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_03_04, NamedForkBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork : par_blk\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join : par_blk\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
