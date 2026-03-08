// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// §9.3.4: Named sequential block elaborates correctly.
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

// §9.3.4: Named fork block elaborates correctly.
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

// §9.3.4: Named block without end label is OK.
TEST(ParserClause09_03_04, NamedBlockWithoutEndLabelOk) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : myblk\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
