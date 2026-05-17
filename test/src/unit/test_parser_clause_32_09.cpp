#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, SdfAnnotateAllSevenArgumentsParse) {
  auto* unit = Parse(R"(
    module top;
      sub u1();
      initial $sdf_annotate("timing.sdf", u1, "cfg.cfg", "annot.log",
                            "MAXIMUM", "1.0:1.0:1.0", "FROM_MTM");
    endmodule
    module sub; endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ApiParseTest, SdfAnnotateAcceptsArrayIndexedScope) {
  auto* unit = Parse(R"(
    module top;
      sub u1[7:0]();
      initial $sdf_annotate("timing.sdf", u1[3]);
    endmodule
    module sub; endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ApiParseTest, SdfAnnotateAcceptsHierarchicalScope) {
  auto* unit = Parse(R"(
    module top;
      sub dut();
      initial $sdf_annotate("timing.sdf", top.dut);
    endmodule
    module sub; endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ApiParseTest, SdfAnnotateAcceptsStringDataTypeAsSdfFile) {
  auto* unit = Parse(R"(
    module m;
      string filename;
      initial begin
        filename = "timing.sdf";
        $sdf_annotate(filename);
      end
    endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ApiParseTest, SdfAnnotateAcceptsIntegralDataTypeAsSdfFile) {
  auto* unit = Parse(R"(
    module m;
      bit [8*16-1:0] packed_filename;
      initial begin
        packed_filename = "timing.sdf";
        $sdf_annotate(packed_filename);
      end
    endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ApiParseTest, SdfAnnotateAcceptsOmittedLeadingOptionals) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf", , , , , "1.0:1.0:1.0");
    endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

}
