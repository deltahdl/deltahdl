#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kLeaf =
    "module leaf #(parameter int Q = 5) ();\n"
    "  initial $display(\"%m Q %0d\", Q);\n"
    "endmodule\n";

std::string WithLeaf(const std::string& rest) { return kLeaf + rest; }

constexpr const char* kConditionalMid =
    "module mid #(parameter int EN = 0) ();\n"
    "  if (EN == 1) begin : g\n"
    "    leaf l();\n"
    "  end\n"
    "endmodule\n";

TEST(DeferredDefparam, TargetInAConditionalBlockADefparamEnables) {
  const char* const kTops[] = {
      "module top;\n  mid m();\n  defparam m.EN = 1;\n"
      "  defparam m.g.l.Q = 7;\nendmodule\n",
      "module top;\n  mid m();\n  defparam m.g.l.Q = 7;\n"
      "  defparam m.EN = 1;\nendmodule\n",
  };
  for (const char* top : kTops) {
    SCOPED_TRACE(top);
    SimFixture f;
    EXPECT_EQ(RunCapture(WithLeaf(std::string(kConditionalMid) + top), f),
              "top.m.g.l Q 7\n");
    EXPECT_EQ(f.diag.ErrorCount(), 0u);
  }
}

TEST(DeferredDefparam, TargetInALoopIterationADefparamBoundCreates) {
  SimFixture f;
  std::string out =
      RunCapture(WithLeaf("module mid #(parameter int N = 0) ();\n"
                          "  for (genvar i = 0; i < N; i = i + 1) begin : g\n"
                          "    leaf l();\n"
                          "  end\n"
                          "endmodule\n"
                          "module top;\n"
                          "  mid m();\n"
                          "  defparam m.N = 3;\n"
                          "  defparam m.g[2].l.Q = 7;\n"
                          "endmodule\n"),
                 f);
  EXPECT_NE(out.find("top.m.g[0].l Q 5\n"), std::string::npos);
  EXPECT_NE(out.find("top.m.g[1].l Q 5\n"), std::string::npos);
  EXPECT_NE(out.find("top.m.g[2].l Q 7\n"), std::string::npos);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(DeferredDefparam, TargetInACaseAlternativeADefparamSelects) {
  SimFixture f;
  EXPECT_EQ(RunCapture(WithLeaf("module mid #(parameter int SEL = 0) ();\n"
                                "  case (SEL)\n"
                                "    1: begin : g\n"
                                "      leaf l();\n"
                                "    end\n"
                                "    default: begin : h\n"
                                "    end\n"
                                "  endcase\n"
                                "endmodule\n"
                                "module top;\n"
                                "  mid m();\n"
                                "  defparam m.SEL = 1;\n"
                                "  defparam m.g.l.Q = 7;\n"
                                "endmodule\n"),
                       f),
            "top.m.g.l Q 7\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(DeferredDefparam, TargetTwoGeneratedLevelsDown) {
  SimFixture f;
  EXPECT_EQ(RunCapture(WithLeaf("module mid2 #(parameter int EN2 = 0) ();\n"
                                "  if (EN2 == 1) begin : h\n"
                                "    leaf l();\n"
                                "  end\n"
                                "endmodule\n"
                                "module mid #(parameter int EN = 0) ();\n"
                                "  if (EN == 1) begin : g\n"
                                "    mid2 m2();\n"
                                "  end\n"
                                "endmodule\n"
                                "module top;\n"
                                "  mid m();\n"
                                "  defparam m.g.m2.h.l.Q = 7;\n"
                                "  defparam m.g.m2.EN2 = 1;\n"
                                "  defparam m.EN = 1;\n"
                                "endmodule\n"),
                       f),
            "top.m.g.m2.h.l Q 7\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(DeferredDefparam, TargetNamedFromASeparateTopModule) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(WithLeaf(std::string(kConditionalMid) +
                                       "module top;\n"
                                       "  mid m();\n"
                                       "  defparam m.EN = 1;\n"
                                       "endmodule\n"
                                       "module setter;\n"
                                       "  defparam top.m.g.l.Q = 7;\n"
                                       "endmodule\n"),
                              f),
            "top.m.g.l Q 7\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
