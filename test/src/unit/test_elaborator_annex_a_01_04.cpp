#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ElaborationSeverityTaskElab, InfoDoesNotCauseError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"build info\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, WarningDoesNotCauseError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $warning(\"potential issue\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, FatalValidFinishNumbers) {
  for (int fn = 0; fn <= 2; ++fn) {
    ElabFixture f;
    auto src = "module m; $fatal(" + std::to_string(fn) + "); endmodule\n";
    auto* design = Elaborate(src, f);
    ASSERT_NE(design, nullptr);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "elaboration FATAL in scope 'm'", 1, "20.10.1"))
        << "finish_number " << fn;
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "finish_number must be 0, 1, or 2", 1, "20.10"))
        << "finish_number " << fn << " should be valid";
  }
}

TEST(ElaborationSeverityTaskElab, FatalInvalidFinishNumber) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "finish_number must be 0, 1, or 2", 2, "20.10"));
}

TEST(ElaborationSeverityTaskElab, FatalNoArgsIsValid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "elaboration FATAL in scope 'm'", 2, "20.10.1"));
}

TEST(ElaborationSeverityTaskElab, FatalFirstArgumentIsAFinishNumber) {
  for (const char* call :
       {"$fatal(\"bad width\");", "$fatal(P, \"bad\");", "$fatal(-1);"}) {
    ElabFixture f;
    Elaborate(std::string("module m;\n  localparam int P = 1;\n  ") + call +
                  "\nendmodule\n",
              f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the first argument of $fatal is a "
                              "finish_number, 0, 1 or 2",
                              3, "A.1.4"))
        << call;
  }
}

TEST(ElaborationSeverityTaskElab, FatalWithAFinishNumberAndMessageIsValid) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  $fatal(1, \"bad\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the first argument of $fatal is a "
                             "finish_number, 0, 1 or 2",
                             2, "A.1.4"));
}

int BoundInIteration(const RtlirDesign* design, std::string_view simple,
                     int64_t index, std::string_view bound) {
  int count = 0;
  for (const auto& ch : design->top_modules[0]->children) {
    if (ch.simple_inst_name != simple || ch.resolved == nullptr) continue;
    if (ch.gen_block_path.empty() || ch.gen_block_path.back().index != index) {
      continue;
    }
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == bound) ++count;
    }
  }
  return count;
}

constexpr const char* kBindTargets =
    "module chk; endmodule\n"
    "module leaf; endmodule\n"
    "module top;\n"
    "  for (genvar i = 0; i < 2; i++) begin : g\n"
    "    leaf v ();\n"
    "  end\n"
    "endmodule\n";

TEST(BindDirectiveElab, ABindTargetSelectNamesOneInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      std::string(kBindTargets) + "bind top.g[1].v chk c2();\n", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInIteration(design, "v", 1, "c2"), 1);
  EXPECT_EQ(BoundInIteration(design, "v", 0, "c2"), 0);
}

TEST(BindDirectiveElab, AnInstanceListEntrySelectNamesOneInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      std::string(kBindTargets) + "bind leaf : top.g[1].v chk c3();\n", f,
      "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInIteration(design, "v", 1, "c3"), 1);
  EXPECT_EQ(BoundInIteration(design, "v", 0, "c3"), 0);
}

TEST(BindDirectiveElab, ABindTargetSelectByAVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module chk; endmodule\n"
      "module leaf; endmodule\n"
      "module top;\n"
      "  int k;\n"
      "  leaf u[0:1] ();\n"
      "endmodule\n"
      "bind top.u[top.k] chk c();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a bind target selects with an expression that is "
                            "not constant",
                            7, "A.1.4"));
}

TEST(BindDirectiveElab, ABindTargetSelectByAParameterSelects) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module chk; endmodule\n"
      "module leaf; endmodule\n"
      "module top;\n"
      "  parameter int P = 1;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    leaf v ();\n"
      "  end\n"
      "  bind g[P].v chk c();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInIteration(design, "v", 1, "c"), 1);
  EXPECT_EQ(BoundInIteration(design, "v", 0, "c"), 0);
}

}  // namespace
