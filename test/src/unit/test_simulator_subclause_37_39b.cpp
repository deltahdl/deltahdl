#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ModulePathRulesOfARun : public VpiDesignRun {
 protected:
  void RunEveryTop(const std::string& src) {
    RtlirDesign* design = ElaborateSrcAllTops(src, f_);
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.has_errors);
    LowerAndRun(design, f_);
  }

  static std::vector<vpiHandle> PathsOf(const char* inst) {
    return ObjectsOf(vpiModPath, By(inst));
  }

  static vpiHandle OnlyTerm(int relation, vpiHandle path) {
    const std::vector<vpiHandle> kTerms = ObjectsOf(relation, path);
    return kTerms.size() == 1 ? kTerms[0] : nullptr;
  }

  static std::string NameOf(vpiHandle obj) {
    if (obj == nullptr) return "";
    const char* name = vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && vpi_compare_objects(a, b) == 1;
  }
};

constexpr const char* kEdgePaths =
    "module m(input clk, input s, input d, output q, output r);\n"
    "  specify\n"
    "    (posedge clk *> (q +: d)) = 1;\n"
    "    if (s) (posedge clk => (r : d)) = 2;\n"
    "    (posedge clk => (q -: d)) = 3;\n"
    "  endspecify\n"
    "endmodule\n"
    "module top; reg clk, s, d; wire q, r; m m1(clk, s, d, q, r); endmodule\n";

TEST_F(ModulePathRulesOfARun, AnEdgeSensitiveFullPathIsAFullPath) {
  Run(kEdgePaths);
  const std::vector<vpiHandle> kPaths = PathsOf("top.m1");
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(vpi_get(vpiPathType, kPaths[0]), vpiPathFull);
  EXPECT_EQ(vpi_get(vpiPathType, kPaths[1]), vpiPathParallel);
}

TEST_F(ModulePathRulesOfARun, AnEdgeSensitiveStateDependentPathHasACondition) {
  Run(kEdgePaths);
  const std::vector<vpiHandle> kPaths = PathsOf("top.m1");
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(NameOf(vpi_handle(vpiCondition, kPaths[1])), "s");
  EXPECT_EQ(vpi_handle(vpiCondition, kPaths[0]), nullptr);
}

TEST_F(ModulePathRulesOfARun, EachDataSourcePolarityIsTheOneWritten) {
  Run(kEdgePaths);
  const std::vector<vpiHandle> kPaths = PathsOf("top.m1");
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(vpi_get(vpiDataPolarity, kPaths[0]), vpiPositive);
  EXPECT_EQ(vpi_get(vpiDataPolarity, kPaths[1]), vpiUnknown);
  EXPECT_EQ(vpi_get(vpiDataPolarity, kPaths[2]), vpiNegative);
}

TEST_F(ModulePathRulesOfARun, APartSelectTermIsAPartSelectOfItsVector) {
  Run("module m(input [3:0] a, output [3:0] b);\n"
      "  specify\n"
      "    (a[1:0] *> b[3:2]) = 1;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top; reg [3:0] a; wire [3:0] b; m m1(a, b); endmodule\n");
  const std::vector<vpiHandle> kPaths = PathsOf("top.m1");
  ASSERT_EQ(kPaths.size(), 1u);
  struct Expected {
    int relation;
    const char* vector;
    int left;
    int right;
  };
  for (const Expected& want : {Expected{vpiModPathIn, "a", 1, 0},
                               Expected{vpiModPathOut, "b", 3, 2}}) {
    vpiHandle expr = vpi_handle(vpiExpr, OnlyTerm(want.relation, kPaths[0]));
    ASSERT_NE(expr, nullptr) << want.vector;
    EXPECT_EQ(vpi_get(vpiType, expr), vpiPartSelect) << want.vector;
    EXPECT_EQ(NameOf(vpi_handle(vpiParent, expr)), want.vector);
    EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, expr)), want.left);
    EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, expr)), want.right);
  }
}

constexpr const char* kInModule =
    "module m(input a, output y);\n"
    "  specify (a => y) = 1; endspecify\n"
    "endmodule\n"
    "module top; reg a; wire y; m m1(a, y); endmodule\n";

TEST_F(ModulePathRulesOfARun, APathInAModuleReachesItsInstanceBothWays) {
  Run(kInModule);
  const std::vector<vpiHandle> kPaths = PathsOf("top.m1");
  ASSERT_EQ(kPaths.size(), 1u);
  EXPECT_TRUE(Same(vpi_handle(vpiModule, kPaths[0]), By("top.m1")));
  EXPECT_TRUE(Same(vpi_handle(vpiInstance, kPaths[0]), By("top.m1")));
}

TEST_F(ModulePathRulesOfARun, EachTopIteratesOnlyItsOwnPaths) {
  RunEveryTop(
      "module ta(input a, output y);\n"
      "  specify (a => y) = 1; endspecify\n"
      "endmodule\n"
      "module tb(input a, b, output y, z);\n"
      "  specify (a => y) = 2; (b => z) = 3; endspecify\n"
      "endmodule\n");
  const std::vector<vpiHandle> kOfA = PathsOf("ta");
  const std::vector<vpiHandle> kOfB = PathsOf("tb");
  ASSERT_EQ(kOfA.size(), 1u);
  ASSERT_EQ(kOfB.size(), 2u);
  EXPECT_TRUE(Same(vpi_handle(vpiInstance, kOfA[0]), By("ta")));
  for (vpiHandle path : kOfB) {
    EXPECT_TRUE(Same(vpi_handle(vpiInstance, path), By("tb")));
  }
}

}  // namespace
}  // namespace delta
