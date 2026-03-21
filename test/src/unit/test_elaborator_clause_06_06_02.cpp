#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UwireElaboration, UwireNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire uw;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "uw");
  EXPECT_EQ(mod->nets[0].net_type, NetType::kUwire);
}

TEST(UwireElaboration, UwireSingleContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UwireElaboration, UwireMultipleContinuousAssignmentsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireNetDeclAssignPlusContinuousAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  uwire w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UwireElaboration, UwireVectorWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  uwire [3:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 4u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kUwire);
}

}  // namespace
