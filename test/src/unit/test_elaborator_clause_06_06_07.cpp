#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(NettypeElaboration,UserDefinedNettypeCreatesNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];

  bool found_net = false;
  for (auto& net : mod->nets) {
    if (net.name == "x") found_net = true;
  }
  EXPECT_TRUE(found_net);
}

TEST(NettypeElaboration,UserDefinedNettypeArrayCreatesNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic mynet;\n"
      "  mynet x [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration,NettypeDeclRegistersType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(NettypeElaboration, NettypeNotInVariables) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];

  bool found_var = false;
  for (const auto& v : mod->variables) {
    if (v.name == "x") found_var = true;
  }
  EXPECT_FALSE(found_var) << "nettype-declared net must not appear in variables";
}

TEST(NettypeElaboration, NettypeWithStructCreatesNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wT;\n"
      "  wT sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];

  bool found_net = false;
  for (const auto& n : mod->nets) {
    if (n.name == "sig") found_net = true;
  }
  EXPECT_TRUE(found_net);
}

TEST(NettypeElaboration, NettypeAliasCreatesNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef real TR[5];\n"
      "  nettype TR wTR;\n"
      "  nettype wTR alias_net;\n"
      "  alias_net sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];

  bool found_net = false;
  for (const auto& n : mod->nets) {
    if (n.name == "sig") found_net = true;
  }
  EXPECT_TRUE(found_net);
}

TEST(NettypeElaboration, ContAssignIndexingNettypeNetIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "  assign x[0] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(NettypeElaboration, ContAssignWholeNettypeNetIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "  assign x = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
