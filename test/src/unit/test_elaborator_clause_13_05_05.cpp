#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaborationSyntax, TaskCallWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd1;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidFunctionWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd1;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, NonvoidFunctionWithoutParensError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int get_val; return 1; endfunction\n"
      "  initial get_val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, TaskAllDefaultsWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x(int v = 42);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     VoidFunctionAllDefaultsWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x(int v = 42);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
