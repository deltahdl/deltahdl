#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, ImplicitNetOnAssignLhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];

  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      found = true;
      EXPECT_EQ(n.width, 1) << "implicit net should be scalar";
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

TEST(Elaboration, ImplicitNetOnInstancePort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found_x = false;
  bool found_y = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") found_x = true;
    if (n.name == "y") found_y = true;
  }
  EXPECT_TRUE(found_x) << "implicit net 'x' not created";
  EXPECT_TRUE(found_y) << "implicit net 'y' not created";
}

// §6.10: Implicit nets on instance ports are scalar (width 1).
TEST(Elaboration, ImplicitNetOnInstancePortIsScalar) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  for (const auto& n : mod->nets) {
    if (n.name == "x") EXPECT_EQ(n.width, 1u);
    if (n.name == "y") EXPECT_EQ(n.width, 1u);
  }
}

// §6.10: Implicit net uses default_nettype (tri instead of wire).
TEST(Elaboration, ImplicitNetUsesDefaultNettype) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module top;\n"
                           "  assign w = 1'b0;\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = NetType::kTri;
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      found = true;
      EXPECT_EQ(n.net_type, NetType::kTri);
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

// §6.10: Existing declared net is not duplicated by implicit declaration.
TEST(Elaboration, ExplicitNetNotDuplicatedByImplicit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "w") ++count;
  }
  EXPECT_EQ(count, 1) << "net 'w' should not be duplicated";
}

TEST(Elaboration, ImplicitNetNone_Error) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module top;\n"
                           "  assign w = 1'b1;\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
