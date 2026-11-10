#include <gtest/gtest.h>

#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

TEST(ImplicitDeclaration, ImplicitNetOnAssignLhs) {
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

TEST(ImplicitDeclaration, ImplicitNetOnInstancePort) {
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

TEST(ImplicitDeclaration, ExplicitNetNotDuplicatedByImplicit) {
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

TEST(ImplicitDeclaration, ImplicitNetDefaultTypeIsWire) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      EXPECT_EQ(n.net_type, NetType::kWire);
    }
  }
}

TEST(ImplicitDeclaration, ImplicitNetBelongsToInnermostScope) {
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
  auto* top = design->top_modules[0];
  bool x_in_top = false;
  bool y_in_top = false;
  for (const auto& n : top->nets) {
    if (n.name == "x") x_in_top = true;
    if (n.name == "y") y_in_top = true;
  }
  EXPECT_TRUE(x_in_top) << "implicit net 'x' should be in top";
  EXPECT_TRUE(y_in_top) << "implicit net 'y' should be in top";

  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  for (const auto& n : child->nets) {
    EXPECT_NE(n.name, "x") << "'x' should not be in child";
    EXPECT_NE(n.name, "y") << "'y' should not be in child";
  }
}

TEST(ImplicitDeclaration, ImplicitNetForbiddenUnderNone) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'w' forbidden by", 2, "22.8"));
}

TEST(ImplicitDeclaration, ImplicitNetOnInstancePortForbiddenUnderNone) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module child(input logic a);\n"
                           "endmodule\n"
                           "module top;\n"
                           "  child u0(.a(x));\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'x' forbidden by", 4, "22.8"));
}

TEST(ImplicitDeclaration, ExplicitVarNotDuplicatedByImplicit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int net_count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "w") ++net_count;
  }
  EXPECT_EQ(net_count, 0)
      << "declared variable 'w' should not create an implicit net";
}

TEST(ImplicitDeclaration, ImplicitPortNetTakesPortWidthAndDefaultType) {
  auto net = MakeImplicitPortNet("a", 8, false, NetType::kTri);
  EXPECT_EQ(net.name, "a");
  EXPECT_EQ(net.net_type, NetType::kTri);
  EXPECT_EQ(net.width, 8u);
}

TEST(ImplicitDeclaration, ImplicitPortNetScalarWhenUnsized) {
  auto net = MakeImplicitPortNet("s", 0, false, NetType::kWire);
  EXPECT_EQ(net.width, 1u);
  EXPECT_EQ(net.net_type, NetType::kWire);
}

TEST(ImplicitDeclaration, ImplicitPortNetTakesDeclaredPortExpressionWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->ports) {
    if (p.name == "a") {
      found = true;
      EXPECT_EQ(p.width, 8u)
          << "implicit net should take the port expression declaration width";
    }
  }
  EXPECT_TRUE(found) << "port-expression identifier 'a' not elaborated";
}

TEST(ImplicitDeclaration, ImplicitNetOnPositionalInstancePort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(x, y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found_x = false;
  bool found_y = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") {
      found_x = true;
      EXPECT_EQ(n.width, 1u) << "implicit net should be scalar";
    }
    if (n.name == "y") found_y = true;
  }
  EXPECT_TRUE(found_x) << "implicit net 'x' not created";
  EXPECT_TRUE(found_y) << "implicit net 'y' not created";
}

TEST(ImplicitDeclaration, OtherImplicitNetsAreUnsigned) {
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
      EXPECT_FALSE(n.is_signed) << "implicit net should be unsigned";
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

TEST(ImplicitDeclaration, ImplicitNetOnInstancePortUsesDefaultNettype) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module child(input logic a);\n"
                           "endmodule\n"
                           "module top;\n"
                           "  child u0(.a(x));\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = NetType::kWand;
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  for (const auto& n : mod->nets) {
    if (n.name == "x") {
      EXPECT_EQ(n.net_type, NetType::kWand);
    }
  }
}

TEST(ImplicitDeclaration, DeclaredInstancePortConnectionNotDuplicated) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int x_count = 0;
  int y_count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "x") ++x_count;
    if (n.name == "y") ++y_count;
  }
  EXPECT_EQ(x_count, 1) << "declared net 'x' should not be duplicated";
  EXPECT_EQ(y_count, 1) << "undeclared 'y' should get one implicit net";
}

TEST(ImplicitDeclaration, ImplicitNetOnPrimitiveTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int found = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "y" || n.name == "a" || n.name == "b") {
      ++found;
      EXPECT_EQ(n.width, 1u) << "primitive terminal net should be scalar";
    }
  }
  EXPECT_EQ(found, 3) << "implicit nets for terminals y, a, b not all created";
}

TEST(ImplicitDeclaration, PrimitiveTerminalForbiddenUnderNone) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module top;\n"
                           "  and g1(y, a, b);\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'y' forbidden by", 2, "22.8"));
}

TEST(ImplicitDeclaration, ImplicitNetInAGenerateBlockIsNotAModuleScopeName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 1; i = i + 1) begin : a\n"
      "      assign w = 1'b1;\n"
      "    end\n"
      "    for (i = 0; i < 2; i = i + 1) begin : w\n"
      "      logic x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool w0 = false;
  bool w1 = false;
  for (const auto& v : mod->variables) {
    if (v.name == "w_0_x") w0 = true;
    if (v.name == "w_1_x") w1 = true;
  }
  EXPECT_TRUE(w0) << "generate block array 'w' instance 0 not elaborated";
  EXPECT_TRUE(w1) << "generate block array 'w' instance 1 not elaborated";
}

TEST(ImplicitDeclaration, ExplicitNetAfterImplicitInOneGenerateBlockIsRedecl) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      assign w = 1'b1;\n"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 5, "6.5"));
}

TEST(ImplicitDeclaration, ImplicitNetInALoopGenerateBlockIsNamedPerIteration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin : b\n"
      "      assign w = 1'b1;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int b0 = 0;
  int b1 = 0;
  int bare = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "b_0_w") ++b0;
    if (n.name == "b_1_w") ++b1;
    if (n.name == "w") ++bare;
  }
  EXPECT_EQ(b0, 1) << "iteration 0 should hold one implicit net";
  EXPECT_EQ(b1, 1) << "iteration 1 should hold one implicit net";
  EXPECT_EQ(bare, 0) << "no net belongs to top under the bare name";
}

TEST(ImplicitDeclaration, ExplicitNetNotDuplicatedByImplicitInAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      wire w;\n"
      "      assign w = 1'b1;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "a_w") ++count;
  }
  EXPECT_EQ(count, 1) << "net 'a_w' should not be duplicated";
}

TEST(ImplicitDeclaration,
     TwoReferencesToOneUndeclaredNameInAGenerateBlockDeclareOneNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      assign w = 1'b1;\n"
      "      and g1(y, w, b);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "a_w") ++count;
  }
  EXPECT_EQ(count, 1) << "two references to 'w' should declare one net 'a_w'";
}

TEST(ImplicitDeclaration,
     ModuleScopeNetIsNotRedeclaredByAGenerateBlockReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire w;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      assign w = 1'b1;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int scoped = 0;
  int bare = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "a_w") ++scoped;
    if (n.name == "w") ++bare;
  }
  EXPECT_EQ(scoped, 0) << "block 'a' should declare no net of its own";
  EXPECT_EQ(bare, 1) << "the module's net 'w' should not be duplicated";
}

TEST(
    ImplicitDeclaration,
    NetOfAnEnclosingConditionalGenerateBlockIsNotRedeclaredByANestedReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : b\n"
      "      wire w;\n"
      "      if (1) begin : a\n"
      "        assign w = 1'b1;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int nested = 0;
  int enclosing = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "b_a_w") ++nested;
    if (n.name == "b_w") ++enclosing;
  }
  EXPECT_EQ(nested, 0) << "block 'a' should declare no net of its own";
  EXPECT_EQ(enclosing, 1) << "block 'b' net 'b_w' should not be duplicated";
}

TEST(ImplicitDeclaration,
     NetOfAnEnclosingLoopGenerateBlockIsNotRedeclaredByANestedReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 5; i = i + 1) begin : b\n"
      "      wire w;\n"
      "      if (1) begin : a\n"
      "        assign w = 1'b1;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int nested = 0;
  int enclosing = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "b_4_a_w") ++nested;
    if (n.name == "b_4_w") ++enclosing;
  }
  EXPECT_EQ(nested, 0) << "block 'a' should declare no net of its own";
  EXPECT_EQ(enclosing, 1) << "block 'b' net 'b_4_w' should not be duplicated";
}

TEST(ImplicitDeclaration,
     ImplicitNetInANestedGenerateBlockIsNamedForEveryEnclosingBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : b\n"
      "      if (1) begin : a\n"
      "        assign w = 1'b1;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "b_a_w") ++count;
  }
  EXPECT_EQ(count, 1) << "block 'a' should declare exactly one net 'b_a_w'";
}

TEST(ImplicitDeclaration,
     ParameterOfAGenerateBlockDoesNotSuppressAModuleLevelImplicitNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = 1;\n"
      "    end\n"
      "  endgenerate\n"
      "  assign P = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "P") ++count;
  }
  EXPECT_EQ(count, 1) << "the module scope should declare one net 'P'";
}

TEST(ImplicitDeclaration,
     ParameterOfAGenerateBlockDoesNotSuppressASiblingBlockImplicitNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = 1;\n"
      "    end\n"
      "    if (1) begin : c\n"
      "      assign P = 1'b1;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "c_P") ++count;
  }
  EXPECT_EQ(count, 1) << "block 'c' should declare one net 'c_P'";
}

TEST(ImplicitDeclaration,
     ParameterOfTheModuleStillSuppressesAGenerateBlockImplicitNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter P = 1;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      assign P = 1'b1;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "a_P" || n.name == "P") ++count;
  }
  EXPECT_EQ(count, 0) << "the module's parameter 'P' should suppress the net";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment to parameter 'P'", 5,
                            "10.3"));
}

TEST(ImplicitDeclaration,
     InterfaceProgramAndCheckerInstancePortsForbiddenUnderNone) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "interface i(input logic a);\n"
                           "endinterface\n"
                           "program p(input logic a);\n"
                           "endprogram\n"
                           "checker c(logic a);\n"
                           "endchecker\n"
                           "module top;\n"
                           "  i ii(.a(n1));\n"
                           "  p pp(.a(n2));\n"
                           "  c cc(n3);\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'n1' forbidden by", 8, "22.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'n2' forbidden by", 9, "22.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'n3' forbidden by", 10, "22.8"));
}

TEST(ImplicitDeclaration,
     DISABLED_ProceduralCheckerInstanceDeclaresNoImplicitNet) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "checker c(logic a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  always @(posedge clk) begin\n"
      "    c cc(nproc);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier 'nproc'", 6, "23.9"));
}

}  // namespace
