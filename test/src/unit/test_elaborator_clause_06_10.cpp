#include "common/types.h"
#include "fixture_elaborator.h"

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

TEST(ImplicitDeclaration, ImplicitNetOnInstancePortIsScalar) {
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
    if (n.name == "x") {
      EXPECT_EQ(n.width, 1u);
    }
    if (n.name == "y") {
      EXPECT_EQ(n.width, 1u);
    }
  }
}

TEST(ImplicitDeclaration, ImplicitNetUsesDefaultNettype) {
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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

// §6.10: an identifier used in a port expression declaration takes an implicit
// net of the default net type, sized to the vector width of the port expression
// declaration. The kind/width half of the implicit-net rule that §6.10 shares
// with §23.2.2.1.
TEST(ImplicitDeclaration, ImplicitPortNetTakesPortWidthAndDefaultType) {
  auto net = MakeImplicitPortNet("a", /*port_width=*/8,
                                 /*port_is_signed=*/false, NetType::kTri);
  EXPECT_EQ(net.name, "a");
  EXPECT_EQ(net.net_type, NetType::kTri);
  EXPECT_EQ(net.width, 8u);
}

// §6.10: a port expression with no declared vector width yields a scalar
// implicit net, matching the scalar nets assumed for instance terminals and
// continuous-assignment targets.
TEST(ImplicitDeclaration, ImplicitPortNetScalarWhenUnsized) {
  auto net = MakeImplicitPortNet("s", /*port_width=*/0,
                                 /*port_is_signed=*/false, NetType::kWire);
  EXPECT_EQ(net.width, 1u);
  EXPECT_EQ(net.net_type, NetType::kWire);
}

// §6.10: an undeclared identifier in the port connection list of a module
// instance gets an implicit scalar net, whether the connection is named or
// ordered. This observes the ordered (positional) connection path.
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

// §23.2.2.1: every implicit net other than a signed port's net is considered
// unsigned. Observes the default signedness of the implicit net that §6.10
// materializes on the real continuous-assignment path (not just the shared
// constructor in isolation).
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

// §6.10: an undeclared identifier appearing in the terminal list of a primitive
// (gate) instance gets an implicit scalar net of the default net type.
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

// §6.10: under `default_nettype none`, an undeclared primitive terminal is an
// error rather than an implicit net.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
