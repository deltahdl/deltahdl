// Tests for §6.10 "Implicit declarations": "In the absence of an explicit
// declaration, an implicit net of default net type shall be assumed" in the
// three circumstances the subclause lists -- a port expression declaration, an
// instance terminal or port connection list, and the left-hand side of a
// continuous assignment.
//
// §6.10 closes by deferring the `default_nettype none case: "See 22.8 for a
// discussion of control of the type for implicitly declared nets with the
// `default_nettype compiler directive." The rejections below therefore name
// §22.8.

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §22.8, not §6.10, is what forbids the implicit net: §6.10 states only when
// one is assumed and sends the reader to §22.8 for the directive that turns
// the assumption off.
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

// The same §22.8 rule reached through an instance port connection rather than
// a continuous assignment, which is a second of the three circumstances §6.10
// lists.
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

// §6.10 (bullet 1): an identifier used in a port expression declaration and not
// separately declared as a net or variable acquires an implicit net whose width
// is the vector width of the port expression declaration. Drive the real
// non-ANSI port syntax of §23.2.2.1 through parse + elaborate — the header
// lists the bare identifier and the body supplies only a direction+range — and
// observe the identifier becoming usable with the declared width, with no
// explicit net declaration and no error. This exercises the port-expression
// case end to end rather than the shared constructor in isolation.
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

// §6.10 (bullet 2, negative + positive): an identifier used in an instance port
// connection list gets an implicit net only if it was not declared previously
// in the scope; a previously declared net is reused (no duplicate implicit
// net), while an undeclared sibling in the same connection list still gets one.
// Drives both the reject path (declared 'x') and the accept path (undeclared
// 'y') through one real instantiation.
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

// Under `default_nettype none an undeclared primitive terminal is an error
// rather than an implicit net, and §22.8 is the subclause the report names --
// the terminal list is the third of the three circumstances §6.10 lists.
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

// §6.10: "The implicit net declaration shall belong to the scope in which the
// net reference appears. For example, if the implicit net is declared by a
// reference in a generate block, then the net is implicitly declared only in
// that generate block." A generate block "comprises a separate scope and a new
// level of hierarchy when it is instantiated" (§27.4, printed page 821), so the
// implicit 'w' below is a declaration of block 'a' and of nothing else, and the
// generate block instance array named 'w' beside it is declared in top. §27.4's
// rule that a block array name shall not conflict with another declaration
// therefore has nothing to fire on.
//
// The elaborator recorded the implicit net under its bare name while naming the
// net itself under the generate prefix, so the bare 'w' outlived block 'a' and
// Elaborator::OpenGenerateForLoop found it: the array was rejected and neither
// of its instances was elaborated.
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

// §6.10 assumes an implicit net only for an identifier that "has not been
// declared previously in the scope", and §23.9 leaves the explicit declaration
// that follows it a second declaration of one name in one scope. This is the
// case the fix above must not lose: recording the implicit net under its bare
// name meant the explicit 'wire w' inside the same block was keyed under the
// block's prefix, matched nothing, and was accepted.
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
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 5, "23.9"));
}

// §6.10 with §27.4: each iteration of a loop generate block is its own scope,
// so the one reference in the shared body declares one implicit net per
// iteration and each carries that iteration's prefix. Nothing is named by the
// bare 'w'.
//
// The absence of a report is the other half of the claim. Elaborator::
// ValidateContAssignIdentLhs reads net_names_ back with the identifier the
// source wrote, so recording the implicit net there under the prefix instead
// would make the second iteration's assignment look like a second assignment to
// a variable and draw §10.3.2.
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

// §6.10 assumes an implicit net only for an identifier that "has not been
// declared previously in the scope where the ... assignment appears", and the
// explicit 'wire w' inside generate block 'a' is that previous declaration.
// Block 'a' therefore holds one net named 'a_w'.
//
// The test fails when mod->nets holds two entries named 'a_w'.
// Elaborator::MaybeCreateImplicitNet in src/elaborator/elaborator_items.cpp
// asks IsNameDeclared about the bare 'w' the source wrote, while the net it
// pushes is named by Elaborator::ScopedName, which prepends the generate block
// prefix 'a_'. Inside a generate block the question and the storage disagree,
// so the declaration the guard is there to find is not found.
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

// §6.10 declares one implicit net for one undeclared identifier in one scope:
// "The implicit net declaration shall belong to the scope in which the net
// reference appears", and only a reference "from outside the generate block or
// in another generate block within the same module" declares another one. Both
// references to 'w' below stand in generate block 'a', so block 'a' holds one
// net named 'a_w'.
//
// The test fails when mod->nets holds two entries named 'a_w'. Two callers of
// Elaborator::MaybeCreateImplicitNet see this one identifier:
// Elaborator::ValidateContAssignIdentLhs in
// src/elaborator/elaborator_cont_assign.cpp for the continuous assignment, and
// CreateImplicitNetsForTerminals in src/elaborator/elaborator_items.cpp for
// the terminal list of gate instance 'g1'. The second pushes a second net
// whenever the guard reads the bare 'w' and the net the first pushed carries
// the prefix Elaborator::ScopedName added.
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

// §6.10 assumes no implicit net for an identifier declared "in any scope whose
// declarations can be directly referenced from" the scope the assignment
// appears in, and the module scope of 'top' is such a scope for generate block
// 'a'. The reference to 'w' inside block 'a' names the module's own net and
// declares nothing, so 'top' holds one net named 'w' and none named 'a_w'.
//
// The test fails when mod->nets holds an entry named 'a_w', which
// Elaborator::MaybeCreateImplicitNet in src/elaborator/elaborator_items.cpp
// pushes if it asks IsNameDeclared only about Elaborator::ScopedName("w") and
// drops the bare 'w' that the module scope declared.
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

// §6.10 assumes no implicit net for an identifier declared "in any scope whose
// declarations can be directly referenced from" the scope the assignment
// appears in, and §23.9 rules that a generate block one level out is such a
// scope: an identifier referenced in a generate block "shall be declared either
// within the ... generate block locally or within a module, interface, program,
// checker, task, function, named block, or generate block that is higher in the
// same branch of the name tree". Block 'b' is higher in the same branch than
// block 'a', so the reference to 'w' inside 'a' names the net 'b' declared and
// declares nothing. The module holds one net named 'b_w' and none named
// 'b_a_w'.
//
// The test fails when mod->nets holds an entry named 'b_a_w', which
// Elaborator::MaybeCreateImplicitNet in src/elaborator/elaborator_items.cpp
// pushes if it asks IsNameDeclared only about Elaborator::ScopedName("w") and
// the bare "w". Those two keys are "b_a_w" and "w" here, and the net block 'b'
// declared is held as "b_w", which neither matches, so a second net shadows it
// and the continuous assignment drives the new one.
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

// The same §6.10 and §23.9 reading where the enclosing scope is a loop generate
// block, whose prefix §27.4 indexes "by adding the '[genvar value]' to the end
// of the generate block identifier" and which the elaborator therefore spells
// with the index in it. The reference to 'w' inside block 'a' names the 'w'
// this iteration of block 'b' declared, so the module holds one net named
// 'b_4_w' and none named 'b_4_a_w'.
//
// The genvar runs from 4 so that no value it takes is also the ordinal of the
// instance the iteration creates, which is 0. A loop starting at zero makes the
// two coincide, and the case then passes whether the prefix is built from the
// index §27.4 names or from the ordinal.
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

// §6.10 rules that "The implicit net declaration shall belong to the scope in
// which the net reference appears" and that "if the implicit net is declared by
// a reference in a generate block, then the net is implicitly declared only in
// that generate block". Nothing declares 'w' here, so the reference in block
// 'a' declares it, and the net belongs to 'a' rather than to 'b' or to the
// module: one net named 'b_a_w'.
//
// This is what the upward walk over the enclosing blocks must not lose. A walk
// that answered that some enclosing scope declared the name would push no net
// at all, and one that named the net for an enclosing block would put the
// declaration in the wrong scope.
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

// §6.10 assumes an implicit net for an identifier not declared "in the scope
// where the continuous assignment statement appears or in any scope whose
// declarations can be directly referenced from" it, and §23.9 lists "Generate
// blocks" among the elements that "define a new scope". The localparam 'P'
// belongs to block 'a' alone, and neither the module scope the assignment
// stands in nor any scope it can reference directly is block 'a', so the
// assignment declares a net named 'P'.
//
// The test fails when mod->nets holds no entry named 'P'. IsParamDeclared in
// src/elaborator/elaborator_items.cpp reads RtlirModule::params, whose entries
// Elaborator::ElaborateParamDecl names bare whatever scope declared them, so a
// question asked with the bare 'P' is answered by block 'a''s localparam and
// Elaborator::MaybeCreateImplicitNet returns without creating anything.
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

// The same reading where the reference stands in a sibling generate block.
// §23.9 rules that an identifier "referenced directly (without a hierarchical
// path)" is declared "locally or within a module, interface, program, checker,
// task, function, named block, or generate block that is higher in the same
// branch of the name tree", and block 'a' is not higher in block 'c''s branch:
// they are siblings. Block 'c' therefore declares a net named 'c_P'.
//
// Neither block is at module level, so the case cannot pass by
// Elaborator::ScopedName being the identity: the keys tested for the reference
// are 'c_P' and 'P', and it is the bare one that reaches block 'a''s
// localparam.
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

// §6.10 assumes no implicit net for an identifier declared "in any scope whose
// declarations can be directly referenced from" the scope the reference stands
// in, and a parameter of the module is such a declaration for every generate
// block in it. The reference in block 'a' names the module's parameter, so no
// net is created under either spelling.
//
// This is the case the fix must not lose. §23.3.3.3 lets any expression drive
// an input port, so a parameter named as a port actual is the expression that
// drives it, and a scalar net created here would shadow the parameter with an
// undriven wire and deliver zero to the port instead.
//
// The claim is about RtlirModule::nets and not about what the source is worth:
// §6.20 leaves a continuous assignment naming a parameter to be rejected
// elsewhere, and this case reads the same whether that report is made or not.
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
}

}  // namespace
