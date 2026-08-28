#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

namespace {

TEST(PackageImportInHeader, TypedefVisibleInPortType) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m import pkg::byte_t; (input byte_t a, output byte_t b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, WildcardTypedefVisibleInPortType) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [15:0] word_t;\n"
             "endpackage\n"
             "module m import pkg::*; (input word_t a, output word_t b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ConstantVisibleInPortRange) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int W = 8;\n"
             "endpackage\n"
             "module m import pkg::W; (input [W-1:0] a, output [W-1:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ConstantVisibleInParameterDefault) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int DEFAULT_W = 16;\n"
             "endpackage\n"
             "module m import pkg::DEFAULT_W; #(parameter int W = DEFAULT_W) "
             "(input [W-1:0] a);\n"
             "endmodule\n"));
}

// The declared width is what says the header import reached the body
// declaration. Nothing reports an unresolved named type -- EvalTypeWidth in
// src/elaborator/type_eval.cpp answers 0 for a DataTypeKind::kNamed it
// could not resolve and the run carries on -- so an assertion that elaboration
// succeeded holds whether pkg::nibble_t was registered or not. 4 is also not
// the 1 that RtlirVariable::width defaults to.
//
// This is the header half of the pair PackageImport.
// BodyImportedTypedefSizesTheVariable in
// test/src/unit/test_elaborator_subclause_26_03a.cpp completes: §26.4 permits
// the import to stand in the header, and §26.3 decides what importing does, so
// the same declaration is sized the same way whichever form carried it.
TEST(PackageImportInHeader, WildcardImportVisibleInBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "endpackage\n"
      "module m import pkg::*; ();\n"
      "  nibble_t n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* n = FindVar(design, "m", "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 4u);
}

TEST(PackageImportInHeader, ExplicitImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic signed [31:0] sword_t;\n"
             "endpackage\n"
             "module m import pkg::sword_t; ();\n"
             "  sword_t s;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, MultipleHeaderImports) {
  EXPECT_TRUE(
      ElabOk("package a;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "package b;\n"
             "  parameter int N = 4;\n"
             "endpackage\n"
             "module m import a::byte_t, b::N; (input byte_t [N-1:0] data);\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, InterfaceHeaderImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "interface ifc import pkg::*; ();\n"
             "  byte_t data;\n"
             "endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"));
}

// §26.4 lists port declarations explicitly among the places a header import is
// visible, and names the interface as one of the three header kinds. Here the
// imported type names an interface port; resolving that port type proves the
// header import reached the port list, not just the body.
TEST(PackageImportInHeader, InterfaceHeaderImportVisibleInPortType) {
  // A top-level interface (no enclosing module) must still be elaborable, so
  // the test names it as the explicit top rather than relying on ElabOk's
  // module default (§26.4 names the interface among the three header kinds).
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "interface ifc import pkg::byte_t; (input byte_t a);\n"
      "  byte_t shadow;\n"
      "  assign shadow = a;\n"
      "endinterface\n",
      f, "ifc");
  EXPECT_FALSE(f.has_errors);
}

// Mirrors the §26.4 example: a single header mixes an explicit import with a
// wildcard import from a second package, and both imported types are consumed
// by ports while an imported-independent parameter sits between them.
TEST(PackageImportInHeader, MixedExplicitAndWildcardHeaderImports) {
  EXPECT_TRUE(
      ElabOk("package A;\n"
             "  typedef logic [7:0] opcode_t;\n"
             "endpackage\n"
             "package B;\n"
             "  typedef logic flag_t;\n"
             "endpackage\n"
             "module m import A::opcode_t, B::*; #(parameter int WIDTH = 4)\n"
             "    (input opcode_t a, output flag_t ok);\n"
             "  assign ok = |a;\n"
             "endmodule\n"));
}

// §26.4 names module, interface, AND program as headers whose imports are
// visible throughout the declaration, including in port declarations. The
// imported type names the port and a body variable; if header import did not
// make it visible, elaboration would fail to resolve the type.
TEST(PackageImportInHeader, ProgramHeaderImportVisibleInPortAndBody) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "program p import pkg::byte_t; (input byte_t a);\n"
      "  byte_t local_b;\n"
      "  initial local_b = a;\n"
      "endprogram\n",
      f, "p");
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImportInHeader, WildcardProgramHeaderImportVisibleInPort) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n"
      "program p import pkg::*; (input word_t a, output word_t b);\n"
      "  initial b = a;\n"
      "endprogram\n",
      f, "p");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
