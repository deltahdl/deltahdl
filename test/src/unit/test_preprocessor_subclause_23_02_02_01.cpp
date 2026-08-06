#include "fixture_parser.h"

using namespace delta;

namespace {

// §23.2.2.1: the input/output declarations of a non-ANSI header still yield
// both ports when the source is run through the preprocessor before the
// parser. test_parser_subclause_23_02_02_01.cpp covers the direct-parse case.
TEST(NonAnsiStylePortDeclarations, BasicInputOutputThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(NonAnsiStylePortDeclarations, MultiplePorts) {
  auto r = ParseWithPreprocessor(
      "module m(a, b, c);\n"
      "  input [7:0] a;\n"
      "  output [7:0] b;\n"
      "  inout c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
}

TEST(NonAnsiStylePortDeclarations, SharedType) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input [7:0] a, b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
}

// §23.2.2.1: an inout port declared with an explicit net type keeps its
// direction across preprocessing. test_parser_subclause_23_02_02_01.cpp covers
// the direct-parse case.
TEST(NonAnsiStylePortDeclarations, InoutPortThroughPreprocessor) {
  auto r = ParseWithPreprocessor("module m(a); inout wire [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

TEST(NonAnsiStylePortDeclarations, OutputReg) {
  auto r = ParseWithPreprocessor("module m(q); output reg q; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(NonAnsiStylePortDeclarations, OutputUnpackedDim) {
  auto r =
      ParseWithPreprocessor("module m(q); output logic q [3:0]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(NonAnsiStylePortDeclarations, SinglePort) {
  auto r = ParseWithPreprocessor("module m(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
}

TEST(NonAnsiStylePortDeclarations, ExplicitPort) {
  auto r = ParseWithPreprocessor(
      "module m(.a(x));\n"
      "  input x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "a");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
}

TEST(NonAnsiStylePortDeclarations, ConcatenationPort) {
  auto r = ParseWithPreprocessor(
      "module m({c, d});\n"
      "  input c, d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kConcatenation);
}

TEST(NonAnsiStylePortDeclarations, PartSelectPort) {
  auto r = ParseWithPreprocessor(
      "module m(a[7:4], a[3:0]);\n"
      "  input [7:0] a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// §23.2.2.1: a concatenation port and a named port_expression in one header,
// with the referenced names declared in the module body, survive preprocessing.
// test_parser_subclause_23_02_02_01.cpp covers the direct-parse case.
TEST(NonAnsiStylePortDeclarations,
     MixedImplicitAndExplicitPortsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m({c, d}, .e(f));\n"
      "  input c, d, f;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// §23.2.2.1: named ports over a concatenation and a bit-select, mixed with a
// plain port reference and backed by body declarations, survive preprocessing.
// test_parser_subclause_23_02_02_01.cpp covers the direct-parse case.
TEST(NonAnsiStylePortDeclarations,
     ExplicitPortConcatSelectAndImplicitThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m(.a({b, c}), f, .g(h[1]));\n"
      "  input b, c, f;\n"
      "  input [7:0] h;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
}

// §23.2.2.1: the port and net/variable declaration pairs that carry signedness
// between them are unaffected by preprocessing.
// test_parser_subclause_23_02_02_01.cpp covers the direct-parse case.
TEST(NonAnsiStylePortDeclarations, SignednessInheritanceThroughPreprocessor) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module test(a, b, c, d, e, f, g, h);\n"
                              "  input [7:0] a;\n"
                              "  input [7:0] b;\n"
                              "  input signed [7:0] c;\n"
                              "  input signed [7:0] d;\n"
                              "  output [7:0] e;\n"
                              "  output [7:0] f;\n"
                              "  output signed [7:0] g;\n"
                              "  output signed [7:0] h;\n"
                              "  wire signed [7:0] b;\n"
                              "  wire [7:0] c;\n"
                              "  logic signed [7:0] f;\n"
                              "  logic [7:0] g;\n"
                              "endmodule\n"));
}

}  // namespace
