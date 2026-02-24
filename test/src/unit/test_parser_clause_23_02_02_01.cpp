// §23.2.2.1: Non-ANSI style port declarations

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// Module with non-ANSI header (list_of_ports).
TEST(SourceText, ModuleNonAnsiHeader) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// Non-ANSI list_of_ports: port with multiple ports and body declarations
TEST(SourceText, NonAnsiMultiplePorts) {
  auto r = Parse(
      "module m(a, b, c);\n"
      "  input [7:0] a;\n"
      "  output [7:0] b;\n"
      "  inout c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
}

// Non-ANSI port_declaration with shared type: input [7:0] a, b;
TEST(SourceText, NonAnsiSharedType) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a, b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
}

TEST(ParserA212, InoutNonAnsi) {
  auto r = Parse("module m(a); inout wire [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

TEST(ParserA212, InputNonAnsiMultiple) {
  // Non-ANSI: input net_port_type list_of_port_identifiers (comma list)
  auto r = Parse("module m(a, b); input wire [7:0] a, b; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto &port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

TEST(ParserA212, OutputNonAnsi) {
  auto r = Parse("module m(q); output reg q; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ParserA212, OutputNonAnsiUnpackedDim) {
  // Non-ANSI: list_of_port_identifiers with unpacked_dimension
  auto r = Parse("module m(q); output logic q [3:0]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

}  // namespace
