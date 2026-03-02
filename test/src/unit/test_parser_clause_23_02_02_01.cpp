// §23.2.2.1: Non-ANSI style port declarations

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfInterfaceIdentifiersMultiple) {
  auto r = Parse("module m(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "c");
}

// Verify a 2-port module has expected names and directions.
static void VerifyTwoPortModule(ParseResult& r, const char* n0, Direction d0,
                                const char* n1, Direction d1) {
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, n0);
  EXPECT_EQ(mod->ports[0].direction, d0);
  EXPECT_EQ(mod->ports[1].name, n1);
  EXPECT_EQ(mod->ports[1].direction, d1);
}

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- Non-ANSI port declarations (LRM §23.2.2.1) ---
TEST(ParserSection23, NonAnsiPortsBasic) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(ParserSection23, NonAnsiPortsWithTypesPortA) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ParserSection23, NonAnsiPortsWithTypesPortB) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(ParserSection23, NonAnsiPortsMixed) {
  auto r = Parse(
      "module m(a, b, c, d);\n"
      "  input a, b;\n"
      "  output [3:0] c;\n"
      "  inout d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  struct Expected {
    const char* name;
    Direction dir;
  };
  Expected expected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kInput},
      {"c", Direction::kOutput},
      {"d", Direction::kInout},
  };
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
  EXPECT_NE(mod->ports[2].data_type.packed_dim_left, nullptr);
}

using ProgramParseTest = ProgramTestParse;

TEST(ParserSection23, Sec23_2_2_NonAnsiPortDeclarations) {
  // Non-ANSI style: port list + separate direction declarations
  auto r = Parse(
      "module m (a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Variants with packed types and inout
  EXPECT_TRUE(
      ParseOk("module m (a, d); input [15:0] a; inout [7:0] d; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m (a, b); inout [7:0] a; inout [7:0] b; endmodule\n"));
}

// =========================================================================
// LRM section 23.2.2.1: Non-ANSI port declarations
// =========================================================================
TEST(ParserSection23, NonAnsiInoutPort) {
  auto r = Parse(
      "module m(bus);\n"
      "  inout [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

}  // namespace
