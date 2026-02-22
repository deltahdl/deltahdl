// §25.5: Modports

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// These unit tests embed SystemVerilog source as inline C++ string literals
// rather than loading external .sv files. This is intentional: each test is
// fully self-contained with the input source and structural assertions in one
// place, so a reader can understand what is being tested without
// cross-referencing a second file. When a test fails, the input and expected
// AST shape are visible together in the test output. Integration and
// conformance testing uses external .sv files instead: the CHIPS Alliance
// sv-tests suite validates broad language coverage, and the sim-tests under
// test/src/e2e/ verify end-to-end simulation behavior against .expected output
// files. This inline pattern is standard practice for compiler parser unit
// tests (used by LLVM, Clang, rustc, etc.).
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

struct StructMemberExpected {
  const char *name;
  DataTypeKind type_kind;
};

struct ModportPortExpected {
  Direction dir;
  const char *name;
};

static void VerifyModportPorts(const std::vector<ModportPort> &ports,
                               const ModportPortExpected expected[],
                               size_t count) {
  ASSERT_EQ(ports.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(ports[i].name, expected[i].name) << "port " << i;
  }
}

namespace {

TEST(Parser, InterfaceWithModport) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] data;\n"
      "  modport master(output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1);
  auto *mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "master");
  ModportPortExpected expected[] = {{Direction::kOutput, "data"}};
  VerifyModportPorts(mp->ports, expected, std::size(expected));
}

TEST(Parser, ModportMultipleGroups) {
  auto r = Parse(
      "interface bus;\n"
      "  logic addr;\n"
      "  logic data;\n"
      "  modport slave(input addr, input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "slave");
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
}

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// Returns true if any item matches the given kind and name.
bool HasItemKindNamed(const std::vector<ModuleItem *> &items,
                      ModuleItemKind kind, std::string_view name) {
  for (auto *item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

// non_port_interface_item ::= modport_declaration
TEST(SourceText, NonPortInterfaceItemModport) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport master(input clk, output data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
}

}  // namespace
