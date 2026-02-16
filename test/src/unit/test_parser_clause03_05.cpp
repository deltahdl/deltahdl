#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3_05 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_05 Parse(const std::string& src) {
  ParseResult3_05 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 3.5 -- Interfaces
// =============================================================================

// §3.5 LRM example: simple_bus interface definition.
// Also covers end label (endinterface : simple_bus) and interface port.
TEST(ParserSection3, Sec3_5_LrmExample) {
  auto r = Parse(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface : simple_bus\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInput);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 5u);
}

// §3.5: "An interface can have parameters, constants, variables"
TEST(ParserSection3, Sec3_5_ParametersConstantsVariables) {
  auto r = Parse(
      "interface ifc #(parameter WIDTH = 8);\n"
      "  localparam DEPTH = 16;\n"
      "  logic [WIDTH-1:0] data;\n"
      "  wire valid;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 2u);
}

// §3.5: "An interface can have ... functions, and tasks"
TEST(ParserSection3, Sec3_5_FunctionsAndTasks) {
  auto r = Parse(
      "interface ifc;\n"
      "  function automatic int get_data;\n"
      "    return 42;\n"
      "  endfunction\n"
      "  task automatic send(input int val);\n"
      "  endtask\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_func = false, has_task = false;
  for (const auto* item : r.cu->interfaces[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl) has_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl) has_task = true;
  }
  EXPECT_TRUE(has_func);
  EXPECT_TRUE(has_task);
}

// §3.5: "an interface can also contain processes (i.e., initial or always
//        procedures) and continuous assignments"
TEST(ParserSection3, Sec3_5_ProcessesAndContinuousAssign) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic sig_a, sig_b;\n"
      "  initial sig_a = 0;\n"
      "  always @(sig_a) sig_b = ~sig_a;\n"
      "  assign sig_b = sig_a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_initial = false, has_always = false, has_assign = false;
  for (const auto* item : r.cu->interfaces[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) has_initial = true;
    if (item->kind == ModuleItemKind::kAlwaysBlock) has_always = true;
    if (item->kind == ModuleItemKind::kContAssign) has_assign = true;
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_always);
  EXPECT_TRUE(has_assign);
}

// §3.5: "the modport construct is provided"
TEST(ParserSection3, Sec3_5_Modport) {
  auto r = Parse(
      "interface myif;\n"
      "  logic [7:0] data;\n"
      "  logic valid, ready;\n"
      "  modport master (output data, output valid, input ready);\n"
      "  modport slave (input data, input valid, output ready);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "slave");
}
