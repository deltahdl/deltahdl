// §3.14: Simulation time units and precision

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
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

namespace {

// ===========================================================================
// §3.14: Timeunit/timeprecision parsing
// ===========================================================================
TEST(Lexical, Timeunit_BasicParse) {
  auto r = Parse("module top;\n"
                 "  timeunit 1ns;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  // Should parse without error. The timeunit decl is consumed.
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Lexical, Timeprecision_BasicParse) {
  auto r = Parse("module top;\n"
                 "  timeprecision 1ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_WithSlash) {
  // timeunit 1ns / 1ps;  (combined form)
  auto r = Parse("module top;\n"
                 "  timeunit 1ns / 1ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_DifferentValues) {
  // Various time unit values
  auto r = Parse("module top;\n"
                 "  timeunit 100us;\n"
                 "  timeprecision 10ns;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Values) {
  // The timeunit/timeprecision values should be stored in ModuleDecl.
  auto r = Parse("module top;\n"
                 "  timeunit 1ns;\n"
                 "  timeprecision 1ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Flags) {
  auto r = Parse("module top;\n"
                 "  timeunit 1ns;\n"
                 "  timeprecision 1ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto *mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
}

} // namespace
