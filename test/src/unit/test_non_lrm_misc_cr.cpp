// Non-LRM tests

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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
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

// Clocking block within a program.
TEST(ParserSection19, ClockingBlock_InProgram) {
  EXPECT_TRUE(
      ParseOk("program test_prog(input clk, input [7:0] data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

// Global clocking block (no signals allowed inside).
TEST(ParserSection19, GlobalClocking_Basic) {
  auto r = Parse(
      "module t;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(item->name, "gclk");
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
}

// Global clocking with compound event expression (or).
TEST(ParserSection19, GlobalClocking_CompoundEvent) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  global clocking sys @(clk1 or clk2);\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Global clocking with end label.
TEST(ParserSection19, GlobalClocking_EndLabel) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  global clocking gclk @(posedge clk);\n"
              "  endclocking : gclk\n"
              "endmodule\n"));
}

// Full LRM example: bus clocking block with default skew,
// hierarchical expression, per-signal overrides, and 1step.
TEST(ParserSection19, FullExample_BusClockingBlock) {
  auto r = Parse(
      "module t;\n"
      "  clocking bus @(posedge clock1);\n"
      "    default input #10ns output #2ns;\n"
      "    input data, ready, enable = top.mem1.enable;\n"
      "    output negedge ack;\n"
      "    input #1step addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(item->name, "bus");
  // Note: default skew is parsed but not stored in the AST.
  ASSERT_EQ(item->clocking_signals.size(), 5u);

  EXPECT_EQ(item->clocking_signals[0].name, "data");
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[1].name, "ready");
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[2].name, "enable");
  EXPECT_EQ(item->clocking_signals[2].direction, Direction::kInput);
  ASSERT_NE(item->clocking_signals[2].hier_expr, nullptr);
  EXPECT_EQ(item->clocking_signals[3].name, "ack");
  EXPECT_EQ(item->clocking_signals[3].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[3].skew_edge, Edge::kNegedge);
  EXPECT_EQ(item->clocking_signals[4].name, "addr");
  EXPECT_EQ(item->clocking_signals[4].direction, Direction::kInput);
}

// Clocking block inside an interface with modport.
TEST(ParserSection19, InterfaceClockingWithModport) {
  EXPECT_TRUE(
      ParseOk("interface bus_A (input clk);\n"
              "  logic [15:0] data;\n"
              "  logic write;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output write;\n"
              "  endclocking\n"
              "  modport test (input data, output write, input clk);\n"
              "  modport dut (output data, input write, input clk);\n"
              "endinterface\n"));
}

// class_item ::= { attribute_instance } covergroup_declaration
TEST(SourceText, ClassCovergroupDecl) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kCovergroup);
  EXPECT_EQ(members[0]->name, "cg");
}

TEST(ParserA211, CovergroupDecl_InClass) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  covergroup cg;\n"
              "  endgroup\n"
              "endclass\n"));
}

// =============================================================================
// A.1.4 Module items
// =============================================================================
// severity_system_task: $fatal with finish_number and arguments.
TEST(SourceText, ElabSeverityFatal) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"assertion failed\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kElabSystemTask);
}

// severity_system_task: all four forms ($fatal, $error, $warning, $info).
TEST(SourceText, ElabSeverityAllForms) {
  auto r = Parse(
      "module m;\n"
      "  $fatal;\n"
      "  $error(\"err\");\n"
      "  $warning(\"warn\");\n"
      "  $info;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 4u);
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(r.cu->modules[0]->items[i]->kind,
              ModuleItemKind::kElabSystemTask);
  }
}

// ============================================================================
// Test helpers
// ============================================================================
struct SysCallFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr* MakeSysCall(Arena& arena, std::string_view name,
                         std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr* MakeIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr* MakeStrLit(Arena& arena, std::string_view text) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  // Store with surrounding quotes, matching parser convention.
  auto len = text.size() + 2;
  char* buf = static_cast<char*>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

static Expr* MakeIdent(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// ============================================================================
// §20.8.1 — $clog2
// ============================================================================
TEST(Section20, Clog2Zero) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Clog2One) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Clog2Two) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 2)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Clog2Three) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(Section20, Clog2PowerOf2) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 256)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(Section20, Clog2NonPowerOf2) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 257)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 9u);
}

// ============================================================================
// §20.6.2 — $bits
// ============================================================================
TEST(Section20, BitsOf32BitValue) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 32u);
}

TEST(Section20, BitsOfVariable) {
  SysCallFixture f;
  auto* var = f.ctx.CreateVariable("wide_var", 64);
  var->value = MakeLogic4VecVal(f.arena, 64, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeIdent(f.arena, "wide_var")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 64u);
}

// ============================================================================
// §20.6.1 — $unsigned, $signed
// ============================================================================
TEST(Section20, Unsigned) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Section20, Signed) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

// ============================================================================
// §20.9 — $countones, $onehot, $onehot0, $isunknown
// ============================================================================
TEST(Section20, CountonesZero) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, CountonesAllBits) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeIntLit(f.arena, 0xFF)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(Section20, CountonesSparse) {
  SysCallFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$countones", {MakeIntLit(f.arena, 0b10101)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(Section20, OnehotTrue) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeIntLit(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, OnehotFalseZero) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, OnehotFalseMultiple) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeIntLit(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Onehot0True) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Onehot0TrueOneBit) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeIntLit(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Onehot0FalseMultiple) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeIntLit(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, IsunknownFalse) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, IsunknownTrueXVar) {
  SysCallFixture f;
  // CreateVariable initializes to X (bval = all ones).
  f.ctx.CreateVariable("xvar", 8);
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeIdent(f.arena, "xvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// ============================================================================
// §20.11 — $test$plusargs, $value$plusargs
// ============================================================================
TEST(Section20, TestPlusargsNotFound) {
  SysCallFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, TestPlusargsFound) {
  SysCallFixture f;
  f.ctx.AddPlusArg("VERBOSE");
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, TestPlusargsPrefixMatch) {
  SysCallFixture f;
  f.ctx.AddPlusArg("VERBOSE=1");
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERB")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, ValuePlusargsFound) {
  SysCallFixture f;
  f.ctx.AddPlusArg("DEPTH=42");
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr = MakeSysCall(
      f.arena, "$value$plusargs",
      {MakeStrLit(f.arena, "DEPTH=%d"), MakeIdent(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest_var->value.ToUint64(), 42u);
}

TEST(Section20, ValuePlusargsNotFound) {
  SysCallFixture f;
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr = MakeSysCall(
      f.arena, "$value$plusargs",
      {MakeStrLit(f.arena, "DEPTH=%d"), MakeIdent(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ============================================================================
// §20.6.1 — $typename
// ============================================================================
TEST(Section20, Typename) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Returns a string-encoded result; just verify it doesn't crash and
  // returns a non-zero width.
  EXPECT_GT(result.width, 0u);
}

// ============================================================================
// §21.3.3 — $sformatf
// ============================================================================
TEST(Section20, SformatfBasic) {
  SysCallFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$sformatf",
                  {MakeStrLit(f.arena, "val=%d"), MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // $sformatf returns a string as a Logic4Vec; the width should be
  // text.size()*8. "val=42" is 6 chars = 48 bits.
  EXPECT_EQ(result.width, 48u);
}

// ============================================================================
// §21.3.1/§21.3.2 — $fopen, $fclose
// ============================================================================
TEST(Section21, FopenFclose) {
  SysCallFixture f;
  // Create a temporary file for the test.
  std::string tmp_path = "/tmp/deltahdl_test_fopen.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "hello\n";
  }
  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  std::remove(tmp_path.c_str());
}

TEST(Section21, FopenInvalidFile) {
  SysCallFixture f;
  auto* expr = MakeSysCall(f.arena, "$fopen",
                           {MakeStrLit(f.arena, "/nonexistent/path/file.txt"),
                            MakeStrLit(f.arena, "r")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ============================================================================
// §21.3.3 — $fdisplay, $fwrite
// ============================================================================
TEST(Section21, FdisplayToFile) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_fdisplay.txt";

  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* fd_lit = MakeIntLit(f.arena, fd_val.ToUint64());
  auto* disp_expr = MakeSysCall(
      f.arena, "$fdisplay",
      {fd_lit, MakeStrLit(f.arena, "value=%d"), MakeIntLit(f.arena, 99)});
  EvalExpr(disp_expr, f.ctx, f.arena);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  // Read back and verify.
  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_EQ(contents, "value=99\n");

  std::remove(tmp_path.c_str());
}

// ============================================================================
// §21.4 — $readmemh, $readmemb
// ============================================================================
TEST(Section21, ReadmemhBasic) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_readmemh.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "0A\n14\n1E\n";
  }

  // Create an array variable (simulate as a 32-bit var for simplicity;
  // the implementation stores values to array indices via the context).
  auto* arr = f.ctx.CreateVariable("mem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MakeSysCall(
      f.arena, "$readmemh",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeIdent(f.arena, "mem")});
  EvalExpr(expr, f.ctx, f.arena);

  // The first value (0x0A = 10) should be in mem[0] = "mem".
  // For a flat variable, readmemh stores the first value.
  EXPECT_EQ(arr->value.ToUint64(), 0x0Au);

  std::remove(tmp_path.c_str());
}

TEST(Section21, ReadmembBasic) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_readmemb.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "1010\n0110\n";
  }

  auto* arr = f.ctx.CreateVariable("bmem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MakeSysCall(
      f.arena, "$readmemb",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeIdent(f.arena, "bmem")});
  EvalExpr(expr, f.ctx, f.arena);

  // First value: 1010 binary = 10 decimal.
  EXPECT_EQ(arr->value.ToUint64(), 0b1010u);

  std::remove(tmp_path.c_str());
}

// ============================================================================
// §21.4 — $writememh, $writememb
// ============================================================================
TEST(Section21, WritememhBasic) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememh.txt";

  auto* var = f.ctx.CreateVariable("wmem", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeSysCall(
      f.arena, "$writememh",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeIdent(f.arena, "wmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());

  EXPECT_NE(contents.find("ff"), std::string::npos);

  std::remove(tmp_path.c_str());
}

TEST(Section21, WritemembBasic) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememb.txt";

  auto* var = f.ctx.CreateVariable("wbmem", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0b10101010);

  auto* expr = MakeSysCall(
      f.arena, "$writememb",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeIdent(f.arena, "wbmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());
  EXPECT_NE(contents.find("10101010"), std::string::npos);

  std::remove(tmp_path.c_str());
}

// ============================================================================
// §21.3.5 — $sscanf
// ============================================================================
TEST(Section21, SscanfDecimal) {
  SysCallFixture f;
  auto* dest = f.ctx.CreateVariable("scanned", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MakeSysCall(f.arena, "$sscanf",
                  {MakeStrLit(f.arena, "42"), MakeStrLit(f.arena, "%d"),
                   MakeIdent(f.arena, "scanned")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);  // 1 item scanned
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

// ============================================================================
// §21.3 — $rewind(fd)
// ============================================================================
TEST(Section21, Rewind) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_rewind.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "ABCD";
  }
  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  // Read first char.
  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('A'));

  // Rewind.
  auto* rw = MakeSysCall(f.arena, "$rewind", {MakeIntLit(f.arena, fd)});
  EvalExpr(rw, f.ctx, f.arena);

  // Read first char again — should be 'A' after rewind.
  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

// ============================================================================
// §21.3 — $ungetc(char, fd)
// ============================================================================
TEST(Section21, Ungetc) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_ungetc.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "XY";
  }
  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  // Push back 'Z'.
  auto* ug = MakeSysCall(f.arena, "$ungetc",
                         {MakeIntLit(f.arena, 'Z'), MakeIntLit(f.arena, fd)});
  EvalExpr(ug, f.ctx, f.arena);

  // Next read should return 'Z'.
  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('Z'));

  // Then 'X' (the original first char).
  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('X'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

struct ParseResult20b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult20b Parse(const std::string& src) {
  ParseResult20b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 20.6.3 -- $isunbounded (range system function)
// =============================================================================
TEST(ParserSection20, IsUnboundedBasic) {
  auto r = Parse(
      "module m #(parameter int P = $);\n"
      "  initial begin\n"
      "    if ($isunbounded(P)) $display(\"unbounded\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, IsUnboundedInConditional) {
  auto r = Parse(
      "module m #(parameter int N = $);\n"
      "  generate\n"
      "    if (!$isunbounded(N)) begin\n"
      "      assign out = in;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, IsUnboundedWithBoundedParam) {
  auto r = Parse(
      "module m #(parameter int P = 42);\n"
      "  initial begin\n"
      "    if ($isunbounded(P)) $display(\"yes\");\n"
      "    else $display(\"no\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 20.7 -- Array querying functions
// =============================================================================
TEST(ParserSection20, ArrayLeftFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $left(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayRightFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $right(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArraySizeFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr [16];\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $size(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayHighLowFunctions) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] mem [0:255];\n"
      "  initial begin\n"
      "    $display(\"high=%0d low=%0d\", $high(mem), $low(mem));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayDimensionsFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0][7:0] data;\n"
      "  initial begin\n"
      "    int d;\n"
      "    d = $dimensions(data);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayIncrementFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $increment(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArraySizeWithDimArg) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $size(mem, 2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayUnpackedDimensionsFunction) {
  auto r = Parse(
      "module m;\n"
      "  logic arr [4][8];\n"
      "  initial begin\n"
      "    int d;\n"
      "    d = $unpacked_dimensions(arr);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

struct ParseResult21 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult21 Parse(const std::string& src) {
  ParseResult21 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// ============================================================================
// LRM section 21.1 -- Display system tasks (general I/O overview)
// ============================================================================
TEST(ParserSection21, DisplayBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

TEST(ParserSection21, DisplayNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display;\n"
              "endmodule\n"));
}

TEST(ParserSection21, DisplayMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"x=%d y=%h\", x, y);\n"
              "endmodule\n"));
}

TEST(ParserSection21, WriteBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $write(\"no newline\");\n"
              "endmodule\n"));
}

TEST(ParserSection21, WriteNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $write;\n"
              "endmodule\n"));
}

TEST(ParserSection21, DisplaybHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $displayb(\"binary: \", val);\n"
              "    $displayh(\"hex: \", val);\n"
              "    $displayo(\"octal: \", val);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, WritebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $writeb(val);\n"
              "    $writeh(val);\n"
              "    $writeo(val);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, StrobeBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $strobe(\"val=%d\", x);\n"
              "endmodule\n"));
}

TEST(ParserSection21, StrobebHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $strobeb(a);\n"
              "    $strobeh(a);\n"
              "    $strobeo(a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, MonitorBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $monitor(\"a=%b b=%b\", a, b);\n"
              "endmodule\n"));
}

TEST(ParserSection21, MonitorbHexOctal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $monitorb(a);\n"
              "    $monitorh(a);\n"
              "    $monitoro(a);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
