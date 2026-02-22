#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

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

static Expr *MakeSysCall(Arena &arena, std::string_view name,
                         std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr *MakeIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr *MakeStrLit(Arena &arena, std::string_view text) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  // Store with surrounding quotes, matching parser convention.
  auto len = text.size() + 2;
  char *buf = static_cast<char *>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

static Expr *MakeIdent(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// ============================================================================
// §20.8.1 — $clog2
// ============================================================================

TEST(Section20, Clog2Zero) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Clog2One) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Clog2Two) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 2)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Clog2Three) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(Section20, Clog2PowerOf2) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 256)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(Section20, Clog2NonPowerOf2) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$clog2", {MakeIntLit(f.arena, 257)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 9u);
}

// ============================================================================
// §20.6.2 — $bits
// ============================================================================

TEST(Section20, BitsOf32BitValue) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$bits", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 32u);
}

TEST(Section20, BitsOfVariable) {
  SysCallFixture f;
  auto *var = f.ctx.CreateVariable("wide_var", 64);
  var->value = MakeLogic4VecVal(f.arena, 64, 0);
  auto *expr = MakeSysCall(f.arena, "$bits", {MakeIdent(f.arena, "wide_var")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 64u);
}

// ============================================================================
// §20.6.1 — $unsigned, $signed
// ============================================================================

TEST(Section20, Unsigned) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$unsigned", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Section20, Signed) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$signed", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

// ============================================================================
// §20.9 — $countones, $onehot, $onehot0, $isunknown
// ============================================================================

TEST(Section20, CountonesZero) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$countones", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, CountonesAllBits) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$countones", {MakeIntLit(f.arena, 0xFF)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(Section20, CountonesSparse) {
  SysCallFixture f;
  auto *expr =
      MakeSysCall(f.arena, "$countones", {MakeIntLit(f.arena, 0b10101)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(Section20, OnehotTrue) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$onehot", {MakeIntLit(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, OnehotFalseZero) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$onehot", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, OnehotFalseMultiple) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$onehot", {MakeIntLit(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Onehot0True) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$onehot0", {MakeIntLit(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Onehot0TrueOneBit) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$onehot0", {MakeIntLit(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Onehot0FalseMultiple) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$onehot0", {MakeIntLit(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, IsunknownFalse) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$isunknown", {MakeIntLit(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, IsunknownTrueXVar) {
  SysCallFixture f;
  // CreateVariable initializes to X (bval = all ones).
  f.ctx.CreateVariable("xvar", 8);
  auto *expr = MakeSysCall(f.arena, "$isunknown", {MakeIdent(f.arena, "xvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// ============================================================================
// §20.11 — $test$plusargs, $value$plusargs
// ============================================================================

TEST(Section20, TestPlusargsNotFound) {
  SysCallFixture f;
  auto *expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, TestPlusargsFound) {
  SysCallFixture f;
  f.ctx.AddPlusArg("VERBOSE");
  auto *expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, TestPlusargsPrefixMatch) {
  SysCallFixture f;
  f.ctx.AddPlusArg("VERBOSE=1");
  auto *expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERB")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, ValuePlusargsFound) {
  SysCallFixture f;
  f.ctx.AddPlusArg("DEPTH=42");
  auto *dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto *expr = MakeSysCall(
      f.arena, "$value$plusargs",
      {MakeStrLit(f.arena, "DEPTH=%d"), MakeIdent(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest_var->value.ToUint64(), 42u);
}

TEST(Section20, ValuePlusargsNotFound) {
  SysCallFixture f;
  auto *dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto *expr = MakeSysCall(
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
  auto *expr = MakeSysCall(f.arena, "$typename", {MakeIntLit(f.arena, 0)});
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
  auto *expr =
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
  auto *open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto *close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  std::remove(tmp_path.c_str());
}

TEST(Section21, FopenInvalidFile) {
  SysCallFixture f;
  auto *expr = MakeSysCall(f.arena, "$fopen",
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

  auto *open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto *fd_lit = MakeIntLit(f.arena, fd_val.ToUint64());
  auto *disp_expr = MakeSysCall(
      f.arena, "$fdisplay",
      {fd_lit, MakeStrLit(f.arena, "value=%d"), MakeIntLit(f.arena, 99)});
  EvalExpr(disp_expr, f.ctx, f.arena);

  auto *close_expr =
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
  auto *arr = f.ctx.CreateVariable("mem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *expr = MakeSysCall(
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

  auto *arr = f.ctx.CreateVariable("bmem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *expr = MakeSysCall(
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

  auto *var = f.ctx.CreateVariable("wmem", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto *expr = MakeSysCall(
      f.arena, "$writememh",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeIdent(f.arena, "wmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());
  // Should contain "ff" or "FF".
  EXPECT_NE(contents.find("ff"), std::string::npos);

  std::remove(tmp_path.c_str());
}

TEST(Section21, WritemembBasic) {
  SysCallFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememb.txt";

  auto *var = f.ctx.CreateVariable("wbmem", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0b10101010);

  auto *expr = MakeSysCall(
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
  auto *dest = f.ctx.CreateVariable("scanned", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *expr =
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
  auto *open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  // Read first char.
  auto *getc1 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('A'));

  // Rewind.
  auto *rw = MakeSysCall(f.arena, "$rewind", {MakeIntLit(f.arena, fd)});
  EvalExpr(rw, f.ctx, f.arena);

  // Read first char again — should be 'A' after rewind.
  auto *getc2 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto *close_expr = MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd)});
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
  auto *open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  // Push back 'Z'.
  auto *ug = MakeSysCall(f.arena, "$ungetc",
                         {MakeIntLit(f.arena, 'Z'), MakeIntLit(f.arena, fd)});
  EvalExpr(ug, f.ctx, f.arena);

  // Next read should return 'Z'.
  auto *getc1 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('Z'));

  // Then 'X' (the original first char).
  auto *getc2 = MakeSysCall(f.arena, "$fgetc", {MakeIntLit(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('X'));

  auto *close_expr = MakeSysCall(f.arena, "$fclose", {MakeIntLit(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}
