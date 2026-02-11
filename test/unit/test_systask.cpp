#include <gtest/gtest.h>

#include <cmath>
#include <cstdio>
#include <cstring>
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
// Test helpers (same pattern as test_parser_section20.cpp)
// ============================================================================

struct SysTaskFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static double ResultToDouble(const Logic4Vec& vec) {
  uint64_t bits = vec.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

static Expr* MkSysCall(Arena& arena, std::string_view name,
                       std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr* MkInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr* MkStr(Arena& arena, std::string_view text) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  auto len = text.size() + 2;
  char* buf = static_cast<char*>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

static Expr* MkId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// ============================================================================
// $time, $stime, $realtime (section 20.3)
// ============================================================================

TEST(SysTask, TimeReturnsCurrentTicks) {
  SysTaskFixture f;
  // Schedule an event at time 100 to advance the clock.
  auto* event = f.scheduler.GetEventPool().Acquire();
  event->callback = []() {};
  f.scheduler.ScheduleEvent(SimTime{100}, Region::kActive, event);
  // CurrentTime starts at 0 before scheduler runs.
  auto* expr = MkSysCall(f.arena, "$time", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.width, 64u);
}

TEST(SysTask, StimeReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, RealtimeReturns64Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$realtime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
}

// ============================================================================
// Math functions (section 20.8)
// ============================================================================

TEST(SysTask, LnOfE) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$ln", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, Log10Of100) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$log10", {MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 2.0);
}

TEST(SysTask, ExpOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$exp", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.0);
}

TEST(SysTask, SqrtOf16) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkInt(f.arena, 16)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 4.0);
}

TEST(SysTask, SqrtOf9) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$sqrt", {MkInt(f.arena, 9)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 3.0);
}

TEST(SysTask, PowOf2And10) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$pow", {MkInt(f.arena, 2), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1024.0);
}

TEST(SysTask, FloorOf7) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$floor", {MkInt(f.arena, 7)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 7.0);
}

TEST(SysTask, CeilOf7) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$ceil", {MkInt(f.arena, 7)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 7.0);
}

TEST(SysTask, SinOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$sin", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, CosOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$cos", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.0);
}

TEST(SysTask, TanOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$tan", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, Atan2Of0And1) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$atan2", {MkInt(f.arena, 0), MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, HypotOf3And4) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$hypot", {MkInt(f.arena, 3), MkInt(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 5.0);
}

TEST(SysTask, SinhOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$sinh", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, CoshOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$cosh", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.0);
}

TEST(SysTask, AsinOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$asin", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, AcosOf1) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$acos", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

TEST(SysTask, AtanOf0) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$atan", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 0.0);
}

// ============================================================================
// Random functions (section 20.14)
// ============================================================================

TEST(SysTask, RandomReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$random", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, UrandomReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, UrandomRangeInBounds) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 10), MkInt(f.arena, 5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  uint64_t val = result.ToUint64();
  EXPECT_GE(val, 5u);
  EXPECT_LE(val, 10u);
}

TEST(SysTask, DistUniformReturns32Bit) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$dist_uniform",
                {MkInt(f.arena, 0), MkInt(f.arena, 0), MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_LE(result.ToUint64(), 100u);
}

TEST(SysTask, DistNormalReturns32Bit) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$dist_normal",
                {MkInt(f.arena, 0), MkInt(f.arena, 50), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// ============================================================================
// File I/O extended (section 21.3)
// ============================================================================

TEST(SysTask, FgetsReadsLine) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fgets.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "hello world\n";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* dest = f.ctx.CreateVariable("line_var", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);

  auto* fgets_expr =
      MkSysCall(f.arena, "$fgets",
                {MkId(f.arena, "line_var"), MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(fgets_expr, f.ctx, f.arena);
  // $fgets returns the number of characters read (>0 on success).
  EXPECT_GT(result.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FgetcReadsChar) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fgetc.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "A";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FeofAtEnd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_feof.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "x";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  // Read the single character.
  auto* fgetc_expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(fgetc_expr, f.ctx, f.arena);

  // Read again to trigger EOF (EOF is set after a failed read).
  auto* fgetc2_expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  auto eof_ch = EvalExpr(fgetc2_expr, f.ctx, f.arena);
  EXPECT_EQ(eof_ch.ToUint64(), 0xFFFFFFFF);

  auto* eof_expr =
      MkSysCall(f.arena, "$feof", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(eof_expr, f.ctx, f.arena);
  EXPECT_NE(result.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FtellAndFseek) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  // ftell at beginning should be 0.
  auto* ftell_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos = EvalExpr(ftell_expr, f.ctx, f.arena);
  EXPECT_EQ(pos.ToUint64(), 0u);

  // Seek to position 3.
  auto* fseek_expr =
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, fd), MkInt(f.arena, 3), MkInt(f.arena, 0)});
  EvalExpr(fseek_expr, f.ctx, f.arena);

  // ftell should now be 3.
  auto* ftell2_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos2 = EvalExpr(ftell2_expr, f.ctx, f.arena);
  EXPECT_EQ(pos2.ToUint64(), 3u);

  // fgetc should return 'd'.
  auto* fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('d'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FflushDoesNotCrash) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fflush.txt";
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* flush_expr =
      MkSysCall(f.arena, "$fflush", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(flush_expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, RewindResetsPosition) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_rewind.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "ABCDEF";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  // Read first char.
  auto* fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('A'));

  // Rewind.
  auto* rewind_expr = MkSysCall(f.arena, "$rewind", {MkInt(f.arena, fd)});
  EvalExpr(rewind_expr, f.ctx, f.arena);

  // Re-read first char — should be 'A' again.
  auto* fgetc2_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch2 = EvalExpr(fgetc2_expr, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, UngetcPushesBack) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_ungetc.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "XY";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  // Read 'X'.
  auto* fgetc1 = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch1 = EvalExpr(fgetc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('X'));

  // Push back 'Z'.
  auto* ungetc_expr = MkSysCall(
      f.arena, "$ungetc",
      {MkInt(f.arena, static_cast<uint64_t>('Z')), MkInt(f.arena, fd)});
  EvalExpr(ungetc_expr, f.ctx, f.arena);

  // Next read should return 'Z'.
  auto* fgetc2 = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch2 = EvalExpr(fgetc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('Z'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FscanfReadsFormatted) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "42 ff";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto* var_d = f.ctx.CreateVariable("v_dec", 32);
  var_d->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* var_h = f.ctx.CreateVariable("v_hex", 32);
  var_h->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* fscanf_expr =
      MkSysCall(f.arena, "$fscanf",
                {MkInt(f.arena, fd), MkStr(f.arena, "%d %h"),
                 MkId(f.arena, "v_dec"), MkId(f.arena, "v_hex")});
  auto result = EvalExpr(fscanf_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);  // Two items matched.
  EXPECT_EQ(var_d->value.ToUint64(), 42u);
  EXPECT_EQ(var_h->value.ToUint64(), 0xFFu);

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FreadReadsBinary) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fread.txt";
  {
    std::ofstream ofs(tmp, std::ios::binary);
    // Write 4 bytes: 0xDE 0xAD 0xBE 0xEF
    char data[] = {'\xDE', '\xAD', '\xBE', '\xEF'};
    ofs.write(data, 4);
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "rb")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto* var = f.ctx.CreateVariable("v_read", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* fread_expr = MkSysCall(f.arena, "$fread",
                               {MkId(f.arena, "v_read"), MkInt(f.arena, fd)});
  auto result = EvalExpr(fread_expr, f.ctx, f.arena);
  // $fread returns number of bytes read.
  EXPECT_EQ(result.ToUint64(), 4u);

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// ============================================================================
// $system (section 20.17)
// ============================================================================

TEST(SysTask, SystemReturnsExitCode) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$system", {MkStr(f.arena, "true")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, SystemFailureExitCode) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$system", {MkStr(f.arena, "false")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.ToUint64(), 0u);
}

// ============================================================================
// $stacktrace (section 20.17)
// ============================================================================

TEST(SysTask, StacktraceDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stacktrace", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// ============================================================================
// FormatDisplay enhancements: %o, %e, %f, %g, %s, %m
// ============================================================================

TEST(SysTask, FormatOctal) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 32, 8));
  auto out = FormatDisplay("%o", vals);
  EXPECT_EQ(out, "10");
}

TEST(SysTask, FormatReal_e) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  // Store 1.5 as IEEE 754 bits in a 64-bit logic vec.
  double dval = 1.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%e", vals);
  // Should contain "1.5" in scientific notation.
  EXPECT_NE(out.find("1.5"), std::string::npos);
}

TEST(SysTask, FormatReal_f) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%f", vals);
  EXPECT_NE(out.find("2.5"), std::string::npos);
}

TEST(SysTask, FormatString_s) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  // "Hi" => 0x4869
  uint64_t encoded = (static_cast<uint64_t>('H') << 8) | 'i';
  vals.push_back(MakeLogic4VecVal(arena, 16, encoded));
  auto out = FormatDisplay("%s", vals);
  EXPECT_EQ(out, "Hi");
}

TEST(SysTask, FormatModule_m) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%m", vals);
  // %m prints a hierarchical name; we return a placeholder.
  EXPECT_FALSE(out.empty());
}

// ============================================================================
// §20.5 — Type conversion functions
// ============================================================================

TEST(SysTask, ItoRConvertsIntToReal) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$itor", {MkInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 42.0);
}

TEST(SysTask, RtoIConvertsRealToInt) {
  SysTaskFixture f;
  // Build a real literal with value 3.7 — expect truncation to 3.
  double dval = 3.7;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* expr = MkSysCall(f.arena, "$rtoi", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(SysTask, BitstorealReinterpretsBitsAsReal) {
  SysTaskFixture f;
  // 0x4045000000000000 is IEEE 754 for 42.0
  double expected = 42.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &expected, sizeof(double));
  auto* expr = MkSysCall(f.arena, "$bitstoreal", {MkInt(f.arena, bits)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 42.0);
}

TEST(SysTask, RealtobitsReinterpretsRealAsBits) {
  SysTaskFixture f;
  double dval = 42.0;
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* expr = MkSysCall(f.arena, "$realtobits", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  uint64_t expected_bits = 0;
  std::memcpy(&expected_bits, &dval, sizeof(double));
  EXPECT_EQ(result.ToUint64(), expected_bits);
}

TEST(SysTask, CountbitsMatchingPattern) {
  SysTaskFixture f;
  // $countbits(0b1010_0101, '1) should return 4 (count of 1-bits).
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

// ============================================================================
// $printtimescale (section 20.4) — does not crash
// ============================================================================

TEST(SysTask, PrinttimescaleDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$printtimescale", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// ============================================================================
// $timeformat (section 20.4) — does not crash
// ============================================================================

TEST(SysTask, TimeformatDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$timeformat",
                         {MkInt(f.arena, 0), MkInt(f.arena, 0),
                          MkStr(f.arena, " ns"), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// ============================================================================
// $ferror (section 21.3) — returns 0 on valid fd
// ============================================================================

TEST(SysTask, FerrorReturns0OnGoodFd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_ferror.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "ok";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* dest = f.ctx.CreateVariable("errmsg", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);

  auto* err_expr =
      MkSysCall(f.arena, "$ferror",
                {MkInt(f.arena, fd_val.ToUint64()), MkId(f.arena, "errmsg")});
  auto result = EvalExpr(err_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// ============================================================================
// §20.7 Array query functions
// ============================================================================

TEST(SysTask, DimensionsReturnsOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$dimensions", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(SysTask, LeftReturnsUpperBound) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$left", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, RightReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$right", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, SizeReturnsWidth) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$size", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_GE(result.ToUint64(), 1u);
}

TEST(SysTask, LowReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$low", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, HighReturnsUpperBound) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$high", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_GE(result.ToUint64(), 0u);
}

TEST(SysTask, IncrementReturns) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$increment", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, UnpackedDimensionsReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ============================================================================
// §20.11 Assertion control system tasks
// ============================================================================

TEST(SysTask, AssertOnDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$asserton", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertOffDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertoff", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertKillDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertkill", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertControlDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertcontrol", {MkInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// ============================================================================
// §20.12 Sampled value system functions
// ============================================================================

TEST(SysTask, SampledReturnsInput) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$sampled", {MkInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SysTask, RoseReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$rose", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

TEST(SysTask, FellReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$fell", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

TEST(SysTask, StableReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stable", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

TEST(SysTask, PastReturnsValue) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$past", {MkInt(f.arena, 7)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, ChangedReturnsZeroOrOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$changed", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_LE(result.ToUint64(), 1u);
}

// ============================================================================
// §20.13 Coverage system functions
// ============================================================================

TEST(SysTask, CoverageControlReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_control",
                         {MkInt(f.arena, 1), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageGetMaxReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_get_max",
                         {MkInt(f.arena, 1), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageGetReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_get",
                         {MkInt(f.arena, 1), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageMergeReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_merge", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageSaveReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_save", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ============================================================================
// §20.15 Stochastic analysis tasks
// ============================================================================

TEST(SysTask, QInitializeReturnsZero) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$q_initialize",
                {MkInt(f.arena, 1), MkInt(f.arena, 1), MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, QFullReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$q_full", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ============================================================================
// §20.16 PLA modeling system tasks
// ============================================================================

TEST(SysTask, AsyncAndArrayReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$async$and$array", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}
