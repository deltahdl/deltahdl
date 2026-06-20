#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

  auto* fgetc1 = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch1 = EvalExpr(fgetc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('X'));

  auto* ungetc_expr = MkSysCall(
      f.arena, "$ungetc",
      {MkInt(f.arena, static_cast<uint64_t>('Z')), MkInt(f.arena, fd)});
  EvalExpr(ungetc_expr, f.ctx, f.arena);

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
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var_d->value.ToUint64(), 42u);
  EXPECT_EQ(var_h->value.ToUint64(), 0xFFu);

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4: a descriptor opened for writing/appending cannot be read. Each read
// function must report its normal failure value when handed a write-only fd.

// Opens `tmp` (creating it with `seed` content first when reading is expected)
// and returns the fd for the given type string.
static uint64_t OpenWith(SysTaskFixture& f, const std::string& tmp,
                         const char* type) {
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, type)});
  return EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
}

TEST(SysTask, FgetcOnWriteOnlyFdReturnsEof) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_wronly_fgetc.txt";
  uint64_t fd = OpenWith(f, tmp, "w");
  ASSERT_NE(fd, 0u);

  auto* expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFFFFFFFu);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FgetsOnWriteOnlyFdReturnsZero) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_wronly_fgets.txt";
  uint64_t fd = OpenWith(f, tmp, "w");
  ASSERT_NE(fd, 0u);

  auto* dest = f.ctx.CreateVariable("wline", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);
  auto* expr = MkSysCall(f.arena, "$fgets",
                         {MkId(f.arena, "wline"), MkInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, UngetcOnWriteOnlyFdReturnsZero) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_wronly_ungetc.txt";
  uint64_t fd = OpenWith(f, tmp, "w");
  ASSERT_NE(fd, 0u);

  auto* expr = MkSysCall(
      f.arena, "$ungetc",
      {MkInt(f.arena, static_cast<uint64_t>('A')), MkInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FscanfOnWriteOnlyFdReturnsZero) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_wronly_fscanf.txt";
  uint64_t fd = OpenWith(f, tmp, "w");
  ASSERT_NE(fd, 0u);

  auto* var = f.ctx.CreateVariable("wv", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%d"), MkId(f.arena, "wv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FreadOnWriteOnlyFdReturnsZero) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_wronly_fread.txt";
  uint64_t fd = OpenWith(f, tmp, "w");
  ASSERT_NE(fd, 0u);

  auto* var = f.ctx.CreateVariable("wr", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "wr"), MkInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, ReadUpdateTypeAllowsReading) {
  // The "r+" type family opens for read-update; reading is permitted (unlike
  // the "w+"/"a+" update types, which §21.3.4 does not authorize for reading).
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_rplus.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "Q";
  }
  uint64_t fd = OpenWith(f, tmp, "r+");
  ASSERT_NE(fd, 0u);

  auto* expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(),
            static_cast<uint64_t>('Q'));

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, WriteUpdateTypeRejectsReading) {
  // The "w+" type opens for update (read and write) per Table 21-6, yet
  // §21.3.4 authorizes reading only for the "r"/"r+" families. A read on a
  // "w+" descriptor must therefore still report failure.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_wplus.txt";
  uint64_t fd = OpenWith(f, tmp, "w+");
  ASSERT_NE(fd, 0u);

  auto* expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, ReadRejectedOnStandardOutputDescriptor) {
  // STDOUT is pre-opened for append, not reading; a read on its reserved
  // descriptor must report end-of-file rather than touch the stream.
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, SimContext::kStdoutFd)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);
}

TEST(SysTask, FreadReadsBinary) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fread.txt";
  {
    std::ofstream ofs(tmp, std::ios::binary);
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
  EXPECT_EQ(result.ToUint64(), 4u);

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
