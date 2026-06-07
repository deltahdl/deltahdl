#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

std::string ReadWholeFile(const std::string& path) {
  std::ifstream in(path, std::ios::binary);
  std::ostringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

// §21.3.6: $fflush given a single file descriptor writes that file's buffered
// output. After flushing, the bytes written through the descriptor are present
// in the underlying file.
TEST(SysTask, FflushFileDescriptor) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fflush_fd.txt";
  std::remove(tmp.c_str());

  auto fd_val = EvalExpr(
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "w")}),
      f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  EvalExpr(MkSysCall(f.arena, "$fwrite",
                     {MkInt(f.arena, fd), MkStr(f.arena, "hello")}),
           f.ctx, f.arena);
  auto result =
      EvalExpr(MkSysCall(f.arena, "$fflush", {MkInt(f.arena, fd)}), f.ctx,
               f.arena);
  EXPECT_EQ(result.width, 1u);

  EXPECT_EQ(ReadWholeFile(tmp), "hello");

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.6: $fflush given a multi-channel descriptor writes the buffered output
// of every channel it selects. A single-argument $fopen returns such an mcd;
// flushing it must operate on the channel's file rather than failing the way a
// plain file-descriptor lookup would.
TEST(SysTask, FflushMultiChannelDescriptor) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fflush_mcd.txt";
  std::remove(tmp.c_str());

  auto mcd_val = EvalExpr(
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp)}), f.ctx, f.arena);
  uint64_t mcd = mcd_val.ToUint64();

  EvalExpr(MkSysCall(f.arena, "$fwrite",
                     {MkInt(f.arena, mcd), MkStr(f.arena, "world")}),
           f.ctx, f.arena);
  auto result =
      EvalExpr(MkSysCall(f.arena, "$fflush", {MkInt(f.arena, mcd)}), f.ctx,
               f.arena);
  EXPECT_EQ(result.width, 1u);

  EXPECT_EQ(ReadWholeFile(tmp), "world");

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, mcd)}), f.ctx,
           f.arena);
  std::remove(tmp.c_str());
}

// §21.3.6 edge: a file descriptor that names no open file (its reserved high
// bit is set but no handle is registered for it) flushes nothing and still
// completes without error, exercising the null-handle guard on the fd branch.
TEST(SysTask, FflushUnopenedFileDescriptor) {
  SysTaskFixture f;
  // High bit set marks this as a file descriptor; channel 5 was never opened.
  uint64_t stale_fd = 0x80000005ull;
  auto result = EvalExpr(
      MkSysCall(f.arena, "$fflush", {MkInt(f.arena, stale_fd)}), f.ctx,
      f.arena);
  EXPECT_EQ(result.width, 1u);
}

// §21.3.6 edge: a multi-channel descriptor that selects no channels resolves to
// no files, so the flush does nothing and still completes without error,
// exercising the empty-resolution path on the mcd branch.
TEST(SysTask, FflushMcdWithNoChannelsSelected) {
  SysTaskFixture f;
  // No high bit and no channel bits set: an mcd that names no open channel.
  auto result =
      EvalExpr(MkSysCall(f.arena, "$fflush", {MkInt(f.arena, 0)}), f.ctx,
               f.arena);
  EXPECT_EQ(result.width, 1u);
}

// §21.3.6: invoked with no arguments, $fflush flushes all open files and still
// reports a width-1 result.
TEST(SysTask, FflushNoArgumentFlushesAllOpenFiles) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fflush_all.txt";
  std::remove(tmp.c_str());

  auto fd_val = EvalExpr(
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "w")}),
      f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  EvalExpr(MkSysCall(f.arena, "$fwrite",
                     {MkInt(f.arena, fd), MkStr(f.arena, "all")}),
           f.ctx, f.arena);
  auto result = EvalExpr(MkSysCall(f.arena, "$fflush", {}), f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);

  EXPECT_EQ(ReadWholeFile(tmp), "all");

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
