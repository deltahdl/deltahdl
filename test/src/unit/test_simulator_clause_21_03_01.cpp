#include <cstdio>
#include <fstream>
#include <string>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

TEST(IoSystemTaskTest, FopenFclose) {
  SimFixture f;

  std::string tmp_path = "/tmp/deltahdl_test_fopen.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "hello\n";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  std::remove(tmp_path.c_str());
}

TEST(IoSystemTaskTest, FopenInvalidFile) {
  SimFixture f;
  auto* expr = MakeSysCall(
      f.arena, "$fopen",
      {MkStr(f.arena, "/nonexistent/path/file.txt"), MkStr(f.arena, "r")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §21.3.1: an fd has its MSB set so the I/O runtime can distinguish it from
// a multichannel descriptor.
TEST(IoSystemTaskTest, FopenFdHasMsbSet) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_msb.txt";
  auto* open_expr = MakeSysCall(
      f.arena, "$fopen", {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  auto fd = static_cast<uint32_t>(fd_val.ToUint64());
  EXPECT_NE(fd & 0x80000000u, 0u);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(path.c_str());
}

// §21.3.1: omitting the type argument requests a multichannel descriptor; its
// MSB is reserved (always clear) and its bit-0 channel is reserved for stdout.
TEST(IoSystemTaskTest, FopenMcdHasMsbClearAndNonZero) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_mcd.txt";
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path.c_str())});
  auto mcd_val = EvalExpr(open_expr, f.ctx, f.arena);
  auto mcd = static_cast<uint32_t>(mcd_val.ToUint64());
  EXPECT_NE(mcd, 0u);
  EXPECT_EQ(mcd & 0x80000000u, 0u);
  EXPECT_EQ(mcd & 0x1u, 0u);  // bit 0 belongs to stdout

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(path.c_str());
}

// §21.3.1: $fopen shall reuse channels that have been closed.
TEST(IoSystemTaskTest, FopenReusesClosedChannel) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_reuse.txt";

  auto* first = MakeSysCall(
      f.arena, "$fopen", {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")});
  auto first_fd = EvalExpr(first, f.ctx, f.arena).ToUint64();

  auto* close_first =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, first_fd)});
  EvalExpr(close_first, f.ctx, f.arena);

  auto* second = MakeSysCall(
      f.arena, "$fopen", {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")});
  auto second_fd = EvalExpr(second, f.ctx, f.arena).ToUint64();

  EXPECT_EQ(first_fd, second_fd);

  auto* close_second =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, second_fd)});
  EvalExpr(close_second, f.ctx, f.arena);
  std::remove(path.c_str());
}

// §21.3.1: STDIN/STDOUT/STDERR are reserved with the documented fd values.
TEST(IoSystemTaskTest, ReservedStdioConstants) {
  EXPECT_EQ(SimContext::kStdinFd, 0x80000000u);
  EXPECT_EQ(SimContext::kStdoutFd, 0x80000001u);
  EXPECT_EQ(SimContext::kStderrFd, 0x80000002u);

  SimFixture f;
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStdoutFd), nullptr);
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStderrFd), nullptr);
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStdinFd), nullptr);
}

// §21.3.1: $fclose on an mcd closes every file selected by its set bits, and
// further attempts to access the channel after close are inert.
TEST(IoSystemTaskTest, FcloseClearsMcdChannel) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fclose_mcd.txt";

  auto* open_expr =
      MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path.c_str())});
  auto mcd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd)});
  EvalExpr(close_expr, f.ctx, f.arena);

  EXPECT_TRUE(f.ctx.GetMcdFiles(static_cast<uint32_t>(mcd)).empty());
  std::remove(path.c_str());
}

// §21.3.1: the "b" in mode strings only distinguishes binary from text on
// systems that make that distinction; $fopen must accept the binary forms.
TEST(IoSystemTaskTest, FopenAcceptsBinaryModeSuffix) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_binary.bin";

  auto write_fd =
      EvalExpr(
          MakeSysCall(f.arena, "$fopen",
                      {MkStr(f.arena, path.c_str()), MkStr(f.arena, "wb")}),
          f.ctx, f.arena)
          .ToUint64();
  EXPECT_NE(write_fd, 0u);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, write_fd)}), f.ctx,
           f.arena);

  auto read_fd =
      EvalExpr(
          MakeSysCall(f.arena, "$fopen",
                      {MkStr(f.arena, path.c_str()), MkStr(f.arena, "rb")}),
          f.ctx, f.arena)
          .ToUint64();
  EXPECT_NE(read_fd, 0u);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, read_fd)}), f.ctx,
           f.arena);
  std::remove(path.c_str());
}

// §21.3.1: after $fclose, no further I/O on the closed fd is allowed.
// $fdisplay through a stale fd must not crash and must not write — the
// runtime drops the request because the descriptor is unmapped.
TEST(IoSystemTaskTest, NoWritesAfterFcloseOnFd) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_no_writes_after_close.txt";

  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fdisplay",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "before")}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fdisplay",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "after")}),
           f.ctx, f.arena);

  std::ifstream ifs(path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_EQ(contents, "before\n");
  std::remove(path.c_str());
}

// §21.3.1: $fopen at simulator level must accept every type string listed
// in Table 21-6, returning a usable fd (non-zero) in each case. This goes
// past the parser-level acceptance check by exercising the runtime mode
// translation that sits between Verilog source and libc.
TEST(IoSystemTaskTest, FopenAcceptsEveryTable21_6Mode) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_all_modes.txt";
  {
    std::ofstream seed(path);
    seed << "seed\n";
  }
  for (const char* mode : {"r", "rb", "w", "wb", "a", "ab", "r+", "r+b", "rb+",
                           "w+", "w+b", "wb+", "a+", "a+b", "ab+"}) {
    auto fd =
        EvalExpr(
            MakeSysCall(f.arena, "$fopen",
                        {MkStr(f.arena, path.c_str()), MkStr(f.arena, mode)}),
            f.ctx, f.arena)
            .ToUint64();
    EXPECT_NE(fd, 0u) << "mode=" << mode;
    EXPECT_NE(fd & 0x80000000u, 0u) << "mode=" << mode;
    EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
             f.arena);
  }
  std::remove(path.c_str());
}

// §21.3.1: $fopen returns a 32-bit value. The value-width width invariant is
// observable at the simulator boundary where the runtime hands back a result
// of fixed 32-bit packed-array width.
TEST(IoSystemTaskTest, FopenReturnValueIsThirtyTwoBits) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_width.txt";

  auto vec_fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena);
  EXPECT_EQ(vec_fd.width, 32u);
  EvalExpr(
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, vec_fd.ToUint64())}),
      f.ctx, f.arena);

  auto vec_mcd =
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path.c_str())}),
               f.ctx, f.arena);
  EXPECT_EQ(vec_mcd.width, 32u);
  EvalExpr(
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, vec_mcd.ToUint64())}),
      f.ctx, f.arena);
  std::remove(path.c_str());
}

// §21.3.1: STDOUT is pre-opened for output. Writing to the reserved STDOUT fd
// must succeed (the descriptor is mapped to a non-null FILE*); this directly
// observes the "STDOUT/STDERR are pre-opened for append" guarantee at the
// simulator layer that produces the mapping.
TEST(IoSystemTaskTest, StdoutFdIsWritable) {
  SimFixture f;
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStdoutFd), nullptr);
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStderrFd), nullptr);
  // $fdisplay to STDOUT must not crash and must not allocate a new fd slot.
  EvalExpr(MakeSysCall(
               f.arena, "$fdisplay",
               {MakeInt(f.arena, SimContext::kStdoutFd), MkStr(f.arena, "")}),
           f.ctx, f.arena);
  // Reopening STDOUT-adjacent slots after writing must still succeed: the
  // reserved descriptors do not consume the user-allocatable channel range.
  std::string path = "/tmp/deltahdl_test_stdout_writable.txt";
  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();
  EXPECT_NE(fd, 0u);
  EXPECT_NE(fd, SimContext::kStdoutFd);
  EXPECT_NE(fd, SimContext::kStderrFd);
  EXPECT_NE(fd, SimContext::kStdinFd);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  std::remove(path.c_str());
}

// §21.3.1: closing a reserved STDIN/STDOUT/STDERR fd must not invalidate the
// underlying libc stream. The runtime must continue to resolve those reserved
// fds to a non-null FILE* after the user attempts $fclose on them.
TEST(IoSystemTaskTest, FcloseDoesNotInvalidateReservedStdio) {
  SimFixture f;
  EvalExpr(MakeSysCall(f.arena, "$fclose",
                       {MakeInt(f.arena, SimContext::kStdoutFd)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fclose",
                       {MakeInt(f.arena, SimContext::kStderrFd)}),
           f.ctx, f.arena);
  EvalExpr(
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, SimContext::kStdinFd)}),
      f.ctx, f.arena);
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStdoutFd), nullptr);
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStderrFd), nullptr);
  EXPECT_NE(f.ctx.GetFileHandle(SimContext::kStdinFd), nullptr);
}

// §21.3.1: filename and type may be supplied as an integral value whose bytes
// encode the characters of the string, not only as a string literal. The
// runtime decodes the byte-packed Logic4Vec value of the variable to recover
// the path / mode at $fopen time.
TEST(IoSystemTaskTest, FopenAcceptsIntegralCharacterStringForFilename) {
  SimFixture f;
  const std::string kPath = "/tmp/x";
  {
    std::ofstream seed(kPath);
    seed << "ok\n";
  }

  auto* fname_var = f.ctx.CreateVariable("fname", 48);
  uint64_t packed = 0;
  for (size_t i = 0; i < kPath.size(); ++i) {
    uint64_t byte_idx = kPath.size() - 1 - i;
    packed |= static_cast<uint64_t>(static_cast<unsigned char>(kPath[i]))
              << (byte_idx * 8);
  }
  fname_var->value = MakeLogic4VecVal(f.arena, 48, packed);

  auto* mode_var = f.ctx.CreateVariable("mode", 8);
  mode_var->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>('r'));

  auto* open_expr = MakeSysCall(
      f.arena, "$fopen", {MakeId(f.arena, "fname"), MakeId(f.arena, "mode")});
  auto fd = EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
  EXPECT_NE(fd, 0u);

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);
  std::remove(kPath.c_str());
}

// §21.3.1: $fopen failure returns 0 for every read-style type string that
// requires the file to already exist. Exercising each read variant separately
// observes the parenthetical enumeration in the failure clause.
TEST(IoSystemTaskTest, FopenReturnsZeroForMissingReadTargets) {
  SimFixture f;
  for (const char* mode : {"r", "rb", "r+", "r+b", "rb+"}) {
    auto result =
        EvalExpr(MakeSysCall(f.arena, "$fopen",
                             {MkStr(f.arena, "/nonexistent/path/no.dat"),
                              MkStr(f.arena, mode)}),
                 f.ctx, f.arena)
            .ToUint64();
    EXPECT_EQ(result, 0u) << "mode=" << mode;
  }
}

// §21.3.1: $fmonitor / $fstrobe operations attached to a descriptor are
// implicitly cancelled when $fclose closes that descriptor. The descriptor
// becomes unmapped, so any later write through it is dropped.
TEST(IoSystemTaskTest, FmonitorAndFstrobeCancelledOnClose) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_cancel_on_close.txt";

  auto fd =
      EvalExpr(MakeSysCall(f.arena, "$fopen",
                           {MkStr(f.arena, path.c_str()), MkStr(f.arena, "w")}),
               f.ctx, f.arena)
          .ToUint64();

  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "m=%d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)}), f.ctx,
           f.arena);

  EvalExpr(MakeSysCall(f.arena, "$fmonitor",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "post=%d"),
                        MakeInt(f.arena, 2)}),
           f.ctx, f.arena);
  EvalExpr(MakeSysCall(f.arena, "$fstrobe",
                       {MakeInt(f.arena, fd), MkStr(f.arena, "strobe=%d"),
                        MakeInt(f.arena, 3)}),
           f.ctx, f.arena);

  std::ifstream ifs(path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_EQ(contents, "m=1\n");
  std::remove(path.c_str());
}

}  // namespace
