#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// Reads back the full contents of a file the simulated source produced.
static std::string SlurpFile(const std::string& path) {
  std::ifstream ifs(path);
  std::stringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

// Drives a whole module through parse -> elaborate -> lower -> run, so $fopen /
// $fclose fire from real source exactly as a user design would trigger them,
// with the descriptor and filename produced by genuine declarations/assignments
// rather than a hand-built system-call node.
static void RunFullSource(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

// Same, but captures everything the run writes to stdout so a $display-observed
// outcome (e.g. an open-failure branch) can be checked.
static std::string RunFullSourceCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

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
TEST(IoSystemTaskTest, FopenAcceptsEveryDocumentedModeAtRuntime) {
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

// §21.3.1: the LSB (bit 0) of a multichannel descriptor always refers to the
// standard output. The runtime pre-wires channel 0 to stdout, so resolving an
// mcd whose only set bit is bit 0 yields exactly the process stdout stream.
TEST(IoSystemTaskTest, McdBitZeroIsStandardOutput) {
  SimFixture f;
  auto channel0 = f.ctx.GetMcdFiles(0x1u);
  ASSERT_EQ(channel0.size(), 1u);
  EXPECT_EQ(channel0.front(), stdout);
}

// §21.3.1: output is directed to two or more files opened with multichannel
// descriptors by bitwise OR-ing their mcds together. Observed here at the
// descriptor-resolution level that §21.3.1 owns: the OR of two single-channel
// mcds selects both underlying files, independent of any file-output task.
TEST(IoSystemTaskTest, OrCombinedMcdSelectsBothChannels) {
  SimFixture f;
  std::string path_a = "/tmp/deltahdl_test_or_mcd_a.txt";
  std::string path_b = "/tmp/deltahdl_test_or_mcd_b.txt";

  auto mcd_a = static_cast<uint32_t>(
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path_a.c_str())}),
               f.ctx, f.arena)
          .ToUint64());
  auto mcd_b = static_cast<uint32_t>(
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path_b.c_str())}),
               f.ctx, f.arena)
          .ToUint64());

  auto only_a = f.ctx.GetMcdFiles(mcd_a);
  auto only_b = f.ctx.GetMcdFiles(mcd_b);
  ASSERT_EQ(only_a.size(), 1u);
  ASSERT_EQ(only_b.size(), 1u);

  // The OR of the two descriptors selects both channels at once.
  auto both = f.ctx.GetMcdFiles(mcd_a | mcd_b);
  ASSERT_EQ(both.size(), 2u);
  EXPECT_NE(both[0], nullptr);
  EXPECT_NE(both[1], nullptr);
  EXPECT_NE(both[0], both[1]);
  EXPECT_EQ(both[0], only_a.front());
  EXPECT_EQ(both[1], only_b.front());

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd_a | mcd_b)}),
           f.ctx, f.arena);
  std::remove(path_a.c_str());
  std::remove(path_b.c_str());
}

// §21.3.1: an mcd returned by $fopen is a 32-bit value in which a single bit is
// set, indicating the one channel just opened. Opening one file must light
// exactly one channel bit (and never bit 0, which is reserved for stdout).
TEST(IoSystemTaskTest, FreshMcdHasExactlyOneChannelBitSet) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_fopen_single_bit.txt";
  auto mcd = static_cast<uint32_t>(
      EvalExpr(MakeSysCall(f.arena, "$fopen", {MkStr(f.arena, path.c_str())}),
               f.ctx, f.arena)
          .ToUint64());
  EXPECT_EQ(__builtin_popcount(mcd), 1) << "mcd=" << mcd;
  EXPECT_EQ(mcd & 0x1u, 0u);  // bit 0 is reserved for stdout, never allocated

  EvalExpr(MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, mcd)}), f.ctx,
           f.arena);
  std::remove(path.c_str());
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

// ---------------------------------------------------------------------------
// §21.3.1 end-to-end: the descriptor and filename are produced by real source
// syntax and driven through the full parse/elaborate/lower/run pipeline. The
// $fopen result is consumed by a file-output task so the roundtrip is visible
// in the file the run actually wrote.
// ---------------------------------------------------------------------------

// §21.3.1: the fd form ($fopen with a type argument) opens a writable file and
// $fclose flushes and closes it. Input form: filename as a string literal.
TEST(IoSystemTaskTest, FdOpenWriteCloseRoundTripFromSource) {
  SimFixture f;
  const std::string path = "/tmp/deltahdl_e2e_fd_roundtrip.txt";
  std::remove(path.c_str());
  RunFullSource(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fwrite(fd, \"e2e=%0d\", 42);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "e2e=42");
  std::remove(path.c_str());
}

// §21.3.1: the mcd form ($fopen with only a filename) opens a channel and
// $fclose closes it. Input form: filename as a string literal, no type.
TEST(IoSystemTaskTest, McdOpenDisplayCloseRoundTripFromSource) {
  SimFixture f;
  const std::string path = "/tmp/deltahdl_e2e_mcd_roundtrip.txt";
  std::remove(path.c_str());
  RunFullSource(
      "module t;\n"
      "  integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"" +
          path +
          "\");\n"
          "    $fdisplay(mcd, \"e2e=%0d\", 7);\n"
          "    $fclose(mcd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "e2e=7\n");
  std::remove(path.c_str());
}

// §21.3.1 input form: the filename may be supplied as a string-data-type
// variable, not only as a literal. Built from real `string` source syntax.
TEST(IoSystemTaskTest, FilenameFromStringDataTypeVariable) {
  SimFixture f;
  const std::string path = "/tmp/deltahdl_e2e_strname.txt";
  std::remove(path.c_str());
  RunFullSource(
      "module t;\n"
      "  string path;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    path = \"" +
          path +
          "\";\n"
          "    fd = $fopen(path, \"w\");\n"
          "    $fwrite(fd, \"str-name\");\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "str-name");
  std::remove(path.c_str());
}

// §21.3.1 input form: the filename may be an integral value whose bytes encode
// the characters. Built from a real packed-vector declaration holding the path.
TEST(IoSystemTaskTest, FilenameFromPackedIntegralVariable) {
  SimFixture f;
  const std::string path = "/tmp/deltahdl_e2e_intname.txt";
  std::remove(path.c_str());
  // A 32-byte packed vector comfortably holds the path; the leading bytes are
  // zero and are ignored when the runtime decodes the characters.
  RunFullSource(
      "module t;\n"
      "  bit [8*32:1] path;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    path = \"" +
          path +
          "\";\n"
          "    fd = $fopen(path, \"w\");\n"
          "    $fwrite(fd, \"int-name\");\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "int-name");
  std::remove(path.c_str());
}

// §21.3.1 input form: the type argument may also be supplied as a
// string-data-type variable rather than a literal; it still selects the mode.
TEST(IoSystemTaskTest, TypeFromStringDataTypeVariable) {
  SimFixture f;
  const std::string path = "/tmp/deltahdl_e2e_modevar.txt";
  std::remove(path.c_str());
  RunFullSource(
      "module t;\n"
      "  string mode;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    mode = \"w\";\n"
      "    fd = $fopen(\"" +
          path +
          "\", mode);\n"
          "    $fwrite(fd, \"modevar\");\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "modevar");
  std::remove(path.c_str());
}

// §21.3.1 negative form: opening a nonexistent file with a read-only type
// returns 0. Driven from source so the failure value flows through the branch.
TEST(IoSystemTaskTest, MissingReadTargetReturnsZeroFromSource) {
  SimFixture f;
  std::string out = RunFullSourceCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"/nonexistent/deltahdl/none.dat\", \"r\");\n"
      "    if (fd == 0) $display(\"open-failed\");\n"
      "    else $display(\"open-ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "open-failed\n");
}

// §21.3.1: $fopen shall reuse a channel that has been closed. Two opens of the
// same path around a $fclose yield the same descriptor value; observed from
// source by comparing the two returned descriptors.
TEST(IoSystemTaskTest, ClosedChannelReusedFromSource) {
  SimFixture f;
  const std::string path = "/tmp/deltahdl_e2e_reuse.txt";
  std::remove(path.c_str());
  std::string out = RunFullSourceCapture(
      "module t;\n"
      "  integer a, b;\n"
      "  initial begin\n"
      "    a = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fclose(a);\n"
          "    b = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fclose(b);\n"
          "    if (a == b) $display(\"reused\");\n"
          "    else $display(\"distinct\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "reused\n");
  std::remove(path.c_str());
}

}  // namespace
