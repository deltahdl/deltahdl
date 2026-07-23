#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(FileReadFunctions, FgetsReadsLine) {
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

TEST(FileReadFunctions, UngetcPushesBack) {
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

TEST(FileReadFunctions, FscanfReadsFormatted) {
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

// §21.3.4: a descriptor may be read from only when its file was opened with a
// read ("r"/"rb") or read-update ("r+"/"r+b"/"rb+") type. Whether a given fd is
// readable is decided entirely by how the descriptor was produced -- the type
// argument of the §21.3.1 $fopen that created it -- so these tests build the
// descriptor from real $fopen source syntax and drive the whole pipeline,
// observing each read function's failure result through $display.

// Runs a single-module source through parse -> elaborate -> lower -> run while
// capturing everything the run writes to stdout.
static std::string RunCapture(const std::string& src, SysTaskFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Creates `path` holding `content` so a read-type $fopen has data to deliver.
static void SeedFile(const std::string& path, const std::string& content) {
  std::ofstream ofs(path, std::ios::binary);
  ofs << content;
}

TEST(FileReadFunctions, FgetcOnWriteOnlyFdReturnsEof) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_w_fgetc.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"c=%0d\", c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FgetcOnUpdateTypeWithDataStillRejected) {
  // "w+" opens for update, so the host stream really can deliver the byte just
  // written once the position is rewound -- yet §21.3.4 authorizes reading only
  // for the "r"/"r+" families, so the read must still fail. This is the case
  // that distinguishes the standard's gate from mere host-stream behavior.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_wplus_data.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w+\");\n"
          "    $fwrite(fd, \"Q\");\n"
          "    r = $rewind(fd);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"c=%0d\", c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FgetcOnAppendUpdateTypeRejected) {
  // "a+" also permits host-level reading (from the start of the file), but is
  // not an "r"/"r+" family type, so the read is refused.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_aplus.txt";
  SeedFile(tmp, "Q");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"a+\");\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"c=%0d\", c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FgetsOnWriteOnlyFdReturnsZeroAndLeavesDest) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_w_fgets.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [63:0] line;\n"
      "  initial begin\n"
      "    line = 64'h4141414141414141;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $fgets(line, fd);\n"
          "    $display(\"code=%0d line=%h\", code, line);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 line=4141414141414141"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, UngetcOnWriteOnlyFdReturnsEof) {
  // A push back is a read-side operation; on a write-only descriptor it fails
  // with the same EOF result a failed host push back reports.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_w_ungetc.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $ungetc(72, fd);\n"
          "    $display(\"code=%0d\", code);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FscanfOnWriteOnlyFdConvertsNothing) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_w_fscanf.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, v;\n"
      "  initial begin\n"
      "    v = 42;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $fscanf(fd, \"%d\", v);\n"
          "    $display(\"code=%0d v=%0d\", code, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 v=42"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FreadOnWriteOnlyFdReturnsZeroAndLeavesDest) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_w_fread.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [31:0] val;\n"
      "  initial begin\n"
      "    val = 32'haabbccdd;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $fread(val, fd);\n"
          "    $display(\"code=%0d val=%h\", code, val);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 val=aabbccdd"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FreadMemoryFormOnWriteOnlyFdRejected) {
  // The gate covers the memory form of $fread as well: no bytes are consumed
  // and the destination words keep their prior contents.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_w_fread_mem.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    mem[0] = 8'h5a;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $fread(mem, fd);\n"
          "    $display(\"code=%0d m0=%h\", code, mem[0]);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 m0=5a"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FgetsAndFreadAllowedOnReadTypeFd) {
  // Accepting side of the gate for $fgets and $fread: on an "r" descriptor the
  // line read returns its character count and, after a rewind, the binary read
  // fills the packed destination big-endian first.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_r_fgets_fread.txt";
  SeedFile(tmp, "HI\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, n1, n2;\n"
      "  reg [31:0] line;\n"
      "  reg [15:0] w;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n1 = $fgets(line, fd);\n"
          "    r = $rewind(fd);\n"
          "    n2 = $fread(w, fd);\n"
          "    $display(\"n1=%0d n2=%0d w=%h\", n1, n2, w);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n1=3 n2=2 w=4849"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, FscanfAllowedOnReadTypeFd) {
  // Accepting side of the gate for $fscanf: a conversion on an "r" descriptor
  // proceeds and reports the matched-field count.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_r_fscanf.txt";
  SeedFile(tmp, "42");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, n, v;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, \"%d\", v);\n"
          "    $display(\"n=%0d v=%0d\", n, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 v=42"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, UngetcAllowedOnReadTypeFd) {
  // Accepting side of the gate for $ungetc: the push back on an "r" descriptor
  // reports success and the pushed character is what the next read delivers.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_r_ungetc.txt";
  SeedFile(tmp, "XY");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, code, c2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(fd);\n"
          "    code = $ungetc(72, fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    $display(\"c1=%0d code=%0d c2=%0d\", c1, code, c2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=88 code=0 c2=72"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, ReadTypeFamilyAllowsReading) {
  // Both spellings of the read type ("r" and the binary "rb") authorize reads.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_r_family.txt";
  SeedFile(tmp, "Q");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd1, fd2, c1, c2;\n"
      "  initial begin\n"
      "    fd1 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(fd1);\n"
          "    fd2 = $fopen(\"" +
          tmp +
          "\", \"rb\");\n"
          "    c2 = $fgetc(fd2);\n"
          "    $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "    $fclose(fd1);\n"
          "    $fclose(fd2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=81 c2=81"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, ReadUpdateTypeFamilyAllowsReading) {
  // The read-update family ("r+" and its binary spelling "rb+") likewise
  // authorizes reads.
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2134_rplus_family.txt";
  SeedFile(tmp, "Q");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd1, fd2, c1, c2;\n"
      "  initial begin\n"
      "    fd1 = $fopen(\"" +
          tmp +
          "\", \"r+\");\n"
          "    c1 = $fgetc(fd1);\n"
          "    fd2 = $fopen(\"" +
          tmp +
          "\", \"rb+\");\n"
          "    c2 = $fgetc(fd2);\n"
          "    $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "    $fclose(fd1);\n"
          "    $fclose(fd2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=81 c2=81"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FileReadFunctions, ReadRejectedOnStandardOutputDescriptor) {
  // STDOUT (32'h8000_0001) is pre-opened for append, not reading; a read on
  // its reserved descriptor reports end-of-file rather than touch the stream.
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer c;\n"
      "  initial begin\n"
      "    c = $fgetc(32'h8000_0001);\n"
      "    $display(\"c=%0d\", c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c=-1"), std::string::npos) << out;
}

TEST(FileReadFunctions, FreadReadsBinary) {
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
