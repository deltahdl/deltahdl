#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// ============================================================================
// LRM section 21.1 -- Display system tasks (general I/O overview)
// ============================================================================

TEST(ParserSection21, DisplayBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n"));
}

TEST(ParserSection21, DisplayNoArgs) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $display;\n"
      "endmodule\n"));
}

TEST(ParserSection21, DisplayMultipleArgs) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $display(\"x=%d y=%h\", x, y);\n"
      "endmodule\n"));
}

TEST(ParserSection21, WriteBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $write(\"no newline\");\n"
      "endmodule\n"));
}

TEST(ParserSection21, WriteNoArgs) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $write;\n"
      "endmodule\n"));
}

TEST(ParserSection21, DisplaybHexOctal) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $displayb(\"binary: \", val);\n"
      "    $displayh(\"hex: \", val);\n"
      "    $displayo(\"octal: \", val);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, WritebHexOctal) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $writeb(val);\n"
      "    $writeh(val);\n"
      "    $writeo(val);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, StrobeBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $strobe(\"val=%d\", x);\n"
      "endmodule\n"));
}

TEST(ParserSection21, StrobebHexOctal) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $strobeb(a);\n"
      "    $strobeh(a);\n"
      "    $strobeo(a);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, MonitorBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $monitor(\"a=%b b=%b\", a, b);\n"
      "endmodule\n"));
}

TEST(ParserSection21, MonitorbHexOctal) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $monitorb(a);\n"
      "    $monitorh(a);\n"
      "    $monitoro(a);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, MonitorOnOff) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $monitoron;\n"
      "    $monitoroff;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, DisplayWithFormatSpecifiers) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    $display(\"dec=%0d hex=%0h bin=%0b oct=%0o\", a, a, a, a);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, DisplayInAlwaysBlock) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg clk;\n"
      "  always @(posedge clk)\n"
      "    $display(\"clock edge at %0t\", $time);\n"
      "endmodule\n"));
}

// ============================================================================
// LRM section 21.3.3 -- Formatting data to a string ($swrite, $sformat,
//                        $sformatf)
// ============================================================================

TEST(ParserSection21, SwriteBasic) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  string s;\n"
      "  initial $swrite(s, \"value=%d\", 42);\n"
      "endmodule\n"));
}

TEST(ParserSection21, SwritebHexOctal) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swriteb(s, val);\n"
      "    $swriteh(s, val);\n"
      "    $swriteo(s, val);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, SformatBasic) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  string s;\n"
      "  initial $sformat(s, \"data is %d\", 123);\n"
      "endmodule\n"));
}

TEST(ParserSection21, SformatNoExtraArgs) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  string s;\n"
      "  initial $sformat(s, \"no args here\");\n"
      "endmodule\n"));
}

TEST(ParserSection21, SformatfInExpression) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  string s;\n"
      "  initial s = $sformatf(\"val=%0d\", 42);\n"
      "endmodule\n"));
}

TEST(ParserSection21, SformatfMultipleArgs) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  string s;\n"
      "  initial s = $sformatf(\"a=%0d b=%0h\", 10, 20);\n"
      "endmodule\n"));
}

TEST(ParserSection21, SformatfUsedAsArgument) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $display(\"%s\", $sformatf(\"nested %d\", 7));\n"
      "endmodule\n"));
}

// ============================================================================
// LRM section 21.3.4 -- Reading data from a file ($fgetc, $ungetc, $fgets,
//                        $fscanf, $sscanf, $fread)
// ============================================================================

TEST(ParserSection21, FgetcCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"test.txt\", \"r\");\n"
      "    c = $fgetc(fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, UngetcCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, code;\n"
      "  initial begin\n"
      "    fd = $fopen(\"test.txt\", \"r\");\n"
      "    code = $ungetc(8'h41, fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FgetsCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, code;\n"
      "  reg [8*80:1] str;\n"
      "  initial begin\n"
      "    fd = $fopen(\"test.txt\", \"r\");\n"
      "    code = $fgets(str, fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FscanfCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, code, val;\n"
      "  initial begin\n"
      "    fd = $fopen(\"data.txt\", \"r\");\n"
      "    code = $fscanf(fd, \"%d\", val);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, SscanfCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer code, val;\n"
      "  initial code = $sscanf(\"42\", \"%d\", val);\n"
      "endmodule\n"));
}

TEST(ParserSection21, FreadBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd;\n"
      "  reg [31:0] data;\n"
      "  initial begin\n"
      "    fd = $fopen(\"bin.dat\", \"rb\");\n"
      "    $fread(data, fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FreadWithStartCount) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial begin\n"
      "    fd = $fopen(\"bin.dat\", \"rb\");\n"
      "    $fread(mem, fd, 0, 256);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FopenFcloseCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"output.log\", \"w\");\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FileIOSequence) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"test.txt\", \"r\");\n"
      "    c = $fgetc(fd);\n"
      "    $fseek(fd, 0, 0);\n"
      "    $rewind(fd);\n"
      "    $fflush(fd);\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FdisplayFwrite) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"log.txt\", \"w\");\n"
      "    $fdisplay(fd, \"value=%d\", 99);\n"
      "    $fwrite(fd, \"no newline\");\n"
      "    $fdisplayb(fd, val);\n"
      "    $fdisplayh(fd, val);\n"
      "    $fdisplayo(fd, val);\n"
      "    $fwriteb(fd, val);\n"
      "    $fwriteh(fd, val);\n"
      "    $fwriteo(fd, val);\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FstrobeAndFmonitor) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"log.txt\", \"w\");\n"
      "    $fstrobe(fd, \"val=%d\", x);\n"
      "    $fstrobeb(fd, x);\n"
      "    $fstrobeh(fd, x);\n"
      "    $fstrobeo(fd, x);\n"
      "    $fmonitor(fd, \"x=%b\", x);\n"
      "    $fmonitorb(fd, x);\n"
      "    $fmonitorh(fd, x);\n"
      "    $fmonitoro(fd, x);\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FeofFerror) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, eof_flag;\n"
      "  reg [8*128:1] msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"data.txt\", \"r\");\n"
      "    eof_flag = $feof(fd);\n"
      "    $ferror(fd, msg);\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FtellFseek) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer fd, pos;\n"
      "  initial begin\n"
      "    fd = $fopen(\"data.txt\", \"r\");\n"
      "    pos = $ftell(fd);\n"
      "    $fseek(fd, 10, 0);\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n"));
}

// ============================================================================
// LRM section 21.7.1 -- Creating 4-state VCD file ($dumpfile, $dumpvars,
//                        $dumpoff, $dumpon, $dumpall, $dumpflush, $dumplimit)
// ============================================================================

TEST(ParserSection21, DumpfileBasic) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpfile(\"dump.vcd\");\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpfileDefaultName) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpfile;\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsNoArgs) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars;\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsWithLevels) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars(1, t);\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsAllLevels) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars(0, t);\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsMultipleScopes) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpOffOnSequence) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $dumpvars;\n"
      "    #100 $dumpoff;\n"
      "    #200 $dumpon;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpallAndFlush) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $dumpvars;\n"
      "    #50 $dumpall;\n"
      "    #50 $dumpflush;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumplimitCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $dumpfile(\"out.vcd\");\n"
      "    $dumplimit(1000000);\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n"));
}

// ============================================================================
// LRM section 21.7.1.2 -- Specifying variables to be dumped ($dumpvars)
// ============================================================================

TEST(ParserSection21, DumpvarsLevelOneModule) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars(1, top);\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsLevelZeroAllHierarchy) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars(0, top);\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsMixedModulesAndVars) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpvarsInInitialBlock) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $dumpfile(\"module1.dump\");\n"
      "    $dumpvars(0, t);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, FullVcdWorkflow) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg clk;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars(0, t);\n"
      "    #10 $dumpoff;\n"
      "    #200 $dumpon;\n"
      "    #800 $dumpoff;\n"
      "  end\n"
      "endmodule\n"));
}

// ============================================================================
// Additional coverage -- Memory load/dump tasks from 21.1 overview
// ============================================================================

TEST(ParserSection21, ReadmemhBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $readmemh(\"data.hex\", mem);\n"
      "endmodule\n"));
}

TEST(ParserSection21, ReadmemhWithAddresses) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $readmemh(\"data.hex\", mem, 0, 127);\n"
      "endmodule\n"));
}

TEST(ParserSection21, ReadmembBasicCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $readmemb(\"data.bin\", mem);\n"
      "endmodule\n"));
}

TEST(ParserSection21, ReadmembWithAddresses) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $readmemb(\"data.bin\", mem, 16, 31);\n"
      "endmodule\n"));
}

TEST(ParserSection21, WritememhCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $writememh(\"out.hex\", mem);\n"
      "endmodule\n"));
}

TEST(ParserSection21, WritemembCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $writememb(\"out.bin\", mem);\n"
      "endmodule\n"));
}

// ============================================================================
// Additional coverage -- Command line input from 21.1 overview
// ============================================================================

TEST(ParserSection21, TestPlusargsCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    if ($test$plusargs(\"VERBOSE\"))\n"
      "      $display(\"verbose mode\");\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, ValuePlusargsCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  integer depth;\n"
      "  initial begin\n"
      "    if ($value$plusargs(\"DEPTH=%d\", depth))\n"
      "      $display(\"depth=%0d\", depth);\n"
      "  end\n"
      "endmodule\n"));
}

// ============================================================================
// Additional coverage -- VCD port dump tasks from 21.1 overview
// ============================================================================

TEST(ParserSection21, DumpportsCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpports(t, \"ports.vcd\");\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpportsOffOnFlush) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    $dumpports(t, \"ports.vcd\");\n"
      "    #100 $dumpportsoff;\n"
      "    #200 $dumpportson;\n"
      "    #300 $dumpportsflush;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserSection21, DumpportslimitCall) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial $dumpportslimit(500000);\n"
      "endmodule\n"));
}

// ============================================================================
// AST-level checks for system calls in initial blocks
// ============================================================================

TEST(ParserSection21, DisplayParsesAsSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserSection21, DumpvarsInsideBeginEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumpfile(\"test.vcd\");\n"
      "    $dumpvars(0, t);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}
