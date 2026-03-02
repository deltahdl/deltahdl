// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

TEST(Section20, OnehotTrue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, OnehotFalseZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, OnehotFalseMultiple) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Onehot0True) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Onehot0TrueOneBit) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Onehot0FalseMultiple) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, IsunknownFalse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, IsunknownTrueXVar) {
  SimFixture f;
  // CreateVariable initializes to X (bval = all ones).
  f.ctx.CreateVariable("xvar", 8);
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeId(f.arena, "xvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// ============================================================================
// §20.11 — $test$plusargs, $value$plusargs
// ============================================================================
TEST(Section20, TestPlusargsNotFound) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, TestPlusargsFound) {
  SimFixture f;
  f.ctx.AddPlusArg("VERBOSE");
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, TestPlusargsPrefixMatch) {
  SimFixture f;
  f.ctx.AddPlusArg("VERBOSE=1");
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MakeStrLit(f.arena, "VERB")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, ValuePlusargsFound) {
  SimFixture f;
  f.ctx.AddPlusArg("DEPTH=42");
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MakeStrLit(f.arena, "DEPTH=%d"), MakeId(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest_var->value.ToUint64(), 42u);
}

TEST(Section20, ValuePlusargsNotFound) {
  SimFixture f;
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MakeStrLit(f.arena, "DEPTH=%d"), MakeId(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ============================================================================
// §20.6.1 — $typename
// ============================================================================
TEST(Section20, Typename) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Returns a string-encoded result; just verify it doesn't crash and
  // returns a non-zero width.
  EXPECT_GT(result.width, 0u);
}

// ============================================================================
// §21.3.3 — $sformatf
// ============================================================================
TEST(Section20, SformatfBasic) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$sformatf",
                  {MakeStrLit(f.arena, "val=%d"), MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // $sformatf returns a string as a Logic4Vec; the width should be
  // text.size()*8. "val=42" is 6 chars = 48 bits.
  EXPECT_EQ(result.width, 48u);
}

// ============================================================================
// §21.3.1/§21.3.2 — $fopen, $fclose
// ============================================================================
TEST(Section21, FopenFclose) {
  SimFixture f;
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
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  std::remove(tmp_path.c_str());
}

TEST(Section21, FopenInvalidFile) {
  SimFixture f;
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
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_fdisplay.txt";

  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* fd_lit = MakeInt(f.arena, fd_val.ToUint64());
  auto* disp_expr = MakeSysCall(
      f.arena, "$fdisplay",
      {fd_lit, MakeStrLit(f.arena, "value=%d"), MakeInt(f.arena, 99)});
  EvalExpr(disp_expr, f.ctx, f.arena);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
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
  SimFixture f;
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
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeId(f.arena, "mem")});
  EvalExpr(expr, f.ctx, f.arena);

  // The first value (0x0A = 10) should be in mem[0] = "mem".
  // For a flat variable, readmemh stores the first value.
  EXPECT_EQ(arr->value.ToUint64(), 0x0Au);

  std::remove(tmp_path.c_str());
}

TEST(Section21, ReadmembBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_readmemb.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "1010\n0110\n";
  }

  auto* arr = f.ctx.CreateVariable("bmem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MakeSysCall(
      f.arena, "$readmemb",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeId(f.arena, "bmem")});
  EvalExpr(expr, f.ctx, f.arena);

  // First value: 1010 binary = 10 decimal.
  EXPECT_EQ(arr->value.ToUint64(), 0b1010u);

  std::remove(tmp_path.c_str());
}

// ============================================================================
// §21.4 — $writememh, $writememb
// ============================================================================
TEST(Section21, WritememhBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememh.txt";

  auto* var = f.ctx.CreateVariable("wmem", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeSysCall(
      f.arena, "$writememh",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeId(f.arena, "wmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());

  EXPECT_NE(contents.find("ff"), std::string::npos);

  std::remove(tmp_path.c_str());
}

TEST(Section21, WritemembBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememb.txt";

  auto* var = f.ctx.CreateVariable("wbmem", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0b10101010);

  auto* expr = MakeSysCall(
      f.arena, "$writememb",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeId(f.arena, "wbmem")});
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
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("scanned", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MakeSysCall(f.arena, "$sscanf",
                  {MakeStrLit(f.arena, "42"), MakeStrLit(f.arena, "%d"),
                   MakeId(f.arena, "scanned")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);  // 1 item scanned
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

// ============================================================================
// §21.3 — $rewind(fd)
// ============================================================================
TEST(Section21, Rewind) {
  SimFixture f;
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
  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('A'));

  // Rewind.
  auto* rw = MakeSysCall(f.arena, "$rewind", {MakeInt(f.arena, fd)});
  EvalExpr(rw, f.ctx, f.arena);

  // Read first char again — should be 'A' after rewind.
  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

// ============================================================================
// §21.3 — $ungetc(char, fd)
// ============================================================================
TEST(Section21, Ungetc) {
  SimFixture f;
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
                         {MakeInt(f.arena, 'Z'), MakeInt(f.arena, fd)});
  EvalExpr(ug, f.ctx, f.arena);

  // Next read should return 'Z'.
  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('Z'));

  // Then 'X' (the original first char).
  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('X'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
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
