#include <iostream>
#include <sstream>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
inline std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

inline std::string DecodeAsciiBytes(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string out;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= vec.nwords) continue;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) out += ch;
  }
  return out;
}

TEST(UtilitySystemTaskTest, Typename) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameDefaultSigningRemoved) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("y", 32);
  var->is_signed = true;
  var->is_4state = false;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "y")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "int");
}

TEST(UtilitySystemTaskTest, TypenameSingleBitLogic) {
  SimFixture f;
  f.ctx.CreateVariable("flag", 1);
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "flag")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameSingleBitTwoState) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("b1", 1);
  var->is_4state = false;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "b1")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "bit");
}

TEST(UtilitySystemTaskTest, TypenameTwoStateSignedNarrowVector) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("by", 8);
  var->is_4state = false;
  var->is_signed = true;
  auto* expr = MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "by")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "bit[7:0]");
}

TEST(UtilitySystemTaskTest, TypenameUnknownIdentifierFallback) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$typename", {MakeId(f.arena, "no_such_var")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

TEST(UtilitySystemTaskTest, TypenameNoArgsFallback) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$typename", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic");
}

// Syntax 20-6 second form: $typename ( data_type ). A built-in type keyword
// resolves to itself. Parsed from real source so the identifier/keyword
// argument arrives exactly as the parser produces it (kIdentifier "int").
TEST(UtilitySystemTaskTest, TypenameDataTypeFormBuiltinKeyword) {
  SimFixture f;
  auto* expr = ParseExprFrom("$typename(int)", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "int");
}

// Syntax 20-6 second form with a packed dimension: $typename(logic [7:0])
// resolves to the keyword with its range rendered as unsized decimal bounds
// (step g). Parsed from real source so the range-select argument arrives as
// the parser produces it (kSelect over the "logic" keyword).
TEST(UtilitySystemTaskTest, TypenameDataTypeFormPackedVector) {
  SimFixture f;
  auto* expr = ParseExprFrom("$typename(logic [7:0])", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(DecodeAsciiBytes(result), "logic[7:0]");
}

// Expression form driven end-to-end: the type name of a real vector
// declaration is reported with its range as an unsized decimal (step g),
// observed through the full parse/elaborate/lower/run pipeline via $display.
TEST(UtilitySystemTaskTest, TypenameExpressionFormVectorEndToEnd) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial $display(\"%s\", $typename(data));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "logic[7:0]\n");
}

// The expression argument yields the self-determined type and is never
// evaluated: the operand carries a runtime value, yet $typename reports the
// declared 2-state type independent of that value. Driven end-to-end.
TEST(UtilitySystemTaskTest, TypenameExpressionOperandNotEvaluated) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0] n;\n"
      "  initial begin\n"
      "    n = 4'hA;\n"
      "    $display(\"%s\", $typename(n));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "bit[3:0]\n");
}

// §20.6.1 notes that $typename produces a string usable for stricter type
// comparison than a type reference (relating to the §6.22.1 type-matching
// process). Built from real declarations: two vectors of the same type yield
// identical strings, while a differently sized vector yields a distinct one.
TEST(UtilitySystemTaskTest, TypenameDistinguishesTypesForStringComparison) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [3:0] c;\n"
      "  initial begin\n"
      "    $display(\"%s\", $typename(a));\n"
      "    $display(\"%s\", $typename(b));\n"
      "    $display(\"%s\", $typename(c));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "logic[7:0]\nlogic[7:0]\nlogic[3:0]\n");
}

}  // namespace
