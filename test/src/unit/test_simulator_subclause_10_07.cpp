#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentExtensionTruncationSim, TruncationDiscardsMSBs) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] a;\n"
      "  initial begin\n"
      "    a = 8'hff;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 0x3Fu);
}

TEST(AssignmentExtensionTruncationSim, TruncationSignedIntoNarrowerSigned) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic signed [4:0] b;\n"
      "  initial begin\n"
      "    b = 8'hff;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);

  EXPECT_EQ(b->value.ToUint64(), 0x1Fu);
}

TEST(AssignmentExtensionTruncationSim, ExtensionZeroPadUnsigned) {
  SimFixture f;
  auto* wide = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  initial begin\n"
      "    wide = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(wide, nullptr);

  EXPECT_EQ(wide->value.ToUint64(), 0x00ABu);
  EXPECT_EQ(wide->value.width, 16u);
}

TEST(AssignmentExtensionTruncationSim, TruncationTo4Bit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin\n"
      "    narrow = 32'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xDu);
}

TEST(AssignmentExtensionTruncationSim, NBATruncation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] narrow;\n"
      "  initial begin\n"
      "    narrow <= 32'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(AssignmentExtensionTruncationSim, NBAExtension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] wide;\n"
      "  initial begin\n"
      "    wide <= 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
  EXPECT_EQ(var->value.width, 32u);
}

TEST(AssignmentExtensionTruncationSim, ContAssignTruncation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] out;\n"
      "  logic [7:0] in_val = 8'hAB;\n"
      "  assign out = in_val;\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(AssignmentExtensionTruncationSim, ContAssignExtension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] out;\n"
      "  logic [3:0] in_val = 4'hA;\n"
      "  assign out = in_val;\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x000Au);
}

TEST(AssignmentExtensionTruncationSim, RhsSizedToLhsWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin narrow = 4'hF; wide = narrow; end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, SignedRhsSignExtendsToLhs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin narrow = -4'sd1; wide = narrow; end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(AssignmentExtensionTruncationSim, WideRhsTruncated) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  initial begin wide = 8'hAB; narrow = wide; end\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(AssignmentExtensionTruncationSim, SignedRhsToUnsignedLhsSignExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic signed [3:0] src;\n"
      "  initial begin src = -4'sd2; dst = src; end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFEu);
}

TEST(AssignmentExtensionTruncationSim, UnsignedRhsToSignedLhsZeroExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] dst;\n"
      "  logic [3:0] src;\n"
      "  initial begin src = 4'hF; dst = src; end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, SignedPositiveRhsZeroFillsUpperBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] dst;\n"
      "  logic signed [3:0] src;\n"
      "  initial begin src = 4'sb0101; dst = src; end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x05u);
}

TEST(AssignmentExtensionTruncationSim, SameWidthNoExtension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic [7:0] src;\n"
      "  initial begin src = 8'hA5; dst = src; end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(AssignmentExtensionTruncationSim, SignedWideTruncated) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] dst;\n"
      "  logic signed [7:0] src;\n"
      "  initial begin src = -8'sd3; dst = src; end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDu);
}

TEST(AssignmentExtensionTruncationSim,
     RhsExpressionSignednessDeterminesExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst_signed_rhs;\n"
      "  logic [7:0] dst_unsigned_rhs;\n"
      "  logic [3:0] val;\n"
      "  initial begin\n"
      "    val = 4'hF;\n"
      "    dst_signed_rhs = $signed(val);\n"
      "    dst_unsigned_rhs = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("dst_signed_rhs");
  auto* u = f.ctx.FindVariable("dst_unsigned_rhs");
  ASSERT_NE(s, nullptr);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 0xFFu);
  EXPECT_EQ(u->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, LhsContextWidensRhsExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [4:0] sum;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 4'h1;\n"
      "    sum = a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x10u);
}

TEST(AssignmentExtensionTruncationSim, TruncationChangesSignOfResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] dst;\n"
      "  logic signed [7:0] src;\n"
      "  initial begin\n"
      "    src = 8'sd120;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8u);
}

TEST(AssignmentExtensionTruncationSim, TruncationToOneBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic dst;\n"
      "  initial dst = 8'hFE;\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AssignmentExtensionTruncationSim, ExtensionOneBitToWide) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic src;\n"
      "  initial begin src = 1'b1; dst = src; end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x01u);
}

TEST(AssignmentExtensionTruncationSim, NBASignedExtension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin\n"
      "    narrow = -4'sd3;\n"
      "    wide <= narrow;\n"
      "  end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFDu);
}

TEST(AssignmentExtensionTruncationSim, ContAssignSignedExtension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow = -4'sd5;\n"
      "  assign wide = narrow;\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFBu);
}

TEST(AssignmentExtensionTruncationSim, ContAssignSignedTruncation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] narrow;\n"
      "  logic signed [7:0] wide = -8'sd113;\n"
      "  assign narrow = wide;\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

TEST(AssignmentExtensionTruncationSim, SignedLiteralTruncatedToUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] a;\n"
      "  initial a = 8'sh8f;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim, TruncationDiscardsUnknownMSBs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow = 8'bxxxx_0101;\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(AssignmentExtensionTruncationSim, SignExtensionPropagatesUnknownSignBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] wide;\n"
      "  logic signed [3:0] narrow;\n"
      "  initial begin narrow = 4'bx101; wide = narrow; end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ((var->value.words[0].bval >> 4) & 0xFull, 0xFull);
}

TEST(AssignmentExtensionTruncationSim, WideSignExtensionAcrossWordBoundary) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [71:0] wide;\n"
      "  logic signed [67:0] narrow;\n"
      "  initial begin narrow = 68'hF_FFFF_FFFF_FFFF_FFFF; wide = narrow; end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 72u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, ~uint64_t{0});
  EXPECT_EQ(var->value.words[0].bval, 0u);
  EXPECT_EQ(var->value.words[1].aval & 0xFFull, 0xFFull);
  EXPECT_EQ(var->value.words[1].bval & 0xFFull, 0u);
}

TEST(AssignmentExtensionTruncationSim, WideTruncationDiscardsHighWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [71:0] wide;\n"
      "  initial begin wide = 72'hFF000000000000000A; narrow = wide; end\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(AssignmentExtensionTruncationSim, DeclarationInitializerTruncates) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] x = 8'hAB;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.width, 4u);
  EXPECT_EQ(x->value.ToUint64(), 0xBu);
}

TEST(AssignmentExtensionTruncationSim, DeclarationInitializerExtendsUnsigned) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] y = 4'hA;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.width, 8u);
  EXPECT_EQ(y->value.ToUint64(), 0x0Au);
}

TEST(AssignmentExtensionTruncationSim, BuiltinSignedTypeSignExtends) {
  SimFixture f;
  auto* wide = RunAndFindVar(
      "module t;\n"
      "  int wide;\n"
      "  byte narrow;\n"
      "  initial begin narrow = -8'sd3; wide = narrow; end\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(wide, nullptr);

  EXPECT_EQ(wide->value.ToUint64(), 0xFFFFFFFDu);
}

TEST(AssignmentExtensionTruncationSim, SizeMismatchAcceptedNotRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow = 32'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* narrow = f.ctx.FindVariable("narrow");
  ASSERT_NE(narrow, nullptr);

  EXPECT_EQ(narrow->value.ToUint64(), 0xDu);
}

TEST(AssignmentExtensionTruncationSim, FunctionBodyTruncatesToTheTargetWidth) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] f();\n"
      "    logic [5:0] a;\n"
      "    a = 8'hff;\n"
      "    return a;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0x3Fu);
}

TEST(AssignmentExtensionTruncationSim, TaskBodyTruncatesToTheTargetWidth) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task automatic narrow(output logic [31:0] o);\n"
      "    logic [5:0] a;\n"
      "    a = 8'hff;\n"
      "    o = a;\n"
      "  endtask\n"
      "  initial begin\n"
      "    narrow(x);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0x3Fu);
}

TEST(AssignmentExtensionTruncationSim,
     FunctionBodyTruncationKeepsTheHighWordOfAWideTarget) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] x;\n"
      "  function logic [63:0] f();\n"
      "    logic [39:0] w;\n"
      "    w = 48'hFFFF00000001;\n"
      "    return w;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 1095216660481ull);
}

TEST(AssignmentExtensionTruncationSim, StringLocalHasNoWidthToTruncateTo) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function int f();\n"
      "    string s;\n"
      "    s = \"hi\";\n"
      "    s = \"hello world\";\n"
      "    return s.len();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 11u);
}

TEST(AssignmentExtensionTruncationSim, BlockDeclarationInitializerTruncates) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    static logic [3:0] v = 8'hAB;\n"
      "    x = v;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0x0Bu);
}

TEST(AssignmentExtensionTruncationSim,
     BlockDeclarationInitializerTruncationKeepsTheHighWord) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] x;\n"
      "  initial begin\n"
      "    static logic [39:0] w = 48'hFFFF00000001;\n"
      "    x = w;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 1095216660481ull);
}

TEST(AssignmentExtensionTruncationSim,
     StringBlockDeclarationInitializerHasNoWidthToTruncateTo) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    static string s = \"hello world\";\n"
      "    x = s.len();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 11u);
}

TEST(AssignmentExtensionTruncationSim,
     TaskBodyArrayElementWriteTruncatesToTheElementWidth) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a [0:3];\n"
      "  task put();\n"
      "    a[1] = 8'hFF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a[1] = 4'h0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n",
      f, "a[1]");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0xFu);
}

TEST(AssignmentExtensionTruncationSim,
     FunctionBodyPartSelectWriteReachesOnlyTheSelectedBits) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  function void put();\n"
      "    v[3:0] = 8'hAB;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    v = 8'hF0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0xFBu);
}

TEST(AssignmentExtensionTruncationSim,
     FunctionBodyBitSelectWriteReachesTheSelectedBit) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  function void put();\n"
      "    v[5] = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0x20u);
}

TEST(AssignmentExtensionTruncationSim,
     TaskBodyPartSelectWriteReachesOnlyTheSelectedBits) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  task put();\n"
      "    v[7:4] = 8'hAB;\n"
      "  endtask\n"
      "  initial begin\n"
      "    v = 8'h0F;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0xBFu);
}

TEST(AssignmentExtensionTruncationSim,
     ClassMethodTaskTruncatesToTheTargetWidth) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "class C;\n"
      "  task put(output logic [7:0] o);\n"
      "    logic [3:0] n;\n"
      "    n = 8'hFF;\n"
      "    o = n;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    v = 8'h00;\n"
      "    c.put(v);\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0x0Fu);
}

TEST(AssignmentExtensionTruncationSim,
     ClassMethodTaskPartSelectWriteReachesOnlyTheSelectedBits) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "class C;\n"
      "  task put(output logic [7:0] o);\n"
      "    o = 8'hF0;\n"
      "    o[3:0] = 8'hAB;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    v = 8'h00;\n"
      "    c.put(v);\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 0xFBu);
}

}  // namespace
