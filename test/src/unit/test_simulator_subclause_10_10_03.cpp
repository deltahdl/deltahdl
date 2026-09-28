

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_string_var.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatSim, TypedAssignPatternInArrayConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3 = '{1, 2, 3};\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (int i = 1; i <= 9; ++i) {
    auto name = "A9[" + std::to_string(i) + "]";
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr) << name;
    EXPECT_EQ(var->value.ToUint64(), static_cast<uint64_t>(i)) << name;
  }
}

TEST(UnpackedArrayConcatSim, UnpackedArrayConcatInAssignPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int C[2][2];\n"
      "  initial C = '{{1, 2}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c00 = f.ctx.FindVariable("C[0][0]");
  auto* c01 = f.ctx.FindVariable("C[0][1]");
  auto* c10 = f.ctx.FindVariable("C[1][0]");
  auto* c11 = f.ctx.FindVariable("C[1][1]");
  ASSERT_NE(c00, nullptr);
  ASSERT_NE(c01, nullptr);
  ASSERT_NE(c10, nullptr);
  ASSERT_NE(c11, nullptr);
  EXPECT_EQ(c00->value.ToUint64(), 1u);
  EXPECT_EQ(c01->value.ToUint64(), 2u);
  EXPECT_EQ(c10->value.ToUint64(), 3u);
  EXPECT_EQ(c11->value.ToUint64(), 4u);
}

TEST(UnpackedArrayConcatSim, VectorConcatInByteArrayConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte BA[2];\n"
      "  initial BA = {{4'h0, 4'h6}, {4'h0, 4'hf}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* ba0 = f.ctx.FindVariable("BA[0]");
  auto* ba1 = f.ctx.FindVariable("BA[1]");
  ASSERT_NE(ba0, nullptr);
  ASSERT_NE(ba1, nullptr);
  EXPECT_EQ(ba0->value.ToUint64(), 6u);
  EXPECT_EQ(ba1->value.ToUint64(), 15u);
}

// §10.10.3, string element type, end-to-end through the §11.4.12 string-
// concatenation dependency: because a complete unpacked array concatenation has
// no self-determined type, a `{...}` written as an item of an outer unpacked
// array concatenation is read as a self-determined STRING concatenation, not as
// an (illegal) nested unpacked array concatenation. The nesting rule is exactly
// what makes that reading unambiguous. Built from real string source and run:
// the inner `{"x", S2}` fuses into ONE queue element ("xbb"), so the queue
// holds two elements rather than three — the observable signature that the
// inner braces were treated as a single self-determined string-concatenation
// item.
TEST(UnpackedArrayConcatSim, StringConcatItemFusesIntoSingleElement) {
  RunAndExpectStringQueue(
      "module t;\n"
      "  string S1, S2;\n"
      "  string SQ[$];\n"
      "  initial begin\n"
      "    S1 = \"aa\";\n"
      "    S2 = \"bb\";\n"
      "    SQ = {S1, {\"x\", S2}};\n"
      "  end\n"
      "endmodule\n",
      "SQ", {"aa", "xbb"});
}

// §10.10.3's own example, run as written. It adds the two things the reduced
// case above leaves out: the queue names itself as an item, so its existing
// elements are expanded in place, and the braced item sits after that
// expansion rather than at a fixed offset. The clause states the result
// exactly -- '{"S1", "element 0", "element 1", "element 3 is S2"} -- so the
// queue ends with four elements, the last of them the two strings inside the
// inner braces joined into one.
// One thing in the clause's source is written differently here, in the setup
// rather than in the line under test, so that a failure can only be about the
// concatenation: the clause declares the queue as
// `typedef string T_SQ[$]; T_SQ SQ;` and it is declared directly instead. That
// substitution produces the same starting queue and replaces a spelling with a
// separate open defect of its own, so leaving it in would make this test fail
// for a reason that has nothing to do with §10.10.3. The seeding assignment
// pattern `SQ = '{"element 0", "element 1"};` is the clause's own.
TEST(UnpackedArrayConcatSim, ClauseExampleExpandsQueueAndFusesBracedItem) {
  RunAndExpectStringQueue(
      "module t;\n"
      "  string S1, S2;\n"
      "  string SQ[$];\n"
      "  initial begin\n"
      "    S1 = \"S1\";\n"
      "    S2 = \"S2\";\n"
      "    SQ = '{\"element 0\", \"element 1\"};\n"
      "    SQ = {S1, SQ, {\"element 3 is \", S2} };\n"
      "  end\n"
      "endmodule\n",
      "SQ", {"S1", "element 0", "element 1", "element 3 is S2"});
}

// Same rule at the declaration-initializer position — a distinct
// assignment-like syntactic position that produces the input differently from a
// procedural assignment. The string-literal items are built from real source
// and the queue is read back from the simulated result: the nested string
// concatenation
// `{"x", "bb"}` again yields a single element, so the initialized queue has two
// elements.
TEST(UnpackedArrayConcatSim, StringConcatItemInDeclInitFusesIntoSingleElement) {
  RunAndExpectStringQueue(
      "module t;\n"
      "  string SQ[$] = {\"aa\", {\"x\", \"bb\"}};\n"
      "endmodule\n",
      "SQ", {"aa", "xbb"});
}

// §10.10.3's own example, `SQ = {S1, SQ, T_SQ'{"element 3 is ", S2}}`: only a
// plain inner brace pair is a string concatenation, and an item that is an
// assignment pattern typed as an array of strings contributes each of its
// elements. Read as the string concatenation "element 3 is S2", the item gave
// one element where the pattern gives two.
TEST(UnpackedArrayConcatSim, TypedPatternItemContributesEachElement) {
  RunAndExpectStringQueue(
      "module t;\n"
      "  typedef string T_SQ[$];\n"
      "  string SQ[$];\n"
      "  initial SQ = {\"S1\", T_SQ'{\"element 3 is \", \"S2\"}};\n"
      "endmodule\n",
      "SQ", {"S1", "element 3 is ", "S2"});
}

// The same of a queue of integers, `{1, T_IQ'{2, 3}}`, and of a typed item
// beside a named queue.
TEST(UnpackedArrayConcatSim, TypedIntegerPatternItemContributesEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef int T_IQ[$];\n"
      "  int s[$], q[$] = '{9};\n"
      "  initial begin\n"
      "    s = {1, T_IQ'{2, 3}, q};\n"
      "    $display(\"%0d %0d %0d %0d\", s.size(), s[1], s[2], s[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 2 3 9\n");
}

// §10.10.3's jagged array example: a queue whose elements are queues, given a
// positional pattern, holds one element per item, and each item is that
// element's queue -- the one-item concatenation {1}, the typed pattern
// T_QI'{2,3,4} and the concatenation {5,6}. No inner queue was built, so every
// element read 0 and jagged[1] was empty. The declaration initializer and the
// procedural assignment take the same pattern.
TEST(UnpackedArrayConcatSim, JaggedQueueOfQueuesBuildsEachInnerQueue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef int T_QI[$];\n"
      "  T_QI jagged[$] = '{ {1}, T_QI'{2,3,4}, {5,6} };\n"
      "  T_QI later[$];\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", jagged[0][0],\n"
      "             jagged[1][0], jagged[1][1], jagged[1][2], jagged[2][0],\n"
      "             jagged[2][1], jagged[1].size());\n"
      "    later = '{ T_QI'{7}, {8, 9} };\n"
      "    $display(\"%0d %0d %0d %0d\", later.size(), later[0][0],\n"
      "             later[1].size(), later[1][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 4 5 6 3\n2 7 2 9\n");
}

}  // namespace
