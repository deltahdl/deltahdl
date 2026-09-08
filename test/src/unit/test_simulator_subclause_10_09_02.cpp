#include <cstdint>
#include <string>
#include <string_view>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// The struct the wide cases are written over. BuildStructTypeInfo lays a packed
// struct out from the top down, so the first-declared member sits at the
// highest bit offset: `a` is at bit 64, above the first word, which is where a
// placement confined to words[0] had nowhere to put it. `w1` takes the keyed
// spelling and `w2` the positional one.
std::string WideStructSource(std::string_view body) {
  return std::string(
             "module t;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] a;\n"
             "    logic [63:0] b;\n"
             "  } wide_t;\n"
             "  wide_t w1, w2;\n"
             "  initial begin\n") +
         std::string(body) +
         "  end\n"
         "endmodule\n";
}

// §10.9.2: "A member:value specifies an explicit value for a named member of
// the structure", and the member is the bits the member occupies. 8'hA5 and
// 64'h42 are chosen so that the answer a placement into words[0] alone gave --
// the two ORed together, 0xE7 -- is neither of them, and so that a case using
// all-ones values could not pass on the OR by accident.
TEST(StructPatternSimulation,
     WideStructNamedPatternPlacesAMemberAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      WideStructSource("    w1 = '{a: 8'hA5, b: 64'h42};\n"), f, "w1");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, 0xA5u);
  EXPECT_EQ(var->value.words[0].aval, 0x42u);
  // No unknown was invented on the way.
  EXPECT_EQ(var->value.words[1].bval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

// §6.3.1: "All bits of 4-state vectors can be independently set to one of the
// four basic values", and §10.9.2 evaluates a member expression in the context
// of an assignment to the member, which for a logic member carries x and z.
// `b`'s known 0x42 is what makes this discriminating: a result that came out
// all-x or all-0 fails, and only the per-member answer passes.
TEST(StructPatternSimulation, NamedStructPatternCarriesAnUnknownMemberValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{a: 8'bxxxxxxxx, b: 8'h42};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx01000010");
}

// The two spellings of one §10.9.2 pattern over one value. The positional form
// falls through to EvalAssignmentPattern, which copies every word and both
// planes, so it is the one that was already right: the assertion states the
// disagreement rather than an expected value, and a fix reaching only the
// keyed arm leaves it standing.
TEST(StructPatternSimulation,
     WideStructNamedPatternAgreesWithThePositionalSpelling) {
  SimFixture f;
  auto* design =
      ElaborateSrc(WideStructSource("    w1 = '{a: 8'bxxxxxxxx, b: 64'h42};\n"
                                    "    w2 = '{8'bxxxxxxxx, 64'h42};\n"),
                   f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* keyed = f.ctx.FindVariable("w1");
  auto* positional = f.ctx.FindVariable("w2");
  ASSERT_NE(keyed, nullptr);
  ASSERT_NE(positional, nullptr);
  ASSERT_EQ(keyed->value.nwords, positional->value.nwords);
  for (uint32_t i = 0; i < keyed->value.nwords; ++i) {
    SCOPED_TRACE(testing::Message() << "word " << i);
    EXPECT_EQ(keyed->value.words[i].aval, positional->value.words[i].aval);
    EXPECT_EQ(keyed->value.words[i].bval, positional->value.words[i].bval);
  }
}

// §10.9.2's default: key reaches its own placement function, with its own
// offset accumulation for a nested substructure, so the member above the first
// word has to be asked of that one separately. 8'hA5 widens to the 64-bit
// member as an assignment to it would.
TEST(StructPatternSimulation,
     WideStructDefaultKeyPlacesEveryMemberAboveTheFirstWord) {
  SimFixture f;
  auto* var =
      RunAndFindVar(WideStructSource("    w1 = '{default: 8'hA5};\n"), f, "w1");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, 0xA5u);
  EXPECT_EQ(var->value.words[0].aval, 0xA5u);
}

TEST(StructPatternSimulation, NamedStructPatternWithDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, default: 8'd99};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2659u);
}

TEST(StructPatternSimulation, NamedStructPatternOnlyDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{default: 8'd55};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 14135u);
}

TEST(StructPatternSimulation, NestedAssignmentPatternEvaluates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  typedef struct { pair_t p1; pair_t p2; } nested_t;\n"
      "  nested_t n;\n"
      "  initial begin\n"
      "    n = '{'{8'd1, 8'd2}, '{8'd3, 8'd4}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StructPatternSimulation, PositionalWithExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { int x; int y; } pair_t;\n"
      "  pair_t s;\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 1;\n"
      "    s = pair_t'{1, 2 + k};\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), (uint64_t{1} << 32) | 3);
}

// §10.9.2: each member expression is evaluated in the context of an assignment
// to the corresponding member's type, so a value wider than the member is
// narrowed to the member's width -- observed here by truncating a 16-bit value
// down to an 8-bit member.
TEST(StructPatternSimulation, MemberValueCoercedToMemberWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 16'hABCD, b: 8'h5A};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD5Au);
}

// §10.9.2: a by-name member value is an arbitrary expression evaluated in the
// context of an assignment to that member -- here a runtime `k + 1` is computed
// through the named-key path and placed into member a.
// §10.9.2: in a positional structure pattern each element is evaluated in the
// context of an assignment to its corresponding member's type, so an element
// wider than its member is narrowed to the member width -- it is not
// concatenated at its self-determined width, which would spill into and corrupt
// the following members.
TEST(StructPatternSimulation, PositionalMemberValueCoercedToMemberWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{16'h1234, 4'h5};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3405u);
}

TEST(StructPatternSimulation, NamedMemberValueEvaluatesExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 5;\n"
      "    p = pair_t'{a: k + 1, b: 8'h02};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0602u);
}

TEST(StructPatternSimulation, ThreeTierPrecedence) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    byte a;\n"
      "    byte b;\n"
      "    logic [7:0] c;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "  initial begin\n"
      "    s = s_t'{a: 8'd1, byte: 8'd2, default: 8'd3};\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);

  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(var->value.ToUint64(), expected);
}

TEST(StructPatternSimulation, TypeKeyMultipleFieldsPipeline) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    int a;\n"
      "    int b;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{int: 32'd42};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), (uint64_t{42} << 32) | 42);
}

// §10.9.2: a type key names a data type and sets every field whose type matches
// it -- here the `logic` vector key covers both logic members (distinct from
// the integer-atom key forms exercised elsewhere).
TEST(StructPatternSimulation, LogicTypeKeyAppliesToVectorFields) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{logic: 8'hCD};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDCDu);
}

// §10.9.2: the default: key is applied recursively to each member of an
// unmatched substructure, so every leaf of the nested struct receives the
// default value -- not just the low bits of the substructure field.
TEST(StructPatternSimulation, DefaultKeyRecursesIntoNestedStruct) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] c; } bc_t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    bc_t bc;\n"
      "  } d_t;\n"
      "  d_t d;\n"
      "  initial begin\n"
      "    d = '{default: 8'hAB};\n"
      "  end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABABu);
}

// §10.9.2: when the same type key appears more than once, the last value is
// used -- and it is applied to every field of that type.
TEST(StructPatternSimulation, TypeKeyLastValueWinsPipeline) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{byte: 8'h11, byte: 8'h22};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2222u);
}

TEST(StructPatternSimulation, ReplicationInStructContext) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{2{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABu);
}

}  // namespace
