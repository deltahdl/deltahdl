#include "builders_ast.h"
#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StructPatternSimulation, NamedStructPatternInit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, b: 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(StructPatternSimulation, NamedStructPatternReversedOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{b: 8'd20, a: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(StructPatternSimulation, PositionalStructPatternInit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd3, 8'd7};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 775u);
}

TEST(StructPatternSimulation, ThreeFieldStructNamedPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] x;\n"
      "    logic [7:0] y;\n"
      "    logic [7:0] z;\n"
      "  } triple_t;\n"
      "  triple_t v;\n"
      "  initial begin\n"
      "    v = triple_t'{x: 8'd1, y: 8'd2, z: 8'd3};\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x010203u);
}

TEST(StructPatternSimulation, ConstPatternInVarDeclInit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p = '{8'd100, 8'd200};\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 25800u);
}

TEST(StructPatternValidation, InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{nonexistent: 8'hFF};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nonexistent' is not a member of the struct", 2,
                            "10.9.2"));
}

// §10.9.2: a member name key resolves only against the top-level members of the
// structure. A name that exists merely inside a substructure is not a valid key
// and is rejected, rather than reaching into the nested member.
TEST(StructPatternValidation, SubstructureMemberNotTopLevelKey) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [7:0] inner; } sub_t;\n"
      "  struct packed { sub_t s; logic [7:0] b; } v = "
      "'{inner: 8'h01, b: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'inner' is not a member of the struct", 3,
                            "10.9.2"));
}

TEST(StructPatternValidation, DuplicateKey) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate member key 'a' in pattern", 2,
                            "10.9.2"));
}

TEST(StructPatternValidation, UncoveredMember) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "member 'b' not covered by assignment pattern", 2,
                            "10.9.2"));
}

TEST(StructPatternValidation, DefaultSatisfiesCoverage) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t s = '{default: 8'h00};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StructPatternValidation, TypeKeySatisfiesCoverage) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { int a; int b; } pair_t;\n"
      "  pair_t s = '{int: 0};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StructPatternValidation, MemberAndTypeKeyCoverage) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { int a; int b; } pair_t;\n"
      "  pair_t s = '{a: 1, int: 0};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StructPatternValidation, AllThreeKeyTypesCoverage) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed {\n"
      "    int a;\n"
      "    int b;\n"
      "    logic [7:0] c;\n"
      "  } s_t;\n"
      "  s_t s = '{a: 1, int: 0, default: 8'd99};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StructPatternValidation, PositionalWrongCountTooMany) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t s = '{8'h01, 8'h02, 8'h03};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "positional struct pattern has 3 elements, but struct has 2 members", 3,
      "10.9.2"));
}

TEST(StructPatternValidation, PositionalWrongCountTooFew) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t s = '{8'h01};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "positional struct pattern has 1 elements, but struct has 2 members", 3,
      "10.9.2"));
}

TEST(StructPatternSimulation, StructTypeKeyedPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "  } mixed_t;\n"
      "  mixed_t m;\n"
      "  initial begin\n"
      "    m = mixed_t'{int: 32'd99, default: 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), uint64_t{99} << 8);
}

}  // namespace
