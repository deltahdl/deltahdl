// §11.5.1 Vector bit-select and part-select addressing, for the bound the rest
// of the family does not exercise: the second one. The clause's sentence on
// printed page 296 -- "A part-select that addresses a range of bits that are
// completely out of the address bounds ... or a part-select that is x or z
// shall yield the value x when read and shall have no effect on the data
// stored when written" -- is said of the select, not of one of its two
// addresses, and "Both msb_expr and lsb_expr shall be constant integer
// expressions" makes both of them addresses. So `a[3 : 1'bx]` is as much an
// x select as `a[1'bx : 3]` is.
//
// Every case here leaves the first bound a plain constant and makes the second
// one unknown, which is what separates this file from its siblings.
// test/src/unit/test_simulator_subclause_11_05_01a.cpp is the home of the
// SelectXZHandling suite and of the rest of this subclause's simulator cases,
// and each of its five x/z cases makes the *first* bound unknown and leaves
// the second a plain literal -- three of them carry no second bound at all and
// the other two give it a known width for an indexed form.
// test/src/unit/test_simulator_subclause_11_05_01b.cpp is the declaration half
// of the clause, the ascending and non-zero-based ranges, which these are not,
// and test/src/unit/test_simulator_subclause_11_05_01c.cpp is what a select
// must not lose across a word boundary or in an unknown bit of its target.
// Those two files are 365 and 900 lines, and 01a is 884, so this family takes
// a fourth file rather than any of them taking three more cases.
//
// A case takes one of the two routes the siblings take. It runs a module
// source through RunAndFindVar in lib/cpp/test_fixtures/fixture_simulator.h
// and reads back the variable the select wrote or read into, or it builds the
// select as Expr nodes with the builders in lib/cpp/test_builders/
// builders_ast.h and calls SelectStorageBits and WriteBitSelect from
// src/simulator/statement_assign.h directly, which is the one way to hold the
// two writers of a select to the same answer within one case.

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// §11.5.1 gives a part-select that "is x or z" the value x when read. The
// second bound reached SelectBoundValue, whose Logic4Vec::ToUint64 is the
// projection src/common/types.h calls "numeric/boolean" and which reads an x
// and a z alike as 0, so `a[3 : 1'bx]` became the well-formed select `a[3:0]`
// and answered the four real bits 4'b0101 -- an answer with no unknown
// anywhere in it.
//
// `a` holds 8'hA5 rather than zeros so that the bits the wrong select names
// are not themselves all x or all 0: 4'b0101 is what the defect answers, and
// no all-zero or all-x target could tell that from a correct 4'bxxxx. The
// assertion is on Logic4Vec::ToString because ToUint64 is the very projection
// under test and reads 4'bxxxx as 0.
//
// The z companion runs in the same module because `aval & ~bval` collapses x
// and z to the same 0 and a repair that tested only for x would leave the z
// select reading real bits.
TEST(SelectXZHandling, NonIndexedPartSelectWithAnUnknownSecondBoundReadsAllX) {
  SimFixture f;
  auto* rx = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] rx;\n"
      "  logic [3:0] rz;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    rx = a[3 : 1'bx];\n"
      "    rz = a[3 : 1'bz];\n"
      "  end\n"
      "endmodule\n",
      f, "rx");
  ASSERT_NE(rx, nullptr);
  auto* rz = f.ctx.FindVariable("rz");
  ASSERT_NE(rz, nullptr);
  EXPECT_EQ(rx->value.ToString(), "xxxx");
  EXPECT_EQ(rz->value.ToString(), "xxxx");
}

// The other half of the same sentence: such a select "shall have no effect on
// the data stored when written". The value is 2'b00 into an object whose
// a[1:0] is 2'b01, so the write that must not happen would change exactly one
// bit -- neither "wrote zeros where zeros already were" nor "wrote the value's
// low bits" can satisfy the assertion.
//
// This is the write companion of PartSelectXZIndexWriteNoEffect in
// test_simulator_subclause_11_05_01a.cpp with the unknown moved from the first
// bound to the second.
TEST(SelectXZHandling, NonIndexedPartSelectWithAnUnknownSecondBoundWritesNone) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    a[1 : 1'bx] = 2'b00;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "10100101");
}

// The rule the two writers of a select have to answer alike: a select whose
// address is unknown names no window, so SelectStorageBits reports a width of
// zero -- which is what the continuous-assignment driver reads to drive
// nothing -- and WriteBitSelect, which every procedural spelling of an
// assignment passes through, stores nothing. Asserting both of one Expr in one
// case is what states it; either half alone passes on a tree where only one
// writer was corrected.
TEST(SelectXZHandling, PartSelectWithAnUnknownSecondBoundAgreesAcrossWriters) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("wsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xA5);
  MakeVar4(f, "wsb", 1, 0, 1);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "wsv");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeId(f.arena, "wsb");

  EXPECT_EQ(SelectStorageBits(*v, sel, f.ctx, f.arena).width, 0u);
  WriteBitSelect(v, sel, MakeLogic4VecVal(f.arena, 2, 0), f.ctx, f.arena);
  EXPECT_EQ(v->value.ToString(), "10100101");
}

}  // namespace
