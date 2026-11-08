#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(AssocArrayAllocation, AssignToNonexistentIntKeyCreatesEntry) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, 42);
  auto rhs = MakeLogic4VecVal(f.arena, 32, 100);
  TryAssocIndexedWrite(sel, rhs, f.ctx, f.arena);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_EQ(aa->int_data.count(42), 1u);
  EXPECT_EQ(aa->int_data[42].ToUint64(), 100u);
}

TEST(AssocArrayAllocation, AssignToNonexistentStringKeyCreatesEntry) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);

  aa->str_data["newkey"] = MakeLogic4VecVal(f.arena, 32, 77);

  ASSERT_EQ(aa->str_data.count("newkey"), 1u);
  EXPECT_EQ(aa->str_data["newkey"].ToUint64(), 77u);
}

TEST(AssocArrayAllocation, AssignToExistingKeyOverwrites) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, 5);
  auto rhs1 = MakeLogic4VecVal(f.arena, 32, 100);
  TryAssocIndexedWrite(sel, rhs1, f.ctx, f.arena);

  auto rhs2 = MakeLogic4VecVal(f.arena, 32, 200);
  TryAssocIndexedWrite(sel, rhs2, f.ctx, f.arena);

  auto* aa = f.ctx.FindAssocArray("aa");
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[5].ToUint64(), 200u);
}

TEST(AssocArrayAllocation, MultipleNonexistentKeysEachAllocated) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  for (int64_t k = 0; k < 5; ++k) {
    auto* sel = MakeAssocSelect(f.arena, k);
    auto rhs = MakeLogic4VecVal(f.arena, 32, static_cast<uint64_t>(k * 10));
    TryAssocIndexedWrite(sel, rhs, f.ctx, f.arena);
  }

  auto* aa = f.ctx.FindAssocArray("aa");
  EXPECT_EQ(aa->int_data.size(), 5u);
  for (int64_t k = 0; k < 5; ++k) {
    EXPECT_EQ(aa->int_data[k].ToUint64(), static_cast<uint64_t>(k * 10));
  }
}

TEST(AssocArrayAllocation, EndToEndAssignCreatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 55;\n"
      "    result = aa[10];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

TEST(AssocArrayAllocation, EndToEndStringKeyAssignCreatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"k\"] = 33;\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

TEST(AssocArrayAllocation, IncrementNonexistentUsesZeroDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, IncrementNonexistentUsesUserDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:10};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 11u);
}

TEST(AssocArrayAllocation, PrefixIncrementNonexistentAllocatesFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    ++aa[1];\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, DecrementNonexistentAllocatesWithDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:5};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3]--;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(AssocArrayAllocation, CompoundAddAssignNonexistentAllocates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] += 7;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(AssocArrayAllocation, CompoundAddAssignNonexistentUsesUserDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:100};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] += 7;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 107u);
}

TEST(AssocArrayAllocation, IncrementThenReadSameKey) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    aa[1]++;\n"
      "    aa[1]++;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayAllocation, AssignAfterIncrementOverwrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    aa[1] = 99;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(AssocArrayAllocation, StringKeyIncrementAllocates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"key\"]++;\n"
      "    result = aa[\"key\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, RefArgToNonexistentElementAllocatesAndPersists) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic set_ref(ref int x);\n"
      "    x = 42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    set_ref(aa[7]);\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAllocation, RefArgAllocationGrowsArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic touch(ref int x);\n"
      "  endtask\n"
      "  initial begin\n"
      "    touch(aa[9]);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, RefArgToNonexistentStringKeyAllocates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  task automatic set_ref(ref int x);\n"
      "    x = 8;\n"
      "  endtask\n"
      "  initial begin\n"
      "    set_ref(aa[\"k\"]);\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 8u);
}

TEST(AssocArrayAllocation, MemberWriteAllocatesElementThenUpdatesTheMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    result = b[2].x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(AssocArrayAllocation, MemberWriteLeavesTheOtherMemberAtItsInitialValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    result = b[2].y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayAllocation, MemberWriteAllocatesExactlyOneEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    result = b.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, MemberWriteToExistingElementKeepsTheOtherMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    b[2].y = 7;\n"
      "    result = b[2].x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(AssocArrayAllocation, MemberReadOfNonexistentElementAllocatesNothing) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int unused;\n"
      "  int result;\n"
      "  initial begin\n"
      "    unused = b[9].x;\n"
      "    result = b.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayAllocation, BitSelectWriteAllocatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][2] = 1'b1;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(AssocArrayAllocation, PartSelectWriteAllocatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][7:0] = 8'hAB;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

TEST(AssocArrayAllocation, BitSelectWriteAllocatesExactlyOneEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][2] = 1'b1;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, PartSelectWriteToExistingElementKeepsItsOtherBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 16'hFF00;\n"
      "    aa[3][3:0] = 4'hA;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFF0Au);
}

TEST(AssocArrayAllocation, RefArgAllocatesWithTheUserSpecifiedDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:9};\n"
      "  int result;\n"
      "  task automatic grab(ref int x);\n"
      "    result = x;\n"
      "  endtask\n"
      "  initial begin\n"
      "    grab(aa[7]);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(AssocArrayAllocation, PartSelectWriteLeavesTheUserDefaultIntact) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int] = '{default:16'h00FF};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][7:0] = 8'hAB;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x00FFu);
}

TEST(AssocArrayAllocation, PartSelectWriteToOneKeyLeavesAnotherKeyAlone) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int] = '{default:16'h00FF};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][7:0] = 8'hAB;\n"
      "    aa[5][15:8] = 8'hCD;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x00ABu);
}

TEST(AssocArrayAllocation, MemberWriteToOneKeyLeavesAnotherKeysMemberAtInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    b[3].y = 7;\n"
      "    result = b[3].x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, MemberWriteToASecondKeyLeavesTheFirstKeyAlone) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    b[3].y = 7;\n"
      "    result = b[2].y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayAllocation, UserDefaultDoesNotShareWithTheVariableItNames) {
  auto v = RunAndGet(
      "module t;\n"
      "  int seed = 9;\n"
      "  int aa[int] = '{default:seed};\n"
      "  int result;\n"
      "  initial begin\n"
      "    seed[3:0] = 4'hF;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(AssocArrayAllocation, StoredElementInitialValueOwnsItsWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* aa = f.ctx.FindAssocArray("b");
  ASSERT_NE(aa, nullptr);
  ASSERT_TRUE(aa->has_elem_init);
  auto* model = f.ctx.FindVariable("b");
  ASSERT_NE(model, nullptr);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(model->value, aa->elem_init));
}

TEST(AssocArrayAllocation, ClassPropertyWriteThenReadOfTheSameKeyInAMethod) {
  auto v = RunAndGet(
      "class C;\n"
      "  int aa[int];\n"
      "  function int round_trip();\n"
      "    aa[7] = 42;\n"
      "    return aa[7];\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    result = c.round_trip();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAllocation, ClassPropertyIncrementedThreeTimesInAMethod) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef enum { UVM_INFO, UVM_WARNING, UVM_ERROR, UVM_FATAL }\n"
      "    uvm_severity;\n"
      "  class srv;\n"
      "    int m_severity_count[uvm_severity];\n"
      "    function void incr_severity_count(uvm_severity s);\n"
      "      if (m_severity_count.exists(s)) m_severity_count[s]++;\n"
      "      else m_severity_count[s] = 1;\n"
      "    endfunction\n"
      "    function int get_severity_count(uvm_severity s);\n"
      "      return m_severity_count[s];\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import p::*;\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static srv o = new;\n"
      "    o.incr_severity_count(UVM_ERROR);\n"
      "    o.incr_severity_count(UVM_ERROR);\n"
      "    o.incr_severity_count(UVM_ERROR);\n"
      "    o.incr_severity_count(UVM_WARNING);\n"
      "    result = o.get_severity_count(UVM_ERROR);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayAllocation, ClassPropertyCompoundAddAssignedInAMethod) {
  auto v = RunAndGet(
      "class C;\n"
      "  int aa[string];\n"
      "  function void bump(string k);\n"
      "    aa[k] += 1;\n"
      "  endfunction\n"
      "  function int get(string k);\n"
      "    return aa[k];\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.bump(\"x\");\n"
      "    c.bump(\"x\");\n"
      "    c.bump(\"x\");\n"
      "    c.bump(\"y\");\n"
      "    result = c.get(\"x\");\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayAllocation, NestedMemberWriteAllocatesTheElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {int k; string s;} in_t;\n"
      "  typedef struct {int n; in_t in;} out_t;\n"
      "  out_t va[int];\n"
      "  out_t tmp;\n"
      "  initial begin\n"
      "    va[1].in.k = 4;\n"
      "    va[1].in.s = \"nested member\";\n"
      "    tmp = va[1];\n"
      "    $display(\"%0d %0d [%s] [%s] %0d\", va.num(), tmp.in.k, tmp.in.s,\n"
      "             va[1].in.s, va[1].in.k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 [nested member] [nested member] 4\n");
}

}  // namespace
