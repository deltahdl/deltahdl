#include <gtest/gtest.h>

#include <cstdint>
#include <utility>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ChandleDataType, ChandleNullDefault) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h == null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ChandleDataType, ChandleBooleanTestNull) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ChandleDataType, ChandleBooleanTestNonNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* handle = f.ctx.FindVariable("h");
  ASSERT_NE(handle, nullptr);
  handle->value = MakeLogic4VecVal(f.arena, 64, 0x1234u);

  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ChandleDataType, ChandleCaseEqualityNullSim) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h === null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ChandleDataType, ChandleInequalityNullSim) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h != null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ChandleDataType, ChandleCaseInequalityNullSim) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    if (h !== null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ChandleDataType, ChandleChandleAssignSim) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle a, b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    if (b == null) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

int handle_cells[3];

void* PickHandle(int32_t i) { return &handle_cells[i]; }

int32_t WhichHandle(void* h) {
  if (h == nullptr) return 0;
  for (int32_t i = 1; i < 3; ++i) {
    if (h == &handle_cells[i]) return i;
  }
  return -1;
}

TEST(ChandleDataType, AHandleFromCKeepsItsPointerInEveryPlaceItIsStored) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function chandle pick(input int i);\n"
      "  import \"DPI-C\" function int which(input chandle h);\n"
      "  class C;\n    chandle h;\n"
      "    function chandle get();\n      return h;\n    endfunction\n"
      "    function void set(chandle x);\n      h = x;\n    endfunction\n"
      "  endclass\n"
      "  typedef struct { chandle h; int k; } S;\n"
      "  chandle a, b, n, z;\n  C c = new;\n  S s;\n"
      "  int aa[chandle];\n  chandle q[$];\n"
      "  function automatic chandle pass(chandle x);\n    return x;\n"
      "  endfunction\n"
      "  task automatic out(input chandle x, output chandle y);\n"
      "    y = x;\n  endtask\n"
      "  int r_if, r_tern, r_eq, r_ne, r_ceq, r_cne, r_same, r_diff;\n"
      "  int r_back, r_prop, r_pass, r_out, r_num, r_exists;\n"
      "  int r_elem, r_queue, r_null, r_nullback, r_while;\n"
      "  initial begin\n"
      "    a = pick(1);\n    b = pick(2);\n"
      "    if (a) r_if = 1;\n    r_tern = a ? 1 : 2;\n"
      "    r_eq = a == null;\n    r_ne = a != null;\n"
      "    r_ceq = a === null;\n    r_cne = a !== null;\n"
      "    n = a;\n    r_same = n == a;\n    r_diff = a == b;\n"
      "    r_back = which(a);\n"
      "    c.set(b);\n    r_prop = which(c.get());\n"
      "    r_pass = which(pass(b));\n"
      "    out(a, z);\n    r_out = which(z);\n"
      "    aa[a] = 10;\n    aa[b] = 20;\n    aa[n] = 30;\n"
      "    r_num = aa.num();\n    r_exists = aa.exists(b);\n"
      "    r_elem = aa[a];\n"
      "    q.push_back(b);\n    r_queue = which(q[0]);\n"
      "    n = null;\n    r_null = n ? 1 : 2;\n    r_nullback = which(n);\n"
      "    while (z) begin\n      r_while++;\n      z = null;\n    end\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"pick", reinterpret_cast<void*>(&PickHandle)},
       {"which", reinterpret_cast<void*>(&WhichHandle)}},
      "subclause_06_14_handles");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  const std::pair<const char*, uint64_t> kExpected[] = {
      {"r_if", 1},   {"r_tern", 1},     {"r_eq", 0},    {"r_ne", 1},
      {"r_ceq", 0},  {"r_cne", 1},      {"r_same", 1},  {"r_diff", 0},
      {"r_back", 1}, {"r_prop", 2},     {"r_pass", 2},  {"r_out", 1},
      {"r_num", 2},  {"r_exists", 1},   {"r_elem", 30}, {"r_queue", 2},
      {"r_null", 2}, {"r_nullback", 0}, {"r_while", 1},
  };
  for (const auto& expected : kExpected) {
    SCOPED_TRACE(expected.first);
    auto* var = f.ctx.FindVariable(expected.first);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->value.ToUint64(), expected.second);
  }
}

TEST(ChandleDataType, AChandleIsNullUntilAssignedInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package k;\n  chandle h;\nendpackage\n"
                 "chandle uh;\n"
                 "class C;\n  chandle h;\n  static chandle sh;\nendclass\n"
                 "interface ifc;\n  chandle h;\nendinterface\n"
                 "module t;\n  chandle h;\n  chandle a[2];\n"
                 "  struct { chandle h; } s;\n  C c = new;\n  ifc i();\n"
                 "  if (1) begin : g\n    chandle h;\n  end\n"
                 "  function automatic int f();\n    chandle l;\n"
                 "    return l == null;\n  endfunction\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d %0d "
                 "%0d %0d %0d\", h == null, k::h == null, uh == null, "
                 "c.h == null, C::sh == null, i.h == null, "
                 "a[1] == null, s.h == null, g.h == null, f(), "
                 "h === null);\n"
                 "endmodule\n",
                 f),
      "1 1 1 1 1 1 1 1 1 1 1\n");
}

TEST(ChandleDataType,
     DISABLED_AHandleFromCKeepsItsPointerInMembersAndProperties) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function chandle pick(input int i);\n"
      "  import \"DPI-C\" function int which(input chandle h);\n"
      "  class C;\n    chandle h;\n  endclass\n"
      "  typedef struct { chandle h; int k; } S;\n"
      "  chandle b;\n  C c = new;\n  S s, u;\n"
      "  int r_pattern, r_member, r_prop;\n"
      "  initial begin\n"
      "    b = pick(2);\n"
      "    s = '{h: b, k: 0};\n    r_pattern = which(s.h);\n"
      "    u.h = b;\n    r_member = which(u.h);\n"
      "    c.h = b;\n    r_prop = which(c.h);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"pick", reinterpret_cast<void*>(&PickHandle)},
       {"which", reinterpret_cast<void*>(&WhichHandle)}},
      "subclause_06_14_member_handles");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  for (const char* name : {"r_pattern", "r_member", "r_prop"}) {
    SCOPED_TRACE(name);
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->value.ToUint64(), 2u);
  }
}

}  // namespace
