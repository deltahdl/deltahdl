#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DataHidingSimulation, PublicPropertyReadWriteAtRuntime) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.x = 7;\n"
                      "    result = p.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(DataHidingSimulation, LocalPropertyIsRealRuntimeStorage) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  local int secret;\n"
                      "  function void store(int v);\n"
                      "    secret = v;\n"
                      "  endfunction\n"
                      "  function int fetch();\n"
                      "    return secret;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.store(42);\n"
                      "    result = p.fetch();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(DataHidingSimulation, CrossInstanceLocalCompareEqualReturnsOne) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  local int i;\n"
                      "  function void set_i(int v);\n"
                      "    i = v;\n"
                      "  endfunction\n"
                      "  function int compare(Packet other);\n"
                      "    return (this.i == other.i);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet a;\n"
                      "    Packet b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.set_i(5);\n"
                      "    b.set_i(5);\n"
                      "    result = a.compare(b);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(DataHidingSimulation, CrossInstanceLocalCompareUnequalReturnsZero) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  local int i;\n"
                      "  function void set_i(int v);\n"
                      "    i = v;\n"
                      "  endfunction\n"
                      "  function int compare(Packet other);\n"
                      "    return (this.i == other.i);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet a;\n"
                      "    Packet c;\n"
                      "    a = new;\n"
                      "    c = new;\n"
                      "    a.set_i(5);\n"
                      "    c.set_i(9);\n"
                      "    result = a.compare(c);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(DataHidingSimulation, ProtectedMemberInheritedRuntime) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  protected int hidden;\n"
                      "  function void set_hidden(int v);\n"
                      "    hidden = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function int read_hidden();\n"
                      "    return hidden;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    d.set_hidden(99);\n"
                      "    result = d.read_hidden();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(DataHidingSimulation, InheritedPublicMethodAccessesBaseLocal) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  local int secret;\n"
                      "  function void store(int v);\n"
                      "    secret = v;\n"
                      "  endfunction\n"
                      "  function int fetch();\n"
                      "    return secret;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    d.store(33);\n"
                      "    result = d.fetch();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

TEST(DataHidingSimulation, InheritedProtectedMethodCalledFromSubclass) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  protected function int secret();\n"
                      "    return 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function int reveal();\n"
                      "    return secret();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    result = d.reveal();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(DataHidingSimulation, UnqualifiedVirtualCallDispatchesOnObjectType) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  virtual function int step();\n"
                      "    return 1;\n"
                      "  endfunction\n"
                      "  function int run();\n"
                      "    return step();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  virtual function int step();\n"
                      "    return 7;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    result = d.run();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(DataHidingSimulation, ClassParametersAreReadFromOutside) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(int N = 4);\n"
      "  localparam int M = N * 3;\n"
      "endclass\n"
      "class D;\n"
      "  parameter int P = 5;\n"
      "  localparam int Q = 6;\n"
      "endclass\n"
      "module m;\n"
      "  C #(7) c = new;\n"
      "  D d = new;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  initial begin\n"
      "    r1 = c.N; r2 = c.M; r3 = C#(9)::N; r4 = C#(9)::M;\n"
      "    r5 = d.P + D::Q; r6 = d.Q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 7u},
                    {"r2", 21u},
                    {"r3", 9u},
                    {"r4", 27u},
                    {"r5", 11u},
                    {"r6", 6u}});
}

}  // namespace
